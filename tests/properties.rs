//! Property tests for the invariants in `dev/DIRECTIVES.md` §4.
//!
//! - A typed generator builds well-typed programs from a stream of choices;
//!   each checks with no diagnostics and every generated expression gets
//!   exactly the type the generator meant.
//! - Mutating one numeric literal of such a program into `true` produces
//!   exactly one diagnostic, at that literal.
//! - Replacing one leaf by an error node produces no diagnostic at all
//!   (error-type containment).
//! - Checking is deterministic, and the dynamic discipline accepts every
//!   generated program.
//!
//! Arbitrary (not well-typed) HIR is covered by `tests/arbitrary.rs`.

mod common;

use common::Kit;
use hir_lang::{
    BinderId, Expr, ExprId, ItemId, Member, NodeRef, OpKind, ParamKind, Prim, Span, Ty, TyId,
};
use proptest::prelude::*;
use typeck_lang::{Profile, Type, TypeId, Types, check};

// ------------------------------------------------------------ the generator

#[derive(Clone, Debug, PartialEq)]
enum T {
    I32,
    I64,
    F64,
    Bool,
    Tup(Vec<T>),
    Arr(Box<T>, u8),
    /// `struct R { a: i64, b: bool }` (with `impl R { fn get(self) -> i64 }`).
    Rec,
    /// `enum O { Some(i64), None }`.
    Opt,
}

impl T {
    fn is_numeric(&self) -> bool {
        matches!(self, T::I32 | T::I64 | T::F64)
    }

    fn mentions_i32(&self) -> bool {
        match self {
            T::I32 => true,
            T::Tup(ts) => ts.iter().any(T::mentions_i32),
            T::Arr(t, _) => t.mentions_i32(),
            _ => false,
        }
    }
}

/// What a generated expression's context does with it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Ctx {
    /// It has an expected type (an annotation, a parameter, a branch of an
    /// expression that has one).
    Expect,
    /// It is an operand: its class is checked where it stands.
    Operand,
    /// Only joined with siblings.
    Free,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mutation {
    None,
    /// The `n`th numeric literal becomes `true`.
    Bool(usize),
    /// The `n`th leaf becomes an error node.
    Err(usize),
}

struct Gen<'c> {
    k: Kit,
    choices: &'c [u8],
    pos: usize,
    scope: Vec<(BinderId, T)>,
    fns: Vec<(ItemId, Vec<T>, T)>,
    expected: Vec<(ExprId, T)>,
    /// Numeric literal leaves in generation order: whether a mutation there
    /// is blamed on the leaf itself.
    numeric_leaves: Vec<bool>,
    leaves: usize,
    mutation: Mutation,
    mutated: Option<ExprId>,
    /// The `r.get()` calls made.
    method_calls: Vec<ExprId>,
    /// The fixed declarations every program starts with.
    decls: Decls,
}

/// The record, sum, and method every generated program declares.
#[derive(Clone, Copy)]
struct Decls {
    rec: ItemId,
    opt: ItemId,
    some: hir_lang::VariantId,
    none: hir_lang::VariantId,
    get: ItemId,
    imp: ItemId,
}

impl Decls {
    /// `struct R { a: i64, b: bool }`, `enum O { Some(i64), None }`,
    /// `impl R { fn get(self) -> i64 { self.a } }`.
    fn declare(k: &mut Kit) -> Self {
        let (ta, tb) = (k.prim(Prim::I64), k.prim(Prim::Bool));
        let rec = k.record("R", &[("a", ta), ("b", tb)]);
        let ts = k.prim(Prim::I64);
        let some = k.variant("Some", &[ts]);
        let none = k.variant("None", &[]);
        let opt = k.sum("O", &[some, none]);
        let (recv, me) = k.receiver(None);
        let base = k.use_(me);
        let read = k.field_expr(base, "a");
        let body = k.block(&[], Some(read));
        let ret = k.prim(Prim::I64);
        let get = k.func("get", &[recv], Some(ret), body);
        let self_ty = k.item_ty("R", rec);
        let imp = k.impl_(self_ty, &[get]);
        Self {
            rec,
            opt,
            some,
            none,
            get,
            imp,
        }
    }
}

impl<'c> Gen<'c> {
    fn new(choices: &'c [u8], mutation: Mutation) -> Self {
        let mut k = Kit::new();
        let decls = Decls::declare(&mut k);
        Self {
            method_calls: Vec::new(),
            decls,
            k,
            choices,
            pos: 0,
            scope: Vec::new(),
            fns: Vec::new(),
            expected: Vec::new(),
            numeric_leaves: Vec::new(),
            leaves: 0,
            mutation,
            mutated: None,
        }
    }

    fn pick(&mut self, n: usize) -> usize {
        let c = self.choices.get(self.pos).copied().unwrap_or(0);
        self.pos += 1;
        usize::from(c) % n.max(1)
    }

    fn ty(&mut self, depth: usize) -> T {
        match self.pick(if depth == 0 { 6 } else { 8 }) {
            0 => T::I32,
            1 => T::I64,
            2 => T::F64,
            3 => T::Bool,
            4 => T::Rec,
            5 => T::Opt,
            6 => T::Tup(vec![self.ty(depth - 1), self.ty(depth - 1)]),
            _ => T::Arr(Box::new(self.ty(depth - 1)), 1 + self.pick(3) as u8),
        }
    }

    fn annotation(&mut self, t: &T) -> TyId {
        match t {
            T::I32 => self.k.prim(Prim::I32),
            T::I64 => self.k.prim(Prim::I64),
            T::F64 => self.k.prim(Prim::F64),
            T::Bool => self.k.prim(Prim::Bool),
            T::Tup(ts) => {
                let ids: Vec<TyId> = ts.iter().map(|t| self.annotation(t)).collect();
                let list = self.k.b.list(&ids);
                self.k.ty(Ty::Tuple(list))
            }
            T::Arr(t, n) => {
                let elem = self.annotation(t);
                let len = self.k.int(i64::from(*n));
                self.k.ty(Ty::Array { elem, len })
            }
            T::Rec => self.k.item_ty("R", self.decls.rec),
            T::Opt => self.k.item_ty("O", self.decls.opt),
        }
    }

    fn record(&mut self, e: ExprId, t: &T) -> ExprId {
        if self.mutated != Some(e) {
            self.expected.push((e, t.clone()));
        }
        e
    }

    fn var_of(&mut self, t: &T) -> Option<BinderId> {
        let candidates: Vec<BinderId> = self
            .scope
            .iter()
            .filter(|(_, vt)| vt == t)
            .map(|(b, _)| *b)
            .collect();
        if candidates.is_empty() {
            return None;
        }
        let i = self.pick(candidates.len());
        candidates.get(i).copied()
    }

    /// A leaf of type `t`.
    fn leaf(&mut self, t: &T, ctx: Ctx) -> ExprId {
        let use_var = self.pick(3) == 0;
        if use_var {
            if let Some(b) = self.var_of(t) {
                let index = self.leaves;
                self.leaves += 1;
                if self.mutation == Mutation::Err(index) {
                    let e = self.k.expr(Expr::Err);
                    self.mutated = Some(e);
                    return e;
                }
                let e = self.k.use_(b);
                return self.record(e, t);
            }
        }
        match t {
            T::I32 | T::I64 | T::F64 | T::Bool => {
                let value = self.pick(200) as i64;
                let index = self.leaves;
                self.leaves += 1;
                if self.mutation == Mutation::Err(index) {
                    let e = self.k.expr(Expr::Err);
                    self.mutated = Some(e);
                    return e;
                }
                if t.is_numeric() {
                    let n = self.numeric_leaves.len();
                    self.numeric_leaves.push(ctx != Ctx::Free);
                    if self.mutation == Mutation::Bool(n) {
                        let e = self.k.bool(true);
                        self.mutated = Some(e);
                        return e;
                    }
                }
                let e = match t {
                    T::F64 => self.k.float(value as f64 + 0.5),
                    T::Bool => self.k.bool(value % 2 == 0),
                    _ => self.k.int(value),
                };
                self.record(e, t)
            }
            T::Tup(ts) => {
                let inner = if ctx == Ctx::Expect {
                    Ctx::Expect
                } else {
                    Ctx::Free
                };
                let elems: Vec<ExprId> = ts.iter().map(|t| self.leaf(t, inner)).collect();
                let list = self.k.b.list(&elems);
                let e = self.k.expr(Expr::Tuple(list));
                self.record(e, t)
            }
            T::Arr(et, n) => {
                let inner = if ctx == Ctx::Expect {
                    Ctx::Expect
                } else {
                    Ctx::Free
                };
                let elems: Vec<ExprId> = (0..*n).map(|_| self.leaf(et, inner)).collect();
                let list = self.k.b.list(&elems);
                let e = self.k.expr(Expr::Array(list));
                self.record(e, t)
            }
            T::Rec => {
                // R { a: .., b: .. }: field values always meet field types.
                let a = self.leaf(&T::I64, Ctx::Expect);
                let b = self.leaf(&T::Bool, Ctx::Expect);
                let n = self.k.name("R");
                let def = self.k.b.def(hir_lang::Def::Item(self.decls.rec));
                let path = self
                    .k
                    .b
                    .resolved_path(n, hir_lang::Ns::Type, hir_lang::Res::Def(def));
                let (ai, bi) = (self.k.ident("a"), self.k.ident("b"));
                let fields = self.k.b.list(&[
                    hir_lang::FieldInit { name: ai, value: a },
                    hir_lang::FieldInit { name: bi, value: b },
                ]);
                let e = self.k.expr(Expr::Record {
                    path: Some(path),
                    fields,
                    base: None,
                });
                self.record(e, t)
            }
            T::Opt => {
                let e = if self.pick(2) == 0 {
                    self.k.variant_expr("None", self.decls.none)
                } else {
                    // Some(..): the argument meets the constructor's field.
                    let v = self.leaf(&T::I64, Ctx::Expect);
                    let callee = self.k.variant_expr("Some", self.decls.some);
                    self.k.b.call(callee, &[v])
                };
                self.record(e, t)
            }
        }
    }

    fn expr(&mut self, t: &T, depth: usize, ctx: Ctx) -> ExprId {
        if depth == 0 {
            return self.leaf(t, ctx);
        }
        let branch = if ctx == Ctx::Expect {
            Ctx::Expect
        } else {
            Ctx::Free
        };
        let d = depth - 1;
        let e = match self.pick(10) {
            // An arithmetic operation.
            1 if t.is_numeric() => {
                let op = [
                    OpKind::Add,
                    OpKind::Sub,
                    OpKind::Mul,
                    OpKind::Min,
                    OpKind::Max,
                ][self.pick(5)];
                let a = self.expr(t, d, Ctx::Operand);
                let b = self.expr(t, d, Ctx::Operand);
                self.k.op(op, &[a, b])
            }
            1 if *t == T::Bool => {
                let op = [OpKind::Lt, OpKind::Le, OpKind::Gt, OpKind::Ge][self.pick(4)];
                let a = self.expr(&T::I64, d, Ctx::Operand);
                let b = self.expr(&T::I64, d, Ctx::Operand);
                self.k.op(op, &[a, b])
            }
            2 => {
                let cond = self.expr(&T::Bool, d, Ctx::Expect);
                let then = self.expr(t, d, branch);
                let other = self.expr(t, d, branch);
                self.k.expr(Expr::If {
                    cond,
                    then,
                    else_: Some(other),
                })
            }
            3 => {
                // { let v: U = e; tail }
                let u = self.ty(1);
                let ann = self.annotation(&u);
                let init = self.expr(&u, d, Ctx::Expect);
                let (s, v) = self.k.let_("v", Some(ann), Some(init));
                self.scope.push((v, u));
                let tail = self.expr(t, d, branch);
                let _ = self.scope.pop();
                self.k.block(&[s], Some(tail))
            }
            4 => {
                let candidates: Vec<usize> = (0..self.fns.len())
                    .filter(|&i| self.fns[i].2 == *t)
                    .collect();
                match candidates.get(self.pick(candidates.len().max(1))) {
                    Some(&i) => {
                        let (item, params, _) = self.fns[i].clone();
                        let args: Vec<ExprId> = params
                            .iter()
                            .map(|p| self.expr(p, d, Ctx::Expect))
                            .collect();
                        self.k.call_item("h", item, &args)
                    }
                    None => return self.leaf(t, ctx),
                }
            }
            5 => {
                // v.i on a tuple variable holding a `t`.
                let found = self.scope.iter().find_map(|(b, vt)| match vt {
                    T::Tup(ts) => ts.iter().position(|x| x == t).map(|i| (*b, i)),
                    _ => None,
                });
                match found {
                    Some((b, i)) => {
                        let base = self.k.use_(b);
                        self.k.expr(Expr::Field {
                            base,
                            member: Member::Index(i as u32),
                            span: Span::empty(0),
                        })
                    }
                    None => return self.leaf(t, ctx),
                }
            }
            6 => {
                // a[i] on an array of `t`s: a variable, else an array expression.
                let found = self.scope.iter().find_map(|(b, vt)| match vt {
                    T::Arr(et, _) if **et == *t => Some(*b),
                    _ => None,
                });
                let base = match found {
                    Some(b) => self.k.use_(b),
                    None => {
                        let arr = T::Arr(Box::new(t.clone()), 2);
                        self.expr(&arr, d, Ctx::Free)
                    }
                };
                let index = self.expr(&T::I64, 0, Ctx::Operand);
                self.k.expr(Expr::Index { base, index })
            }
            7 if matches!(t, T::I32 | T::I64 | T::F64) => {
                let a = self.expr(t, d, Ctx::Operand);
                self.k.op(OpKind::Neg, &[a])
            }
            7 if *t == T::Bool => {
                let a = self.expr(&T::Bool, d, Ctx::Expect);
                let b = self.expr(&T::Bool, d, Ctx::Expect);
                // `and` on bools; `bool` operands are not mutated.
                self.k.op(OpKind::And, &[a, b])
            }
            8 if matches!(t, T::I64 | T::Bool) => {
                // `r.a`, `r.get()`, `r.b` on a record: a variable, else a record
                // expression.
                let base = match self.var_of(&T::Rec) {
                    Some(r) => self.k.use_(r),
                    None => self.expr(&T::Rec, d, Ctx::Free),
                };
                match t {
                    T::Bool => self.k.field_expr(base, "b"),
                    _ if self.pick(2) == 0 => self.k.field_expr(base, "a"),
                    _ => {
                        let call = self.k.method_call(base, "get", &[]);
                        self.method_calls.push(call);
                        call
                    }
                }
            }
            9 => {
                // match o { Some(x) => .., None => .. }, `x` in scope in the
                // first arm.
                let scrutinee = self.expr(&T::Opt, d, Ctx::Free);
                let (x, xp) = self.k.local("x");
                let n = self.k.name("Some");
                let def = self.k.b.def(hir_lang::Def::Variant(self.decls.some));
                let sp = self
                    .k
                    .b
                    .resolved_path(n, hir_lang::Ns::Pattern, hir_lang::Res::Def(def));
                let elems = self.k.b.list(&[xp]);
                let some_pat = self.k.b.pat(hir_lang::Pat::Ctor {
                    path: sp,
                    elems,
                    rest: None,
                });
                self.scope.push((x, T::I64));
                let first = self.expr(t, d, branch);
                let _ = self.scope.pop();
                let n = self.k.name("None");
                let def = self.k.b.def(hir_lang::Def::Variant(self.decls.none));
                let np = self
                    .k
                    .b
                    .resolved_path(n, hir_lang::Ns::Pattern, hir_lang::Res::Def(def));
                let none_pat = self.k.b.pat(hir_lang::Pat::Path(np));
                let second = self.expr(t, d, branch);
                let arms = self.k.b.list(&[
                    hir_lang::Arm {
                        pat: some_pat,
                        guard: None,
                        body: first,
                    },
                    hir_lang::Arm {
                        pat: none_pat,
                        guard: None,
                        body: second,
                    },
                ]);
                self.k.expr(Expr::Match { scrutinee, arms })
            }
            _ => return self.leaf(t, ctx),
        };
        self.record(e, t)
    }

    /// Helper functions, then `main` with a run of `let`s.
    fn program(mut self) -> Program {
        let n_fns = self.pick(3);
        let d = self.decls;
        let mut items = vec![d.rec, d.opt, d.imp];
        for _ in 0..n_fns {
            let params: Vec<T> = (0..self.pick(3)).map(|_| self.ty(1)).collect();
            let ret = self.ty(1);
            let mut pids = Vec::new();
            for p in &params {
                let ann = self.annotation(p);
                let (pid, b) = self.k.param("p", Some(ann), ParamKind::Normal, None);
                pids.push(pid);
                self.scope.push((b, p.clone()));
            }
            let body_expr = self.expr(&ret, 3, Ctx::Expect);
            self.scope.clear();
            let body = self.k.block(&[], Some(body_expr));
            let ann = self.annotation(&ret);
            let f = self.k.func("h", &pids, Some(ann), body);
            items.push(f);
            self.fns.push((f, params, ret));
        }
        let mut stmts = Vec::new();
        for _ in 0..1 + self.pick(6) {
            let t = self.ty(2);
            let annotate = t.mentions_i32() || self.pick(2) == 0;
            let ctx = if annotate { Ctx::Expect } else { Ctx::Free };
            let init = self.expr(&t, 3, ctx);
            let ann = annotate.then(|| self.annotation(&t));
            let (s, b) = self.k.let_("v", ann, Some(init));
            stmts.push(s);
            self.scope.push((b, t));
        }
        let body = self.k.block(&stmts, None);
        let main = self.k.func("main", &[], None, body);
        items.push(main);
        let root = self.k.b.module(None, &items);
        let hir = self.k.b.finish(root).expect("generated HIR validates");
        Program {
            method_calls: self.method_calls,
            decls: d,
            hir,
            expected: self.expected,
            numeric_leaves: self.numeric_leaves,
            leaves: self.leaves,
            mutated: self.mutated,
        }
    }
}

struct Program {
    method_calls: Vec<ExprId>,
    decls: Decls,
    hir: hir_lang::Hir,
    expected: Vec<(ExprId, T)>,
    numeric_leaves: Vec<bool>,
    leaves: usize,
    mutated: Option<ExprId>,
}

fn generate(choices: &[u8], mutation: Mutation) -> Program {
    Gen::new(choices, mutation).program()
}

/// Whether type `id` is the generator's type `t`.
fn is(types: &Types, decls: &Decls, id: TypeId, t: &T) -> bool {
    match (types.get(id), t) {
        (Type::Adt { item: i, .. }, T::Rec) => i == decls.rec,
        (Type::Adt { item: i, .. }, T::Opt) => i == decls.opt,
        (Type::Prim(Prim::I32), T::I32)
        | (Type::Prim(Prim::I64), T::I64)
        | (Type::Prim(Prim::F64), T::F64)
        | (Type::Prim(Prim::Bool), T::Bool) => true,
        (Type::Tuple(ids), T::Tup(ts)) => {
            ids.len() == ts.len() && ids.iter().zip(ts).all(|(&i, t)| is(types, decls, i, t))
        }
        (Type::Array { elem, len }, T::Arr(t, n)) => {
            len == u64::from(*n) && is(types, decls, elem, t)
        }
        _ => false,
    }
}

fn live_exprs(hir: &hir_lang::Hir) -> Vec<ExprId> {
    let mut out = Vec::new();
    hir_lang::walk(hir, |n| {
        if let NodeRef::Expr(e) = n {
            out.push(e);
        }
    });
    out
}

fn choices() -> impl Strategy<Value = Vec<u8>> {
    proptest::collection::vec(any::<u8>(), 0..160)
}

proptest! {
    // Some generated programs have no literal whose mutation is blamed on
    // the literal itself; those are rejected, so allow plenty of rejects.
    #![proptest_config(ProptestConfig { cases: 512, max_global_rejects: 1 << 20, ..ProptestConfig::default() })]

    /// Well-typed programs check clean, with exactly the generated types.
    #[test]
    fn prop_well_typed_programs_get_their_types(c in choices()) {
        let p = generate(&c, Mutation::None);
        let typed = check(&p.hir, &Profile::static_explicit()).unwrap();
        prop_assert!(typed.is_ok(), "{:?}", typed.diagnostics());
        for (e, t) in &p.expected {
            let got = typed.expr(*e);
            prop_assert!(got.is_some_and(|id| is(typed.types(), &p.decls, id, t)), "{:?}: {:?} vs {:?}", e, got.map(|g| typed.types().get(g)), t);
        }
        for e in live_exprs(&p.hir) {
            prop_assert!(typed.expr(e).is_some());
        }
        for &call in &p.method_calls {
            prop_assert_eq!(typed.method(call), Some(p.decls.get));
        }
    }

    /// One wrong literal: one diagnostic, at that literal.
    #[test]
    fn prop_mutations_are_reported_at_the_mutation_site(c in choices(), pick in any::<u16>()) {
        let clean = generate(&c, Mutation::None);
        let blamed: Vec<usize> = clean.numeric_leaves.iter().enumerate().filter(|(_, b)| **b).map(|(i, _)| i).collect();
        prop_assume!(!blamed.is_empty());
        let target = blamed[usize::from(pick) % blamed.len()];
        let p = generate(&c, Mutation::Bool(target));
        let site = p.mutated.expect("the mutation happened");
        let typed = check(&p.hir, &Profile::static_explicit()).unwrap();
        prop_assert_eq!(typed.diagnostics().len(), 1, "{:?}", typed.diagnostics());
        prop_assert_eq!(typed.diagnostics()[0].node, NodeRef::Expr(site));
    }

    /// An error node anywhere produces no diagnostic.
    #[test]
    fn prop_error_nodes_are_contained(c in choices(), pick in any::<u16>()) {
        let clean = generate(&c, Mutation::None);
        prop_assume!(clean.leaves > 0);
        let p = generate(&c, Mutation::Err(usize::from(pick) % clean.leaves));
        prop_assert!(p.mutated.is_some());
        let typed = check(&p.hir, &Profile::static_explicit()).unwrap();
        prop_assert!(typed.is_ok(), "{:?}", typed.diagnostics());
    }

    /// Same input, same result; the dynamic discipline accepts every
    /// generated program, mutated or not, and types every value `any`.
    #[test]
    fn prop_deterministic_and_dynamic_accepts(c in choices(), pick in any::<u16>()) {
        let clean = generate(&c, Mutation::None);
        let n = clean.numeric_leaves.len().max(1);
        let p = generate(&c, Mutation::Bool(usize::from(pick) % n));
        for profile in [Profile::static_explicit(), Profile::dynamic()] {
            let a = check(&p.hir, &profile).unwrap();
            let b = check(&generate(&c, Mutation::Bool(usize::from(pick) % n)).hir, &profile).unwrap();
            prop_assert_eq!(&a, &b);
        }
        let dynamic = check(&p.hir, &Profile::dynamic()).unwrap();
        prop_assert!(dynamic.is_ok());
        for e in live_exprs(&p.hir) {
            prop_assert_eq!(dynamic.expr(e), Some(TypeId::ANY));
        }
    }
}

/// The generator is not vacuous: across seeds it produces every form the
/// properties claim to cover.
#[test]
fn test_generator_covers_the_forms() {
    use proptest::strategy::ValueTree;
    let mut runner = proptest::test_runner::TestRunner::deterministic();
    let strategy = choices();
    let mut seen = [0usize; 7];
    for _ in 0..500 {
        let c = strategy.new_tree(&mut runner).unwrap().current();
        let p = generate(&c, Mutation::None);
        let mut here = [false; 7];
        for e in live_exprs(&p.hir) {
            let slot = match p.hir.expr(e) {
                Expr::Match { .. } => 0,
                Expr::Record { .. } => 1,
                Expr::MethodCall { .. } => 2,
                Expr::Call { .. } => 3,
                Expr::If { .. } => 4,
                Expr::Index { .. } => 5,
                Expr::Field { .. } => 6,
                _ => continue,
            };
            here[slot] = true;
        }
        for (s, h) in seen.iter_mut().zip(here) {
            *s += usize::from(h);
        }
    }
    assert!(
        seen.iter().all(|&n| n >= 25),
        "programs containing match/record/method/call/if/index/field: {seen:?}"
    );
}
