//! Property tests for the `static-inferred` discipline: a typed generator
//! builds well-typed programs over generic declarations (a generic record
//! with a generic impl, a generic sum, interfaces with a default method, an
//! associated type and a bounded generic impl, generic functions with
//! bounds, closures whose signatures are inferred), and records what every
//! expression's type, every method call's target, and the plan's instances
//! must be.
//!
//! - Well-typed programs check clean, every generated expression has
//!   exactly the generated type (generic arguments included), every method
//!   call resolves to the expected method (an impl's, a generic impl's, or an
//!   interface's default), and the monomorphization plan has an instance for
//!   every generic call with exactly the generated arguments.
//! - One wrong literal where an expectation reaches it (through generic
//!   calls by bidirectional checking, record literals, constructors,
//!   closures' operands) gives exactly one diagnostic, at the literal.
//! - Error nodes anywhere give no diagnostic.
//! - Checking is deterministic.

mod common;

use common::Kit;
use hir_lang::{BinderId, Expr, ExprId, ItemId, NodeRef, OpKind, ParamKind, Prim, Res, TyId};
use proptest::prelude::*;
use typeck_lang::{Profile, Type, TypeId, Types, check};

#[derive(Clone, Debug, PartialEq)]
enum G {
    I64,
    F64,
    Bool,
    /// `Box<T>`.
    Bx(Box<G>),
    /// `Opt<T>`.
    Opt(Box<G>),
    /// `(A, B)`.
    Pair(Box<G>, Box<G>),
}

impl G {
    fn numeric(&self) -> bool {
        matches!(self, G::I64 | G::F64)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Ctx {
    /// A concrete expected type reaches the expression when it is checked.
    Expect,
    /// An operand of an arithmetic operation.
    Operand,
    /// Nothing constrains it where it stands.
    Free,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mutation {
    None,
    Bool(usize),
    Err(usize),
}

/// The declarations every program starts with.
#[derive(Clone, Copy)]
struct Decls {
    bx: ItemId,
    get: ItemId,
    opt: ItemId,
    some: hir_lang::VariantId,
    none: hir_lang::VariantId,
    show_i64: ItemId,
    show_bool: ItemId,
    show_box: ItemId,
    twice: ItemId,
    id: ItemId,
    pair: ItemId,
    describe: ItemId,
    first: ItemId,
    apply: ItemId,
}

impl Decls {
    #[allow(clippy::too_many_lines)]
    fn declare(k: &mut Kit, items: &mut Vec<ItemId>) -> Self {
        // struct Box<T> { val: T }  impl<T> Box<T> { fn get(self) -> T { self.val } }
        let t = k.type_param("T");
        let gp = k.gparam(t, &[]);
        let g = k.generics(&[gp], &[]);
        let tt = k.tp("T", t);
        let bx = k.grecord("Box", g, &[("val", tt)]);
        let u = k.type_param("U");
        let gp = k.gparam(u, &[]);
        let g = k.generics(&[gp], &[]);
        let ut = k.tp("U", u);
        let self_ty = k.path_ty("Box", bx, &[ut]);
        let ret = k.tp("U", u);
        let get = k.method("get", None, &[], Some(ret), |k, me| {
            let b = k.use_(me);
            let f = k.field_expr(b, "val");
            k.block(&[], Some(f))
        });
        let box_impl = k.impl_of(g, None, self_ty, &[get]);
        // enum Opt<T> { None, Some(T) }
        let t = k.type_param("T");
        let gp = k.gparam(t, &[]);
        let g = k.generics(&[gp], &[]);
        let none = k.variant("None", &[]);
        let tt = k.tp("T", t);
        let some = k.variant("Some", &[tt]);
        let opt = k.gsum("Opt", g, &[none, some]);
        // trait Show { fn show(&self) -> i64; fn twice(&self) -> i64 { self.show() } }
        let st = k.self_ty();
        let r = k.ref_ty(false, st);
        let (recv, _) = k.receiver(Some(r));
        let ret = k.prim(Prim::I64);
        let show_decl = k.decl("show", &[recv], Some(ret));
        let st = k.self_ty();
        let r = k.ref_ty(false, st);
        let ret = k.prim(Prim::I64);
        let twice = k.method("twice", Some(r), &[], Some(ret), |k, me| {
            let b = k.use_(me);
            let c = k.method_call(b, "show", &[]);
            k.block(&[], Some(c))
        });
        let g = k.generics(&[], &[]);
        let show = k.iface("Show", g, &[], &[show_decl, twice]);
        let show_impl = |k: &mut Kit,
                         self_ty: TyId,
                         g: hir_lang::Generics,
                         body: &dyn Fn(&mut Kit, BinderId) -> ExprId| {
            let st = k.self_ty();
            let r = k.ref_ty(false, st);
            let ret = k.prim(Prim::I64);
            let m = k.method("show", Some(r), &[], Some(ret), |k, me| body(k, me));
            let it = k.path_ty("Show", show, &[]);
            (k.impl_of(g, Some(it), self_ty, &[m]), m)
        };
        let i = k.prim(Prim::I64);
        let g0 = k.generics(&[], &[]);
        let (imp_i, show_i64) = show_impl(k, i, g0, &|k, _| {
            let one = k.int(1);
            k.block(&[], Some(one))
        });
        let b = k.prim(Prim::Bool);
        let g0 = k.generics(&[], &[]);
        let (imp_b, show_bool) = show_impl(k, b, g0, &|k, _| {
            let two = k.int(2);
            k.block(&[], Some(two))
        });
        // impl<V: Show> Show for Box<V> { fn show(&self) -> i64 { self.val.show() } }
        let v = k.type_param("V");
        let sb = k.path_ty("Show", show, &[]);
        let gp = k.gparam(v, &[sb]);
        let g = k.generics(&[gp], &[]);
        let vt = k.tp("V", v);
        let bvt = k.path_ty("Box", bx, &[vt]);
        let (imp_box, show_box) = show_impl(k, bvt, g, &|k, me| {
            let b = k.use_(me);
            let f = k.field_expr(b, "val");
            let c = k.method_call(f, "show", &[]);
            k.block(&[], Some(c))
        });
        // trait Iter { type Item; fn next(&self) -> Self::Item; }
        let item = k.assoc("Item", &[], None);
        let st = k.self_ty();
        let r = k.ref_ty(false, st);
        let (recv, _) = k.receiver(Some(r));
        let ret = k.self_assoc_ty("Item");
        let next = k.decl("next", &[recv], Some(ret));
        let g = k.generics(&[], &[]);
        let iter = k.iface("Iter", g, &[], &[item, next]);
        // impl<W> Iter for Box<W> { type Item = W; fn next(&self) -> W { self.val } }
        let w = k.type_param("W");
        let gp = k.gparam(w, &[]);
        let g = k.generics(&[gp], &[]);
        let wt = k.tp("W", w);
        let g0 = k.generics(&[], &[]);
        let item_def = k.alias("Item", g0, wt);
        let st = k.self_ty();
        let r = k.ref_ty(false, st);
        let ret = k.tp("W", w);
        let next_def = k.method("next", Some(r), &[], Some(ret), |k, me| {
            let b = k.use_(me);
            let f = k.field_expr(b, "val");
            k.block(&[], Some(f))
        });
        let it = k.path_ty("Iter", iter, &[]);
        let wt = k.tp("W", w);
        let bw = k.path_ty("Box", bx, &[wt]);
        let imp_iter = k.impl_of(g, Some(it), bw, &[item_def, next_def]);
        // fn id<T>(x: T) -> T { x }
        let t = k.type_param("T");
        let gp = k.gparam(t, &[]);
        let g = k.generics(&[gp], &[]);
        let tt = k.tp("T", t);
        let (p, x) = k.param("x", Some(tt), ParamKind::Normal, None);
        let ux = k.use_(x);
        let body = k.block(&[], Some(ux));
        let ret = k.tp("T", t);
        let id = k.gfunc("id", g, &[p], Some(ret), body);
        // fn pair<A, B>(a: A, b: B) -> (A, B) { (a, b) }
        let a = k.type_param("A");
        let bb = k.type_param("B");
        let (ga, gb) = (k.gparam(a, &[]), k.gparam(bb, &[]));
        let g = k.generics(&[ga, gb], &[]);
        let at = k.tp("A", a);
        let bt = k.tp("B", bb);
        let (pa, xa) = k.param("a", Some(at), ParamKind::Normal, None);
        let (pb, xb) = k.param("b", Some(bt), ParamKind::Normal, None);
        let (ua, ub) = (k.use_(xa), k.use_(xb));
        let tl = k.b.list(&[ua, ub]);
        let tup = k.expr(Expr::Tuple(tl));
        let body = k.block(&[], Some(tup));
        let (rat, rbt) = (k.tp("A", a), k.tp("B", bb));
        let rl = k.b.list(&[rat, rbt]);
        let ret = k.ty(hir_lang::Ty::Tuple(rl));
        let pair = k.gfunc("pair", g, &[pa, pb], Some(ret), body);
        // fn describe<T: Show>(x: T) -> i64 { x.show() }
        let t = k.type_param("T");
        let sb = k.path_ty("Show", show, &[]);
        let gp = k.gparam(t, &[sb]);
        let g = k.generics(&[gp], &[]);
        let tt = k.tp("T", t);
        let (p, x) = k.param("x", Some(tt), ParamKind::Normal, None);
        let ux = k.use_(x);
        let c = k.method_call(ux, "show", &[]);
        let body = k.block(&[], Some(c));
        let ret = k.prim(Prim::I64);
        let describe = k.gfunc("describe", g, &[p], Some(ret), body);
        // fn first<I: Iter>(i: I) -> I::Item { i.next() }
        let ib = k.type_param("I");
        let bound = k.path_ty("Iter", iter, &[]);
        let gp = k.gparam(ib, &[bound]);
        let g = k.generics(&[gp], &[]);
        let it = k.tp("I", ib);
        let (p, iv) = k.param("i", Some(it), ParamKind::Normal, None);
        let ui = k.use_(iv);
        let c = k.method_call(ui, "next", &[]);
        let body = k.block(&[], Some(c));
        let ret = k.assoc_ty("I", Res::Local(ib), "Item");
        let first = k.gfunc("first", g, &[p], Some(ret), body);
        // fn apply<T>(f: fn(T) -> T, x: T) -> T { f(x) }
        let t = k.type_param("T");
        let gp = k.gparam(t, &[]);
        let g = k.generics(&[gp], &[]);
        let (ta, tb, tc) = (k.tp("T", t), k.tp("T", t), k.tp("T", t));
        let ps = k.b.list(&[ta]);
        let fty = k.ty(hir_lang::Ty::Fn {
            params: ps,
            ret: tb,
            effects: hir_lang::Effects::NONE,
            throws: None,
            abi: None,
        });
        let (pf, f) = k.param("f", Some(fty), ParamKind::Normal, None);
        let (px, x) = k.param("x", Some(tc), ParamKind::Normal, None);
        let (uf, ux) = (k.use_(f), k.use_(x));
        let call = k.b.call(uf, &[ux]);
        let body = k.block(&[], Some(call));
        let ret = k.tp("T", t);
        let apply = k.gfunc("apply", g, &[pf, px], Some(ret), body);
        items.extend([
            bx, box_impl, opt, show, imp_i, imp_b, imp_box, iter, imp_iter, id, pair, describe,
            first, apply,
        ]);
        Decls {
            bx,
            get,
            opt,
            some,
            none,
            show_i64,
            show_bool,
            show_box,
            twice,
            id,
            pair,
            describe,
            first,
            apply,
        }
    }
}

struct Gen<'c> {
    k: Kit,
    d: Decls,
    choices: &'c [u8],
    pos: usize,
    scope: Vec<(BinderId, G)>,
    expected: Vec<(ExprId, G)>,
    /// Method calls and the method each must resolve to.
    methods: Vec<(ExprId, ItemId)>,
    /// Generic calls and the instance the plan must contain.
    instances: Vec<(ItemId, Vec<G>)>,
    numeric_leaves: Vec<bool>,
    leaves: usize,
    mutation: Mutation,
    mutated: Option<ExprId>,
    items: Vec<ItemId>,
}

impl<'c> Gen<'c> {
    fn new(choices: &'c [u8], mutation: Mutation) -> Self {
        let mut k = Kit::new();
        let mut items = Vec::new();
        let d = Decls::declare(&mut k, &mut items);
        Self {
            k,
            d,
            choices,
            pos: 0,
            scope: Vec::new(),
            expected: Vec::new(),
            methods: Vec::new(),
            instances: Vec::new(),
            numeric_leaves: Vec::new(),
            leaves: 0,
            mutation,
            mutated: None,
            items,
        }
    }

    fn pick(&mut self, n: usize) -> usize {
        let c = self.choices.get(self.pos).copied().unwrap_or(0);
        self.pos += 1;
        usize::from(c) % n.max(1)
    }

    fn ty(&mut self, depth: usize) -> G {
        match self.pick(if depth == 0 { 3 } else { 6 }) {
            0 => G::I64,
            1 => G::F64,
            2 => G::Bool,
            3 => G::Bx(Box::new(self.ty(depth - 1))),
            4 => G::Opt(Box::new(self.ty(depth - 1))),
            _ => G::Pair(Box::new(self.ty(depth - 1)), Box::new(self.ty(depth - 1))),
        }
    }

    fn showable(&mut self) -> G {
        match self.pick(4) {
            0 => G::I64,
            1 => G::Bool,
            2 => G::Bx(Box::new(G::I64)),
            _ => G::Bx(Box::new(G::Bx(Box::new(G::Bool)))),
        }
    }

    fn annotation(&mut self, t: &G) -> TyId {
        match t {
            G::I64 => self.k.prim(Prim::I64),
            G::F64 => self.k.prim(Prim::F64),
            G::Bool => self.k.prim(Prim::Bool),
            G::Bx(u) => {
                let a = self.annotation(u);
                self.k.path_ty("Box", self.d.bx, &[a])
            }
            G::Opt(u) => {
                let a = self.annotation(u);
                self.k.path_ty("Opt", self.d.opt, &[a])
            }
            G::Pair(a, b) => {
                let (x, y) = (self.annotation(a), self.annotation(b));
                let l = self.k.b.list(&[x, y]);
                self.k.ty(hir_lang::Ty::Tuple(l))
            }
        }
    }

    fn record(&mut self, e: ExprId, t: &G) -> ExprId {
        if self.mutated != Some(e) {
            self.expected.push((e, t.clone()));
        }
        e
    }

    /// A leaf: a variable, or a literal value of `t`.
    fn leaf(&mut self, t: &G, ctx: Ctx) -> ExprId {
        if self.pick(3) == 0 {
            let vars: Vec<BinderId> = self
                .scope
                .iter()
                .filter(|(_, vt)| vt == t)
                .map(|(b, _)| *b)
                .collect();
            if !vars.is_empty() {
                let b = vars[self.pick(vars.len())];
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
        let inner = if ctx == Ctx::Expect {
            Ctx::Expect
        } else {
            Ctx::Free
        };
        match t {
            G::I64 | G::F64 | G::Bool => {
                let index = self.leaves;
                self.leaves += 1;
                if self.mutation == Mutation::Err(index) {
                    let e = self.k.expr(Expr::Err);
                    self.mutated = Some(e);
                    return e;
                }
                if t.numeric() {
                    let n = self.numeric_leaves.len();
                    self.numeric_leaves.push(ctx != Ctx::Free);
                    if self.mutation == Mutation::Bool(n) {
                        let e = self.k.bool(true);
                        self.mutated = Some(e);
                        return e;
                    }
                }
                let v = self.pick(100) as i64;
                let e = match t {
                    G::F64 => self.k.float(v as f64 + 0.5),
                    G::Bool => self.k.bool(v % 2 == 0),
                    _ => self.k.int(v),
                };
                self.record(e, t)
            }
            G::Bx(u) => {
                let v = self.leaf(u, inner);
                let e = self.box_lit(v);
                self.record(e, t)
            }
            G::Opt(u) => {
                let e = if ctx == Ctx::Expect && self.pick(2) == 0 {
                    self.k.variant_expr("None", self.d.none)
                } else {
                    let v = self.leaf(u, inner);
                    let c = self.k.variant_expr("Some", self.d.some);
                    self.k.b.call(c, &[v])
                };
                self.record(e, t)
            }
            G::Pair(a, b) => {
                let (x, y) = (self.leaf(a, inner), self.leaf(b, inner));
                let l = self.k.b.list(&[x, y]);
                let e = self.k.expr(Expr::Tuple(l));
                self.record(e, t)
            }
        }
    }

    fn box_lit(&mut self, v: ExprId) -> ExprId {
        let n = self.k.name("Box");
        let def = self.k.b.def(hir_lang::Def::Item(self.d.bx));
        let path = self.k.b.resolved_path(n, hir_lang::Ns::Type, Res::Def(def));
        let val = self.k.ident("val");
        let fields = self.k.b.list(&[hir_lang::FieldInit {
            name: val,
            value: v,
        }]);
        self.k.expr(Expr::Record {
            path: Some(path),
            fields,
            base: None,
        })
    }

    #[allow(clippy::too_many_lines)]
    fn expr(&mut self, t: &G, depth: usize, ctx: Ctx) -> ExprId {
        if depth == 0 {
            return self.leaf(t, ctx);
        }
        let d = depth - 1;
        // An argument meets a concrete expectation only if its call has one
        // (bidirectional checking through the instantiated signature).
        let through = if ctx == Ctx::Expect {
            Ctx::Expect
        } else {
            Ctx::Free
        };
        // Interface forms only type as `i64`: give them a fair share there.
        let choice = if *t == G::I64 && self.pick(3) == 0 {
            10 + self.pick(2)
        } else {
            self.pick(14)
        };
        let e = match choice {
            0 if t.numeric() => {
                let op = [OpKind::Add, OpKind::Sub, OpKind::Mul][self.pick(3)];
                let a = self.expr(t, d, Ctx::Operand);
                let b = self.expr(t, d, Ctx::Operand);
                self.k.op(op, &[a, b])
            }
            1 => {
                let cond = self.expr(&G::Bool, d, Ctx::Expect);
                let a = self.expr(t, d, through);
                let b = self.expr(t, d, through);
                self.k.expr(Expr::If {
                    cond,
                    then: a,
                    else_: Some(b),
                })
            }
            2 => {
                let u = self.ty(1);
                let ann = self.annotation(&u);
                let init = self.expr(&u, d, Ctx::Expect);
                let (s, v) = self.k.let_("v", Some(ann), Some(init));
                self.scope.push((v, u));
                let tail = self.expr(t, d, through);
                let _ = self.scope.pop();
                self.k.block(&[s], Some(tail))
            }
            3 => {
                let a = self.expr(t, d, through);
                self.instances.push((self.d.id, vec![t.clone()]));
                self.k.call_item("id", self.d.id, &[a])
            }
            4 => match t {
                G::Pair(a, b) => {
                    let (x, y) = (self.expr(a, d, through), self.expr(b, d, through));
                    self.instances
                        .push((self.d.pair, vec![(**a).clone(), (**b).clone()]));
                    self.k.call_item("pair", self.d.pair, &[x, y])
                }
                _ => return self.leaf(t, ctx),
            },
            5 => match t {
                G::Bx(u) => {
                    let v = self.expr(u, d, through);
                    self.box_lit(v)
                }
                _ => return self.leaf(t, ctx),
            },
            6 => {
                // e.get() on a `Box<t>`.
                let bt = G::Bx(Box::new(t.clone()));
                let r = self.expr(&bt, d, Ctx::Free);
                let c = self.k.method_call(r, "get", &[]);
                self.methods.push((c, self.d.get));
                self.instances.push((self.d.get, vec![t.clone()]));
                c
            }
            7 => {
                // e.val on a `Box<t>`.
                let bt = G::Bx(Box::new(t.clone()));
                let r = self.expr(&bt, d, Ctx::Free);
                self.k.field_expr(r, "val")
            }
            8 => match t {
                G::Opt(u) => {
                    let v = self.expr(u, d, through);
                    let c = self.k.variant_expr("Some", self.d.some);
                    self.k.b.call(c, &[v])
                }
                _ => return self.leaf(t, ctx),
            },
            9 => {
                // match o { Some(x) => .., None => .. }
                let u = self.ty(1);
                let ot = G::Opt(Box::new(u.clone()));
                let scrutinee = self.expr(&ot, d, Ctx::Free);
                let (x, xp) = self.k.local("x");
                let some_pat = self.k.variant_pat("Some", self.d.some, &[xp]);
                self.scope.push((x, u));
                let first = self.expr(t, d, through);
                let _ = self.scope.pop();
                let none_pat = self.k.unit_variant_pat("None", self.d.none);
                let second = self.expr(t, d, through);
                self.k
                    .match_(scrutinee, &[(some_pat, first), (none_pat, second)])
            }
            10 if *t == G::I64 => {
                let s = self.showable();
                let a = self.expr(&s, d, Ctx::Free);
                self.instances.push((self.d.describe, vec![s]));
                self.k.call_item("describe", self.d.describe, &[a])
            }
            11 if *t == G::I64 => {
                // e.show() or e.twice() on a showable value.
                let s = self.showable();
                let r = self.expr(&s, d, Ctx::Free);
                if self.pick(3) == 0 {
                    let c = self.k.method_call(r, "twice", &[]);
                    self.methods.push((c, self.d.twice));
                    c
                } else {
                    let c = self.k.method_call(r, "show", &[]);
                    let m = match s {
                        G::I64 => self.d.show_i64,
                        G::Bool => self.d.show_bool,
                        _ => self.d.show_box,
                    };
                    self.methods.push((c, m));
                    c
                }
            }
            12 => {
                // first(b) on a `Box<t>`: through the associated type.
                let bt = G::Bx(Box::new(t.clone()));
                let r = self.expr(&bt, d, Ctx::Free);
                self.instances.push((self.d.first, vec![bt]));
                self.k.call_item("first", self.d.first, &[r])
            }
            13 if t.numeric() => {
                // apply(|y| y + lit, e): the closure's parameter is inferred.
                let (py, y) = self.k.param("y", None, ParamKind::Normal, None);
                let uy = self.k.use_(y);
                let lit = self.leaf(t, Ctx::Operand);
                let add = self.k.op(OpKind::Add, &[uy, lit]);
                let clo = self.k.closure(&[py], None, add);
                let x = self.expr(t, d, through);
                self.instances.push((self.d.apply, vec![t.clone()]));
                self.k.call_item("apply", self.d.apply, &[clo, x])
            }
            _ => return self.leaf(t, ctx),
        };
        self.record(e, t)
    }

    fn program(mut self) -> Program {
        let mut stmts = Vec::new();
        for _ in 0..1 + self.pick(5) {
            let t = self.ty(2);
            let annotate = self.pick(2) == 0;
            let ctx = if annotate { Ctx::Expect } else { Ctx::Free };
            let init = self.expr(&t, 3, ctx);
            let ann = annotate.then(|| self.annotation(&t));
            let (s, b) = self.k.let_("v", ann, Some(init));
            stmts.push(s);
            self.scope.push((b, t));
        }
        let body = self.k.block(&stmts, None);
        let main = self.k.func("main", &[], None, body);
        self.items.push(main);
        let root = self.k.b.module(None, &self.items);
        let hir = self.k.b.finish(root).expect("generated HIR validates");
        Program {
            d: self.d,
            hir,
            expected: self.expected,
            methods: self.methods,
            instances: self.instances,
            numeric_leaves: self.numeric_leaves,
            leaves: self.leaves,
            mutated: self.mutated,
        }
    }
}

struct Program {
    d: Decls,
    hir: hir_lang::Hir,
    expected: Vec<(ExprId, G)>,
    methods: Vec<(ExprId, ItemId)>,
    instances: Vec<(ItemId, Vec<G>)>,
    numeric_leaves: Vec<bool>,
    leaves: usize,
    mutated: Option<ExprId>,
}

fn generate(choices: &[u8], mutation: Mutation) -> Program {
    Gen::new(choices, mutation).program()
}

/// Whether `id` is exactly the generator's type `t`.
fn is(types: &Types, d: &Decls, id: TypeId, t: &G) -> bool {
    match (types.get(id), t) {
        (Type::Prim(Prim::I64), G::I64)
        | (Type::Prim(Prim::F64), G::F64)
        | (Type::Prim(Prim::Bool), G::Bool) => true,
        (Type::Adt { item, args: [a] }, G::Bx(u)) => item == d.bx && is(types, d, *a, u),
        (Type::Adt { item, args: [a] }, G::Opt(u)) => item == d.opt && is(types, d, *a, u),
        (Type::Tuple([x, y]), G::Pair(a, b)) => is(types, d, *x, a) && is(types, d, *y, b),
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
    #![proptest_config(ProptestConfig { cases: 512, max_global_rejects: 1 << 20, ..ProptestConfig::default() })]

    /// Well-typed generic programs check clean, with exactly the generated
    /// types, method targets, and plan instances.
    #[test]
    fn prop_generic_programs_get_their_types(c in choices()) {
        let p = generate(&c, Mutation::None);
        let typed = check(&p.hir, &Profile::static_inferred()).unwrap();
        prop_assert!(typed.is_ok(), "{:?}", typed.diagnostics());
        for (e, t) in &p.expected {
            let got = typed.expr(*e);
            prop_assert!(
                got.is_some_and(|id| is(typed.types(), &p.d, id, t)),
                "{:?}: {:?} vs {:?}", e, got.map(|g| typed.types().get(g)), t
            );
        }
        for e in live_exprs(&p.hir) {
            prop_assert!(typed.expr(e).is_some());
        }
        for &(call, m) in &p.methods {
            prop_assert_eq!(typed.method(call), Some(m));
        }
        let plan = typed.mono_plan();
        for (item, args) in &p.instances {
            prop_assert!(
                plan.instances_of(*item).any(|i| i.args.len() == args.len()
                    && i.args.iter().zip(args).all(|(&a, t)| is(typed.types(), &p.d, a, t))),
                "no instance of {:?} with {:?}", item, args
            );
        }
    }

    /// One wrong literal where an expectation reaches it: one diagnostic,
    /// at that literal.
    #[test]
    fn prop_generic_mutations_are_reported_at_the_mutation_site(c in choices(), pick in any::<u16>()) {
        let clean = generate(&c, Mutation::None);
        let blamed: Vec<usize> = clean.numeric_leaves.iter().enumerate().filter(|(_, b)| **b).map(|(i, _)| i).collect();
        prop_assume!(!blamed.is_empty());
        let target = blamed[usize::from(pick) % blamed.len()];
        let p = generate(&c, Mutation::Bool(target));
        let site = p.mutated.expect("the mutation happened");
        let typed = check(&p.hir, &Profile::static_inferred()).unwrap();
        prop_assert_eq!(typed.diagnostics().len(), 1, "{:?}", typed.diagnostics());
        prop_assert_eq!(typed.diagnostics()[0].node, NodeRef::Expr(site));
    }

    /// Error nodes anywhere: no diagnostic.
    #[test]
    fn prop_generic_error_nodes_are_contained(c in choices(), pick in any::<u16>()) {
        let clean = generate(&c, Mutation::None);
        prop_assume!(clean.leaves > 0);
        let p = generate(&c, Mutation::Err(usize::from(pick) % clean.leaves));
        prop_assert!(p.mutated.is_some());
        let typed = check(&p.hir, &Profile::static_inferred()).unwrap();
        prop_assert!(typed.is_ok(), "{:?}", typed.diagnostics());
    }

    /// Same input, same result (types, diagnostics, plan).
    #[test]
    fn prop_generic_checking_is_deterministic(c in choices()) {
        let a = check(&generate(&c, Mutation::None).hir, &Profile::static_inferred()).unwrap();
        let b = check(&generate(&c, Mutation::None).hir, &Profile::static_inferred()).unwrap();
        prop_assert_eq!(a, b);
    }
}

/// The generator reaches every generic form the properties claim.
#[test]
fn test_generic_generator_covers_the_forms() {
    use proptest::strategy::ValueTree;
    let mut runner = proptest::test_runner::TestRunner::deterministic();
    let strategy = choices();
    let mut methods = [0usize; 5];
    let mut calls = [0usize; 5];
    let mut blamed_under_generic = 0;
    for _ in 0..600 {
        let c = strategy.new_tree(&mut runner).unwrap().current();
        let p = generate(&c, Mutation::None);
        let d = p.d;
        for (i, m) in [d.get, d.show_i64, d.show_bool, d.show_box, d.twice]
            .iter()
            .enumerate()
        {
            methods[i] += usize::from(p.methods.iter().any(|(_, x)| x == m));
        }
        for (i, f) in [d.id, d.pair, d.describe, d.first, d.apply]
            .iter()
            .enumerate()
        {
            calls[i] += usize::from(p.instances.iter().any(|(x, _)| x == f));
        }
        blamed_under_generic += usize::from(
            p.numeric_leaves.iter().filter(|b| **b).count() > 0 && !p.instances.is_empty(),
        );
    }
    assert!(methods.iter().all(|&n| n >= 10), "methods {methods:?}");
    assert!(calls.iter().all(|&n| n >= 20), "generic calls {calls:?}");
    assert!(blamed_under_generic >= 100, "{blamed_under_generic}");
}
