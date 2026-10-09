//! Totality on arbitrary valid HIR.
//!
//! A random tree builder makes HIR of every form with random links (paths
//! naming random binders and items, wrong shapes, wrong namespaces);
//! lenient validation repairs it into a valid `Hir`. On that, checking never
//! panics, always terminates (any budget either suffices or stops the check
//! with a budget error), types every live expression, and is deterministic.

use hir_lang::{
    Arg, ArgKind, Arm, BinderId, BinderKind, Block, Closure, Def, Effects, Expr, ExprId, FieldDef,
    FieldInit, FnDef, Ident, ImplDef, Item, ItemId, ItemKind, Lit, Member, Name, NodeRef, Ns, Op,
    OpKind, Overflow, Param, ParamKind, Pat, PatId, Prim, RecordDef, Res, Span, Stmt, StmtId,
    SumDef, Symbol, Ty, TyId, Variant,
};
use proptest::prelude::*;
use typeck_lang::{Budget, CheckError, Checker, Limit, Profile, RecordTyping, TryHook, check};

/// The kinds of a random generic-argument list.
fn alloc_args(s: &RawStep) -> Vec<u8> {
    (0..1 + s.b % 3)
        .map(|i| (s.a.wrapping_add(i)) % 3)
        .collect()
}

/// One random construction step: a form and three operands.
#[derive(Clone, Debug)]
struct RawStep {
    kind: u8,
    a: u8,
    b: u8,
    c: u8,
}

fn raw_steps() -> impl Strategy<Value = Vec<RawStep>> {
    proptest::collection::vec(
        (any::<u8>(), any::<u8>(), any::<u8>(), any::<u8>()).prop_map(|(kind, a, b, c)| RawStep {
            kind,
            a,
            b,
            c,
        }),
        0..96,
    )
}

/// Builds a tree bottom-up: each step pops its children from pools of
/// parentless nodes (making a leaf when a pool is empty) and pushes the new
/// node.
struct Random {
    b: hir_lang::Builder,
    sym: Symbol,
    exprs: Vec<ExprId>,
    pats: Vec<PatId>,
    tys: Vec<TyId>,
    stmts: Vec<StmtId>,
    params: Vec<hir_lang::ParamId>,
    items: Vec<ItemId>,
    binders: Vec<BinderId>,
    all_items: Vec<ItemId>,
}

const OPS: [OpKind; 14] = [
    OpKind::Add,
    OpKind::Sub,
    OpKind::Lt,
    OpKind::Eq,
    OpKind::Neg,
    OpKind::Shl,
    OpKind::And,
    OpKind::Not,
    OpKind::Sqrt,
    OpKind::FloorDiv,
    OpKind::IntCast(Prim::I8),
    OpKind::Sext(Prim::I64),
    OpKind::IntToFloat(Prim::F64),
    OpKind::TotalCmp,
];

const PRIMS: [Prim; 7] = [
    Prim::I32,
    Prim::I64,
    Prim::Bool,
    Prim::F64,
    Prim::U8,
    Prim::Str,
    Prim::Char,
];

impl Random {
    fn new(sym: Symbol) -> Self {
        Self {
            b: hir_lang::Builder::new(),
            sym,
            exprs: Vec::new(),
            pats: Vec::new(),
            tys: Vec::new(),
            stmts: Vec::new(),
            params: Vec::new(),
            items: Vec::new(),
            binders: Vec::new(),
            all_items: Vec::new(),
        }
    }

    fn name(&self) -> Name {
        Name::new(self.sym)
    }

    fn ident(&self, at: u32) -> Ident {
        Ident::new(self.sym, Span::empty(at))
    }

    fn expr(&mut self) -> ExprId {
        match self.exprs.pop() {
            Some(e) => e,
            None => self.b.int(1),
        }
    }

    fn exprs(&mut self, n: u8) -> Vec<ExprId> {
        (0..n % 4).map(|_| self.expr()).collect()
    }

    fn pat(&mut self) -> PatId {
        match self.pats.pop() {
            Some(p) => p,
            None => self.b.pat(Pat::Wild),
        }
    }

    fn ty(&mut self) -> TyId {
        match self.tys.pop() {
            Some(t) => t,
            None => self.b.ty(Ty::Prim(Prim::I64)),
        }
    }

    fn binder(&mut self, kind: BinderKind) -> BinderId {
        let b = self.b.binder(hir_lang::Binder::new(self.name(), kind));
        self.binders.push(b);
        b
    }

    fn path(&mut self, ns: Ns, x: u8) -> hir_lang::PathId {
        let res = match x % 6 {
            0 | 1 if !self.binders.is_empty() => {
                Res::Local(self.binders[usize::from(x) % self.binders.len()])
            }
            2 | 3 if !self.all_items.is_empty() => {
                let item = self.all_items[usize::from(x) % self.all_items.len()];
                Res::Def(self.b.def(Def::Item(item)))
            }
            4 => Res::Extern(self.sym),
            _ => Res::Unresolved,
        };
        self.b.resolved_path(self.name(), ns, res)
    }

    fn item(&mut self, item: ItemId) {
        self.items.push(item);
        self.all_items.push(item);
    }

    fn take_tail<T: Copy>(pool: &mut Vec<T>, n: u8) -> Vec<T> {
        let n = usize::from(n).min(pool.len());
        pool.split_off(pool.len() - n)
    }

    fn step(&mut self, s: &RawStep) {
        let kind = s.kind % 62;
        if kind < 29 {
            let e = self.expr_step(kind, s);
            self.exprs.push(e);
        } else if kind < 48 {
            self.other_step(kind, s);
        } else {
            self.v3_step(kind, s);
        }
    }

    /// A bound list of up to two interface-ish paths.
    fn bounds(&mut self, n: u8, x: u8) -> hir_lang::List<hir_lang::Bound> {
        let bs: Vec<hir_lang::Bound> = (0..n % 3)
            .map(|i| {
                let p = self.path(Ns::Type, x.wrapping_add(i));
                hir_lang::Bound::Ty(self.b.ty(Ty::Path(p)))
            })
            .collect();
        self.b.list(&bs)
    }

    /// Generic parameters with random bounds; the parameters' types are
    /// pushed to the type pool (they may end up out of scope, which lenient
    /// validation repairs).
    fn generics(&mut self, s: &RawStep) -> hir_lang::Generics {
        let n = s.b % 3;
        let mut params = Vec::new();
        for i in 0..n {
            let kind = if s.c % 5 == 0 {
                BinderKind::ConstParam
            } else {
                BinderKind::TypeParam
            };
            let binder = self.binder(kind);
            let bounds = self.bounds(s.a.wrapping_add(i), s.c);
            let ty = (kind == BinderKind::ConstParam).then(|| self.b.ty(Ty::Prim(Prim::Usize)));
            params.push(hir_lang::GenericParam {
                binder,
                bounds,
                ty,
                default: None,
            });
            let p = self
                .b
                .resolved_path(self.name(), Ns::Type, Res::Local(binder));
            let t = self.b.ty(Ty::Path(p));
            self.tys.push(t);
        }
        let preds = if s.a % 4 == 0 {
            let subject = hir_lang::Bound::Ty(self.ty());
            let bounds = self.bounds(1, s.b);
            self.b.list(&[hir_lang::WherePred { subject, bounds }])
        } else {
            hir_lang::List::EMPTY
        };
        hir_lang::Generics {
            params: self.b.list(&params),
            preds,
        }
    }

    /// HIR v3 forms and the generic and interface forms.
    #[allow(clippy::too_many_lines)]
    fn v3_step(&mut self, kind: u8, s: &RawStep) {
        match kind {
            48 => {
                // A generic function over the pending parameters.
                let generics = self.generics(s);
                let params = Self::take_tail(&mut self.params, s.a % 3);
                let params = self.b.list(&params);
                let ret = (s.c % 2 == 0).then(|| self.ty());
                let body = Some(self.expr());
                let item = self.b.item(Item::new(
                    Some(self.name()),
                    ItemKind::Fn(FnDef {
                        generics,
                        params,
                        ret,
                        body,
                        ..FnDef::default()
                    }),
                ));
                self.item(item);
            }
            49 => {
                // An interface with members, supertraits, and an associated
                // type.
                let generics = self.generics(s);
                let mut members = Self::take_tail(&mut self.items, s.a % 2);
                if s.c % 2 == 0 {
                    let bounds = self.bounds(s.b, s.a);
                    let default = (s.a % 3 == 0).then(|| self.ty());
                    let a = self.b.item(Item::new(
                        Some(self.name()),
                        ItemKind::AssocType { bounds, default },
                    ));
                    members.push(a);
                }
                let supers: Vec<TyId> = (0..s.b % 2)
                    .map(|_| {
                        let p = self.path(Ns::Type, s.c);
                        self.b.ty(Ty::Path(p))
                    })
                    .collect();
                let items = self.b.list(&members);
                let supers = self.b.list(&supers);
                let item = self.b.item(Item::new(
                    Some(self.name()),
                    ItemKind::Interface(hir_lang::InterfaceDef {
                        generics,
                        supers,
                        items,
                    }),
                ));
                self.item(item);
            }
            50 => {
                // An impl of an interface, possibly generic.
                let generics = self.generics(s);
                let self_ty = self.ty();
                let p = self.path(Ns::Type, s.a);
                let iface = (s.c % 3 != 0).then(|| self.b.ty(Ty::Path(p)));
                let mut members = Self::take_tail(&mut self.items, s.a % 3);
                if s.b % 2 == 0 {
                    let t = self.ty();
                    let a = self.b.item(Item::new(
                        Some(self.name()),
                        ItemKind::Alias {
                            generics: hir_lang::Generics::default(),
                            ty: t,
                        },
                    ));
                    members.push(a);
                }
                let items = self.b.list(&members);
                let item = self.b.item(Item::new(
                    None,
                    ItemKind::Impl(ImplDef {
                        generics,
                        interface: iface,
                        self_ty,
                        items,
                    }),
                ));
                self.item(item);
            }
            51 => {
                let (a, b) = (self.ty(), self.ty());
                let l = self.b.list(&[a, b]);
                let t = self.b.ty(if s.a % 2 == 0 {
                    Ty::Union(l)
                } else {
                    Ty::Intersection(l)
                });
                self.tys.push(t);
            }
            52 => {
                let bounds = self.bounds(1 + s.b % 2, s.a);
                let t = self.b.ty(if s.c % 2 == 0 {
                    Ty::Object(bounds)
                } else {
                    Ty::Impl(bounds)
                });
                self.tys.push(t);
            }
            53 => {
                // A path type with generic arguments (and an associated-type
                // binding or a constant).
                let mut args = alloc_args(s);
                let fill: Vec<hir_lang::GenericArg> = args
                    .drain(..)
                    .map(|k| match k {
                        0 => hir_lang::GenericArg::Ty(self.ty()),
                        1 => hir_lang::GenericArg::Const(self.b.int(i64::from(s.c % 5))),
                        _ => hir_lang::GenericArg::Binding {
                            name: self.ident(0),
                            ty: self.ty(),
                        },
                    })
                    .collect();
                let args = self.b.list(&fill);
                let res = match s.a % 3 {
                    0 if !self.all_items.is_empty() => {
                        let item = self.all_items[usize::from(s.b) % self.all_items.len()];
                        Res::Def(self.b.def(Def::Item(item)))
                    }
                    1 if !self.binders.is_empty() => {
                        Res::Local(self.binders[usize::from(s.b) % self.binders.len()])
                    }
                    _ => Res::Extern(self.sym),
                };
                let origin = self.b.origin();
                let seg = hir_lang::Segment {
                    args,
                    ..hir_lang::Segment::new(self.name(), origin)
                };
                let segs = if s.c % 4 == 0 {
                    vec![hir_lang::Segment::new(self.name(), origin), seg]
                } else {
                    vec![seg]
                };
                let unresolved = u32::from(segs.len() == 2);
                let segments = self.b.list(&segs);
                let p = self.b.path(hir_lang::Path {
                    res,
                    unresolved,
                    ..hir_lang::Path::new(segments, Ns::Type)
                });
                let t = self.b.ty(Ty::Path(p));
                self.tys.push(t);
            }
            54 => {
                let binder = self.binder(BinderKind::Place);
                let (place, body) = (self.expr(), self.expr());
                let e = self.b.expr(Expr::LetPlace {
                    binder,
                    place,
                    body,
                });
                self.exprs.push(e);
            }
            55 => {
                let e = self.expr();
                let e = if s.a % 2 == 0 {
                    self.b.expr(Expr::YieldFrom(e))
                } else {
                    let key = Some(self.expr());
                    self.b.expr(Expr::Yield {
                        key,
                        value: Some(e),
                    })
                };
                self.exprs.push(e);
            }
            56 => {
                let kind = if s.a % 2 == 0 {
                    OpKind::BitNot
                } else {
                    OpKind::Pow
                };
                let args: Vec<ExprId> = (0..kind.arity()).map(|_| self.expr()).collect();
                let e = self.b.op(kind, &args);
                self.exprs.push(e);
            }
            57 => {
                // A generic record or sum.
                let generics = self.generics(s);
                let t = self.ty();
                let f = self.b.field(FieldDef {
                    ty: Some(t),
                    ..FieldDef::named(self.ident(0))
                });
                let fields = self.b.list(&[f]);
                let item = self.b.item(Item::new(
                    Some(self.name()),
                    ItemKind::Record(RecordDef {
                        generics,
                        fields,
                        ..RecordDef::default()
                    }),
                ));
                self.item(item);
            }
            58 => {
                // A method call with generic arguments, or `T::name`.
                let receiver = self.expr();
                let t = self.ty();
                let ga = self.b.list(&[hir_lang::GenericArg::Ty(t)]);
                let args: Vec<Arg> = self.exprs(s.a).into_iter().map(Arg::positional).collect();
                let args = self.b.list(&args);
                let e = if s.b % 2 == 0 {
                    self.b.expr(Expr::MethodCall {
                        receiver,
                        method: self.ident(0),
                        generic_args: ga,
                        args,
                    })
                } else {
                    let origin = self.b.origin();
                    let segments = self.b.list(&[
                        hir_lang::Segment::new(self.name(), origin),
                        hir_lang::Segment::new(self.name(), origin),
                    ]);
                    let res = match s.c % 2 {
                        0 if !self.binders.is_empty() => {
                            Res::Local(self.binders[usize::from(s.a) % self.binders.len()])
                        }
                        _ if !self.all_items.is_empty() => {
                            let item = self.all_items[usize::from(s.a) % self.all_items.len()];
                            Res::Def(self.b.def(Def::Item(item)))
                        }
                        _ => Res::Extern(self.sym),
                    };
                    let p = self.b.path(hir_lang::Path {
                        res,
                        unresolved: 1,
                        ..hir_lang::Path::new(segments, Ns::Value)
                    });
                    self.b.expr(Expr::Path(p))
                };
                self.exprs.push(e);
            }
            59 => {
                // A generic sum with a type-parameter field.
                let generics = self.generics(s);
                let t = self.ty();
                let f = self.b.field(FieldDef {
                    name: None,
                    vis: hir_lang::Vis::Private,
                    ty: Some(t),
                    default: None,
                });
                let fields = self.b.list(&[f]);
                let (n0, n1) = (self.ident(0), self.ident(1));
                let v = self.b.variant(Variant {
                    name: n0,
                    shape: hir_lang::Shape::Tuple,
                    fields,
                    discriminant: None,
                });
                let u = self.b.variant(Variant {
                    name: n1,
                    shape: hir_lang::Shape::Unit,
                    fields: hir_lang::List::EMPTY,
                    discriminant: None,
                });
                let variants = self.b.list(&[v, u]);
                let item = self.b.item(Item::new(
                    Some(self.name()),
                    ItemKind::Sum(SumDef { generics, variants }),
                ));
                self.item(item);
            }
            60 => {
                // A range or or-pattern (for exhaustiveness).
                let p = if s.a % 2 == 0 {
                    let lo = self
                        .b
                        .pat(Pat::Lit(Lit::Int(hir_lang::IntLit::new(u64::from(s.b)))));
                    let hi = self
                        .b
                        .pat(Pat::Lit(Lit::Int(hir_lang::IntLit::new(u64::from(s.c)))));
                    self.b.pat(Pat::Range {
                        lo: Some(lo),
                        hi: Some(hi),
                        inclusive: s.c % 2 == 0,
                    })
                } else {
                    let (x, y) = (self.pat(), self.pat());
                    let l = self.b.list(&[x, y]);
                    self.b.pat(Pat::Or(l))
                };
                self.pats.push(p);
            }
            _ => {
                // An intrinsic named like the `?` hook.
                let arg = self.expr();
                let args = self.b.list(&[arg]);
                let e = self.b.expr(Expr::Intrinsic {
                    kind: hir_lang::Intrinsic::Named(self.sym),
                    generic_args: hir_lang::List::EMPTY,
                    args,
                });
                self.exprs.push(e);
            }
        }
    }

    fn expr_step(&mut self, kind: u8, s: &RawStep) -> ExprId {
        match kind {
            0 => self.b.int(i64::from(s.a) - 100),
            1 => self.b.lit(Lit::Bool(s.a % 2 == 0)),
            2 => self
                .b
                .lit(Lit::Float(hir_lang::FloatLit::new(f64::from(s.a)))),
            3 => self.b.str_lit("s"),
            4 => self.b.lit(Lit::Null),
            5 => self.b.expr(Expr::Err),
            6 | 7 => {
                let p = self.path(Ns::Value, s.a);
                self.b.expr(Expr::Path(p))
            }
            8 | 9 => {
                let l = self.exprs(s.a);
                let l = self.b.list(&l);
                self.b.expr(if kind == 8 {
                    Expr::Tuple(l)
                } else {
                    Expr::Array(l)
                })
            }
            10 | 11 => {
                let op_kind = OPS[usize::from(s.a) % OPS.len()];
                let args: Vec<ExprId> = (0..op_kind.arity()).map(|_| self.expr()).collect();
                let mut op = Op::new(op_kind);
                if s.b % 5 == 0 && op.policy.overflow.is_some() {
                    op = op.with_overflow(Overflow::Promote);
                }
                self.b.op_with(op, &args)
            }
            12 => {
                let (cond, then) = (self.expr(), self.expr());
                let else_ = (s.a % 3 != 0).then(|| self.expr());
                self.b.expr(Expr::If { cond, then, else_ })
            }
            13 => {
                let stmts = Self::take_tail(&mut self.stmts, s.a % 4);
                let tail = (s.b % 2 == 0).then(|| self.expr());
                let label = (s.c % 7 == 0).then(|| self.binder(BinderKind::Label));
                let stmts = self.b.list(&stmts);
                self.b.expr(Expr::Block(Block {
                    stmts,
                    tail,
                    label,
                    is_unsafe: false,
                }))
            }
            14 => {
                let scrutinee = self.expr();
                let arms: Vec<Arm> = (0..1 + s.a % 3)
                    .map(|i| {
                        let pat = self.pat();
                        let guard = (i == 0 && s.b % 3 == 0).then(|| self.expr());
                        let body = self.expr();
                        Arm { pat, guard, body }
                    })
                    .collect();
                let arms = self.b.list(&arms);
                self.b.expr(Expr::Match { scrutinee, arms })
            }
            15 => {
                let body = self.expr();
                let label = (s.a % 3 == 0).then(|| self.binder(BinderKind::Label));
                self.b.expr(Expr::Loop {
                    label,
                    body,
                    step: None,
                })
            }
            16 => {
                let value = (s.a % 2 == 0).then(|| self.expr());
                self.b.expr(Expr::Break { label: None, value })
            }
            17 => {
                let value = (s.a % 2 == 0).then(|| self.expr());
                self.b.expr(Expr::Return(value))
            }
            18 => {
                let params = Self::take_tail(&mut self.params, s.a % 3);
                let params = self.b.list(&params);
                let body = self.expr();
                let ret = (s.b % 3 == 0).then(|| self.ty());
                let effects = if s.c % 4 == 0 {
                    Effects::ASYNC
                } else {
                    Effects::NONE
                };
                self.b.expr(Expr::Closure(Closure {
                    params,
                    ret,
                    effects,
                    implicit: Some(hir_lang::CaptureMode::Infer),
                    ..Closure::new(body)
                }))
            }
            19 | 20 => {
                let callee = self.expr();
                let args: Vec<Arg> = (0..s.a % 4)
                    .map(|i| {
                        let value = self.expr();
                        let kind = match s.b.wrapping_add(i) % 6 {
                            0 => ArgKind::Named(self.ident(u32::from(i))),
                            1 => ArgKind::Spread,
                            _ => ArgKind::Positional,
                        };
                        Arg {
                            kind,
                            value,
                            place: false,
                        }
                    })
                    .collect();
                let args = self.b.list(&args);
                self.b.expr(Expr::Call { callee, args })
            }
            21 => {
                let receiver = self.expr();
                let args: Vec<Arg> = self.exprs(s.a).into_iter().map(Arg::positional).collect();
                let args = self.b.list(&args);
                let method = self.ident(0);
                self.b.expr(Expr::MethodCall {
                    receiver,
                    method,
                    generic_args: hir_lang::List::EMPTY,
                    args,
                })
            }
            22 => {
                let base = self.expr();
                let member = if s.a % 2 == 0 {
                    Member::Named(self.sym)
                } else {
                    Member::Index(u32::from(s.b % 3))
                };
                self.b.expr(Expr::Field {
                    base,
                    member,
                    span: Span::empty(0),
                })
            }
            23 => {
                let (base, index) = (self.expr(), self.expr());
                self.b.expr(Expr::Index { base, index })
            }
            24 => {
                let (target, value) = (self.expr(), self.expr());
                let op = (s.a % 3 == 0).then(|| Op::new(OpKind::Add));
                self.b.expr(Expr::Assign { target, op, value })
            }
            25 => {
                let expr = self.expr();
                let ty = self.ty();
                self.b.expr(Expr::Cast {
                    expr,
                    ty,
                    policy: hir_lang::Policy::CAST,
                })
            }
            26 => {
                let path = (s.a % 2 == 0).then(|| self.path(Ns::Type, s.b));
                let value = self.expr();
                let name = self.ident(0);
                let fields = self.b.list(&[FieldInit { name, value }]);
                self.b.expr(Expr::Record {
                    path,
                    fields,
                    base: None,
                })
            }
            27 => {
                let e = self.expr();
                self.b.expr(match s.a % 6 {
                    0 => Expr::Deref(e),
                    1 => Expr::Borrow {
                        kind: hir_lang::BorrowKind::Shared,
                        expr: e,
                    },
                    2 => Expr::Await(e),
                    3 => Expr::Spawn(e),
                    4 => Expr::Throw(e),
                    _ => Expr::Yield {
                        key: None,
                        value: Some(e),
                    },
                })
            }
            _ => {
                let entries: Vec<hir_lang::MapEntry> = (0..s.a % 3)
                    .map(|i| {
                        let key = (i % 2 == 0).then(|| self.expr());
                        let value = self.expr();
                        hir_lang::MapEntry { key, value }
                    })
                    .collect();
                let entries = self.b.list(&entries);
                self.b.expr(Expr::Map(entries))
            }
        }
    }

    #[allow(clippy::too_many_lines)]
    fn other_step(&mut self, kind: u8, s: &RawStep) {
        match kind {
            29 => {
                let binder = self.binder(BinderKind::Local);
                let p = self.b.bind(binder);
                self.pats.push(p);
            }
            30 => {
                let elems = Self::take_tail(&mut self.pats, s.a % 3);
                let elems = self.b.list(&elems);
                let p = self.b.pat(Pat::Tuple {
                    elems,
                    rest: (s.b % 3 == 0).then_some(0),
                });
                self.pats.push(p);
            }
            31 => {
                let p = self
                    .b
                    .pat(Pat::Lit(Lit::Int(hir_lang::IntLit::new(u64::from(s.a)))));
                self.pats.push(p);
            }
            32 => {
                let path = self.path(Ns::Pattern, s.a);
                let elems: Vec<PatId> = (0..s.b % 2).map(|_| self.pat()).collect();
                let elems = self.b.list(&elems);
                let p = self.b.pat(Pat::Ctor {
                    path,
                    elems,
                    rest: None,
                });
                self.pats.push(p);
            }
            33 => {
                let ty = self.ty();
                let inner = (s.a % 2 == 0).then(|| self.pat());
                let p = self.b.pat(Pat::TypeTest { ty, pat: inner });
                self.pats.push(p);
            }
            34 => {
                let t = self.b.ty(Ty::Prim(PRIMS[usize::from(s.a) % PRIMS.len()]));
                self.tys.push(t);
            }
            35 => {
                let inner = self.ty();
                let t = match s.a % 5 {
                    0 => Ty::Slice(inner),
                    1 => Ty::Nullable(inner),
                    2 => Ty::Ref {
                        mutable: s.b % 2 == 0,
                        region: None,
                        inner,
                    },
                    3 => {
                        let len = self.b.int(i64::from(s.c % 4));
                        Ty::Array { elem: inner, len }
                    }
                    _ => {
                        let l = self.b.list(&[inner]);
                        Ty::Tuple(l)
                    }
                };
                let t = self.b.ty(t);
                self.tys.push(t);
            }
            36 => {
                let p = self.path(Ns::Type, s.a);
                let t = self.b.ty(match s.b % 4 {
                    0 => Ty::Any,
                    1 => Ty::Infer,
                    2 => Ty::Never,
                    _ => Ty::Path(p),
                });
                self.tys.push(t);
            }
            37 | 38 => {
                let pat = self.pat();
                let ty = (s.a % 2 == 0).then(|| self.ty());
                let init = (s.b % 4 != 0).then(|| self.expr());
                let st = self.b.stmt(Stmt::Let {
                    pat,
                    ty,
                    init,
                    else_: None,
                });
                self.stmts.push(st);
            }
            39 => {
                let e = self.expr();
                let st = self.b.stmt(Stmt::Expr(e));
                self.stmts.push(st);
            }
            40 => {
                let binder = self.binder(BinderKind::Param);
                let pat = self.b.bind(binder);
                let kinds = [
                    ParamKind::Normal,
                    ParamKind::Normal,
                    ParamKind::Rest,
                    ParamKind::NamedOnly,
                    ParamKind::PositionalOnly,
                ];
                let ty = (s.a % 3 != 0).then(|| self.ty());
                let default = (s.b % 4 == 0).then(|| self.expr());
                let p = self.b.param(Param {
                    pat,
                    ty,
                    default,
                    kind: kinds[usize::from(s.c) % kinds.len()],
                    by_ref: false,
                });
                self.params.push(p);
            }
            41 | 42 => {
                let params = Self::take_tail(&mut self.params, s.a % 3);
                let params = self.b.list(&params);
                let ret = (s.b % 2 == 0).then(|| self.ty());
                let body = Some(self.expr());
                let effects = [
                    Effects::NONE,
                    Effects::ASYNC,
                    Effects::YIELD,
                    Effects::THROWS,
                ][usize::from(s.c % 4)];
                let item = self.b.item(Item::new(
                    Some(self.name()),
                    ItemKind::Fn(FnDef {
                        params,
                        ret,
                        effects,
                        body,
                        ..FnDef::default()
                    }),
                ));
                self.item(item);
            }
            43 => {
                let ty = (s.a % 4 != 0).then(|| self.ty());
                let name = self.ident(0);
                let f = self.b.field(FieldDef {
                    ty,
                    ..FieldDef::named(name)
                });
                let fields = self.b.list(&[f]);
                let item = self.b.item(Item::new(
                    Some(self.name()),
                    ItemKind::Record(RecordDef {
                        fields,
                        ..RecordDef::default()
                    }),
                ));
                self.item(item);
            }
            44 => {
                let t = self.ty();
                let f = self.b.field(FieldDef {
                    name: None,
                    vis: hir_lang::Vis::Private,
                    ty: Some(t),
                    default: None,
                });
                let fields = self.b.list(&[f]);
                let (n0, n1) = (self.ident(0), self.ident(1));
                let v = self.b.variant(Variant {
                    name: n0,
                    shape: hir_lang::Shape::Tuple,
                    fields,
                    discriminant: None,
                });
                let u = self.b.variant(Variant {
                    name: n1,
                    shape: hir_lang::Shape::Unit,
                    fields: hir_lang::List::EMPTY,
                    discriminant: None,
                });
                let variants = self.b.list(&[v, u]);
                let item = self.b.item(Item::new(
                    Some(self.name()),
                    ItemKind::Sum(SumDef {
                        variants,
                        ..SumDef::default()
                    }),
                ));
                self.item(item);
            }
            45 => {
                let ty = (s.a % 3 != 0).then(|| self.ty());
                let value = Some(self.expr());
                let item = self
                    .b
                    .item(Item::new(Some(self.name()), ItemKind::Const { ty, value }));
                self.item(item);
            }
            46 => {
                let self_ty = self.ty();
                let members = Self::take_tail(&mut self.items, s.a % 2);
                let items = self.b.list(&members);
                let item = self.b.item(Item::new(
                    None,
                    ItemKind::Impl(ImplDef {
                        items,
                        ..ImplDef::new(self_ty)
                    }),
                ));
                self.item(item);
            }
            _ => {
                let members = Self::take_tail(&mut self.items, s.a % 2);
                let items = self.b.list(&members);
                let bases: Vec<TyId> = (0..s.b % 2).map(|_| self.ty()).collect();
                let bases = self.b.list(&bases);
                let item = self.b.item(Item::new(
                    Some(self.name()),
                    ItemKind::Class(hir_lang::ClassDef {
                        items,
                        bases,
                        ..Default::default()
                    }),
                ));
                self.item(item);
            }
        }
    }

    /// Roots the leftovers: expressions and statements become the body of
    /// one more function; every parentless item goes in the root module.
    fn finish(mut self) -> (hir_lang::Builder, ItemId) {
        let mut stmts = core::mem::take(&mut self.stmts);
        for e in core::mem::take(&mut self.exprs) {
            stmts.push(self.b.stmt(Stmt::Expr(e)));
        }
        let body = self.b.block(&stmts, None);
        let params = core::mem::take(&mut self.params);
        let params = self.b.list(&params);
        let main = self.b.item(Item::new(
            Some(self.name()),
            ItemKind::Fn(FnDef {
                params,
                body: Some(body),
                ..FnDef::default()
            }),
        ));
        self.items.push(main);
        let root = self.b.module(None, &self.items);
        (self.b, root)
    }
}

fn arbitrary(steps: &[RawStep], names: &mut intern_lang::Interner) -> (hir_lang::Builder, ItemId) {
    let mut r = Random::new(names.intern("g"));
    for s in steps {
        r.step(s);
    }
    r.finish()
}

fn live_pats(hir: &hir_lang::Hir) -> Vec<PatId> {
    let mut out = Vec::new();
    hir_lang::walk(hir, |n| {
        if let NodeRef::Pat(p) = n {
            out.push(p);
        }
    });
    out
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

proptest! {
    #![proptest_config(ProptestConfig { cases: 2048, ..ProptestConfig::default() })]

    /// Never panics, types every live expression, deterministic: under both
    /// disciplines and a permissive static profile.
    #[test]
    fn prop_checking_is_total_on_arbitrary_hir(steps in raw_steps()) {
        let mut names = intern_lang::Interner::new();
        let (b, root) = arbitrary(&steps, &mut names);
        let Ok((hir, _)) = b.finish_lenient(root) else {
            return Ok(());
        };
        let live = live_exprs(&hir);
        let permissive = Profile::static_explicit()
            .with_records(RecordTyping::Structural)
            .with_subtyping(true)
            .with_numeric_widening(true)
            .with_null_safety(false)
            .with_string_add(true);
        let inferred = Profile::static_inferred()
            .with_try_hook(TryHook::Intrinsic { name: names.intern("g"), convert: None });
        let interfaces = Profile::static_inferred()
            .with_polymorphism(typeck_lang::Polymorphism::Interfaces)
            .with_mono(typeck_lang::MonoPolicy::Selective { max_nodes: 8 });
        for profile in [Profile::static_explicit(), Profile::dynamic(), permissive, inferred, interfaces] {
            // A cyclic interface resolution (`impl<T: I> I for T`) is a
            // budget error, deterministically; nothing else may fail.
            let (a, b) = match (check(&hir, &profile), check(&hir, &profile)) {
                (Ok(a), Ok(b)) => (a, b),
                (Err(CheckError::BudgetExceeded { limit: Limit::TraitDepth }), Err(e2)) => {
                    prop_assert_eq!(e2, CheckError::BudgetExceeded { limit: Limit::TraitDepth });
                    continue;
                }
                (a, b) => {
                    prop_assert!(false, "{:?} / {:?}", a.err(), b.err());
                    continue;
                }
            };
            prop_assert_eq!(&a, &b);
            for &e in &live {
                prop_assert!(a.expr(e).is_some(), "untyped live expression {:?}", e);
            }
            for &p in &live_pats(&hir) {
                prop_assert!(a.pat(p).is_some(), "untyped live pattern {:?}", p);
            }
            for d in a.diagnostics() {
                let _ = a.message(d, &names);
            }
        }
    }

    /// Any budget either suffices or stops the check with a budget error.
    #[test]
    fn prop_any_budget_terminates(steps in raw_steps(), limit in 0u64..600) {
        let mut names = intern_lang::Interner::new();
        let (b, root) = arbitrary(&steps, &mut names);
        let Ok((hir, _)) = b.finish_lenient(root) else {
            return Ok(());
        };
        for profile in [Profile::static_explicit(), Profile::static_inferred()] {
            let mut checker = Checker::new(&hir, profile);
            let _ = checker.set_budget(Budget { steps: limit, ..Budget::default() });
            match checker.check() {
                Ok(_) | Err(CheckError::BudgetExceeded { .. }) => {}
                Err(other) => prop_assert!(false, "{other:?}"),
            }
        }
    }
}

/// The properties above are not vacuous: random trees repair into valid HIR
/// with many live expressions, and the checker reports on most of them.
#[test]
fn test_arbitrary_hir_reaches_the_checker() {
    use proptest::strategy::ValueTree;
    let mut runner = proptest::test_runner::TestRunner::deterministic();
    let strategy = raw_steps();
    let (mut valid, mut rich, mut with_diags) = (0, 0, 0);
    for _ in 0..400 {
        let steps = strategy.new_tree(&mut runner).unwrap().current();
        let mut names = intern_lang::Interner::new();
        let (b, root) = arbitrary(&steps, &mut names);
        if let Ok((hir, _)) = b.finish_lenient(root) {
            valid += 1;
            if live_exprs(&hir).len() >= 20 {
                rich += 1;
            }
            if !check(&hir, &Profile::static_explicit()).unwrap().is_ok() {
                with_diags += 1;
            }
        }
    }
    assert!(valid >= 390, "valid {valid}/400");
    assert!(rich >= 150, "rich {rich}/400");
    assert!(with_diags >= 150, "with diagnostics {with_diags}/400");
}

/// The generic and interface forms survive repair and reach the checker's
/// new rules (not vacuous for the 0.3 forms).
#[test]
fn test_arbitrary_hir_reaches_the_generic_rules() {
    use proptest::strategy::ValueTree;
    let mut runner = proptest::test_runner::TestRunner::deterministic();
    let strategy = raw_steps();
    let (mut generic, mut impls, mut new_codes) = (0, 0, 0);
    for _ in 0..600 {
        let steps = strategy.new_tree(&mut runner).unwrap().current();
        let mut names = intern_lang::Interner::new();
        let (b, root) = arbitrary(&steps, &mut names);
        let Ok((hir, _)) = b.finish_lenient(root) else {
            continue;
        };
        let mut has_generic = false;
        let mut has_impl = false;
        hir_lang::walk(&hir, |n| {
            if let NodeRef::Item(i) = n {
                match hir.item(i).kind {
                    ItemKind::Fn(d) if !d.generics.params.is_empty() => has_generic = true,
                    ItemKind::Impl(d) if d.interface.is_some() => has_impl = true,
                    _ => {}
                }
            }
        });
        generic += usize::from(has_generic);
        impls += usize::from(has_impl);
        if let Ok(typed) = check(&hir, &Profile::static_inferred()) {
            let new = typed.diagnostics().iter().any(|d| d.kind.code() >= "T0040");
            new_codes += usize::from(new);
        }
    }
    assert!(generic >= 60, "generic functions in {generic}/600");
    assert!(impls >= 60, "interface impls in {impls}/600");
    assert!(new_codes >= 60, "0.3 diagnostics in {new_codes}/600");
}
