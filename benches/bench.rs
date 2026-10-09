//! Checking throughput at realistic scale: programs of 100k and 1M HIR
//! nodes under `static-explicit`, `static-inferred`, and `dynamic`; generic
//! programs (generic containers, generic impls, bounded generic functions,
//! interface methods resolved through generic impls, closures with inferred
//! signatures) at 100k and 1M nodes under `static-inferred`; and the ISSUES
//! M39 doubling chain (shared type structure) at 100k levels.
//!
//! Run with `cargo bench --bench bench`.

use std::hint::black_box;

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use hir_lang::{
    Arm, BinderKind, Bound, Builder, CaptureMode, Closure, Def, Expr, FieldDef, FieldInit, FnDef,
    GenericArg, GenericParam, Generics, Hir, IdKind, Ident, ImplDef, InterfaceDef, Item, ItemId,
    ItemKind, Lit, Name, Ns, OpKind, Param, ParamKind, Pat, Path, Prim, RecordDef, Res, Segment,
    Span, Stmt, SumDef, Symbol, Ty, TyId, Variant, VariantId,
};
use intern_lang::Interner;
use typeck_lang::{Profile, check};

struct Names {
    a: Symbol,
    b: Symbol,
    f: Symbol,
    x: Symbol,
    p: Symbol,
}

fn typed_param(b: &mut Builder, name: Symbol) -> (hir_lang::ParamId, hir_lang::BinderId) {
    let ty = b.ty(Ty::Prim(Prim::I64));
    let binder = b.new_binder(Name::new(name), BinderKind::Param);
    let pat = b.bind(binder);
    let param = b.param(Param {
        pat,
        ty: Some(ty),
        default: None,
        kind: ParamKind::Normal,
        by_ref: false,
    });
    (param, binder)
}

fn local(
    b: &mut Builder,
    name: Symbol,
    init: hir_lang::ExprId,
) -> (hir_lang::StmtId, hir_lang::BinderId) {
    let binder = b.new_binder(Name::new(name), BinderKind::Local);
    let pat = b.bind(binder);
    (b.let_stmt(pat, Some(init)), binder)
}

/// A function of about 50 HIR nodes exercising the common forms: typed
/// parameters, `let` inference, arithmetic, comparison, `if`, a record
/// literal and field access, a call, and a `match` on a sum.
fn function(
    b: &mut Builder,
    n: &Names,
    point: ItemId,
    circle: VariantId,
    prev: Option<ItemId>,
) -> ItemId {
    let (pa, a) = typed_param(b, n.a);
    let (pb, bb) = typed_param(b, n.b);
    // let x = a * b + 1;
    let (ua, ub) = (b.use_binder(a), b.use_binder(bb));
    let mul = b.op(OpKind::Mul, &[ua, ub]);
    let one = b.int(1);
    let add = b.op(OpKind::Add, &[mul, one]);
    let (s1, x) = local(b, n.x, add);
    // let p = Point { x: x };
    let pdef = b.def(Def::Item(point));
    let ppath = b.resolved_path(Name::new(n.p), Ns::Type, Res::Def(pdef));
    let ux = b.use_binder(x);
    let fields = b.list(&[FieldInit {
        name: Ident::new(n.x, Span::empty(0)),
        value: ux,
    }]);
    let lit = b.expr(Expr::Record {
        path: Some(ppath),
        fields,
        base: None,
    });
    let (s2, p) = local(b, n.p, lit);
    // let y = if p.x > a { prev(p.x, b) } else { 0 };
    let up = b.use_binder(p);
    let member = hir_lang::Member::Named(n.x);
    let px = b.expr(Expr::Field {
        base: up,
        member,
        span: Span::empty(0),
    });
    let ua2 = b.use_binder(a);
    let gt = b.op(OpKind::Gt, &[px, ua2]);
    let then = match prev {
        Some(f) => {
            let fdef = b.def(Def::Item(f));
            let fpath = b.resolved_path(Name::new(n.f), Ns::Value, Res::Def(fdef));
            let callee = b.expr(Expr::Path(fpath));
            let up2 = b.use_binder(p);
            let px2 = b.expr(Expr::Field {
                base: up2,
                member,
                span: Span::empty(0),
            });
            let ub2 = b.use_binder(bb);
            b.call(callee, &[px2, ub2])
        }
        None => b.int(2),
    };
    let tb = b.block(&[], Some(then));
    let zero = b.int(0);
    let eb = b.block(&[], Some(zero));
    let iff = b.expr(Expr::If {
        cond: gt,
        then: tb,
        else_: Some(eb),
    });
    let (s3, y) = local(b, n.x, iff);
    // match Circle(y) { Circle(r) => r, _ => 0 }
    let cdef = b.def(Def::Variant(circle));
    let cpath = b.resolved_path(Name::new(n.p), Ns::Value, Res::Def(cdef));
    let ccallee = b.expr(Expr::Path(cpath));
    let uy = b.use_binder(y);
    let scrutinee = b.call(ccallee, &[uy]);
    let r = b.new_binder(Name::new(n.x), BinderKind::Local);
    let rp = b.bind(r);
    let cpath2 = b.resolved_path(Name::new(n.p), Ns::Pattern, Res::Def(cdef));
    let elems = b.list(&[rp]);
    let cpat = b.pat(Pat::Ctor {
        path: cpath2,
        elems,
        rest: None,
    });
    let ur = b.use_binder(r);
    let wild = b.pat(Pat::Wild);
    let z2 = b.int(0);
    let arms = b.list(&[
        Arm {
            pat: cpat,
            guard: None,
            body: ur,
        },
        Arm {
            pat: wild,
            guard: None,
            body: z2,
        },
    ]);
    let m = b.expr(Expr::Match { scrutinee, arms });
    let body = b.block(&[s1, s2, s3], Some(m));
    let params = b.list(&[pa, pb]);
    let ret = b.ty(Ty::Prim(Prim::I64));
    b.item(Item::new(
        Some(Name::new(n.f)),
        ItemKind::Fn(FnDef {
            params,
            ret: Some(ret),
            body: Some(body),
            ..FnDef::default()
        }),
    ))
}

/// A unit of `fns` functions plus the record and sum they use.
fn program(fns: usize) -> Hir {
    let mut names = Interner::new();
    let n = Names {
        a: names.intern("a"),
        b: names.intern("b"),
        f: names.intern("f"),
        x: names.intern("x"),
        p: names.intern("Point"),
    };
    let mut b = Builder::new();
    let t = b.ty(Ty::Prim(Prim::I64));
    let fx = b.field(FieldDef {
        ty: Some(t),
        ..FieldDef::named(Ident::new(n.x, Span::empty(0)))
    });
    let fields = b.list(&[fx]);
    let point = b.item(Item::new(
        Some(Name::new(n.p)),
        ItemKind::Record(RecordDef {
            fields,
            ..RecordDef::default()
        }),
    ));
    let t2 = b.ty(Ty::Prim(Prim::I64));
    let vf = b.field(FieldDef {
        name: None,
        vis: hir_lang::Vis::Private,
        ty: Some(t2),
        default: None,
    });
    let vfields = b.list(&[vf]);
    let circle = b.variant(Variant {
        name: Ident::new(n.p, Span::empty(0)),
        shape: hir_lang::Shape::Tuple,
        fields: vfields,
        discriminant: None,
    });
    let unit = b.variant(Variant {
        name: Ident::new(n.x, Span::empty(0)),
        shape: hir_lang::Shape::Unit,
        fields: hir_lang::List::EMPTY,
        discriminant: None,
    });
    let variants = b.list(&[circle, unit]);
    let shape = b.item(Item::new(
        Some(Name::new(n.f)),
        ItemKind::Sum(SumDef {
            variants,
            ..SumDef::default()
        }),
    ));
    let mut items = vec![point, shape];
    let mut prev = None;
    for _ in 0..fns {
        let f = function(&mut b, &n, point, circle, prev);
        items.push(f);
        prev = Some(f);
    }
    let root = b.module(None, &items);
    let hir = b.finish(root).expect("bench HIR validates");
    let typed = check(&hir, &Profile::static_explicit()).expect("checks");
    assert!(typed.is_ok(), "{:?}", typed.diagnostics().first());
    hir
}

fn nodes(hir: &Hir) -> u64 {
    [
        IdKind::Item,
        IdKind::Expr,
        IdKind::Stmt,
        IdKind::Pat,
        IdKind::Ty,
        IdKind::Path,
        IdKind::Field,
        IdKind::Variant,
        IdKind::Param,
    ]
    .into_iter()
    .map(|k| hir.count(k) as u64)
    .sum()
}

/// `let x0 = 1; let x1 = (x0, x0); ...` and the same chain from an
/// unannotated variable, then unified: the M39 pattern.
fn doubling_chain(n: usize) -> Hir {
    let mut names = Interner::new();
    let x = Name::new(names.intern("x"));
    let mut b = Builder::new();
    let mut stmts = Vec::with_capacity(2 * n + 3);
    let chain =
        |b: &mut Builder, init: Option<hir_lang::ExprId>, stmts: &mut Vec<hir_lang::StmtId>| {
            let mut v = b.new_binder(x, BinderKind::Local);
            let p = b.bind(v);
            stmts.push(b.let_stmt(p, init));
            for _ in 0..n {
                let (l, r) = (b.use_binder(v), b.use_binder(v));
                let list = b.list(&[l, r]);
                let pair = b.expr(Expr::Tuple(list));
                let next = b.new_binder(x, BinderKind::Local);
                let p = b.bind(next);
                stmts.push(b.let_stmt(p, Some(pair)));
                v = next;
            }
            v
        };
    let one = b.lit(Lit::Int(hir_lang::IntLit::new(1)));
    let xs = chain(&mut b, Some(one), &mut stmts);
    let ys = chain(&mut b, None, &mut stmts);
    let target = b.use_binder(ys);
    let value = b.use_binder(xs);
    let assign = b.expr(Expr::Assign {
        target,
        op: None,
        value,
    });
    stmts.push(b.stmt(Stmt::Expr(assign)));
    let body = b.block(&stmts, None);
    let main = b.func(x, &[], body);
    let root = b.module(None, &[main]);
    b.finish(root).expect("chain validates")
}

// ------------------------------------------------------- generic programs

/// The declarations of a generic program.
struct GenericDecls {
    bx: ItemId,
    id: ItemId,
    describe: ItemId,
    apply: ItemId,
}

struct Gb<'n> {
    b: Builder,
    names: &'n mut Interner,
}

impl Gb<'_> {
    fn name(&mut self, s: &str) -> Name {
        Name::new(self.names.intern(s))
    }

    fn ident(&mut self, s: &str) -> Ident {
        Ident::new(self.names.intern(s), Span::empty(0))
    }

    fn tparam(&mut self, s: &str) -> hir_lang::BinderId {
        let n = self.name(s);
        self.b.new_binder(n, BinderKind::TypeParam)
    }

    fn tp(&mut self, s: &str, binder: hir_lang::BinderId) -> TyId {
        let n = self.name(s);
        let p = self.b.resolved_path(n, Ns::Type, Res::Local(binder));
        self.b.ty(Ty::Path(p))
    }

    fn item_ty(&mut self, s: &str, item: ItemId, args: &[TyId]) -> TyId {
        let n = self.name(s);
        let origin = self.b.origin();
        let ga: Vec<GenericArg> = args.iter().map(|&t| GenericArg::Ty(t)).collect();
        let args = self.b.list(&ga);
        let seg = Segment {
            args,
            ..Segment::new(n, origin)
        };
        let segments = self.b.list(&[seg]);
        let def = self.b.def(Def::Item(item));
        let p = self.b.path(Path {
            res: Res::Def(def),
            ..Path::new(segments, Ns::Type)
        });
        self.b.ty(Ty::Path(p))
    }

    fn generics(&mut self, params: &[(hir_lang::BinderId, Option<TyId>)]) -> Generics {
        let gps: Vec<GenericParam> = params
            .iter()
            .map(|&(binder, bound)| {
                let bounds: Vec<Bound> = bound.into_iter().map(Bound::Ty).collect();
                GenericParam {
                    bounds: self.b.list(&bounds),
                    ..GenericParam::new(binder)
                }
            })
            .collect();
        Generics {
            params: self.b.list(&gps),
            preds: hir_lang::List::EMPTY,
        }
    }

    fn param(
        &mut self,
        s: &str,
        ty: Option<TyId>,
        kind: ParamKind,
    ) -> (hir_lang::ParamId, hir_lang::BinderId) {
        let n = self.name(s);
        let binder = self.b.new_binder(n, BinderKind::Param);
        let pat = self.b.bind(binder);
        let p = self.b.param(Param {
            pat,
            ty,
            default: None,
            kind,
            by_ref: false,
        });
        (p, binder)
    }

    fn func(
        &mut self,
        s: &str,
        generics: Generics,
        params: &[hir_lang::ParamId],
        ret: Option<TyId>,
        body: Option<hir_lang::ExprId>,
    ) -> ItemId {
        let n = self.name(s);
        let params = self.b.list(params);
        self.b.item(Item::new(
            Some(n),
            ItemKind::Fn(FnDef {
                generics,
                params,
                ret,
                body,
                ..FnDef::default()
            }),
        ))
    }

    fn call(&mut self, s: &str, item: ItemId, args: &[hir_lang::ExprId]) -> hir_lang::ExprId {
        let n = self.name(s);
        let def = self.b.def(Def::Item(item));
        let p = self.b.resolved_path(n, Ns::Value, Res::Def(def));
        let callee = self.b.expr(Expr::Path(p));
        self.b.call(callee, args)
    }

    fn method(&mut self, recv: hir_lang::ExprId, s: &str) -> hir_lang::ExprId {
        let method = self.ident(s);
        self.b.expr(Expr::MethodCall {
            receiver: recv,
            method,
            generic_args: hir_lang::List::EMPTY,
            args: hir_lang::List::EMPTY,
        })
    }

    fn boxed(&mut self, bx: ItemId, v: hir_lang::ExprId) -> hir_lang::ExprId {
        let n = self.name("Box");
        let def = self.b.def(Def::Item(bx));
        let path = self.b.resolved_path(n, Ns::Type, Res::Def(def));
        let val = self.ident("val");
        let fields = self.b.list(&[FieldInit {
            name: val,
            value: v,
        }]);
        self.b.expr(Expr::Record {
            path: Some(path),
            fields,
            base: None,
        })
    }

    fn receiver(&mut self) -> (hir_lang::ParamId, hir_lang::BinderId) {
        let selfty = self.b.ty(Ty::SelfTy);
        self.param("self", Some(selfty), ParamKind::Receiver)
    }

    fn val(&mut self, base: hir_lang::ExprId) -> hir_lang::ExprId {
        let fv = self.names.intern("val");
        self.b.expr(Expr::Field {
            base,
            member: hir_lang::Member::Named(fv),
            span: Span::empty(0),
        })
    }

    /// `Box<T>` with a generic `get`, `Show` for `i64` and (bounded) for
    /// `Box<T>`, `id`, `describe<T: Show>`, `apply<T>(f: fn(T) -> T, x: T)`.
    #[allow(clippy::too_many_lines)]
    fn declare(&mut self, items: &mut Vec<ItemId>) -> GenericDecls {
        let t = self.tparam("T");
        let g = self.generics(&[(t, None)]);
        let tt = self.tp("T", t);
        let vi = self.ident("val");
        let f = self.b.field(FieldDef {
            ty: Some(tt),
            ..FieldDef::named(vi)
        });
        let fields = self.b.list(&[f]);
        let n = self.name("Box");
        let bx = self.b.item(Item::new(
            Some(n),
            ItemKind::Record(RecordDef {
                generics: g,
                fields,
                ..RecordDef::default()
            }),
        ));
        // impl<U> Box<U> { fn get(self) -> U { self.val } }
        let u = self.tparam("U");
        let g = self.generics(&[(u, None)]);
        let ut = self.tp("U", u);
        let st = self.item_ty("Box", bx, &[ut]);
        let (r, me) = self.receiver();
        let um = self.b.use_binder(me);
        let field = self.val(um);
        let body = self.b.block(&[], Some(field));
        let ret = self.tp("U", u);
        let get = self.func("get", Generics::default(), &[r], Some(ret), Some(body));
        let gi = self.b.list(&[get]);
        let box_impl = self.b.item(Item::new(
            None,
            ItemKind::Impl(ImplDef {
                generics: g,
                items: gi,
                ..ImplDef::new(st)
            }),
        ));
        // trait Show { fn show(self) -> i64; }
        let (r, _) = self.receiver();
        let ret = self.b.ty(Ty::Prim(Prim::I64));
        let decl = self.func("show", Generics::default(), &[r], Some(ret), None);
        let di = self.b.list(&[decl]);
        let n = self.name("Show");
        let show = self.b.item(Item::new(
            Some(n),
            ItemKind::Interface(InterfaceDef {
                items: di,
                ..InterfaceDef::default()
            }),
        ));
        // impl Show for i64 { fn show(self) -> i64 { self } }
        let (r, me) = self.receiver();
        let um = self.b.use_binder(me);
        let body = self.b.block(&[], Some(um));
        let ret = self.b.ty(Ty::Prim(Prim::I64));
        let m = self.func("show", Generics::default(), &[r], Some(ret), Some(body));
        let mi = self.b.list(&[m]);
        let iface = self.item_ty("Show", show, &[]);
        let i64t = self.b.ty(Ty::Prim(Prim::I64));
        let imp_i = self.b.item(Item::new(
            None,
            ItemKind::Impl(ImplDef {
                interface: Some(iface),
                items: mi,
                ..ImplDef::new(i64t)
            }),
        ));
        // impl<V: Show> Show for Box<V> { fn show(self) -> i64 { self.val.show() } }
        let v = self.tparam("V");
        let sb = self.item_ty("Show", show, &[]);
        let g = self.generics(&[(v, Some(sb))]);
        let vt = self.tp("V", v);
        let bvt = self.item_ty("Box", bx, &[vt]);
        let (r, me) = self.receiver();
        let um = self.b.use_binder(me);
        let field = self.val(um);
        let inner = self.method(field, "show");
        let body = self.b.block(&[], Some(inner));
        let ret = self.b.ty(Ty::Prim(Prim::I64));
        let m = self.func("show", Generics::default(), &[r], Some(ret), Some(body));
        let mi = self.b.list(&[m]);
        let iface = self.item_ty("Show", show, &[]);
        let imp_b = self.b.item(Item::new(
            None,
            ItemKind::Impl(ImplDef {
                generics: g,
                interface: Some(iface),
                items: mi,
                ..ImplDef::new(bvt)
            }),
        ));
        // fn id<T>(x: T) -> T { x }
        let t = self.tparam("T");
        let g = self.generics(&[(t, None)]);
        let tt = self.tp("T", t);
        let (p, x) = self.param("x", Some(tt), ParamKind::Normal);
        let ux = self.b.use_binder(x);
        let body = self.b.block(&[], Some(ux));
        let ret = self.tp("T", t);
        let id = self.func("id", g, &[p], Some(ret), Some(body));
        // fn describe<T: Show>(x: T) -> i64 { x.show() }
        let t = self.tparam("T");
        let sb = self.item_ty("Show", show, &[]);
        let g = self.generics(&[(t, Some(sb))]);
        let tt = self.tp("T", t);
        let (p, x) = self.param("x", Some(tt), ParamKind::Normal);
        let ux = self.b.use_binder(x);
        let c = self.method(ux, "show");
        let body = self.b.block(&[], Some(c));
        let ret = self.b.ty(Ty::Prim(Prim::I64));
        let describe = self.func("describe", g, &[p], Some(ret), Some(body));
        // fn apply<T>(f: fn(T) -> T, x: T) -> T { f(x) }
        let t = self.tparam("T");
        let g = self.generics(&[(t, None)]);
        let (ta, tb, tc) = (self.tp("T", t), self.tp("T", t), self.tp("T", t));
        let ps = self.b.list(&[ta]);
        let fty = self.b.ty(Ty::Fn {
            params: ps,
            ret: tb,
            effects: hir_lang::Effects::NONE,
            throws: None,
            abi: None,
        });
        let (pf, f) = self.param("f", Some(fty), ParamKind::Normal);
        let (px, x) = self.param("x", Some(tc), ParamKind::Normal);
        let (uf, ux) = (self.b.use_binder(f), self.b.use_binder(x));
        let call = self.b.call(uf, &[ux]);
        let body = self.b.block(&[], Some(call));
        let ret = self.tp("T", t);
        let apply = self.func("apply", g, &[pf, px], Some(ret), Some(body));
        items.extend([bx, box_impl, show, imp_i, imp_b, id, describe, apply]);
        GenericDecls {
            bx,
            id,
            describe,
            apply,
        }
    }

    fn local(&mut self, s: &str, init: hir_lang::ExprId) -> (hir_lang::StmtId, hir_lang::BinderId) {
        let n = self.name(s);
        let binder = self.b.new_binder(n, BinderKind::Local);
        let pat = self.b.bind(binder);
        (self.b.let_stmt(pat, Some(init)), binder)
    }

    /// `fn f(a: i64) -> i64 { let b = id(Box { val: a }); let c = b.get();
    /// let d = describe(Box { val: Box { val: c } });
    /// let e = apply(|y| y + d, c); e + d }`: about 50 nodes.
    fn function(&mut self, d: &GenericDecls) -> ItemId {
        let i64t = self.b.ty(Ty::Prim(Prim::I64));
        let (pa, a) = self.param("a", Some(i64t), ParamKind::Normal);
        let ua = self.b.use_binder(a);
        let bx = self.boxed(d.bx, ua);
        let idc = self.call("id", d.id, &[bx]);
        let (s1, b) = self.local("b", idc);
        let ub = self.b.use_binder(b);
        let get = self.method(ub, "get");
        let (s2, c) = self.local("c", get);
        let uc = self.b.use_binder(c);
        let inner = self.boxed(d.bx, uc);
        let outer = self.boxed(d.bx, inner);
        let desc = self.call("describe", d.describe, &[outer]);
        let (s3, dd) = self.local("d", desc);
        let (py, y) = self.param("y", None, ParamKind::Normal);
        let uy = self.b.use_binder(y);
        let ud = self.b.use_binder(dd);
        let add = self.b.op(OpKind::Add, &[uy, ud]);
        let params = self.b.list(&[py]);
        let clo = self.b.expr(Expr::Closure(Closure {
            params,
            implicit: Some(CaptureMode::ByRef),
            ..Closure::new(add)
        }));
        let uc2 = self.b.use_binder(c);
        let ap = self.call("apply", d.apply, &[clo, uc2]);
        let (s4, e) = self.local("e", ap);
        let (ue, ud2) = (self.b.use_binder(e), self.b.use_binder(dd));
        let sum = self.b.op(OpKind::Add, &[ue, ud2]);
        let body = self.b.block(&[s1, s2, s3, s4], Some(sum));
        let ret = self.b.ty(Ty::Prim(Prim::I64));
        self.func("f", Generics::default(), &[pa], Some(ret), Some(body))
    }
}

/// A unit of `fns` generic-heavy functions.
fn generic_program(fns: usize) -> Hir {
    let mut names = Interner::new();
    let mut gb = Gb {
        b: Builder::new(),
        names: &mut names,
    };
    let mut items = Vec::new();
    let d = gb.declare(&mut items);
    for _ in 0..fns {
        let f = gb.function(&d);
        items.push(f);
    }
    let root = gb.b.module(None, &items);
    let Gb { b, .. } = gb;
    let hir = b.finish(root).expect("generic bench HIR validates");
    let typed = check(&hir, &Profile::static_inferred()).expect("checks");
    assert!(typed.is_ok(), "{:?}", typed.diagnostics().first());
    hir
}

fn bench_generics(c: &mut Criterion) {
    let mut group = c.benchmark_group("generic");
    group.sample_size(10);
    for (label, fns) in [("100k", 2_000usize), ("1M", 20_000)] {
        let hir = generic_program(fns);
        group.throughput(Throughput::Elements(nodes(&hir)));
        group.bench_with_input(
            BenchmarkId::new("static-inferred", label),
            &hir,
            |bench, hir| {
                bench.iter(|| black_box(check(hir, &Profile::static_inferred())));
            },
        );
    }
    group.finish();
}

fn bench_scale(c: &mut Criterion) {
    let mut group = c.benchmark_group("check");
    group.sample_size(10);
    for (label, fns) in [("100k", 1_700usize), ("1M", 17_000)] {
        let hir = program(fns);
        group.throughput(Throughput::Elements(nodes(&hir)));
        group.bench_with_input(
            BenchmarkId::new("static-explicit", label),
            &hir,
            |bench, hir| {
                bench.iter(|| black_box(check(hir, &Profile::static_explicit())));
            },
        );
        group.bench_with_input(
            BenchmarkId::new("static-inferred", label),
            &hir,
            |bench, hir| {
                bench.iter(|| black_box(check(hir, &Profile::static_inferred())));
            },
        );
        group.bench_with_input(BenchmarkId::new("dynamic", label), &hir, |bench, hir| {
            bench.iter(|| black_box(check(hir, &Profile::dynamic())));
        });
    }
    group.finish();
}

fn bench_shared_structure(c: &mut Criterion) {
    let mut group = c.benchmark_group("doubling-chain");
    group.sample_size(10);
    let hir = doubling_chain(100_000);
    group.throughput(Throughput::Elements(nodes(&hir)));
    group.bench_function("100k-levels", |bench| {
        bench.iter(|| black_box(check(&hir, &Profile::static_explicit())));
    });
    group.finish();
}

criterion_group!(benches, bench_scale, bench_generics, bench_shared_structure);
criterion_main!(benches);
