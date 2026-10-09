//! Checking throughput at realistic scale: programs of 100k and 1M HIR
//! nodes under `static-explicit` and `dynamic`, and the ISSUES M39 doubling
//! chain (shared type structure) at 100k levels.
//!
//! Run with `cargo bench --bench bench`.

use std::hint::black_box;

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use hir_lang::{
    Arm, BinderKind, Builder, Def, Expr, FieldDef, FieldInit, FnDef, Hir, IdKind, Ident, Item,
    ItemId, ItemKind, Lit, Name, Ns, OpKind, Param, ParamKind, Pat, Prim, RecordDef, Res, Span,
    Stmt, SumDef, Symbol, Ty, Variant, VariantId,
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

criterion_group!(benches, bench_scale, bench_shared_structure);
criterion_main!(benches);
