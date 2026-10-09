//! Hostile inputs for generics and interfaces: deep generic arguments and
//! calls (iterative, linear), recursive bounds and ever-growing resolution
//! (budget errors, never hangs), supertrait and alias cycles, cyclic
//! associated types, and impl tables at scale.

mod common;

use common::{Kit, inferred_check, messages};
use hir_lang::{Expr, ItemId, ParamKind, Prim, Res};
use typeck_lang::{Budget, CheckError, Checker, Limit, Profile, TypeId, check};

const I64: TypeId = TypeId::prim(Prim::I64);

/// `struct W<T> { v: T }`.
fn wrap(k: &mut Kit) -> ItemId {
    let t = k.type_param("T");
    let gp = k.gparam(t, &[]);
    let g = k.generics(&[gp], &[]);
    let tt = k.tp("T", t);
    k.grecord("W", g, &[("v", tt)])
}

/// `trait Tr {}`.
fn marker(k: &mut Kit, name: &str) -> ItemId {
    let g = k.generics(&[], &[]);
    k.iface(name, g, &[], &[])
}

/// `fn need<U: Tr>(x: U) {}`.
fn need(k: &mut Kit, tr: ItemId) -> ItemId {
    let u = k.type_param("U");
    let b = k.path_ty("Tr", tr, &[]);
    let gp = k.gparam(u, &[b]);
    let g = k.generics(&[gp], &[]);
    let ut = k.tp("U", u);
    let (p, _) = k.param("x", Some(ut), ParamKind::Normal, None);
    let body = k.block(&[], None);
    k.gfunc("need", g, &[p], None, body)
}

/// `W { v: e }`.
fn wrap_lit(k: &mut Kit, w: ItemId, e: hir_lang::ExprId) -> hir_lang::ExprId {
    let n = k.name("W");
    let def = k.b.def(hir_lang::Def::Item(w));
    let path = k.b.resolved_path(n, hir_lang::Ns::Type, Res::Def(def));
    let v = k.ident("v");
    let fields = k.b.list(&[hir_lang::FieldInit { name: v, value: e }]);
    k.expr(Expr::Record {
        path: Some(path),
        fields,
        base: None,
    })
}

#[test]
fn test_deep_generic_arguments_lower_and_unify_iteratively() {
    let depth = 30_000;
    let mut k = Kit::new();
    let w = wrap(&mut k);
    let mut ann = k.prim(Prim::I64);
    for _ in 0..depth {
        ann = k.path_ty("W", w, &[ann]);
    }
    let (p, x) = k.param("x", Some(ann), ParamKind::Normal, None);
    let ux = k.use_(x);
    let (s, y) = k.let_("y", None, Some(ux));
    let body = k.block(&[s], None);
    let f = k.func("f", &[p], None, body);
    let (hir, names) = k.finish_items(&[w, f]);
    let typed = inferred_check(&hir);
    assert!(typed.is_ok(), "{:?}", messages(&typed, &names));
    assert_eq!(typed.binder(y), typed.binder(x));
    // Rendering is capped.
    let shown = typed.display(typed.binder(y).unwrap(), &names).to_string();
    assert!(shown.len() < 400);
}

/// `fn id<T>(x: T) -> T { x }`.
fn id_fn(k: &mut Kit) -> ItemId {
    let t = k.type_param("T");
    let gp = k.gparam(t, &[]);
    let g = k.generics(&[gp], &[]);
    let tt = k.tp("T", t);
    let (p, x) = k.param("x", Some(tt), ParamKind::Normal, None);
    let ux = k.use_(x);
    let body = k.block(&[], Some(ux));
    let ret = k.tp("T", t);
    k.gfunc("id", g, &[p], Some(ret), body)
}

fn nested_id_steps(depth: usize) -> u64 {
    let mut k = Kit::new();
    let id = id_fn(&mut k);
    let mut e = k.int(1);
    for _ in 0..depth {
        e = k.call_item("id", id, &[e]);
    }
    let (s, r) = k.let_("r", None, Some(e));
    let body = k.block(&[s], None);
    let (hir, _) = k.finish_main(&[id], body);
    let typed = inferred_check(&hir);
    assert!(typed.is_ok());
    assert_eq!(typed.binder(r), Some(I64));
    assert_eq!(
        typed.mono_plan().len(),
        1,
        "one instance, however many calls"
    );
    typed.stats().steps
}

#[test]
fn test_deep_generic_calls_are_linear() {
    let small = nested_id_steps(10_000);
    let large = nested_id_steps(20_000);
    let ratio = large as f64 / small as f64;
    assert!((1.6..2.6).contains(&ratio), "steps {small} -> {large}");
    let _ = nested_id_steps(50_000);
}

#[test]
fn test_recursive_blanket_bound_is_a_budget_error() {
    let mut k = Kit::new();
    let tr = marker(&mut k, "Tr");
    // impl<T: Tr> Tr for T {}
    let t = k.type_param("T");
    let b = k.path_ty("Tr", tr, &[]);
    let gp = k.gparam(t, &[b]);
    let g = k.generics(&[gp], &[]);
    let it = k.path_ty("Tr", tr, &[]);
    let tt = k.tp("T", t);
    let imp = k.impl_of(g, Some(it), tt, &[]);
    let nd = need(&mut k, tr);
    let one = k.int(1);
    let c = k.call_item("need", nd, &[one]);
    let s = k.stmt(c);
    let body = k.block(&[s], None);
    let (hir, _) = k.finish_main(&[tr, imp, nd], body);
    assert_eq!(
        check(&hir, &Profile::static_inferred()),
        Err(CheckError::BudgetExceeded {
            limit: Limit::TraitDepth
        })
    );
}

#[test]
fn test_ever_growing_resolution_is_a_budget_error() {
    let mut k = Kit::new();
    let w = wrap(&mut k);
    let tr = marker(&mut k, "Tr");
    // impl<T> Tr for W<T> where W<W<T>>: Tr {}
    let t = k.type_param("T");
    let gp = k.gparam(t, &[]);
    let tt = k.tp("T", t);
    let wt = k.path_ty("W", w, &[tt]);
    let wwt = k.path_ty("W", w, &[wt]);
    let b = k.path_ty("Tr", tr, &[]);
    let pred = k.where_(wwt, &[b]);
    let g = k.generics(&[gp], &[pred]);
    let it = k.path_ty("Tr", tr, &[]);
    let tt2 = k.tp("T", t);
    let self_ty = k.path_ty("W", w, &[tt2]);
    let imp = k.impl_of(g, Some(it), self_ty, &[]);
    let nd = need(&mut k, tr);
    let one = k.int(1);
    let lit = wrap_lit(&mut k, w, one);
    let c = k.call_item("need", nd, &[lit]);
    let s = k.stmt(c);
    let body = k.block(&[s], None);
    let (hir, _) = k.finish_main(&[w, tr, imp, nd], body);
    assert_eq!(
        check(&hir, &Profile::static_inferred()),
        Err(CheckError::BudgetExceeded {
            limit: Limit::TraitDepth
        })
    );
}

#[test]
fn test_trait_depth_budget_is_honoured() {
    // impl<T: Tr> Tr for W<T> {}  impl Tr for i64 {}
    // need(W{W{W{W{1}}}}) needs depth 5.
    let mut k = Kit::new();
    let w = wrap(&mut k);
    let tr = marker(&mut k, "Tr");
    let t = k.type_param("T");
    let b = k.path_ty("Tr", tr, &[]);
    let gp = k.gparam(t, &[b]);
    let g = k.generics(&[gp], &[]);
    let it = k.path_ty("Tr", tr, &[]);
    let tt = k.tp("T", t);
    let self_ty = k.path_ty("W", w, &[tt]);
    let imp = k.impl_of(g, Some(it), self_ty, &[]);
    let it2 = k.path_ty("Tr", tr, &[]);
    let i = k.prim(Prim::I64);
    let g = k.generics(&[], &[]);
    let base = k.impl_of(g, Some(it2), i, &[]);
    let nd = need(&mut k, tr);
    let mut e = k.int(1);
    for _ in 0..5 {
        e = wrap_lit(&mut k, w, e);
    }
    let c = k.call_item("need", nd, &[e]);
    let s = k.stmt(c);
    let body = k.block(&[s], None);
    let (hir, names) = k.finish_main(&[w, tr, imp, base, nd], body);
    let typed = inferred_check(&hir);
    assert!(typed.is_ok(), "{:?}", messages(&typed, &names));
    let mut checker = Checker::new(&hir, Profile::static_inferred());
    let _ = checker.set_budget(Budget {
        trait_depth: 3,
        ..Budget::default()
    });
    assert_eq!(
        checker.check(),
        Err(CheckError::BudgetExceeded {
            limit: Limit::TraitDepth
        })
    );
}

#[test]
fn test_supertrait_cycle_terminates() {
    let mut k = Kit::new();
    // trait A: B {}  trait B: A {}  -- built with forward references.
    let a_id = probe(&mut k) + 1;
    let a_ref = ItemId::from_index(a_id).expect("id");
    let b_ref = ItemId::from_index(a_id + 1).expect("id");
    let sb = k.path_ty("B", b_ref, &[]);
    let g = k.generics(&[], &[]);
    let a = k.iface("A", g, &[sb], &[]);
    assert_eq!(a, a_ref);
    let sa = k.path_ty("A", a, &[]);
    let g = k.generics(&[], &[]);
    let bi = k.iface("B", g, &[sa], &[]);
    assert_eq!(bi, b_ref);
    // fn f<T: A>(x: T) { x.m() }
    let t = k.type_param("T");
    let bound = k.path_ty("A", a, &[]);
    let gp = k.gparam(t, &[bound]);
    let g = k.generics(&[gp], &[]);
    let tt = k.tp("T", t);
    let (p, x) = k.param("x", Some(tt), ParamKind::Normal, None);
    let ux = k.use_(x);
    let call = k.method_call(ux, "m", &[]);
    let s = k.stmt(call);
    let body = k.block(&[s], None);
    let f = k.gfunc("f", g, &[p], None, body);
    let (hir, names) = k.finish_items(&[a, bi, f]);
    let typed = inferred_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0013 `T` has no method or associated item `m`"]
    );
}

/// Burns an item id (a dead error item) and returns it, so later items'
/// ids are known before they are built.
fn probe(k: &mut Kit) -> usize {
    k.b.item(hir_lang::Item::new(None, hir_lang::ItemKind::Err))
        .index()
}

#[test]
fn test_cyclic_generic_aliases_are_reported() {
    let mut k = Kit::new();
    let first = probe(&mut k) + 1;
    let a_ref = ItemId::from_index(first).expect("id");
    let b_ref = ItemId::from_index(first + 1).expect("id");
    // type A<T> = B<T>;  type B<U> = A<U>;
    let t = k.type_param("T");
    let gp = k.gparam(t, &[]);
    let g = k.generics(&[gp], &[]);
    let tt = k.tp("T", t);
    let body = k.path_ty("B", b_ref, &[tt]);
    let a = k.alias("A", g, body);
    assert_eq!(a, a_ref);
    let u = k.type_param("U");
    let gp = k.gparam(u, &[]);
    let g = k.generics(&[gp], &[]);
    let ut = k.tp("U", u);
    let body = k.path_ty("A", a, &[ut]);
    let b = k.alias("B", g, body);
    assert_eq!(b, b_ref);
    let i = k.prim(Prim::I64);
    let ann = k.path_ty("A", a, &[i]);
    let (p, _) = k.param("x", Some(ann), ParamKind::Normal, None);
    let body = k.block(&[], None);
    let f = k.func("f", &[p], None, body);
    let (hir, names) = k.finish_items(&[a, b, f]);
    let typed = inferred_check(&hir);
    let msgs = messages(&typed, &names);
    assert!(msgs.iter().any(|m| m.starts_with("T0029")), "{msgs:?}");
}

#[test]
fn test_cyclic_associated_type_is_a_budget_error() {
    let mut k = Kit::new();
    // trait Tr { type A; }  struct X {}  impl Tr for X { type A = <X as Tr>::A; }
    let assoc = k.assoc("A", &[], None);
    let g = k.generics(&[], &[]);
    let tr = k.iface("Tr", g, &[], &[assoc]);
    let x = k.record("X", &[]);
    let qself = k.item_ty("X", x);
    let a = k.name("Tr");
    let n = k.name("A");
    let origin = k.b.origin();
    let segments = k.b.list(&[
        hir_lang::Segment::new(a, origin),
        hir_lang::Segment::new(n, origin),
    ]);
    let def = k.b.def(hir_lang::Def::Item(tr));
    let path = k.b.path(hir_lang::Path {
        res: Res::Def(def),
        unresolved: 1,
        qself: Some(hir_lang::QSelf {
            ty: qself,
            trait_len: 1,
        }),
        ..hir_lang::Path::new(segments, hir_lang::Ns::Type)
    });
    let cyc = k.ty(hir_lang::Ty::Path(path));
    let g = k.generics(&[], &[]);
    let adef = k.alias("A", g, cyc);
    let it = k.path_ty("Tr", tr, &[]);
    let xt = k.item_ty("X", x);
    let g = k.generics(&[], &[]);
    let imp = k.impl_of(g, Some(it), xt, &[adef]);
    let (hir, _) = k.finish_items(&[tr, x, imp]);
    // On a 1 MiB stack (a Windows main thread), in a debug build.
    let result = std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(1 << 20)
            .spawn_scoped(scope, || check(&hir, &Profile::static_inferred()))
            .expect("thread")
            .join()
            .expect("no stack overflow")
    });
    match result {
        Err(CheckError::BudgetExceeded {
            limit: Limit::TraitDepth,
        }) => {}
        Ok(t) => assert!(!t.is_ok(), "a cycle must not check clean"),
        Err(other) => panic!("{other:?}"),
    }
}

fn many_impls_steps(n: usize) -> u64 {
    let mut k = Kit::new();
    // trait Show { fn show(&self) -> i64; }
    let st = k.self_ty();
    let r = k.ref_ty(false, st);
    let (recv, _) = k.receiver(Some(r));
    let ret = k.prim(Prim::I64);
    let decl = k.decl("show", &[recv], Some(ret));
    let g = k.generics(&[], &[]);
    let show = k.iface("Show", g, &[], &[decl]);
    let mut items = vec![show];
    let mut stmts = Vec::new();
    for i in 0..n {
        let rec = k.record(&format!("R{i}"), &[]);
        let st = k.self_ty();
        let r = k.ref_ty(false, st);
        let ret = k.prim(Prim::I64);
        let m = k.method("show", Some(r), &[], Some(ret), |k, _| {
            let one = k.int(1);
            k.block(&[], Some(one))
        });
        let it = k.path_ty("Show", show, &[]);
        let rt = k.item_ty("R", rec);
        let g = k.generics(&[], &[]);
        let imp = k.impl_of(g, Some(it), rt, &[m]);
        items.push(rec);
        items.push(imp);
        // let v = R_i {}; v.show();
        let nm = k.name("R");
        let def = k.b.def(hir_lang::Def::Item(rec));
        let path = k.b.resolved_path(nm, hir_lang::Ns::Type, Res::Def(def));
        let fields = k.b.list(&[]);
        let lit = k.expr(Expr::Record {
            path: Some(path),
            fields,
            base: None,
        });
        let (s, v) = k.let_("v", None, Some(lit));
        let uv = k.use_(v);
        let call = k.method_call(uv, "show", &[]);
        stmts.push(s);
        stmts.push(k.stmt(call));
    }
    let body = k.block(&stmts, None);
    let (hir, _) = k.finish_main(&items, body);
    let typed = inferred_check(&hir);
    assert!(typed.is_ok());
    typed.stats().steps
}

#[test]
fn test_impl_tables_scale_linearly() {
    let small = many_impls_steps(2_000);
    let large = many_impls_steps(4_000);
    let ratio = large as f64 / small as f64;
    assert!((1.6..2.6).contains(&ratio), "steps {small} -> {large}");
}

#[test]
fn test_cyclic_generic_default_is_a_budget_error_on_a_small_stack() {
    // struct S<T = S> { v: T }: lowering `S` fills its default with `S`...
    let run = || {
        let mut k = Kit::new();
        let first = probe(&mut k) + 1;
        let s_ref = ItemId::from_index(first).expect("id");
        let t = k.type_param("T");
        let default = k.path_ty("S", s_ref, &[]);
        let gp = k.gparam_default(t, default);
        let g = k.generics(&[gp], &[]);
        let tt = k.tp("T", t);
        let s = k.grecord("S", g, &[("v", tt)]);
        assert_eq!(s, s_ref);
        let ann = k.path_ty("S", s, &[]);
        let (p, _) = k.param("x", Some(ann), ParamKind::Normal, None);
        let body = k.block(&[], None);
        let f = k.func("f", &[p], None, body);
        let (hir, _) = k.finish_items(&[s, f]);
        check(&hir, &Profile::static_inferred())
    };
    // A 1 MiB stack, like a Windows main thread, in a debug build.
    let r = std::thread::Builder::new()
        .stack_size(1 << 20)
        .spawn(run)
        .expect("thread")
        .join()
        .expect("no stack overflow");
    assert_eq!(
        r.map(|t| t.is_ok()),
        Err(CheckError::BudgetExceeded {
            limit: Limit::TraitDepth
        })
    );
}
