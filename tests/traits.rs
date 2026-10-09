//! Interfaces in depth: `dyn` and `impl Trait` types, coherence (overlap),
//! conformance (missing and extra members, signatures), supertraits,
//! where clauses, interface paths (`T::make()`, `Show::show(x)`), qualified
//! associated types, `Interfaces` polymorphism with classes, auto-ref as a
//! profile toggle, unions and intersections.

mod common;

use common::{Kit, inferred_check, messages};
use hir_lang::{Bound, ItemId, ParamKind, Prim, QSelf, Res, Ty};
use typeck_lang::{Coercion, Dispatch, Polymorphism, Profile, Type, TypeId, check};

const I64: TypeId = TypeId::prim(Prim::I64);
const STR: TypeId = TypeId::prim(Prim::Str);

/// `trait Show { fn show(&self) -> str; }`
fn show_iface(k: &mut Kit) -> ItemId {
    let st = k.self_ty();
    let r = k.ref_ty(false, st);
    let (recv, _) = k.receiver(Some(r));
    let ret = k.prim(Prim::Str);
    let decl = k.decl("show", &[recv], Some(ret));
    let g = k.generics(&[], &[]);
    k.iface("Show", g, &[], &[decl])
}

/// `impl Show for <self_ty> { fn show(&self) -> str { "x" } }`
fn show_impl(k: &mut Kit, iface: ItemId, self_ty: hir_lang::TyId) -> (ItemId, ItemId) {
    let st = k.self_ty();
    let r = k.ref_ty(false, st);
    let ret = k.prim(Prim::Str);
    let m = k.method("show", Some(r), &[], Some(ret), |k, _| {
        let s = k.str("x");
        k.block(&[], Some(s))
    });
    let it = k.path_ty("Show", iface, &[]);
    let g = k.generics(&[], &[]);
    (k.impl_of(g, Some(it), self_ty, &[m]), m)
}

fn dyn_show(k: &mut Kit, iface: ItemId) -> hir_lang::TyId {
    let it = k.path_ty("Show", iface, &[]);
    let bounds = k.b.list(&[Bound::Ty(it)]);
    k.ty(Ty::Object(bounds))
}

#[test]
fn test_dyn_coercion_and_dynamic_dispatch() {
    let mut k = Kit::new();
    let iface = show_iface(&mut k);
    let i = k.prim(Prim::I64);
    let (imp, _) = show_impl(&mut k, iface, i);
    // fn print(x: &dyn Show) -> str { x.show() }
    let d = dyn_show(&mut k, iface);
    let rd = k.ref_ty(false, d);
    let (p, x) = k.param("x", Some(rd), ParamKind::Normal, None);
    let ux = k.use_(x);
    let call = k.method_call(ux, "show", &[]);
    let body = k.block(&[], Some(call));
    let ret = k.prim(Prim::Str);
    let print = k.func("print", &[p], Some(ret), body);
    // main: let n: i64 = 3; print(&n)
    let i2 = k.prim(Prim::I64);
    let three = k.int(3);
    let (s1, n) = k.let_("n", Some(i2), Some(three));
    let un = k.use_(n);
    let borrow = k.expr(hir_lang::Expr::Borrow {
        kind: hir_lang::BorrowKind::Shared,
        expr: un,
    });
    let pc = k.call_item("print", print, &[borrow]);
    let s2 = k.stmt(pc);
    let body = k.block(&[s1, s2], None);
    let (hir, names) = k.finish_main(&[iface, imp, print], body);
    let typed = inferred_check(&hir);
    assert!(typed.is_ok(), "{:?}", messages(&typed, &names));
    assert_eq!(typed.expr(call), Some(STR));
    assert_eq!(
        typed.instantiation(call).map(|i| i.dispatch),
        Some(Dispatch::Dynamic)
    );
    assert!(matches!(typed.coercion(borrow), Some((Coercion::ToDyn, _))));
    assert_eq!(
        typed.display(typed.binder(x).unwrap(), &names).to_string(),
        "&dyn Show"
    );
}

#[test]
fn test_dyn_of_type_without_impl_is_unsatisfied() {
    let mut k = Kit::new();
    let iface = show_iface(&mut k);
    let d = dyn_show(&mut k, iface);
    let rd = k.ref_ty(false, d);
    let (p, _) = k.param("x", Some(rd), ParamKind::Normal, None);
    let body = k.block(&[], None);
    let take = k.func("take", &[p], None, body);
    let b = k.bool(true);
    let borrow = k.expr(hir_lang::Expr::Borrow {
        kind: hir_lang::BorrowKind::Shared,
        expr: b,
    });
    let c = k.call_item("take", take, &[borrow]);
    let s = k.stmt(c);
    let body = k.block(&[s], None);
    let (hir, names) = k.finish_main(&[iface, take], body);
    let typed = inferred_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0046 `bool` does not implement `Show`"]
    );
}

#[test]
fn test_impl_trait_result_is_opaque_with_hidden_type() {
    let mut k = Kit::new();
    let iface = show_iface(&mut k);
    let i = k.prim(Prim::I64);
    let (imp, _) = show_impl(&mut k, iface, i);
    // fn make() -> impl Show { 5 }
    let it = k.path_ty("Show", iface, &[]);
    let bounds = k.b.list(&[Bound::Ty(it)]);
    let opaque = k.ty(Ty::Impl(bounds));
    let five = k.int(5);
    let body = k.block(&[], Some(five));
    let make = k.func("make", &[], Some(opaque), body);
    // main: let v = make(); v.show()
    let c = k.call_item("make", make, &[]);
    let (s1, v) = k.let_("v", None, Some(c));
    let uv = k.use_(v);
    let call = k.method_call(uv, "show", &[]);
    let s2 = k.stmt(call);
    let body = k.block(&[s1, s2], None);
    let (hir, names) = k.finish_main(&[iface, imp, make], body);
    let typed = inferred_check(&hir);
    assert!(typed.is_ok(), "{:?}", messages(&typed, &names));
    assert_eq!(typed.expr(call), Some(STR));
    assert_eq!(typed.opaque_type(opaque), Some(I64));
    assert!(matches!(
        typed.types().get(typed.binder(v).unwrap()),
        Type::Opaque { .. }
    ));
    assert_eq!(
        typed.display(typed.binder(v).unwrap(), &names).to_string(),
        "impl Show"
    );
}

#[test]
fn test_impl_trait_parameter_is_generic() {
    let mut k = Kit::new();
    let iface = show_iface(&mut k);
    let i = k.prim(Prim::I64);
    let (imp, _) = show_impl(&mut k, iface, i);
    // fn print(x: impl Show) -> str { x.show() }
    let it = k.path_ty("Show", iface, &[]);
    let bounds = k.b.list(&[Bound::Ty(it)]);
    let apit = k.ty(Ty::Impl(bounds));
    let (p, x) = k.param("x", Some(apit), ParamKind::Normal, None);
    let ux = k.use_(x);
    let call = k.method_call(ux, "show", &[]);
    let body = k.block(&[], Some(call));
    let ret = k.prim(Prim::Str);
    let print = k.func("print", &[p], Some(ret), body);
    let one = k.int(1);
    let c1 = k.call_item("print", print, &[one]);
    let s1 = k.stmt(c1);
    let f = k.float(1.5);
    let c2 = k.call_item("print", print, &[f]);
    let s2 = k.stmt(c2);
    let body = k.block(&[s1, s2], None);
    let (hir, names) = k.finish_main(&[iface, imp, print], body);
    let typed = inferred_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0046 `f64` does not implement `Show`"]
    );
    assert!(
        typed
            .mono_plan()
            .instances_of(print)
            .any(|i| i.args == [I64])
    );
}

#[test]
fn test_overlapping_impls_are_reported() {
    let mut k = Kit::new();
    let iface = show_iface(&mut k);
    let i = k.prim(Prim::I64);
    let (a, _) = show_impl(&mut k, iface, i);
    // impl<T> Show for T  -- overlaps the impl for i64
    let t = k.type_param("T");
    let gp = k.gparam(t, &[]);
    let g = k.generics(&[gp], &[]);
    let tt = k.tp("T", t);
    let st = k.self_ty();
    let r = k.ref_ty(false, st);
    let ret = k.prim(Prim::Str);
    let m = k.method("show", Some(r), &[], Some(ret), |k, _| {
        let s = k.str("t");
        k.block(&[], Some(s))
    });
    let it = k.path_ty("Show", iface, &[]);
    let blanket = k.impl_of(g, Some(it), tt, &[m]);
    let (hir, names) = k.finish_items(&[iface, a, blanket]);
    let typed = inferred_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0048 this implementation overlaps an earlier one"]
    );
}

#[test]
fn test_extra_member_and_signature_mismatch() {
    let mut k = Kit::new();
    let iface = show_iface(&mut k);
    // impl Show for bool { fn show(&self) -> i64 { 1 } fn extra(&self) {} }
    let st = k.self_ty();
    let r = k.ref_ty(false, st);
    let ret = k.prim(Prim::I64);
    let m = k.method("show", Some(r), &[], Some(ret), |k, _| {
        let one = k.int(1);
        k.block(&[], Some(one))
    });
    let st = k.self_ty();
    let r = k.ref_ty(false, st);
    let extra = k.method("extra", Some(r), &[], None, |k, _| k.block(&[], None));
    let it = k.path_ty("Show", iface, &[]);
    let b = k.prim(Prim::Bool);
    let g = k.generics(&[], &[]);
    let imp = k.impl_of(g, Some(it), b, &[m, extra]);
    let (hir, names) = k.finish_items(&[iface, imp]);
    let typed = inferred_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        [
            "T0001 mismatched types: expected `str`, found `i64`",
            "T0050 `extra` is not a member of `Show`",
        ]
    );
}

#[test]
fn test_supertrait_methods_through_a_bound() {
    let mut k = Kit::new();
    let base = show_iface(&mut k);
    // trait Pretty: Show {}
    let sup = k.path_ty("Show", base, &[]);
    let g = k.generics(&[], &[]);
    let pretty = k.iface("Pretty", g, &[sup], &[]);
    // fn f<T: Pretty>(x: &T) -> str { x.show() }
    let t = k.type_param("T");
    let pb = k.path_ty("Pretty", pretty, &[]);
    let gp = k.gparam(t, &[pb]);
    let g = k.generics(&[gp], &[]);
    let tt = k.tp("T", t);
    let rt = k.ref_ty(false, tt);
    let (p, x) = k.param("x", Some(rt), ParamKind::Normal, None);
    let ux = k.use_(x);
    let call = k.method_call(ux, "show", &[]);
    let body = k.block(&[], Some(call));
    let ret = k.prim(Prim::Str);
    let f = k.gfunc("f", g, &[p], Some(ret), body);
    let (hir, names) = k.finish_items(&[base, pretty, f]);
    let typed = inferred_check(&hir);
    assert!(typed.is_ok(), "{:?}", messages(&typed, &names));
    assert_eq!(typed.expr(call), Some(STR));
}

#[test]
fn test_static_member_through_bound_and_interface_path() {
    let mut k = Kit::new();
    // trait Make { fn make() -> Self; }
    let ret = k.self_ty();
    let decl = k.decl("make", &[], Some(ret));
    let g = k.generics(&[], &[]);
    let make = k.iface("Make", g, &[], &[decl]);
    // impl Make for i64 { fn make() -> i64 { 0 } }
    let r = k.prim(Prim::I64);
    let zero = k.int(0);
    let body = k.block(&[], Some(zero));
    let mdef = k.func("make", &[], Some(r), body);
    let mt = k.path_ty("Make", make, &[]);
    let i = k.prim(Prim::I64);
    let g = k.generics(&[], &[]);
    let imp = k.impl_of(g, Some(mt), i, &[mdef]);
    // fn build<T: Make>() -> T { T::make() }
    let t = k.type_param("T");
    let mb = k.path_ty("Make", make, &[]);
    let gp = k.gparam(t, &[mb]);
    let g = k.generics(&[gp], &[]);
    let callee = k.assoc_expr("T", Res::Local(t), "make");
    let call = k.b.call(callee, &[]);
    let body = k.block(&[], Some(call));
    let ret = k.tp("T", t);
    let build = k.gfunc("build", g, &[], Some(ret), body);
    // main: let a: i64 = build(); let b: i64 = Make::make();
    let i2 = k.prim(Prim::I64);
    let c1 = k.call_item("build", build, &[]);
    let (s1, _) = k.let_("a", Some(i2), Some(c1));
    let i3 = k.prim(Prim::I64);
    let res = k.res(make);
    let callee2 = k.assoc_expr("Make", res, "make");
    let c2 = k.b.call(callee2, &[]);
    let (s2, _) = k.let_("b", Some(i3), Some(c2));
    let body = k.block(&[s1, s2], None);
    let (hir, names) = k.finish_main(&[make, imp, build], body);
    let typed = inferred_check(&hir);
    assert!(typed.is_ok(), "{:?}", messages(&typed, &names));
    assert_eq!(typed.expr(c2), Some(I64));
    // The plan resolves `Make::make` on `i64` to the impl's function.
    assert!(
        typed
            .mono_plan()
            .instances_of(build)
            .any(|i| i.args == [I64])
    );
}

#[test]
fn test_qualified_associated_type() {
    let mut k = Kit::new();
    // trait Container { type Elem; }
    let elem = k.assoc("Elem", &[], None);
    let g = k.generics(&[], &[]);
    let cont = k.iface("Container", g, &[], &[elem]);
    // impl Container for str { type Elem = char; }
    let ch = k.prim(Prim::Char);
    let g = k.generics(&[], &[]);
    let edef = k.alias("Elem", g, ch);
    let ct = k.path_ty("Container", cont, &[]);
    let st = k.prim(Prim::Str);
    let g = k.generics(&[], &[]);
    let imp = k.impl_of(g, Some(ct), st, &[edef]);
    // fn f(c: <str as Container>::Elem) -> char { c }
    let qself_ty = k.prim(Prim::Str);
    let a = k.name("Container");
    let n = k.name("Elem");
    let origin = k.b.origin();
    let segments = k.b.list(&[
        hir_lang::Segment::new(a, origin),
        hir_lang::Segment::new(n, origin),
    ]);
    let def = k.b.def(hir_lang::Def::Item(cont));
    let path = k.b.path(hir_lang::Path {
        res: Res::Def(def),
        unresolved: 1,
        qself: Some(QSelf {
            ty: qself_ty,
            trait_len: 1,
        }),
        ..hir_lang::Path::new(segments, hir_lang::Ns::Type)
    });
    let qt = k.ty(Ty::Path(path));
    let (p, c) = k.param("c", Some(qt), ParamKind::Normal, None);
    let uc = k.use_(c);
    let body = k.block(&[], Some(uc));
    let ret = k.prim(Prim::Char);
    let f = k.func("f", &[p], Some(ret), body);
    let (hir, names) = k.finish_items(&[cont, imp, f]);
    let typed = inferred_check(&hir);
    assert!(typed.is_ok(), "{:?}", messages(&typed, &names));
    assert_eq!(typed.binder(c), Some(TypeId::prim(Prim::Char)));
}

#[test]
fn test_interfaces_polymorphism_with_classes() {
    let mut k = Kit::new();
    let iface = show_iface(&mut k);
    // class Point implements Show { x: i64; fn show(&self) -> str { "p" } }
    let st = k.self_ty();
    let r = k.ref_ty(false, st);
    let ret = k.prim(Prim::Str);
    let m = k.method("show", Some(r), &[], Some(ret), |k, _| {
        let s = k.str("p");
        k.block(&[], Some(s))
    });
    let it = k.path_ty("Show", iface, &[]);
    let i = k.prim(Prim::I64);
    let g = k.generics(&[], &[]);
    let point = k.class("Point", g, &[], &[it], &[("x", i)], &[m]);
    // fn use(s: &Show) -> str { s.show() }   -- the interface as a type
    let ity = k.path_ty("Show", iface, &[]);
    let rt = k.ref_ty(false, ity);
    let (p, s) = k.param("s", Some(rt), ParamKind::Normal, None);
    let us = k.use_(s);
    let call = k.method_call(us, "show", &[]);
    let body = k.block(&[], Some(call));
    let ret = k.prim(Prim::Str);
    let f = k.func("use_it", &[p], Some(ret), body);
    let (hir, names) = k.finish_items(&[iface, point, f]);
    let interfaces = Profile::static_inferred().with_polymorphism(Polymorphism::Interfaces);
    let typed = check(&hir, &interfaces).unwrap();
    assert!(typed.is_ok(), "{:?}", messages(&typed, &names));
    assert_eq!(typed.expr(call), Some(STR));
    // Under `Traits`, an interface is not a type.
    let traits = inferred_check(&hir);
    assert_eq!(
        messages(&traits, &names),
        ["T0051 an interface is not a type here; write `dyn` or `impl` before it"]
    );
}

#[test]
fn test_method_autoref_toggle() {
    let mut k = Kit::new();
    let iface = show_iface(&mut k);
    let i = k.prim(Prim::I64);
    let (imp, _) = show_impl(&mut k, iface, i);
    let i2 = k.prim(Prim::I64);
    let one = k.int(1);
    let (s1, n) = k.let_("n", Some(i2), Some(one));
    let un = k.use_(n);
    let call = k.method_call(un, "show", &[]);
    let s2 = k.stmt(call);
    let body = k.block(&[s1, s2], None);
    let (hir, names) = k.finish_main(&[iface, imp], body);
    let on = inferred_check(&hir);
    assert!(on.is_ok(), "{:?}", messages(&on, &names));
    assert!(matches!(on.coercion(un), Some((Coercion::AutoRef, _))));
    let off = check(&hir, &Profile::static_inferred().with_method_autoref(false)).unwrap();
    assert_eq!(
        messages(&off, &names),
        ["T0001 mismatched types: expected `&i64`, found `i64`"]
    );
}

#[test]
fn test_unions_and_intersections() {
    let mut k = Kit::new();
    // fn f(x: i64 | str) {}
    let (i, s) = (k.prim(Prim::I64), k.prim(Prim::Str));
    let members = k.b.list(&[i, s]);
    let u = k.ty(Ty::Union(members));
    let (p, x) = k.param("x", Some(u), ParamKind::Normal, None);
    let body = k.block(&[], None);
    let f = k.func("f", &[p], None, body);
    let one = k.int(1);
    let c1 = k.call_item("f", f, &[one]);
    let hi = k.str("hi");
    let c2 = k.call_item("f", f, &[hi]);
    let yes = k.bool(true);
    let c3 = k.call_item("f", f, &[yes]);
    let stmts = [k.stmt(c1), k.stmt(c2), k.stmt(c3)];
    let body = k.block(&stmts, None);
    let (hir, names) = k.finish_main(&[f], body);
    let typed = inferred_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0001 mismatched types: expected `i64 | str`, found `bool`"]
    );
    assert!(matches!(typed.coercion(one), Some((Coercion::ToUnion, _))));
    assert!(matches!(typed.types().get(typed.binder(x).unwrap()), Type::Union(m) if m.len() == 2));
    let _ = I64;
}
