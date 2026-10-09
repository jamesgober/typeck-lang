//! Generic items in detail: explicit and inferred arguments, defaults,
//! argument counts, constant parameters (`Buf<4>`, `[T; N]`), generic
//! aliases, bounds checked at instantiation, and what is reported as
//! unsupported.

mod common;

use common::{Kit, inferred_check, messages};
use hir_lang::{ParamKind, Prim, Ty};
use typeck_lang::{DiagnosticKind, Feature, Type, TypeId};

const I64: TypeId = TypeId::prim(Prim::I64);

#[test]
fn test_explicit_generic_arguments_on_a_call() {
    let mut k = Kit::new();
    // fn id<T>(x: T) -> T { x }  main: let a = id::<i32>(1); let b = id::<bool>(1);
    let t = k.type_param("T");
    let gp = k.gparam(t, &[]);
    let g = k.generics(&[gp], &[]);
    let tt = k.tp("T", t);
    let (p, x) = k.param("x", Some(tt), ParamKind::Normal, None);
    let ux = k.use_(x);
    let body = k.block(&[], Some(ux));
    let ret = k.tp("T", t);
    let id = k.gfunc("id", g, &[p], Some(ret), body);
    let i32_ = k.prim(Prim::I32);
    let callee = k.item_expr_args("id", id, &[i32_]);
    let one = k.int(1);
    let c1 = k.b.call(callee, &[one]);
    let (s1, a) = k.let_("a", None, Some(c1));
    let bt = k.prim(Prim::Bool);
    let callee = k.item_expr_args("id", id, &[bt]);
    let one2 = k.int(1);
    let c2 = k.b.call(callee, &[one2]);
    let s2 = k.stmt(c2);
    let i1 = k.prim(Prim::I64);
    let i2 = k.prim(Prim::I64);
    let callee = k.item_expr_args("id", id, &[i1, i2]);
    let one3 = k.int(1);
    let c3 = k.b.call(callee, &[one3]);
    let s3 = k.stmt(c3);
    let body = k.block(&[s1, s2, s3], None);
    let (hir, names) = k.finish_main(&[id], body);
    let typed = inferred_check(&hir);
    assert_eq!(typed.binder(a), Some(TypeId::prim(Prim::I32)));
    assert_eq!(
        messages(&typed, &names),
        [
            "T0001 mismatched types: expected `bool`, found `i64`",
            "T0043 expected 1 generic arguments, found 2",
        ]
    );
    assert_eq!(typed.diagnostics()[0].node, hir_lang::NodeRef::Expr(one2));
}

#[test]
fn test_defaults_and_missing_arguments_in_annotations() {
    let mut k = Kit::new();
    // struct P<A, B = A> { a: A, b: B }
    let a = k.type_param("A");
    let b = k.type_param("B");
    let ga = k.gparam(a, &[]);
    let dflt = k.tp("A", a);
    let gb = k.gparam_default(b, dflt);
    let g = k.generics(&[ga, gb], &[]);
    let (at, bt) = (k.tp("A", a), k.tp("B", b));
    let pr = k.grecord("P", g, &[("a", at), ("b", bt)]);
    // fn f(x: P<i64>) {}       -- B defaults to A = i64
    let i = k.prim(Prim::I64);
    let ann = k.path_ty("P", pr, &[i]);
    let (p, x) = k.param("x", Some(ann), ParamKind::Normal, None);
    let body = k.block(&[], None);
    let f = k.func("f", &[p], None, body);
    // fn g(y: P) {}            -- A has no default: an error in a signature
    let ann = k.path_ty("P", pr, &[]);
    let (p2, _) = k.param("y", Some(ann), ParamKind::Normal, None);
    let body = k.block(&[], None);
    let g_fn = k.func("g", &[p2], None, body);
    let (hir, names) = k.finish_items(&[pr, f, g_fn]);
    let typed = inferred_check(&hir);
    assert_eq!(
        typed.display(typed.binder(x).unwrap(), &names).to_string(),
        "P<i64, i64>"
    );
    assert_eq!(
        messages(&typed, &names),
        ["T0043 expected 2 generic arguments, found 0"]
    );
}

#[test]
fn test_constant_generic_parameters() {
    let mut k = Kit::new();
    // struct Buf<const N: usize> { len: usize }
    let n = k.const_param("N");
    let us = k.prim(Prim::Usize);
    let gp = k.gconst(n, us);
    let g = k.generics(&[gp], &[]);
    let us2 = k.prim(Prim::Usize);
    let buf = k.grecord("Buf", g, &[("len", us2)]);
    // fn first<T, const M: usize>(a: [T; M]) -> usize { M }
    let t = k.type_param("T");
    let m = k.const_param("M");
    let gt = k.gparam(t, &[]);
    let us3 = k.prim(Prim::Usize);
    let gm = k.gconst(m, us3);
    let g = k.generics(&[gt, gm], &[]);
    let tt = k.tp("T", t);
    let len = k.cp_expr("M", m);
    let arr = k.ty(Ty::Array { elem: tt, len });
    let (p, xa) = k.param("a", Some(arr), ParamKind::Normal, None);
    let mv = k.cp_expr("M", m);
    let body = k.block(&[], Some(mv));
    let ret = k.prim(Prim::Usize);
    let first = k.gfunc("first", g, &[p], Some(ret), body);
    // fn g(b4: Buf<4>, b8: Buf<8>) { let n = first([1, 2, 3]); b4 = b8; }
    let four = k.int(4);
    let a4 = k.path_ty_args("Buf", buf, &[hir_lang::GenericArg::Const(four)]);
    let (p4, b4) = k.param("b4", Some(a4), ParamKind::Normal, None);
    let eight = k.int(8);
    let a8 = k.path_ty_args("Buf", buf, &[hir_lang::GenericArg::Const(eight)]);
    let (p8, b8) = k.param("b8", Some(a8), ParamKind::Normal, None);
    let elems: Vec<_> = (1..=3).map(|v| k.int(v)).collect();
    let el = k.b.list(&elems);
    let arr_lit = k.expr(hir_lang::Expr::Array(el));
    let call = k.call_item("first", first, &[arr_lit]);
    let (s1, nb) = k.let_("n", None, Some(call));
    let (u4, u8b) = (k.use_(b4), k.use_(b8));
    let assign = k.expr(hir_lang::Expr::Assign {
        target: u4,
        op: None,
        value: u8b,
    });
    let s2 = k.stmt(assign);
    let body = k.block(&[s1, s2], None);
    let g_fn = k.func("g", &[p4, p8], None, body);
    let (hir, names) = k.finish_items(&[buf, first, g_fn]);
    let typed = inferred_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0001 mismatched types: expected `Buf<4>`, found `Buf<8>`"]
    );
    assert_eq!(typed.binder(nb), Some(TypeId::prim(Prim::Usize)));
    assert!(matches!(
        typed.types().get(typed.binder(xa).unwrap()),
        Type::ParamArray { .. }
    ));
    let inst = typed
        .mono_plan()
        .instances_of(first)
        .next()
        .expect("instance");
    assert_eq!(inst.args.first(), Some(&I64));
    assert!(matches!(typed.types().get(inst.args[1]), Type::Const(3)));
}

#[test]
fn test_generic_alias_expands_with_its_arguments() {
    let mut k = Kit::new();
    // type Pair<T> = (T, T);  fn f(p: Pair<bool>) -> bool { p.0 }
    let t = k.type_param("T");
    let gp = k.gparam(t, &[]);
    let g = k.generics(&[gp], &[]);
    let (a, b) = (k.tp("T", t), k.tp("T", t));
    let l = k.b.list(&[a, b]);
    let tup = k.ty(Ty::Tuple(l));
    let pair = k.alias("Pair", g, tup);
    let bt = k.prim(Prim::Bool);
    let ann = k.path_ty("Pair", pair, &[bt]);
    let (p, x) = k.param("p", Some(ann), ParamKind::Normal, None);
    let body = k.block(&[], None);
    let f = k.func("f", &[p], None, body);
    let (hir, names) = k.finish_items(&[pair, f]);
    let typed = inferred_check(&hir);
    assert!(typed.is_ok(), "{:?}", messages(&typed, &names));
    assert_eq!(
        typed.display(typed.binder(x).unwrap(), &names).to_string(),
        "(bool, bool)"
    );
}

#[test]
fn test_generic_associated_type_is_reported_unsupported() {
    let mut k = Kit::new();
    let item = k.assoc("Item", &[], None);
    let g = k.generics(&[], &[]);
    let tr = k.iface("Tr", g, &[], &[item]);
    // impl Tr for i64 { type Item<U> = U; }
    let u = k.type_param("U");
    let gp = k.gparam(u, &[]);
    let g = k.generics(&[gp], &[]);
    let ut = k.tp("U", u);
    let alias = k.alias("Item", g, ut);
    let it = k.path_ty("Tr", tr, &[]);
    let i = k.prim(Prim::I64);
    let g0 = k.generics(&[], &[]);
    let imp = k.impl_of(g0, Some(it), i, &[alias]);
    let (hir, _) = k.finish_items(&[tr, imp]);
    let typed = inferred_check(&hir);
    assert_eq!(
        typed.diagnostics()[0].kind,
        DiagnosticKind::Unsupported {
            feature: Feature::GenericAssocTypes
        }
    );
}

#[test]
fn test_bounds_are_checked_at_instantiation_of_types() {
    let mut k = Kit::new();
    // trait Ord {} impl Ord for i64 {}  struct Sorted<T: Ord> { v: T }
    let g = k.generics(&[], &[]);
    let ord = k.iface("Ord", g, &[], &[]);
    let it = k.path_ty("Ord", ord, &[]);
    let i = k.prim(Prim::I64);
    let g = k.generics(&[], &[]);
    let imp = k.impl_of(g, Some(it), i, &[]);
    let t = k.type_param("T");
    let b = k.path_ty("Ord", ord, &[]);
    let gp = k.gparam(t, &[b]);
    let g = k.generics(&[gp], &[]);
    let tt = k.tp("T", t);
    let sorted = k.grecord("Sorted", g, &[("v", tt)]);
    // main: let ok = Sorted { v: 1 };  let bad = Sorted { v: true };
    let mk = |k: &mut Kit, v: hir_lang::ExprId| {
        let n = k.name("Sorted");
        let def = k.b.def(hir_lang::Def::Item(sorted));
        let path =
            k.b.resolved_path(n, hir_lang::Ns::Type, hir_lang::Res::Def(def));
        let f = k.ident("v");
        let fields = k.b.list(&[hir_lang::FieldInit { name: f, value: v }]);
        k.expr(hir_lang::Expr::Record {
            path: Some(path),
            fields,
            base: None,
        })
    };
    let one = k.int(1);
    let ok = mk(&mut k, one);
    let (s1, _) = k.let_("ok", None, Some(ok));
    let yes = k.bool(true);
    let bad = mk(&mut k, yes);
    let (s2, _) = k.let_("bad", None, Some(bad));
    let body = k.block(&[s1, s2], None);
    let (hir, names) = k.finish_main(&[ord, imp, sorted], body);
    let typed = inferred_check(&hir);
    let msgs = messages(&typed, &names);
    // Construction sites check the record's bounds.
    assert_eq!(msgs, ["T0046 `bool` does not implement `Ord`"], "{msgs:?}");
}

#[test]
fn test_bounds_are_checked_in_annotations() {
    let mut k = Kit::new();
    // trait Ord {}  struct Sorted<T: Ord> { v: T }
    let g = k.generics(&[], &[]);
    let ord = k.iface("Ord", g, &[], &[]);
    let t = k.type_param("T");
    let b = k.path_ty("Ord", ord, &[]);
    let gp = k.gparam(t, &[b]);
    let g = k.generics(&[gp], &[]);
    let tt = k.tp("T", t);
    let sorted = k.grecord("Sorted", g, &[("v", tt)]);
    // fn ok<U: Ord>(x: Sorted<U>) {}   fn bad<V>(x: Sorted<V>) {}
    let u = k.type_param("U");
    let b = k.path_ty("Ord", ord, &[]);
    let gp = k.gparam(u, &[b]);
    let g = k.generics(&[gp], &[]);
    let ut = k.tp("U", u);
    let ann = k.path_ty("Sorted", sorted, &[ut]);
    let (p, _) = k.param("x", Some(ann), ParamKind::Normal, None);
    let body = k.block(&[], None);
    let ok = k.gfunc("ok", g, &[p], None, body);
    let v = k.type_param("V");
    let gp = k.gparam(v, &[]);
    let g = k.generics(&[gp], &[]);
    let vt = k.tp("V", v);
    let ann = k.path_ty("Sorted", sorted, &[vt]);
    let (p, _) = k.param("x", Some(ann), ParamKind::Normal, None);
    let body = k.block(&[], None);
    let bad = k.gfunc("bad", g, &[p], None, body);
    let (hir, names) = k.finish_items(&[ord, sorted, ok, bad]);
    let typed = inferred_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0046 `V` does not implement `Ord`"]
    );
    assert!(matches!(
        typed.diagnostics()[0].node,
        hir_lang::NodeRef::Ty(_)
    ));
}
