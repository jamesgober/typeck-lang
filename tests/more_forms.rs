//! Forms not covered elsewhere: anonymous records under structural typing,
//! named-variant literals through partial paths, `&self` receivers, tuple
//! spreads, by-reference parameters, constants, `Self::` paths, enum
//! discriminants, and field defaults.

mod common;

use common::{Kit, messages, static_check};
use hir_lang::{
    Arg, ArgKind, Def, Expr, FieldInit, Ident, Item, ItemKind, List, Ns, ParamKind, Path, PathRoot,
    Prim, Res, Segment, Shape, Span, SumDef, Ty, Variant,
};
use typeck_lang::{Coercion, Profile, RecordTyping, Type, TypeId, check};

const I64: TypeId = TypeId::prim(Prim::I64);
const F64: TypeId = TypeId::prim(Prim::F64);

#[test]
fn test_anonymous_record_literals() {
    let mut k = Kit::new();
    let (t1, t2) = (k.prim(Prim::F64), k.prim(Prim::F64));
    let point = k.record("Point", &[("x", t1), ("y", t2)]);
    // let p: Point = { x: 1.0, y: 2.0 };
    let (one, two) = (k.float(1.0), k.float(2.0));
    let (xi, yi) = (k.ident("x"), k.ident("y"));
    let fields = k.b.list(&[
        FieldInit {
            name: yi,
            value: two,
        },
        FieldInit {
            name: xi,
            value: one,
        },
    ]);
    let anon = k.expr(Expr::Record {
        path: None,
        fields,
        base: None,
    });
    let pt = k.item_ty("Point", point);
    let (s, p) = k.let_("p", Some(pt), Some(anon));
    let body = k.block(&[s], None);
    let (hir, names) = k.finish_main(&[point], body);
    // Nominal: an anonymous record is not a `Point`.
    let nominal = static_check(&hir);
    assert_eq!(
        messages(&nominal, &names),
        ["T0001 mismatched types: expected `Point`, found `{ x: f64, y: f64 }`"]
    );
    // Structural: it is.
    let structural = check(
        &hir,
        &Profile::static_explicit().with_records(RecordTyping::Structural),
    )
    .unwrap();
    assert!(structural.is_ok(), "{:?}", structural.diagnostics());
    assert!(
        matches!(structural.types().get(structural.binder(p).unwrap()), Type::Adt { item: i, .. } if i == point)
    );
}

#[test]
fn test_named_variant_literals_through_partial_paths() {
    let mut k = Kit::new();
    // enum Shape { Rect { w: f64, h: f64 } }
    let (tw, th) = (k.prim(Prim::F64), k.prim(Prim::F64));
    let (fw, fh) = (k.field("w", Some(tw)), k.field("h", Some(th)));
    let fields = k.b.list(&[fw, fh]);
    let rect_name = k.ident("Rect");
    let rect = k.b.variant(Variant {
        name: rect_name,
        shape: Shape::Named,
        fields,
        discriminant: None,
    });
    let variants = k.b.list(&[rect]);
    let sn = k.name("Shape");
    let shape = k.b.item(Item::new(
        Some(sn),
        ItemKind::Sum(SumDef {
            variants,
            ..SumDef::default()
        }),
    ));
    // Shape::Rect { w: 1.0 }   (missing h)
    let (a, r) = (k.name("Shape"), k.name("Rect"));
    let origin = k.b.origin();
    let segs =
        k.b.list(&[Segment::new(a, origin), Segment::new(r, origin)]);
    let def = k.b.def(Def::Item(shape));
    let path = k.b.path(Path {
        res: Res::Def(def),
        unresolved: 1,
        ..Path::new(segs, Ns::Type)
    });
    let one = k.float(1.0);
    let wi = k.ident("w");
    let inits = k.b.list(&[FieldInit {
        name: wi,
        value: one,
    }]);
    let lit = k.expr(Expr::Record {
        path: Some(path),
        fields: inits,
        base: None,
    });
    let s = k.stmt(lit);
    let body = k.block(&[s], None);
    let (hir, names) = k.finish_main(&[shape], body);
    let typed = static_check(&hir);
    assert_eq!(messages(&typed, &names), ["T0015 missing field `h`"]);
    assert_eq!(typed.path_def(path), Some(Def::Variant(rect)));
    assert_eq!(typed.expr(one), Some(F64));
    assert!(
        matches!(typed.types().get(typed.expr(lit).unwrap()), Type::Adt { item: i, .. } if i == shape)
    );
}

#[test]
fn test_ref_self_receivers_are_borrowed_automatically() {
    let mut k = Kit::new();
    let t = k.prim(Prim::I64);
    let rec = k.record("C", &[("n", t)]);
    // impl C { fn n(self: &Self) -> i64 { 1 } }
    let self_ty = k.ty(Ty::SelfTy);
    let ref_self = k.ty(Ty::Ref {
        mutable: false,
        region: None,
        inner: self_ty,
    });
    let (recv, _) = k.receiver(Some(ref_self));
    let one = k.int(1);
    let body = k.block(&[], Some(one));
    let ret = k.prim(Prim::I64);
    let m = k.func("n", &[recv], Some(ret), body);
    let st = k.item_ty("C", rec);
    let imp = k.impl_(st, &[m]);
    // fn main(c: C) { c.n(); (&c).n(); }
    let ct = k.item_ty("C", rec);
    let (pc, c) = k.param("c", Some(ct), ParamKind::Normal, None);
    let uc = k.use_(c);
    let call1 = k.method_call(uc, "n", &[]);
    let s1 = k.stmt(call1);
    let uc2 = k.use_(c);
    let borrowed = k.expr(Expr::Borrow {
        kind: hir_lang::BorrowKind::Shared,
        expr: uc2,
    });
    let call2 = k.method_call(borrowed, "n", &[]);
    let s2 = k.stmt(call2);
    let main_body = k.block(&[s1, s2], None);
    let main = k.func("main", &[pc], None, main_body);
    let (hir, _) = k.finish_items(&[rec, imp, main]);
    let typed = static_check(&hir);
    assert!(typed.is_ok(), "{:?}", typed.diagnostics());
    assert_eq!(typed.coercion(uc).map(|c| c.0), Some(Coercion::AutoRef));
    assert_eq!(typed.coercion(borrowed), None);
    assert_eq!(typed.expr(call1), Some(I64));
    assert_eq!(typed.expr(call2), Some(I64));
}

#[test]
fn test_tuple_spreads_and_by_ref_parameters() {
    let mut k = Kit::new();
    let (t1, t2) = (k.prim(Prim::I64), k.prim(Prim::Bool));
    let (pa, _) = k.param("a", Some(t1), ParamKind::Normal, None);
    let (pb, _) = k.param("b", Some(t2), ParamKind::Normal, None);
    let body = k.block(&[], None);
    let f = k.func("f", &[pa, pb], None, body);
    // f(...(1, true))  fine;  f(...(true, 1)) twice wrong, reported at the spread
    let (one, yes) = (k.int(1), k.bool(true));
    let tl = k.b.list(&[one, yes]);
    let tup = k.expr(Expr::Tuple(tl));
    let callee = k.item_expr("f", f);
    let good = k.call_args(
        callee,
        &[Arg {
            kind: ArgKind::Spread,
            value: tup,
            place: false,
        }],
    );
    let s1 = k.stmt(good);
    let (yes2, one2) = (k.bool(true), k.int(1));
    let tl2 = k.b.list(&[yes2, one2]);
    let tup2 = k.expr(Expr::Tuple(tl2));
    let callee2 = k.item_expr("f", f);
    let bad = k.call_args(
        callee2,
        &[Arg {
            kind: ArgKind::Spread,
            value: tup2,
            place: false,
        }],
    );
    let s2 = k.stmt(bad);
    // fn g(&x: i64)   g(5) -> the by-ref parameter needs a place
    let t3 = k.prim(Prim::I64);
    let xn = k.name("x");
    let xb = k.b.new_binder(xn, hir_lang::BinderKind::Param);
    let xp = k.b.bind(xb);
    let px = k.b.param(hir_lang::Param {
        pat: xp,
        ty: Some(t3),
        default: None,
        kind: ParamKind::Normal,
        by_ref: true,
    });
    let gbody = k.block(&[], None);
    let g = k.func("g", &[px], None, gbody);
    let five = k.int(5);
    let gcall = k.call_item("g", g, &[five]);
    let s3 = k.stmt(gcall);
    let main_body = k.block(&[s1, s2, s3], None);
    let (hir, names) = k.finish_main(&[f, g], main_body);
    let typed = static_check(&hir);
    let got = messages(&typed, &names);
    assert_eq!(got.len(), 3, "{got:?}");
    assert!(got[0].starts_with("T0001"), "{got:?}");
    assert_eq!(typed.diagnostics()[0].node, hir_lang::NodeRef::Expr(tup2));
    assert_eq!(
        got[2],
        "T0034 a by-reference parameter needs a place argument"
    );
}

#[test]
fn test_constants_globals_and_array_lengths() {
    let mut k = Kit::new();
    // const N: usize = 2 + 1;  const BAD = 1;  let a: [i64; N] = [1, 2, 3];
    let usize_ty = k.prim(Prim::Usize);
    let (two, one) = (k.int(2), k.int(1));
    let sum = k.op(hir_lang::OpKind::Add, &[two, one]);
    let nn = k.name("N");
    let n_item = k.b.item(Item::new(
        Some(nn),
        ItemKind::Const {
            ty: Some(usize_ty),
            value: Some(sum),
        },
    ));
    let lit = k.int(1);
    let bn = k.name("BAD");
    let bad = k.b.item(Item::new(
        Some(bn),
        ItemKind::Const {
            ty: None,
            value: Some(lit),
        },
    ));
    let elem = k.prim(Prim::I64);
    let len = k.item_expr("N", n_item);
    let arr_ty = k.ty(Ty::Array { elem, len });
    let (x, y, z) = (k.int(1), k.int(2), k.int(3));
    let al = k.b.list(&[x, y, z]);
    let arr = k.expr(Expr::Array(al));
    let (s, a) = k.let_("a", Some(arr_ty), Some(arr));
    let body = k.block(&[s], None);
    let (hir, names) = k.finish_main(&[n_item, bad], body);
    let typed = static_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0002 a type annotation is required here"]
    );
    assert_eq!(
        typed.types().get(typed.binder(a).unwrap()),
        Type::Array { elem: I64, len: 3 }
    );
    // The length expression inside the annotation is typed too.
    assert_eq!(typed.expr(len), Some(TypeId::prim(Prim::Usize)));
    assert_eq!(typed.expr(sum), Some(TypeId::prim(Prim::Usize)));
}

#[test]
fn test_self_paths_inside_impls() {
    let mut k = Kit::new();
    let t = k.prim(Prim::I64);
    let rec = k.record("R", &[("v", t)]);
    // impl R { fn zero() -> i64 { 0 }  fn one() -> i64 { Self::zero() + 1 } }
    let z = k.int(0);
    let zb = k.block(&[], Some(z));
    let zr = k.prim(Prim::I64);
    let zero = k.func("zero", &[], Some(zr), zb);
    let zn = k.name("zero");
    let origin = k.b.origin();
    let segs = k.b.list(&[Segment::new(zn, origin)]);
    let self_path = k.b.path(Path {
        root: PathRoot::SelfType,
        unresolved: 1,
        ..Path::new(segs, Ns::Value)
    });
    let callee = k.expr(Expr::Path(self_path));
    let call = k.b.call(callee, &[]);
    let one = k.int(1);
    let sum = k.op(hir_lang::OpKind::Add, &[call, one]);
    let ob = k.block(&[], Some(sum));
    let or = k.prim(Prim::I64);
    let one_fn = k.func("one", &[], Some(or), ob);
    let st = k.item_ty("R", rec);
    let imp = k.impl_(st, &[zero, one_fn]);
    let (hir, _) = k.finish_items(&[rec, imp]);
    let typed = static_check(&hir);
    assert!(typed.is_ok(), "{:?}", typed.diagnostics());
    assert_eq!(typed.path_def(self_path), Some(Def::Item(zero)));
    assert_eq!(typed.expr(call), Some(I64));
}

#[test]
fn test_discriminants_and_field_defaults() {
    let mut k = Kit::new();
    // enum E { A = 1, B = true }   struct S { n: i64 = "x" }
    let one = k.int(1);
    let yes = k.bool(true);
    let an = k.ident("A");
    let bn = k.ident("B");
    let va = k.b.variant(Variant {
        name: an,
        shape: Shape::Unit,
        fields: List::EMPTY,
        discriminant: Some(one),
    });
    let vb = k.b.variant(Variant {
        name: bn,
        shape: Shape::Unit,
        fields: List::EMPTY,
        discriminant: Some(yes),
    });
    let vs = k.b.list(&[va, vb]);
    let en = k.name("E");
    let e = k.b.item(Item::new(
        Some(en),
        ItemKind::Sum(SumDef {
            variants: vs,
            ..SumDef::default()
        }),
    ));
    let t = k.prim(Prim::I64);
    let dflt = k.str("x");
    let nid = Ident::new(k.sym("n"), Span::empty(0));
    let f = k.b.field(hir_lang::FieldDef {
        ty: Some(t),
        default: Some(dflt),
        ..hir_lang::FieldDef::named(nid)
    });
    let fl = k.b.list(&[f]);
    let sn = k.name("S");
    let s = k.b.item(Item::new(
        Some(sn),
        ItemKind::Record(hir_lang::RecordDef {
            fields: fl,
            ..Default::default()
        }),
    ));
    let (hir, names) = k.finish_items(&[e, s]);
    let typed = static_check(&hir);
    let got = messages(&typed, &names);
    assert_eq!(got.len(), 2, "{got:?}");
    assert_eq!(typed.diagnostics()[0].node, hir_lang::NodeRef::Expr(yes));
    assert_eq!(typed.diagnostics()[1].node, hir_lang::NodeRef::Expr(dflt));
    assert_eq!(typed.expr(one), Some(I64));
}

#[test]
fn test_recursive_records_compare_structurally_and_terminate() {
    let mut k = Kit::new();
    // struct Node { next: Node? }  struct Link { next: Link? }
    let node_id = hir_lang::ItemId::from_index(0).unwrap();
    let link_id = hir_lang::ItemId::from_index(1).unwrap();
    let nt = k.item_ty("Node", node_id);
    let nn = k.ty(Ty::Nullable(nt));
    let node = k.record("Node", &[("next", nn)]);
    let lt = k.item_ty("Link", link_id);
    let ln = k.ty(Ty::Nullable(lt));
    let link = k.record("Link", &[("next", ln)]);
    assert_eq!((node, link), (node_id, link_id));
    let a_ty = k.item_ty("Node", node);
    let (pa, a) = k.param("a", Some(a_ty), ParamKind::Normal, None);
    let ua = k.use_(a);
    let b_ty = k.item_ty("Link", link);
    let (s, b) = k.let_("b", Some(b_ty), Some(ua));
    let body = k.block(&[s], None);
    let f = k.func("f", &[pa], None, body);
    let (hir, _) = k.finish_items(&[node, link, f]);
    let typed = check(
        &hir,
        &Profile::static_explicit().with_records(RecordTyping::Structural),
    )
    .unwrap();
    assert!(typed.is_ok(), "{:?}", typed.diagnostics());
    // Each binder keeps its declared nominal type.
    assert!(
        matches!(typed.types().get(typed.binder(a).unwrap()), Type::Adt { item: i, .. } if i == node)
    );
    assert!(
        matches!(typed.types().get(typed.binder(b).unwrap()), Type::Adt { item: i, .. } if i == link)
    );
    assert!(!static_check(&hir).is_ok(), "nominal: two types");
}

#[test]
fn test_unknown_and_literal_receivers() {
    let mut k = Kit::new();
    // let x; x.m(); x.f;   -> only CannotInfer
    let (s1, x) = k.let_("x", None, None);
    let ux = k.use_(x);
    let m = k.method_call(ux, "m", &[]);
    let s2 = k.stmt(m);
    let ux2 = k.use_(x);
    let f = k.field_expr(ux2, "f");
    let s3 = k.stmt(f);
    // 5()  -> not callable
    let five = k.int(5);
    let call = k.b.call(five, &[]);
    let s4 = k.stmt(call);
    // 7.foo()  -> looked up on the default integer type
    let seven = k.int(7);
    let mc = k.method_call(seven, "foo", &[]);
    let s5 = k.stmt(mc);
    let body = k.block(&[s1, s2, s3, s4, s5], None);
    let (hir, names) = k.finish_main(&[], body);
    let typed = static_check(&hir);
    let mut got = messages(&typed, &names);
    got.sort();
    assert_eq!(
        got,
        [
            "T0011 `i64` is not callable",
            "T0013 `i64` has no method or associated item `foo`",
            "T0023 cannot infer a type here; add an annotation",
        ]
    );
}
