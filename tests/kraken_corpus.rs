//! A corpus of Kraken-like programs, built as HIR by hand and checked under
//! `static-inferred`: generic containers, interface-dispatched methods (by
//! bound, by `dyn`, through a bounded generic impl), closures passed to
//! generic functions, `?` lowered as a template, an iterator interface with
//! an associated type bound by `Item = ..`, where clauses, and `match`
//! exhaustiveness. Each program asserts its types, dispatch, and plan, and a
//! broken variant asserts the one diagnostic it should get.

mod common;

use common::{Kit, inferred_check, messages};
use hir_lang::{Expr, ItemId, OpKind, ParamKind, Prim, Res};
use typeck_lang::{Dispatch, Strategy, Type, TypeId};

const I64: TypeId = TypeId::prim(Prim::I64);
const F64: TypeId = TypeId::prim(Prim::F64);
const STR: TypeId = TypeId::prim(Prim::Str);

/// `enum Opt<T> { None, Some(T) }`
struct Opt {
    item: ItemId,
    none: hir_lang::VariantId,
    some: hir_lang::VariantId,
}

fn opt(k: &mut Kit) -> Opt {
    let t = k.type_param("T");
    let gp = k.gparam(t, &[]);
    let g = k.generics(&[gp], &[]);
    let none = k.variant("None", &[]);
    let tt = k.tp("T", t);
    let some = k.variant("Some", &[tt]);
    Opt {
        item: k.gsum("Opt", g, &[none, some]),
        none,
        some,
    }
}

/// `enum Res<T, E> { Ok(T), Err(E) }`
struct ResT {
    item: ItemId,
    ok: hir_lang::VariantId,
    err: hir_lang::VariantId,
}

fn res(k: &mut Kit) -> ResT {
    let t = k.type_param("T");
    let e = k.type_param("E");
    let (a, b) = (k.gparam(t, &[]), k.gparam(e, &[]));
    let g = k.generics(&[a, b], &[]);
    let tt = k.tp("T", t);
    let ok = k.variant("Ok", &[tt]);
    let et = k.tp("E", e);
    let err = k.variant("Err", &[et]);
    ResT {
        item: k.gsum("Res", g, &[ok, err]),
        ok,
        err,
    }
}

fn record_lit(
    k: &mut Kit,
    name: &str,
    item: ItemId,
    fields: &[(&str, hir_lang::ExprId)],
) -> hir_lang::ExprId {
    let n = k.name(name);
    let def = k.b.def(hir_lang::Def::Item(item));
    let path = k.b.resolved_path(n, hir_lang::Ns::Type, Res::Def(def));
    let inits: Vec<hir_lang::FieldInit> = fields
        .iter()
        .map(|&(f, value)| hir_lang::FieldInit {
            name: k.ident(f),
            value,
        })
        .collect();
    let fields = k.b.list(&inits);
    k.expr(Expr::Record {
        path: Some(path),
        fields,
        base: None,
    })
}

/// Shapes: `trait Shape { fn area(&self) -> f64; fn name(&self) -> str { "shape" } }`,
/// `struct Circle { r: f64 }`, `struct Rect { w: f64, h: f64 }`, impls;
/// `fn bigger<T: Shape>(a: T, b: T) -> f64 { max(a.area(), b.area()) }`;
/// `fn measure(s: &dyn Shape) -> f64 { s.area() }`.
#[test]
fn test_shapes_dispatch_by_bound_and_by_dyn() {
    let mut k = Kit::new();
    let st = k.self_ty();
    let r = k.ref_ty(false, st);
    let (recv, _) = k.receiver(Some(r));
    let ret = k.prim(Prim::F64);
    let area = k.decl("area", &[recv], Some(ret));
    let st = k.self_ty();
    let r = k.ref_ty(false, st);
    let ret = k.prim(Prim::Str);
    let name = k.method("name", Some(r), &[], Some(ret), |k, _| {
        let s = k.str("shape");
        k.block(&[], Some(s))
    });
    let g = k.generics(&[], &[]);
    let shape = k.iface("Shape", g, &[], &[area, name]);
    let f = k.prim(Prim::F64);
    let circle = k.record("Circle", &[("r", f)]);
    let (f1, f2) = (k.prim(Prim::F64), k.prim(Prim::F64));
    let rect = k.record("Rect", &[("w", f1), ("h", f2)]);
    let mut impls = Vec::new();
    let mut area_impls = Vec::new();
    for (tyname, item, fields) in [("Circle", circle, ["r", "r"]), ("Rect", rect, ["w", "h"])] {
        let st = k.self_ty();
        let r = k.ref_ty(false, st);
        let ret = k.prim(Prim::F64);
        let m = k.method("area", Some(r), &[], Some(ret), |k, me| {
            let a = k.use_(me);
            let fa = k.field_expr(a, fields[0]);
            let b = k.use_(me);
            let fb = k.field_expr(b, fields[1]);
            let mul = k.op(OpKind::Mul, &[fa, fb]);
            k.block(&[], Some(mul))
        });
        let it = k.path_ty("Shape", shape, &[]);
        let self_ty = k.item_ty(tyname, item);
        let g = k.generics(&[], &[]);
        impls.push(k.impl_of(g, Some(it), self_ty, &[m]));
        area_impls.push(m);
    }
    // fn bigger<T: Shape>(a: T, b: T) -> f64 { max(a.area(), b.area()) }
    let t = k.type_param("T");
    let b = k.path_ty("Shape", shape, &[]);
    let gp = k.gparam(t, &[b]);
    let g = k.generics(&[gp], &[]);
    let (ta, tb) = (k.tp("T", t), k.tp("T", t));
    let (pa, a) = k.param("a", Some(ta), ParamKind::Normal, None);
    let (pb, bv) = k.param("b", Some(tb), ParamKind::Normal, None);
    let ua = k.use_(a);
    let ca = k.method_call(ua, "area", &[]);
    let ub = k.use_(bv);
    let cb = k.method_call(ub, "area", &[]);
    let max = k.op(OpKind::Max, &[ca, cb]);
    let ret = k.prim(Prim::F64);
    let body = k.block(&[], Some(max));
    let bigger = k.gfunc("bigger", g, &[pa, pb], Some(ret), body);
    // fn measure(s: &dyn Shape) -> f64 { s.area() }
    let it = k.path_ty("Shape", shape, &[]);
    let bounds = k.b.list(&[hir_lang::Bound::Ty(it)]);
    let d = k.ty(hir_lang::Ty::Object(bounds));
    let rd = k.ref_ty(false, d);
    let (ps, s) = k.param("s", Some(rd), ParamKind::Normal, None);
    let us = k.use_(s);
    let dyn_call = k.method_call(us, "area", &[]);
    let body = k.block(&[], Some(dyn_call));
    let ret = k.prim(Prim::F64);
    let measure = k.func("measure", &[ps], Some(ret), body);
    // main: let c = Circle { r: 1.5 }; let x = bigger(c, c); let n = c.name();
    //       let m = measure(&Rect { w: 2.0, h: 3.0 });
    let r15 = k.float(1.5);
    let c_lit = record_lit(&mut k, "Circle", circle, &[("r", r15)]);
    let (s1, c) = k.let_("c", None, Some(c_lit));
    let (u1, u2) = (k.use_(c), k.use_(c));
    let call = k.call_item("bigger", bigger, &[u1, u2]);
    let (s2, x) = k.let_("x", None, Some(call));
    let u3 = k.use_(c);
    let name_call = k.method_call(u3, "name", &[]);
    let (s3, n) = k.let_("n", None, Some(name_call));
    let (w, h) = (k.float(2.0), k.float(3.0));
    let rl = record_lit(&mut k, "Rect", rect, &[("w", w), ("h", h)]);
    let borrow = k.expr(Expr::Borrow {
        kind: hir_lang::BorrowKind::Shared,
        expr: rl,
    });
    let mc = k.call_item("measure", measure, &[borrow]);
    let (s4, m) = k.let_("m", None, Some(mc));
    let body = k.block(&[s1, s2, s3, s4], None);
    let mut items = vec![shape, circle, rect];
    items.extend(&impls);
    items.extend([bigger, measure]);
    let (hir, names) = k.finish_main(&items, body);
    let typed = inferred_check(&hir);
    assert!(typed.is_ok(), "{:?}", messages(&typed, &names));
    assert_eq!(typed.binder(x), Some(F64));
    assert_eq!(typed.binder(n), Some(STR));
    assert_eq!(typed.binder(m), Some(F64));
    assert_eq!(typed.method(name_call), Some(name));
    assert_eq!(
        typed.instantiation(ca).map(|i| i.dispatch),
        Some(Dispatch::Bound)
    );
    assert_eq!(
        typed.instantiation(dyn_call).map(|i| i.dispatch),
        Some(Dispatch::Dynamic)
    );
    // The plan: `bigger<Circle>`.
    let circle_ty = typed.types().get(typed.binder(c).unwrap());
    assert!(matches!(circle_ty, Type::Adt { item, .. } if item == circle));
    let plan = typed.mono_plan();
    assert!(
        plan.instances_of(bigger)
            .any(|i| i.args == [typed.binder(c).unwrap()] && i.strategy == Strategy::Copy)
    );
}

/// `struct Stack<T> { top: Opt<T>, size: i64 }` with
/// `impl<T> Stack<T> { fn peek(self) -> Opt<T>; fn depth(self) -> i64 }`
/// and a generic `fn push<T>(s: Stack<T>, x: T) -> Stack<T>`.
#[test]
fn test_generic_container() {
    let mut k = Kit::new();
    let o = opt(&mut k);
    let t = k.type_param("T");
    let gp = k.gparam(t, &[]);
    let g = k.generics(&[gp], &[]);
    let tt = k.tp("T", t);
    let ot = k.path_ty("Opt", o.item, &[tt]);
    let i = k.prim(Prim::I64);
    let stack = k.grecord("Stack", g, &[("top", ot), ("size", i)]);
    // impl<U> Stack<U> { fn peek(self) -> Opt<U> { self.top } fn depth(self) -> i64 { self.size } }
    let u = k.type_param("U");
    let gp = k.gparam(u, &[]);
    let g = k.generics(&[gp], &[]);
    let ut = k.tp("U", u);
    let ret = k.path_ty("Opt", o.item, &[ut]);
    let peek = k.method("peek", None, &[], Some(ret), |k, me| {
        let s = k.use_(me);
        let f = k.field_expr(s, "top");
        k.block(&[], Some(f))
    });
    let ret = k.prim(Prim::I64);
    let depth = k.method("depth", None, &[], Some(ret), |k, me| {
        let s = k.use_(me);
        let f = k.field_expr(s, "size");
        k.block(&[], Some(f))
    });
    let ut = k.tp("U", u);
    let self_ty = k.path_ty("Stack", stack, &[ut]);
    let imp = k.impl_of(g, None, self_ty, &[peek, depth]);
    // fn push<V>(s: Stack<V>, x: V) -> Stack<V> { Stack { top: Some(x), size: s.size + 1 } }
    let v = k.type_param("V");
    let gp = k.gparam(v, &[]);
    let g = k.generics(&[gp], &[]);
    let vt = k.tp("V", v);
    let st = k.path_ty("Stack", stack, &[vt]);
    let (ps, s) = k.param("s", Some(st), ParamKind::Normal, None);
    let vt2 = k.tp("V", v);
    let (px, x) = k.param("x", Some(vt2), ParamKind::Normal, None);
    let ux = k.use_(x);
    let some = k.variant_expr("Some", o.some);
    let top = k.b.call(some, &[ux]);
    let us = k.use_(s);
    let sz = k.field_expr(us, "size");
    let one = k.int(1);
    let inc = k.op(OpKind::Add, &[sz, one]);
    let lit = record_lit(&mut k, "Stack", stack, &[("top", top), ("size", inc)]);
    let body = k.block(&[], Some(lit));
    let vt3 = k.tp("V", v);
    let ret = k.path_ty("Stack", stack, &[vt3]);
    let push = k.gfunc("push", g, &[ps, px], Some(ret), body);
    // main: let e: Stack<str> = Stack { top: None, size: 0 };
    //       let s1 = push(e, "a"); let top = s1.peek(); let d = s1.depth();
    let st = k.prim(Prim::Str);
    let ann = k.path_ty("Stack", stack, &[st]);
    let none = k.variant_expr("None", o.none);
    let zero = k.int(0);
    let empty = record_lit(&mut k, "Stack", stack, &[("top", none), ("size", zero)]);
    let (s1, e) = k.let_("e", Some(ann), Some(empty));
    let ue = k.use_(e);
    let a = k.str("a");
    let pushed = k.call_item("push", push, &[ue, a]);
    let (s2, s1b) = k.let_("s1", None, Some(pushed));
    let u = k.use_(s1b);
    let peek_call = k.method_call(u, "peek", &[]);
    let (s3, top_b) = k.let_("top", None, Some(peek_call));
    let u = k.use_(s1b);
    let depth_call = k.method_call(u, "depth", &[]);
    let (s4, d) = k.let_("d", None, Some(depth_call));
    let body = k.block(&[s1, s2, s3, s4], None);
    let (hir, names) = k.finish_main(&[o.item, stack, imp, push], body);
    let typed = inferred_check(&hir);
    assert!(typed.is_ok(), "{:?}", messages(&typed, &names));
    assert_eq!(
        typed
            .display(typed.binder(s1b).unwrap(), &names)
            .to_string(),
        "Stack<str>"
    );
    assert_eq!(
        typed
            .display(typed.binder(top_b).unwrap(), &names)
            .to_string(),
        "Opt<str>"
    );
    assert_eq!(typed.binder(d), Some(I64));
    assert_eq!(typed.method(peek_call), Some(peek));
    let plan = typed.mono_plan();
    assert!(plan.instances_of(push).any(|i| i.args == [STR]));
    assert!(plan.instances_of(peek).any(|i| i.args == [STR]));
    let _ = (e, x);
}

/// `fn map<T, U>(o: Opt<T>, f: fn(T) -> U) -> Opt<U>` with a closure whose
/// parameter is inferred, and `?` lowered as a template over `Res`.
#[test]
fn test_closures_and_question_mark_template() {
    let mut k = Kit::new();
    let o = opt(&mut k);
    let r = res(&mut k);
    // fn map<T, U>(o: Opt<T>, f: fn(T) -> U) -> Opt<U> {
    //     match o { Some(x) => Some(f(x)), None => None } }
    let t = k.type_param("T");
    let u = k.type_param("U");
    let (gt, gu) = (k.gparam(t, &[]), k.gparam(u, &[]));
    let g = k.generics(&[gt, gu], &[]);
    let tt = k.tp("T", t);
    let ot = k.path_ty("Opt", o.item, &[tt]);
    let (po, ov) = k.param("o", Some(ot), ParamKind::Normal, None);
    let (ta, ub) = (k.tp("T", t), k.tp("U", u));
    let ps = k.b.list(&[ta]);
    let fty = k.ty(hir_lang::Ty::Fn {
        params: ps,
        ret: ub,
        effects: hir_lang::Effects::NONE,
        throws: None,
        abi: None,
    });
    let (pf, fv) = k.param("f", Some(fty), ParamKind::Normal, None);
    let uo = k.use_(ov);
    let (xb, xp) = k.local("x");
    let some_pat = k.variant_pat("Some", o.some, &[xp]);
    let uf = k.use_(fv);
    let ux = k.use_(xb);
    let fx = k.b.call(uf, &[ux]);
    let some = k.variant_expr("Some", o.some);
    let arm1 = k.b.call(some, &[fx]);
    let none_pat = k.unit_variant_pat("None", o.none);
    let arm2 = k.variant_expr("None", o.none);
    let m = k.match_(uo, &[(some_pat, arm1), (none_pat, arm2)]);
    let body = k.block(&[], Some(m));
    let uu = k.tp("U", u);
    let ret = k.path_ty("Opt", o.item, &[uu]);
    let map = k.gfunc("map", g, &[po, pf], Some(ret), body);
    // fn parse(x: i64) -> Res<i64, str> { if x > 0 { Ok(x) } else { Err("neg") } }
    let i = k.prim(Prim::I64);
    let (px, xv) = k.param("x", Some(i), ParamKind::Normal, None);
    let ux = k.use_(xv);
    let zero = k.int(0);
    let cond = k.op(OpKind::Gt, &[ux, zero]);
    let okc = k.variant_expr("Ok", r.ok);
    let ux2 = k.use_(xv);
    let ok_v = k.b.call(okc, &[ux2]);
    let errc = k.variant_expr("Err", r.err);
    let neg = k.str("neg");
    let err_v = k.b.call(errc, &[neg]);
    let iff = k.expr(Expr::If {
        cond,
        then: ok_v,
        else_: Some(err_v),
    });
    let body = k.block(&[], Some(iff));
    let (i2, s2) = (k.prim(Prim::I64), k.prim(Prim::Str));
    let ret = k.path_ty("Res", r.item, &[i2, s2]);
    let parse = k.func("parse", &[px], Some(ret), body);
    // fn twice(x: i64) -> Res<i64, str> {
    //     let v = match parse(x) { Ok(v) => v, Err(e) => return Err(e) };  // `parse(x)?`
    //     Ok(v * 2) }
    let i = k.prim(Prim::I64);
    let (px, xv) = k.param("x", Some(i), ParamKind::Normal, None);
    let ux = k.use_(xv);
    let pc = k.call_item("parse", parse, &[ux]);
    let (vb, vp) = k.local("v");
    let okp = k.variant_pat("Ok", r.ok, &[vp]);
    let uv = k.use_(vb);
    let (eb, ep) = k.local("e");
    let errp = k.variant_pat("Err", r.err, &[ep]);
    let errc = k.variant_expr("Err", r.err);
    let ue = k.use_(eb);
    let rewrap = k.b.call(errc, &[ue]);
    let ret_e = k.expr(Expr::Return(Some(rewrap)));
    let q = k.match_(pc, &[(okp, uv), (errp, ret_e)]);
    let (sv, v) = k.let_("v", None, Some(q));
    let uv = k.use_(v);
    let two = k.int(2);
    let mul = k.op(OpKind::Mul, &[uv, two]);
    let okc = k.variant_expr("Ok", r.ok);
    let out = k.b.call(okc, &[mul]);
    let body = k.block(&[sv], Some(out));
    let (i3, s3) = (k.prim(Prim::I64), k.prim(Prim::Str));
    let ret = k.path_ty("Res", r.item, &[i3, s3]);
    let twice = k.func("twice", &[px], Some(ret), body);
    // main: let doubled = map(Some(2), |y| y * 3); let labels = map(Some(1), |y| "n");
    let two = k.int(2);
    let some = k.variant_expr("Some", o.some);
    let s2v = k.b.call(some, &[two]);
    let (py, y) = k.param("y", None, ParamKind::Normal, None);
    let uy = k.use_(y);
    let three = k.int(3);
    let mul = k.op(OpKind::Mul, &[uy, three]);
    let clo = k.closure(&[py], None, mul);
    let mapped = k.call_item("map", map, &[s2v, clo]);
    let (sa, doubled) = k.let_("doubled", None, Some(mapped));
    let one = k.int(1);
    let some = k.variant_expr("Some", o.some);
    let s1v = k.b.call(some, &[one]);
    let (pz, _) = k.param("z", None, ParamKind::Normal, None);
    let lbl = k.str("n");
    let clo2 = k.closure(&[pz], None, lbl);
    let mapped2 = k.call_item("map", map, &[s1v, clo2]);
    let (sb, labels) = k.let_("labels", None, Some(mapped2));
    let body = k.block(&[sa, sb], None);
    let (hir, names) = k.finish_main(&[o.item, r.item, map, parse, twice], body);
    let typed = inferred_check(&hir);
    assert!(typed.is_ok(), "{:?}", messages(&typed, &names));
    assert_eq!(
        typed
            .display(typed.binder(doubled).unwrap(), &names)
            .to_string(),
        "Opt<i64>"
    );
    assert_eq!(
        typed
            .display(typed.binder(labels).unwrap(), &names)
            .to_string(),
        "Opt<str>"
    );
    assert_eq!(typed.binder(v), Some(I64));
    assert_eq!(typed.binder(y), Some(I64));
    let plan = typed.mono_plan();
    assert!(plan.instances_of(map).any(|i| i.args == [I64, I64]));
    assert!(plan.instances_of(map).any(|i| i.args == [I64, STR]));
}

/// An iterator interface with an associated type, a bound that fixes it
/// (`I: Iter<Item = i64>`), and a where clause.
#[test]
fn test_iterator_with_bound_binding_and_where_clause() {
    let mut k = Kit::new();
    let o = opt(&mut k);
    // trait Iter { type Item; fn next(&self) -> Opt<Self::Item>; }
    let item = k.assoc("Item", &[], None);
    let st = k.self_ty();
    let r = k.ref_ty(false, st);
    let (recv, _) = k.receiver(Some(r));
    let si = k.self_assoc_ty("Item");
    let ret = k.path_ty("Opt", o.item, &[si]);
    let next = k.decl("next", &[recv], Some(ret));
    let g = k.generics(&[], &[]);
    let iter = k.iface("Iter", g, &[], &[item, next]);
    // struct Counter { n: i64 } impl Iter for Counter { type Item = i64; fn next(&self) -> Opt<i64> { Some(self.n) } }
    let i = k.prim(Prim::I64);
    let counter = k.record("Counter", &[("n", i)]);
    let i = k.prim(Prim::I64);
    let g0 = k.generics(&[], &[]);
    let item_def = k.alias("Item", g0, i);
    let st = k.self_ty();
    let r = k.ref_ty(false, st);
    let i = k.prim(Prim::I64);
    let ret = k.path_ty("Opt", o.item, &[i]);
    let some_item = o.some;
    let next_def = k.method("next", Some(r), &[], Some(ret), |k, me| {
        let s = k.use_(me);
        let f = k.field_expr(s, "n");
        let some = k.variant_expr("Some", some_item);
        let c = k.b.call(some, &[f]);
        k.block(&[], Some(c))
    });
    let it = k.path_ty("Iter", iter, &[]);
    let ct = k.item_ty("Counter", counter);
    let g = k.generics(&[], &[]);
    let imp = k.impl_of(g, Some(it), ct, &[item_def, next_def]);
    // fn first_or_zero<I>(it: I) -> i64 where I: Iter<Item = i64> {
    //     match it.next() { Some(v) => v, None => 0 } }
    let ib = k.type_param("I");
    let gp = k.gparam(ib, &[]);
    let subj = k.tp("I", ib);
    let i = k.prim(Prim::I64);
    let bound = k.iface_ty_bind("Iter", iter, &[], &[("Item", i)]);
    let pred = k.where_(subj, &[bound]);
    let g = k.generics(&[gp], &[pred]);
    let ity = k.tp("I", ib);
    let (p, itv) = k.param("it", Some(ity), ParamKind::Normal, None);
    let ui = k.use_(itv);
    let nc = k.method_call(ui, "next", &[]);
    let (vb, vp) = k.local("v");
    let sp = k.variant_pat("Some", o.some, &[vp]);
    let uv = k.use_(vb);
    let np = k.unit_variant_pat("None", o.none);
    let zero = k.int(0);
    let m = k.match_(nc, &[(sp, uv), (np, zero)]);
    let body = k.block(&[], Some(m));
    let ret = k.prim(Prim::I64);
    let first = k.gfunc("first_or_zero", g, &[p], Some(ret), body);
    // main: let c = Counter { n: 7 }; let x = first_or_zero(c);
    let seven = k.int(7);
    let lit = record_lit(&mut k, "Counter", counter, &[("n", seven)]);
    let (s1, c) = k.let_("c", None, Some(lit));
    let uc = k.use_(c);
    let call = k.call_item("first_or_zero", first, &[uc]);
    let (s2, x) = k.let_("x", None, Some(call));
    let body = k.block(&[s1, s2], None);
    let (hir, names) = k.finish_main(&[o.item, iter, counter, imp, first], body);
    let typed = inferred_check(&hir);
    assert!(typed.is_ok(), "{:?}", messages(&typed, &names));
    assert_eq!(typed.binder(x), Some(I64));
    // Inside the generic body, `v` is `i64` through the binding.
    assert_eq!(typed.binder(vb), Some(I64));
}

/// `match` over a Kraken token sum: a missing variant is reported with its
/// witness; an exhaustive match is silent.
#[test]
fn test_token_match_exhaustiveness() {
    let mut k = Kit::new();
    let i = k.prim(Prim::I64);
    let num = k.variant("Num", &[i]);
    let c = k.prim(Prim::Char);
    let op = k.variant("Op", &[c]);
    let end = k.variant("End", &[]);
    let token = k.sum("Token", &[num, op, end]);
    // fn weight(t: Token) -> i64 { match t { Num(n) => n, Op(_) => 1 } }
    let tt = k.item_ty("Token", token);
    let (p, tv) = k.param("t", Some(tt), ParamKind::Normal, None);
    let ut = k.use_(tv);
    let (nb, np) = k.local("n");
    let p1 = k.variant_pat("Num", num, &[np]);
    let un = k.use_(nb);
    let w = k.wild();
    let p2 = k.variant_pat("Op", op, &[w]);
    let one = k.int(1);
    let m = k.match_(ut, &[(p1, un), (p2, one)]);
    let body = k.block(&[], Some(m));
    let ret = k.prim(Prim::I64);
    let weight = k.func("weight", &[p], Some(ret), body);
    let (hir, names) = k.finish_items(&[token, weight]);
    let typed = inferred_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0027 non-exhaustive match: `End` not covered"]
    );
    assert_eq!(typed.witnesses(m, &names), ["End"]);
}

/// Broken programs: one diagnostic each, at the mistake.
#[test]
fn test_broken_programs_one_diagnostic_each() {
    // A closure whose body does not fit the bound of the generic it is
    // passed to: `apply(|y| y + true, 1)`.
    let mut k = Kit::new();
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
    let (py, y) = k.param("y", None, ParamKind::Normal, None);
    let uy = k.use_(y);
    let bad = k.bool(true);
    let add = k.op(OpKind::Add, &[uy, bad]);
    let clo = k.closure(&[py], None, add);
    let one = k.int(1);
    let c = k.call_item("apply", apply, &[clo, one]);
    let s = k.stmt(c);
    let body = k.block(&[s], None);
    let (hir, names) = k.finish_main(&[apply], body);
    let typed = inferred_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0018 `add` is not defined for `bool`"]
    );
    assert_eq!(typed.diagnostics()[0].node, hir_lang::NodeRef::Expr(bad));
}
