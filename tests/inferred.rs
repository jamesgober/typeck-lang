//! The `static-inferred` discipline, rule by rule: generic functions and
//! types, bounds and where clauses, interfaces with methods, associated
//! types and default methods, impl blocks (generic ones too), trait method
//! resolution, closures with inferred signatures, `dyn` and `impl Trait`.

mod common;

use common::{Kit, inferred_check, messages};
use hir_lang::{Lit, ParamKind, Prim, Res};
use typeck_lang::{Coercion, DiagnosticKind, Dispatch, Profile, Type, TypeId, check};

const I64: TypeId = TypeId::prim(Prim::I64);
const BOOL: TypeId = TypeId::prim(Prim::Bool);
const STR: TypeId = TypeId::prim(Prim::Str);

/// `struct Box<T> { val: T }` and `impl<T> Box<T> { fn get(self) -> T }`.
fn boxed(k: &mut Kit) -> (hir_lang::ItemId, hir_lang::ItemId, hir_lang::ItemId) {
    let t = k.type_param("T");
    let gp = k.gparam(t, &[]);
    let g = k.generics(&[gp], &[]);
    let tt = k.tp("T", t);
    let bx = k.grecord("Box", g, &[("val", tt)]);
    // impl<U> Box<U> { fn get(self) -> U { self.val } }
    let u = k.type_param("U");
    let gp = k.gparam(u, &[]);
    let g = k.generics(&[gp], &[]);
    let ut = k.tp("U", u);
    let self_ty = k.path_ty("Box", bx, &[ut]);
    let ret = k.tp("U", u);
    let get = k.method("get", None, &[], Some(ret), |k, me| {
        let base = k.use_(me);
        let f = k.field_expr(base, "val");
        k.block(&[], Some(f))
    });
    let imp = k.impl_of(g, None, self_ty, &[get]);
    (bx, get, imp)
}

#[test]
fn test_generic_record_and_generic_impl_method() {
    let mut k = Kit::new();
    let (bx, get, imp) = boxed(&mut k);
    // let b = Box { val: 1 }; let v = b.get();
    let one = k.int(1);
    let n = k.name("Box");
    let def = k.b.def(hir_lang::Def::Item(bx));
    let p = k.b.resolved_path(n, hir_lang::Ns::Type, Res::Def(def));
    let val = k.ident("val");
    let fields = k.b.list(&[hir_lang::FieldInit {
        name: val,
        value: one,
    }]);
    let lit = k.expr(hir_lang::Expr::Record {
        path: Some(p),
        fields,
        base: None,
    });
    let (s1, b) = k.let_("b", None, Some(lit));
    let ub = k.use_(b);
    let call = k.method_call(ub, "get", &[]);
    let (s2, v) = k.let_("v", None, Some(call));
    let body = k.block(&[s1, s2], None);
    let (hir, names) = k.finish_main(&[bx, imp], body);
    let typed = inferred_check(&hir);
    assert!(typed.is_ok(), "{:?}", messages(&typed, &names));
    assert_eq!(typed.binder(v), Some(I64));
    assert_eq!(typed.method(call), Some(get));
    match typed.types().get(typed.binder(b).unwrap()) {
        Type::Adt { item, args } => {
            assert_eq!(item, bx);
            assert_eq!(args, &[I64]);
        }
        other => panic!("{other:?}"),
    }
    assert_eq!(
        typed.display(typed.binder(b).unwrap(), &names).to_string(),
        "Box<i64>"
    );
    let inst = typed.instantiation(call).expect("method instantiation");
    assert_eq!(inst.item, get);
    assert_eq!(inst.args, &[I64]);
    assert_eq!(inst.dispatch, Dispatch::Static);
}

/// `trait Show { fn show(&self) -> str; }` with `impl Show for i64`.
fn show(k: &mut Kit) -> (hir_lang::ItemId, hir_lang::ItemId, hir_lang::ItemId) {
    let st = k.self_ty();
    let r = k.ref_ty(false, st);
    let (recv, _) = k.receiver(Some(r));
    let ret = k.prim(Prim::Str);
    let decl = k.decl("show", &[recv], Some(ret));
    let g = k.generics(&[], &[]);
    let iface = k.iface("Show", g, &[], &[decl]);
    let st = k.self_ty();
    let r = k.ref_ty(false, st);
    let ret = k.prim(Prim::Str);
    let m = k.method("show", Some(r), &[], Some(ret), |k, _| {
        let s = k.str("int");
        k.block(&[], Some(s))
    });
    let iface_ty = k.path_ty("Show", iface, &[]);
    let self_ty = k.prim(Prim::I64);
    let g = k.generics(&[], &[]);
    let imp = k.impl_of(g, Some(iface_ty), self_ty, &[m]);
    (iface, imp, m)
}

/// `fn describe<T: Show>(x: T) -> str { x.show() }`.
fn describe(k: &mut Kit, iface: hir_lang::ItemId) -> (hir_lang::ItemId, hir_lang::ExprId) {
    let t = k.type_param("T");
    let bound = k.path_ty("Show", iface, &[]);
    let gp = k.gparam(t, &[bound]);
    let g = k.generics(&[gp], &[]);
    let tt = k.tp("T", t);
    let (p, x) = k.param("x", Some(tt), ParamKind::Normal, None);
    let ux = k.use_(x);
    let call = k.method_call(ux, "show", &[]);
    let body = k.block(&[], Some(call));
    let ret = k.prim(Prim::Str);
    (k.gfunc("describe", g, &[p], Some(ret), body), call)
}

#[test]
fn test_bounded_generic_function_and_trait_method_on_parameter() {
    let mut k = Kit::new();
    let (iface, imp, m) = show(&mut k);
    let (desc, inner) = describe(&mut k, iface);
    let five = k.int(5);
    let ok = k.call_item("describe", desc, &[five]);
    let s1 = k.stmt(ok);
    let yes = k.bool(true);
    let bad = k.call_item("describe", desc, &[yes]);
    let s2 = k.stmt(bad);
    let body = k.block(&[s1, s2], None);
    let (hir, names) = k.finish_main(&[iface, imp, desc], body);
    let typed = inferred_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0046 `bool` does not implement `Show`"]
    );
    assert_eq!(typed.expr(ok), Some(STR));
    // Inside the generic body the call goes through the bound.
    let inst = typed.instantiation(inner).expect("bound call");
    assert_eq!(inst.dispatch, Dispatch::Bound);
    // The plan resolves it to the impl's method for `i64`.
    let plan = typed.mono_plan();
    assert!(plan.instances_of(desc).any(|i| i.args == [I64]), "{plan:?}");
    let _ = m;
}

#[test]
fn test_associated_type_through_impl_and_bound() {
    let mut k = Kit::new();
    // trait Iter { type Item; fn next(&self) -> Self::Item; }
    let item = k.assoc("Item", &[], None);
    let st = k.self_ty();
    let r = k.ref_ty(false, st);
    let (recv, _) = k.receiver(Some(r));
    let ret = k.self_assoc_ty("Item");
    let next = k.decl("next", &[recv], Some(ret));
    let g = k.generics(&[], &[]);
    let iter = k.iface("Iter", g, &[], &[item, next]);
    // struct Counter {} ; impl Iter for Counter { type Item = i64; fn next(&self) -> i64 { 1 } }
    let counter = k.record("Counter", &[]);
    let i64t = k.prim(Prim::I64);
    let g = k.generics(&[], &[]);
    let item_def = k.alias("Item", g, i64t);
    let st = k.self_ty();
    let r = k.ref_ty(false, st);
    let ret = k.prim(Prim::I64);
    let next_def = k.method("next", Some(r), &[], Some(ret), |k, _| {
        let one = k.int(1);
        k.block(&[], Some(one))
    });
    let iter_ty = k.path_ty("Iter", iter, &[]);
    let self_ty = k.item_ty("Counter", counter);
    let g = k.generics(&[], &[]);
    let imp = k.impl_of(g, Some(iter_ty), self_ty, &[item_def, next_def]);
    // fn first<I: Iter>(i: I) -> I::Item { i.next() }
    let ib = k.type_param("I");
    let bound = k.path_ty("Iter", iter, &[]);
    let gp = k.gparam(ib, &[bound]);
    let g = k.generics(&[gp], &[]);
    let it = k.tp("I", ib);
    let (p, i) = k.param("i", Some(it), ParamKind::Normal, None);
    let ui = k.use_(i);
    let call = k.method_call(ui, "next", &[]);
    let body = k.block(&[], Some(call));
    let ret = k.assoc_ty("I", Res::Local(ib), "Item");
    let first = k.gfunc("first", g, &[p], Some(ret), body);
    // main: let c = Counter {}; let x = first(c);
    let n = k.name("Counter");
    let def = k.b.def(hir_lang::Def::Item(counter));
    let path = k.b.resolved_path(n, hir_lang::Ns::Type, Res::Def(def));
    let fields = k.b.list(&[]);
    let lit = k.expr(hir_lang::Expr::Record {
        path: Some(path),
        fields,
        base: None,
    });
    let (s1, c) = k.let_("c", None, Some(lit));
    let uc = k.use_(c);
    let fc = k.call_item("first", first, &[uc]);
    let (s2, x) = k.let_("x", None, Some(fc));
    let body = k.block(&[s1, s2], None);
    let (hir, names) = k.finish_main(&[iter, counter, imp, first], body);
    let typed = inferred_check(&hir);
    assert!(typed.is_ok(), "{:?}", messages(&typed, &names));
    assert_eq!(typed.binder(x), Some(I64));
    // Inside `first`, the result is the rigid projection.
    assert_eq!(
        typed.display(typed.expr(call).unwrap(), &names).to_string(),
        "<I as Iter>::Item"
    );
}

#[test]
fn test_default_method_and_missing_member() {
    let mut k = Kit::new();
    // trait Greet { fn name(&self) -> str; fn hello(&self) -> str { self.name() } }
    let st = k.self_ty();
    let r = k.ref_ty(false, st);
    let (recv, _) = k.receiver(Some(r));
    let ret = k.prim(Prim::Str);
    let name_decl = k.decl("name", &[recv], Some(ret));
    let st = k.self_ty();
    let r = k.ref_ty(false, st);
    let ret = k.prim(Prim::Str);
    let hello = k.method("hello", Some(r), &[], Some(ret), |k, me| {
        let u = k.use_(me);
        let c = k.method_call(u, "name", &[]);
        k.block(&[], Some(c))
    });
    let g = k.generics(&[], &[]);
    let greet = k.iface("Greet", g, &[], &[name_decl, hello]);
    // struct Dog {} impl Greet for Dog { fn name(&self) -> str { "d" } }
    let dog = k.record("Dog", &[]);
    let st = k.self_ty();
    let r = k.ref_ty(false, st);
    let ret = k.prim(Prim::Str);
    let name_def = k.method("name", Some(r), &[], Some(ret), |k, _| {
        let s = k.str("d");
        k.block(&[], Some(s))
    });
    let gt = k.path_ty("Greet", greet, &[]);
    let dt = k.item_ty("Dog", dog);
    let g = k.generics(&[], &[]);
    let imp = k.impl_of(g, Some(gt), dt, &[name_def]);
    // struct Cat {} impl Greet for Cat {}   -- missing `name`
    let cat = k.record("Cat", &[]);
    let gt = k.path_ty("Greet", greet, &[]);
    let ct = k.item_ty("Cat", cat);
    let g = k.generics(&[], &[]);
    let bad_imp = k.impl_of(g, Some(gt), ct, &[]);
    // main: let d: Dog = Dog {}; d.hello()
    let n = k.name("Dog");
    let def = k.b.def(hir_lang::Def::Item(dog));
    let path = k.b.resolved_path(n, hir_lang::Ns::Type, Res::Def(def));
    let fields = k.b.list(&[]);
    let lit = k.expr(hir_lang::Expr::Record {
        path: Some(path),
        fields,
        base: None,
    });
    let (s1, d) = k.let_("d", None, Some(lit));
    let ud = k.use_(d);
    let call = k.method_call(ud, "hello", &[]);
    let s2 = k.stmt(call);
    let body = k.block(&[s1, s2], None);
    let (hir, names) = k.finish_main(&[greet, dog, imp, cat, bad_imp], body);
    let typed = inferred_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0049 missing interface member `name`"]
    );
    assert_eq!(typed.expr(call), Some(STR));
    assert_eq!(typed.method(call), Some(hello));
    // The default method's coercion of the receiver: `&Dog` from `Dog`.
    assert!(matches!(typed.coercion(ud), Some((Coercion::AutoRef, _))));
}

#[test]
fn test_closure_signature_from_expected_function_type() {
    let mut k = Kit::new();
    // fn apply<T>(f: fn(T) -> T, x: T) -> T { f(x) }
    let t = k.type_param("T");
    let gp = k.gparam(t, &[]);
    let g = k.generics(&[gp], &[]);
    let (a, b, c) = (k.tp("T", t), k.tp("T", t), k.tp("T", t));
    let params = k.b.list(&[a]);
    let fty = k.ty(hir_lang::Ty::Fn {
        params,
        ret: b,
        effects: hir_lang::Effects::NONE,
        throws: None,
        abi: None,
    });
    let (pf, f) = k.param("f", Some(fty), ParamKind::Normal, None);
    let (px, x) = k.param("x", Some(c), ParamKind::Normal, None);
    let uf = k.use_(f);
    let ux = k.use_(x);
    let call = k.b.call(uf, &[ux]);
    let body = k.block(&[], Some(call));
    let ret = k.tp("T", t);
    let apply = k.gfunc("apply", g, &[pf, px], Some(ret), body);
    // main: let r = apply(|y| y + 1, 2);
    let (py, y) = k.param("y", None, ParamKind::Normal, None);
    let uy = k.use_(y);
    let one = k.int(1);
    let add = k.op(hir_lang::OpKind::Add, &[uy, one]);
    let clo = k.closure(&[py], None, add);
    let two = k.int(2);
    let r = k.call_item("apply", apply, &[clo, two]);
    let (s, rb) = k.let_("r", None, Some(r));
    let body = k.block(&[s], None);
    let (hir, names) = k.finish_main(&[apply], body);
    let typed = inferred_check(&hir);
    assert!(typed.is_ok(), "{:?}", messages(&typed, &names));
    assert_eq!(typed.binder(rb), Some(I64));
    assert_eq!(typed.binder(y), Some(I64));
    // static-explicit wants the annotation.
    let explicit = check(&hir, &Profile::static_explicit()).unwrap();
    assert!(
        explicit
            .diagnostics()
            .iter()
            .any(|d| d.kind == DiagnosticKind::MissingAnnotation)
    );
}

#[test]
fn test_let_null_is_nullable_under_static_inferred() {
    let mut k = Kit::new();
    let null = k.null();
    let (s1, x) = k.let_("x", None, Some(null));
    let ux = k.use_(x);
    let five = k.int(5);
    let assign = k.expr(hir_lang::Expr::Assign {
        target: ux,
        op: None,
        value: five,
    });
    let s2 = k.stmt(assign);
    let body = k.block(&[s1, s2], None);
    let (hir, names) = k.finish_main(&[], body);
    let typed = inferred_check(&hir);
    assert!(typed.is_ok(), "{:?}", messages(&typed, &names));
    assert_eq!(
        typed.display(typed.binder(x).unwrap(), &names).to_string(),
        "i64?"
    );
    // The 0.2 convention: `null`, so the assignment is a mismatch.
    let old = check(&hir, &Profile::static_explicit()).unwrap();
    assert_eq!(old.binder(x), Some(TypeId::NULL));
    assert_eq!(old.diagnostics().len(), 1);
    let _ = (BOOL, Lit::Null);
}
