//! The monomorphization plan (every reachable instance of a generic
//! function, copied or shared per the profile's policy), and `?` through the
//! profile's hook.

mod common;

use common::{Kit, inferred_check, messages};
use hir_lang::{Attr, Expr, Intrinsic, ItemId, List, NodeRef, ParamKind, Prim, Res};
use typeck_lang::{
    Checker, Coercion, DiagnosticKind, MonoPolicy, Profile, Strategy, TryHook, TypeId, check,
};

const I64: TypeId = TypeId::prim(Prim::I64);
const BOOL: TypeId = TypeId::prim(Prim::Bool);
const STR: TypeId = TypeId::prim(Prim::Str);

/// `fn id<T>(x: T) -> T { x }`
fn id_fn(k: &mut Kit, name: &str) -> ItemId {
    let t = k.type_param("T");
    let gp = k.gparam(t, &[]);
    let g = k.generics(&[gp], &[]);
    let tt = k.tp("T", t);
    let (p, x) = k.param("x", Some(tt), ParamKind::Normal, None);
    let ux = k.use_(x);
    let body = k.block(&[], Some(ux));
    let ret = k.tp("T", t);
    k.gfunc(name, g, &[p], Some(ret), body)
}

/// `fn twice<U>(u: U) -> U { id(u) }`
fn twice_fn(k: &mut Kit, id: ItemId) -> ItemId {
    let u = k.type_param("U");
    let gp = k.gparam(u, &[]);
    let g = k.generics(&[gp], &[]);
    let ut = k.tp("U", u);
    let (p, x) = k.param("u", Some(ut), ParamKind::Normal, None);
    let ux = k.use_(x);
    let call = k.call_item("id", id, &[ux]);
    let body = k.block(&[], Some(call));
    let ret = k.tp("U", u);
    k.gfunc("twice", g, &[p], Some(ret), body)
}

fn program(k: &mut Kit) -> (ItemId, ItemId, ExprIds) {
    let id = id_fn(k, "id");
    let twice = twice_fn(k, id);
    let one = k.int(1);
    let c1 = k.call_item("id", id, &[one]);
    let t = k.bool(true);
    let c2 = k.call_item("id", id, &[t]);
    let s = k.str("s");
    let c3 = k.call_item("twice", twice, &[s]);
    (id, twice, ExprIds(vec![c1, c2, c3]))
}

struct ExprIds(Vec<hir_lang::ExprId>);

#[test]
fn test_plan_copies_every_reached_instance() {
    let mut k = Kit::new();
    let (id, twice, calls) = program(&mut k);
    let stmts: Vec<_> = calls.0.iter().map(|&c| k.stmt(c)).collect();
    let body = k.block(&stmts, None);
    let (hir, names) = k.finish_main(&[id, twice], body);
    let typed = inferred_check(&hir);
    assert!(typed.is_ok(), "{:?}", messages(&typed, &names));
    let plan = typed.mono_plan();
    let mut ids: Vec<Vec<TypeId>> = plan.instances_of(id).map(|i| i.args.to_vec()).collect();
    ids.sort();
    let mut want = vec![vec![I64], vec![BOOL], vec![STR]];
    want.sort();
    assert_eq!(ids, want);
    assert!(plan.instances_of(twice).any(|i| i.args == [STR]));
    assert!(plan.instances().all(|i| i.strategy == Strategy::Copy));
    assert_eq!(plan.len(), 4);
}

#[test]
fn test_shared_policy_keeps_one_body() {
    let mut k = Kit::new();
    let (id, twice, calls) = program(&mut k);
    let stmts: Vec<_> = calls.0.iter().map(|&c| k.stmt(c)).collect();
    let body = k.block(&stmts, None);
    let (hir, _) = k.finish_main(&[id, twice], body);
    let typed = check(
        &hir,
        &Profile::static_inferred().with_mono(MonoPolicy::Shared),
    )
    .unwrap();
    let plan = typed.mono_plan();
    assert!(plan.instances().all(|i| i.strategy == Strategy::Shared));
    // One shared body each (with its own placeholders), plus the call
    // sites' concrete instances.
    let bodies = plan
        .instances_of(id)
        .filter(|i| {
            i.args
                .iter()
                .all(|&a| typed.types().get(a) != typeck_lang::Type::Prim(Prim::I64))
        })
        .count();
    assert!(bodies >= 1);
    assert!(plan.instances_of(id).any(|i| i.args == [I64]));
}

#[test]
fn test_selective_policy_and_attribute_override() {
    let mut k = Kit::new();
    let small = id_fn(&mut k, "small");
    // A large generic function: many statements.
    let t = k.type_param("T");
    let gp = k.gparam(t, &[]);
    let g = k.generics(&[gp], &[]);
    let tt = k.tp("T", t);
    let (p, x) = k.param("x", Some(tt), ParamKind::Normal, None);
    let mut stmts = Vec::new();
    for _ in 0..50 {
        let one = k.int(1);
        stmts.push(k.stmt(one));
    }
    let ux = k.use_(x);
    let body = k.block(&stmts, Some(ux));
    let ret = k.tp("T", t);
    let large = k.gfunc("large", g, &[p], Some(ret), body);
    let hot = id_fn(&mut k, "hot_one");
    let hot_name = k.ident("hot");
    let none = k.b.list(&[]);
    k.b.attach(
        NodeRef::Item(hot),
        &[Attr {
            name: hot_name,
            args: none,
        }],
    );
    let calls = [
        {
            let a = k.int(1);
            k.call_item("small", small, &[a])
        },
        {
            let a = k.int(1);
            k.call_item("large", large, &[a])
        },
        {
            let a = k.int(1);
            k.call_item("hot_one", hot, &[a])
        },
    ];
    let stmts: Vec<_> = calls.iter().map(|&c| k.stmt(c)).collect();
    let body = k.block(&stmts, None);
    let hot_sym = k.sym("hot");
    let (hir, _) = k.finish_main(&[small, large, hot], body);
    let profile = Profile::static_inferred().with_mono(MonoPolicy::Selective { max_nodes: 20 });
    let typed = check(&hir, &profile).unwrap();
    let plan = typed.mono_plan();
    assert!(
        plan.instances_of(small)
            .all(|i| i.strategy == Strategy::Copy)
    );
    assert!(
        plan.instances_of(large)
            .all(|i| i.strategy == Strategy::Shared)
    );
    // `@hot` forces a copy under a shared-everything policy.
    let mut checker = Checker::new(
        &hir,
        Profile::static_inferred().with_mono(MonoPolicy::Shared),
    );
    checker.declare_mono_attribute(hot_sym, Strategy::Copy);
    let typed = checker.check().unwrap();
    let plan = typed.mono_plan();
    assert!(plan.instances_of(hot).all(|i| i.strategy == Strategy::Copy));
    assert!(
        plan.instances_of(small)
            .all(|i| i.strategy == Strategy::Shared)
    );
}

#[test]
fn test_polymorphic_recursion_is_cut_and_reported() {
    let mut k = Kit::new();
    // struct Wrap<T> { val: T }
    let t = k.type_param("T");
    let gp = k.gparam(t, &[]);
    let g = k.generics(&[gp], &[]);
    let tt = k.tp("T", t);
    let wrap = k.grecord("Wrap", g, &[("val", tt)]);
    // fn grow<U>(x: U) { grow::<Wrap<U>>(Wrap { val: x }) }
    let u = k.type_param("U");
    let gp = k.gparam(u, &[]);
    let g = k.generics(&[gp], &[]);
    let ut = k.tp("U", u);
    let (p, x) = k.param("x", Some(ut), ParamKind::Normal, None);
    let ux = k.use_(x);
    let n = k.name("Wrap");
    let def = k.b.def(hir_lang::Def::Item(wrap));
    let path = k.b.resolved_path(n, hir_lang::Ns::Type, Res::Def(def));
    let val = k.ident("val");
    let fields = k.b.list(&[hir_lang::FieldInit {
        name: val,
        value: ux,
    }]);
    let lit = k.expr(Expr::Record {
        path: Some(path),
        fields,
        base: None,
    });
    // The callee path names `grow` itself, which is created below: build
    // the function first with a placeholder body, then patch? Paths can
    // name items created later by id, so mint the id now.
    let ut2 = k.tp("U", u);
    let wt = k.path_ty("Wrap", wrap, &[ut2]);
    let grow_id = hir_lang::ItemId::from_index(k_next_item(&mut k)).expect("id");
    let callee = k.item_expr_args("grow", grow_id, &[wt]);
    let call = k.b.call(callee, &[lit]);
    let s = k.stmt(call);
    let body = k.block(&[s], None);
    let grow = k.gfunc("grow", g, &[p], None, body);
    assert_eq!(grow, grow_id);
    let one = k.int(1);
    let c = k.call_item("grow", grow, &[one]);
    let s = k.stmt(c);
    let body = k.block(&[s], None);
    let (hir, names) = k.finish_main(&[wrap, grow], body);
    let typed = inferred_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0054 instantiating this generic item recurses without bound"]
    );
    // The plan is finite: one instance per depth up to the cap.
    assert!(typed.mono_plan().len() <= 300);
}

/// The id the next item built by `k` gets (probed with a dead error item,
/// which validation allows).
fn k_next_item(k: &mut Kit) -> usize {
    let probe = k.b.item(hir_lang::Item::new(None, hir_lang::ItemKind::Err));
    probe.index() + 1
}

// ------------------------------------------------------------- `?` hook

fn try_expr(k: &mut Kit, arg: hir_lang::ExprId) -> hir_lang::ExprId {
    let name = k.sym("try");
    let args = k.b.list(&[arg]);
    k.expr(Expr::Intrinsic {
        kind: Intrinsic::Named(name),
        generic_args: List::EMPTY,
        args,
    })
}

fn try_profile(k: &mut Kit, convert: Option<&str>) -> Profile {
    let name = k.sym("try");
    let convert = convert.map(|c| k.sym(c));
    Profile::static_inferred().with_try_hook(TryHook::Intrinsic { name, convert })
}

#[test]
fn test_try_on_nullable_and_option_like_sums() {
    let mut k = Kit::new();
    // enum Opt<T> { None, Some(T) }
    let t = k.type_param("T");
    let gp = k.gparam(t, &[]);
    let g = k.generics(&[gp], &[]);
    let none = k.variant("None", &[]);
    let tt = k.tp("T", t);
    let some = k.variant("Some", &[tt]);
    let opt = k.gsum("Opt", g, &[none, some]);
    // fn f(o: Opt<i64>) -> Opt<bool> { let v = try(o); Some(true) }
    let i = k.prim(Prim::I64);
    let ot = k.path_ty("Opt", opt, &[i]);
    let (p, o) = k.param("o", Some(ot), ParamKind::Normal, None);
    let uo = k.use_(o);
    let tr = try_expr(&mut k, uo);
    let (s, v) = k.let_("v", None, Some(tr));
    let yes = k.bool(true);
    let ctor = k.variant_expr("Some", some);
    let res = k.b.call(ctor, &[yes]);
    let body = k.block(&[s], Some(res));
    let b = k.prim(Prim::Bool);
    let rt = k.path_ty("Opt", opt, &[b]);
    let f = k.func("f", &[p], Some(rt), body);
    // fn g(x: i64?) -> bool { try(x); true }  -- not a carrier result
    let i2 = k.prim(Prim::I64);
    let n = k.ty(hir_lang::Ty::Nullable(i2));
    let (p2, x) = k.param("x", Some(n), ParamKind::Normal, None);
    let ux = k.use_(x);
    let tr2 = try_expr(&mut k, ux);
    let s2 = k.stmt(tr2);
    let t2 = k.bool(true);
    let body2 = k.block(&[s2], Some(t2));
    let b2 = k.prim(Prim::Bool);
    let g_fn = k.func("g", &[p2], Some(b2), body2);
    let profile = try_profile(&mut k, None);
    let (hir, names) = k.finish_items(&[opt, f, g_fn]);
    let typed = check(&hir, &profile).unwrap();
    assert_eq!(typed.binder(v), Some(I64));
    assert_eq!(typed.expr(tr2), Some(I64));
    assert_eq!(
        messages(&typed, &names),
        ["T0055 `bool` cannot propagate a failure here"]
    );
    // Without the hook, the intrinsic is an unknown host intrinsic.
    let plain = inferred_check(&hir);
    assert!(
        plain
            .diagnostics()
            .iter()
            .any(|d| matches!(d.kind, DiagnosticKind::UnknownExtern { .. }))
    );
}

#[test]
fn test_try_on_result_like_with_conversion() {
    let mut k = Kit::new();
    // enum Res<T, E> { Ok(T), Err(E) }
    let t = k.type_param("T");
    let e = k.type_param("E");
    let (gt, ge) = (k.gparam(t, &[]), k.gparam(e, &[]));
    let g = k.generics(&[gt, ge], &[]);
    let tt = k.tp("T", t);
    let ok = k.variant("Ok", &[tt]);
    let et = k.tp("E", e);
    let err = k.variant("Err", &[et]);
    let res = k.gsum("Res", g, &[ok, err]);
    // trait Conv<X> {}  impl Conv<i64> for str {}
    let x = k.type_param("X");
    let gx = k.gparam(x, &[]);
    let g = k.generics(&[gx], &[]);
    let conv = k.iface("Conv", g, &[], &[]);
    let i = k.prim(Prim::I64);
    let ct = k.path_ty("Conv", conv, &[i]);
    let st = k.prim(Prim::Str);
    let g = k.generics(&[], &[]);
    let imp = k.impl_of(g, Some(ct), st, &[]);
    // fn f(r: Res<bool, i64>) -> Res<bool, str> { let b = try(r); Ok(b) }
    let (b1, i1) = (k.prim(Prim::Bool), k.prim(Prim::I64));
    let rt = k.path_ty("Res", res, &[b1, i1]);
    let (p, r) = k.param("r", Some(rt), ParamKind::Normal, None);
    let ur = k.use_(r);
    let tr = try_expr(&mut k, ur);
    let (s, bv) = k.let_("b", None, Some(tr));
    let ub = k.use_(bv);
    let okc = k.variant_expr("Ok", ok);
    let ret_v = k.b.call(okc, &[ub]);
    let body = k.block(&[s], Some(ret_v));
    let (b2, s2) = (k.prim(Prim::Bool), k.prim(Prim::Str));
    let ret = k.path_ty("Res", res, &[b2, s2]);
    let f = k.func("f", &[p], Some(ret), body);
    let with = try_profile(&mut k, Some("Conv"));
    let without = try_profile(&mut k, None);
    let (hir, names) = k.finish_items(&[res, conv, imp, f]);
    let typed = check(&hir, &with).unwrap();
    assert!(typed.is_ok(), "{:?}", messages(&typed, &names));
    assert_eq!(typed.binder(bv), Some(BOOL));
    assert!(matches!(typed.coercion(tr), Some((Coercion::ErrorConvert, t)) if t == STR));
    let typed = check(&hir, &without).unwrap();
    assert_eq!(
        messages(&typed, &names),
        ["T0001 mismatched types: expected `str`, found `i64`"]
    );
}
