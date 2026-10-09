//! The static-explicit discipline, rule by rule.

mod common;

use common::{Kit, messages, static_check};
use hir_lang::{Arm, Effects, Expr, NodeRef, Op, OpKind, Overflow, ParamKind, Pat, Prim, Stmt, Ty};
use typeck_lang::{Coercion, DiagnosticKind, OpClass, Profile, Type, TypeId, check};

const I32: TypeId = TypeId::prim(Prim::I32);
const I64: TypeId = TypeId::prim(Prim::I64);
const BOOL: TypeId = TypeId::prim(Prim::Bool);
const F64: TypeId = TypeId::prim(Prim::F64);
const STR: TypeId = TypeId::prim(Prim::Str);

#[test]
fn test_literals_default_and_take_expected_types() {
    let mut k = Kit::new();
    let i32_ = k.prim(Prim::I32);
    let one = k.int(1);
    let (a, _) = k.let_("a", Some(i32_), Some(one));
    let two = k.int(2);
    let (b, _) = k.let_("b", None, Some(two));
    let half = k.float(0.5);
    let (c, _) = k.let_("c", None, Some(half));
    let body = k.block(&[a, b, c], None);
    let (hir, _) = k.finish_main(&[], body);
    let typed = static_check(&hir);
    assert!(typed.is_ok(), "{:?}", typed.diagnostics());
    assert_eq!(typed.expr(one), Some(I32));
    assert_eq!(
        typed.expr(two),
        Some(I64),
        "unconstrained: the profile default"
    );
    assert_eq!(typed.expr(half), Some(F64));
}

#[test]
fn test_let_infers_from_initializer_and_uses_flow() {
    let mut k = Kit::new();
    let t = k.bool(true);
    let (s1, x) = k.let_("x", None, Some(t));
    let use_x = k.use_(x);
    let (s2, y) = k.let_("y", None, Some(use_x));
    let body = k.block(&[s1, s2], None);
    let (hir, _) = k.finish_main(&[], body);
    let typed = static_check(&hir);
    assert!(typed.is_ok());
    assert_eq!(typed.binder(x), Some(BOOL));
    assert_eq!(typed.binder(y), Some(BOOL));
}

#[test]
fn test_mismatch_is_reported_at_the_initializer() {
    let mut k = Kit::new();
    let i32_ = k.prim(Prim::I32);
    let s = k.str("no");
    let (st, x) = k.let_("x", Some(i32_), Some(s));
    let body = k.block(&[st], None);
    let (hir, names) = k.finish_main(&[], body);
    let typed = static_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0001 mismatched types: expected `i32`, found `str`"]
    );
    assert_eq!(typed.diagnostics()[0].node, NodeRef::Expr(s));
    // The annotation still types the binder: uses of `x` do not cascade.
    assert_eq!(typed.binder(x), Some(I32));
}

#[test]
fn test_function_signature_drives_calls_and_return() {
    let mut k = Kit::new();
    let i64_ = k.prim(Prim::I64);
    let i64b = k.prim(Prim::I64);
    let (p, n) = k.param("n", Some(i64_), ParamKind::Normal, None);
    let use_n = k.use_(n);
    let one = k.int(1);
    let sum = k.op(OpKind::Add, &[use_n, one]);
    let body = k.block(&[], Some(sum));
    let inc = k.func("inc", &[p], Some(i64b), body);
    let arg = k.int(41);
    let call = k.call_item("inc", inc, &[arg]);
    let s = k.stmt(call);
    let main_body = k.block(&[s], None);
    let (hir, _) = k.finish_main(&[inc], main_body);
    let typed = static_check(&hir);
    assert!(typed.is_ok(), "{:?}", typed.diagnostics());
    assert_eq!(typed.expr(call), Some(I64));
    assert_eq!(typed.expr(arg), Some(I64));
    assert_eq!(typed.op_class(sum), Some(OpClass::Int(Prim::I64)));
}

#[test]
fn test_missing_parameter_annotation_is_one_diagnostic() {
    let mut k = Kit::new();
    let (p, x) = k.param("x", None, ParamKind::Normal, None);
    let use_x = k.use_(x);
    let s = k.stmt(use_x);
    let body = k.block(&[s], None);
    let f = k.func("f", &[p], None, body);
    let (hir, names) = k.finish_items(&[f]);
    let typed = static_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0002 a type annotation is required here"]
    );
    assert_eq!(typed.binder(x), Some(TypeId::ERROR));
}

#[test]
fn test_return_values_meet_the_declared_type() {
    let mut k = Kit::new();
    let i32_ = k.prim(Prim::I32);
    let t = k.bool(true);
    let ret = k.expr(Expr::Return(Some(t)));
    let s = k.stmt(ret);
    let body = k.block(&[s], None);
    let f = k.func("f", &[], Some(i32_), body);
    let (hir, names) = k.finish_items(&[f]);
    let typed = static_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0001 mismatched types: expected `i32`, found `bool`"]
    );
    assert_eq!(typed.diagnostics()[0].node, NodeRef::Expr(t));
    // The block ends in `return`: it diverges, so it fits `i32`.
    assert_eq!(typed.expr(body), Some(TypeId::NEVER));
}

#[test]
fn test_named_default_and_variadic_arguments() {
    let mut k = Kit::new();
    let str_ = k.prim(Prim::Str);
    let i64_ = k.prim(Prim::I64);
    let any = k.ty(Ty::Any);
    let str2 = k.prim(Prim::Str);
    let dflt = k.int(1);
    let app = k.str("app");
    let (msg, _) = k.param("msg", Some(str_), ParamKind::Normal, None);
    let (level, _) = k.param("level", Some(i64_), ParamKind::Normal, Some(dflt));
    let (args, args_b) = k.param("args", Some(any), ParamKind::Rest, None);
    let (tag, _) = k.param("tag", Some(str2), ParamKind::NamedOnly, Some(app));
    let body = k.block(&[], None);
    let log = k.func("log", &[msg, level, args, tag], None, body);
    // log("hi", 3, true, 'x', tag: "t")
    let a = k.str("hi");
    let b = k.int(3);
    let c = k.bool(true);
    let d = k.expr(Expr::Lit(hir_lang::Lit::Char('x')));
    let e = k.str("t");
    let callee = k.item_expr("log", log);
    let named = k.named("tag", e);
    let call = k.call_args(
        callee,
        &[
            hir_lang::Arg::positional(a),
            hir_lang::Arg::positional(b),
            hir_lang::Arg::positional(c),
            hir_lang::Arg::positional(d),
            named,
        ],
    );
    let s = k.stmt(call);
    let main_body = k.block(&[s], None);
    let (hir, _) = k.finish_main(&[log], main_body);
    let typed = static_check(&hir);
    assert!(typed.is_ok(), "{:?}", typed.diagnostics());
    // The rest parameter's binder is a slice of its element type.
    assert!(
        matches!(typed.types().get(typed.binder(args_b).unwrap()), Type::Slice(t) if t == TypeId::ANY)
    );
    // Extra positional arguments flowed into `any`.
    assert_eq!(typed.coercion(c), Some((Coercion::ToAny, TypeId::ANY)));
}

#[test]
fn test_argument_errors() {
    let mut k = Kit::new();
    let i64_ = k.prim(Prim::I64);
    let (x, _) = k.param("x", Some(i64_), ParamKind::Normal, None);
    let body = k.block(&[], None);
    let f = k.func("f", &[x], None, body);
    // f()            -> missing x
    let c1 = k.call_item("f", f, &[]);
    // f(1, 2)        -> too many
    let (one, two) = (k.int(1), k.int(2));
    let c2 = k.call_item("f", f, &[one, two]);
    // f(y: 1)        -> unknown name (and x missing)
    let three = k.int(3);
    let callee = k.item_expr("f", f);
    let named = k.named("y", three);
    let c3 = k.call_args(callee, &[named]);
    // f(4, x: 5)     -> duplicate
    let (four, five) = (k.int(4), k.int(5));
    let callee = k.item_expr("f", f);
    let named = k.named("x", five);
    let c4 = k.call_args(callee, &[hir_lang::Arg::positional(four), named]);
    let stmts: Vec<_> = [c1, c2, c3, c4].iter().map(|&c| k.stmt(c)).collect();
    let main_body = k.block(&stmts, None);
    let (hir, names) = k.finish_main(&[f], main_body);
    let typed = static_check(&hir);
    let mut got = messages(&typed, &names);
    got.sort();
    assert_eq!(
        got,
        [
            "T0007 expected 1 arguments, found 2",
            "T0008 no parameter named `y`",
            "T0009 parameter `x` is given more than once",
            "T0010 missing argument for parameter `x`",
            "T0010 missing argument for parameter `x`",
        ]
    );
}

#[test]
fn test_records_fields_and_literals() {
    let mut k = Kit::new();
    let f64_ = k.prim(Prim::F64);
    let f64b = k.prim(Prim::F64);
    let point = k.record("Point", &[("x", f64_), ("y", f64b)]);
    let pt = k.item_ty("Point", point);
    // let p: Point = Point { x: 1.0, y: 2.0 }; p.x
    let n = k.name("Point");
    let def = k.b.def(hir_lang::Def::Item(point));
    let path =
        k.b.resolved_path(n, hir_lang::Ns::Type, hir_lang::Res::Def(def));
    let (one, two) = (k.float(1.0), k.float(2.0));
    let (xi, yi) = (k.ident("x"), k.ident("y"));
    let fields = k.b.list(&[
        hir_lang::FieldInit {
            name: xi,
            value: one,
        },
        hir_lang::FieldInit {
            name: yi,
            value: two,
        },
    ]);
    let lit = k.expr(Expr::Record {
        path: Some(path),
        fields,
        base: None,
    });
    let (s, p) = k.let_("p", Some(pt), Some(lit));
    let use_p = k.use_(p);
    let fx = k.field_expr(use_p, "x");
    let use_p2 = k.use_(p);
    let fz = k.field_expr(use_p2, "z");
    let s2 = k.stmt(fz);
    let body = k.block(&[s, s2], Some(fx));
    let ret = k.prim(Prim::F64);
    let main = k.func("get", &[], Some(ret), body);
    let (hir, names) = k.finish_items(&[point, main]);
    let typed = static_check(&hir);
    assert_eq!(messages(&typed, &names), ["T0012 `Point` has no field `z`"]);
    assert_eq!(typed.expr(fx), Some(F64));
    assert!(matches!(typed.types().get(typed.expr(lit).unwrap()), Type::Adt(i) if i == point));
}

#[test]
fn test_record_literal_missing_and_unknown_fields() {
    let mut k = Kit::new();
    let i32_ = k.prim(Prim::I32);
    let i32b = k.prim(Prim::I32);
    let point = k.record("P", &[("x", i32_), ("y", i32b)]);
    let n = k.name("P");
    let def = k.b.def(hir_lang::Def::Item(point));
    let path =
        k.b.resolved_path(n, hir_lang::Ns::Type, hir_lang::Res::Def(def));
    let one = k.int(1);
    let xi = k.ident("x");
    let fields = k.b.list(&[hir_lang::FieldInit {
        name: xi,
        value: one,
    }]);
    let lit = k.expr(Expr::Record {
        path: Some(path),
        fields,
        base: None,
    });
    let s = k.stmt(lit);
    let body = k.block(&[s], None);
    let (hir, names) = k.finish_main(&[point], body);
    let typed = static_check(&hir);
    assert_eq!(messages(&typed, &names), ["T0015 missing field `y`"]);
}

#[test]
fn test_impl_methods_and_partial_paths() {
    let mut k = Kit::new();
    let i32_ = k.prim(Prim::I32);
    let counter = k.record("Counter", &[("n", i32_)]);
    // impl Counter { fn get(self) -> i32 { self.n }  fn zero() -> i32 { 0 } }
    let (recv, self_b) = k.receiver(None);
    let use_self = k.use_(self_b);
    let get_n = k.field_expr(use_self, "n");
    let get_body = k.block(&[], Some(get_n));
    let ret = k.prim(Prim::I32);
    let get = k.func("get", &[recv], Some(ret), get_body);
    let zero_lit = k.int(0);
    let zero_body = k.block(&[], Some(zero_lit));
    let ret2 = k.prim(Prim::I32);
    let zero = k.func("zero", &[], Some(ret2), zero_body);
    let self_ty = k.item_ty("Counter", counter);
    let imp = k.impl_(self_ty, &[get, zero]);
    // fn main() { let c: Counter = ...param; c.get(); Counter::zero(); }
    let ct = k.item_ty("Counter", counter);
    let (pc, c) = k.param("c", Some(ct), ParamKind::Normal, None);
    let use_c = k.use_(c);
    let mcall = k.method_call(use_c, "get", &[]);
    let s1 = k.stmt(mcall);
    let ap = k.assoc_path("Counter", counter, "zero");
    let callee = k.expr(Expr::Path(ap));
    let zcall = k.b.call(callee, &[]);
    let s2 = k.stmt(zcall);
    let use_c2 = k.use_(c);
    let bad = k.method_call(use_c2, "nope", &[]);
    let s3 = k.stmt(bad);
    let body = k.block(&[s1, s2, s3], None);
    let main = k.func("main", &[pc], None, body);
    let (hir, names) = k.finish_items(&[counter, imp, main]);
    let typed = static_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0013 `Counter` has no method or associated item `nope`"]
    );
    assert_eq!(typed.expr(mcall), Some(I32));
    assert_eq!(typed.method(mcall), Some(get));
    assert_eq!(typed.expr(zcall), Some(I32));
    assert_eq!(typed.path_def(ap), Some(hir_lang::Def::Item(zero)));
}

#[test]
fn test_sum_variants_match_and_exhaustiveness() {
    let mut k = Kit::new();
    let f64_ = k.prim(Prim::F64);
    let circle = k.variant("Circle", &[f64_]);
    let empty = k.variant("Empty", &[]);
    let shape = k.sum("Shape", &[circle, empty]);
    let st = k.item_ty("Shape", shape);
    let (ps, s) = k.param("s", Some(st), ParamKind::Normal, None);
    // match s { Circle(r) => r, _ => 0.0 }
    let use_s = k.use_(s);
    let (r, rpat) = k.local("r");
    let n = k.name("Circle");
    let def = k.b.def(hir_lang::Def::Variant(circle));
    let cpath =
        k.b.resolved_path(n, hir_lang::Ns::Pattern, hir_lang::Res::Def(def));
    let elems = k.b.list(&[rpat]);
    let cpat = k.b.pat(Pat::Ctor {
        path: cpath,
        elems,
        rest: None,
    });
    let use_r = k.use_(r);
    let wild = k.b.pat(Pat::Wild);
    let zero = k.float(0.0);
    let arms = k.b.list(&[
        Arm {
            pat: cpat,
            guard: None,
            body: use_r,
        },
        Arm {
            pat: wild,
            guard: None,
            body: zero,
        },
    ]);
    let m = k.expr(Expr::Match {
        scrutinee: use_s,
        arms,
    });
    let body = k.block(&[], Some(m));
    let ret = k.prim(Prim::F64);
    let area = k.func("area", &[ps], Some(ret), body);
    // A second function without the catch-all: non-exhaustive.
    let st2 = k.item_ty("Shape", shape);
    let (ps2, s2) = k.param("s", Some(st2), ParamKind::Normal, None);
    let use_s2 = k.use_(s2);
    let (_, rpat2) = k.local("r2");
    let n2 = k.name("Circle");
    let def2 = k.b.def(hir_lang::Def::Variant(circle));
    let cpath2 =
        k.b.resolved_path(n2, hir_lang::Ns::Pattern, hir_lang::Res::Def(def2));
    let elems2 = k.b.list(&[rpat2]);
    let cpat2 = k.b.pat(Pat::Ctor {
        path: cpath2,
        elems: elems2,
        rest: None,
    });
    let unit = k.expr(Expr::Tuple(hir_lang::List::EMPTY));
    let arms2 = k.b.list(&[Arm {
        pat: cpat2,
        guard: None,
        body: unit,
    }]);
    let m2 = k.expr(Expr::Match {
        scrutinee: use_s2,
        arms: arms2,
    });
    let s_m2 = k.stmt(m2);
    let body2 = k.block(&[s_m2], None);
    let partial = k.func("partial", &[ps2], None, body2);
    let (hir, names) = k.finish_items(&[shape, area, partial]);
    let typed = static_check(&hir);
    assert_eq!(messages(&typed, &names), ["T0027 non-exhaustive match"]);
    assert_eq!(
        typed.diagnostics()[0].kind,
        DiagnosticKind::NonExhaustive {
            missing: Some(empty)
        }
    );
    assert_eq!(typed.binder(r), Some(F64));
    assert_eq!(typed.expr(m), Some(F64));
    // Without the toggle, nothing is reported.
    let lax = check(
        &hir,
        &Profile::static_explicit().with_exhaustive_match(false),
    )
    .unwrap();
    assert!(lax.is_ok());
}

#[test]
fn test_if_and_loops() {
    let mut k = Kit::new();
    // let x = if true { 1 } else { 2 };
    let c = k.bool(true);
    let (one, two) = (k.int(1), k.int(2));
    let iff = k.expr(Expr::If {
        cond: c,
        then: one,
        else_: Some(two),
    });
    let (s1, x) = k.let_("x", None, Some(iff));
    // let y = loop { break 5 };
    let five = k.int(5);
    let brk = k.expr(Expr::Break {
        label: None,
        value: Some(five),
    });
    let lp = k.expr(Expr::Loop {
        label: None,
        body: brk,
        step: None,
    });
    let (s2, y) = k.let_("y", None, Some(lp));
    // if 3 { }   -> condition must be bool
    let three = k.int(3);
    let unit = k.block(&[], None);
    let bad = k.expr(Expr::If {
        cond: three,
        then: unit,
        else_: None,
    });
    let s3 = k.stmt(bad);
    let body = k.block(&[s1, s2, s3], None);
    let (hir, names) = k.finish_main(&[], body);
    let typed = static_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0001 mismatched types: expected `bool`, found `i64`"]
    );
    assert_eq!(typed.diagnostics()[0].node, NodeRef::Expr(three));
    assert_eq!(typed.binder(x), Some(I64));
    assert_eq!(typed.binder(y), Some(I64));
    assert_eq!(typed.expr(lp), Some(I64));
}

#[test]
fn test_ops_follow_ops_policies() {
    let mut k = Kit::new();
    // promote on a static result is rejected
    let (a, b) = (k.int(1), k.int(2));
    let promote = k.b.op_with(
        Op::new(OpKind::Add).with_overflow(Overflow::Promote),
        &[a, b],
    );
    let s1 = k.stmt(promote);
    // shifts take any integer amount
    let u8_lit = k.b.lit(hir_lang::Lit::Int(
        hir_lang::IntLit::new(1).with_suffix(Prim::U8),
    ));
    let amount = k.b.lit(hir_lang::Lit::Int(
        hir_lang::IntLit::new(3).with_suffix(Prim::I64),
    ));
    let shl = k.op(OpKind::Shl, &[u8_lit, amount]);
    let s2 = k.stmt(shl);
    // sqrt is IEEE-only
    let i = k.int(4);
    let sqrt = k.op(OpKind::Sqrt, &[i]);
    let s3 = k.stmt(sqrt);
    // comparisons give bool; floats compare
    let (f1, f2) = (k.float(1.0), k.float(2.0));
    let lt = k.op(OpKind::Lt, &[f1, f2]);
    let s4 = k.stmt(lt);
    // conversions
    let big = k.b.lit(hir_lang::Lit::Int(
        hir_lang::IntLit::new(1).with_suffix(Prim::I64),
    ));
    let sext = k.op(OpKind::Sext(Prim::I8), &[big]);
    let s5 = k.stmt(sext);
    let body = k.block(&[s1, s2, s3, s4, s5], None);
    let (hir, names) = k.finish_main(&[], body);
    let typed = static_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        [
            "T0019 the `promote` overflow policy needs a dynamically typed result (`add`)",
            "T0018 `sqrt` is not defined for `i64`",
            "T0021 `sext` cannot convert from `i64`",
        ]
    );
    assert_eq!(typed.expr(shl), Some(TypeId::prim(Prim::U8)));
    assert_eq!(typed.expr(lt), Some(BOOL));
    assert_eq!(typed.op_class(lt), Some(OpClass::Float(Prim::F64)));
    assert_eq!(typed.expr(sext), Some(TypeId::prim(Prim::I8)));
}

#[test]
fn test_numeric_widening_toggle() {
    let mut k = Kit::new();
    let i32_ = k.prim(Prim::I32);
    let i64_ = k.prim(Prim::I64);
    let one = k.b.lit(hir_lang::Lit::Int(
        hir_lang::IntLit::new(1).with_suffix(Prim::I32),
    ));
    let (s1, x) = k.let_("x", Some(i32_), Some(one));
    let use_x = k.use_(x);
    let (s2, _) = k.let_("y", Some(i64_), Some(use_x));
    let body = k.block(&[s1, s2], None);
    let (hir, names) = k.finish_main(&[], body);
    let strict = static_check(&hir);
    assert_eq!(
        messages(&strict, &names),
        ["T0001 mismatched types: expected `i64`, found `i32`"]
    );
    let wide = check(
        &hir,
        &Profile::static_explicit().with_numeric_widening(true),
    )
    .unwrap();
    assert!(wide.is_ok());
    assert_eq!(wide.coercion(use_x), Some((Coercion::Widen, I64)));
}

#[test]
fn test_null_safety() {
    let mut k = Kit::new();
    let i32_ = k.prim(Prim::I32);
    let opt = k.ty(Ty::Nullable(i32_));
    let n1 = k.null();
    let (s1, x) = k.let_("x", Some(opt), Some(n1));
    let one = k.int(1);
    let i32b = k.prim(Prim::I32);
    let opt2 = k.ty(Ty::Nullable(i32b));
    let (s2, _) = k.let_("y", Some(opt2), Some(one));
    // x == null is a null check
    let use_x = k.use_(x);
    let n2 = k.null();
    let eq = k.op(OpKind::Eq, &[use_x, n2]);
    let s3 = k.stmt(eq);
    // let z: i32 = null;  -> error under null safety
    let i32c = k.prim(Prim::I32);
    let n3 = k.null();
    let (s4, _) = k.let_("z", Some(i32c), Some(n3));
    let body = k.block(&[s1, s2, s3, s4], None);
    let (hir, names) = k.finish_main(&[], body);
    let typed = static_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0001 mismatched types: expected `i32`, found `null`"]
    );
    assert_eq!(
        typed.coercion(one),
        Some((Coercion::WrapNullable, typed.binder(x).unwrap()))
    );
    assert_eq!(typed.op_class(eq), Some(OpClass::NullCheck));
}

#[test]
fn test_unresolved_and_unknown_externs() {
    let mut k = Kit::new();
    let f = k.name("missing");
    let callee = k.b.name_expr(f);
    let call = k.b.call(callee, &[]);
    let s1 = k.stmt(call);
    let sym = k.sym("print");
    let n = k.name("print");
    let p =
        k.b.resolved_path(n, hir_lang::Ns::Value, hir_lang::Res::Extern(sym));
    let ext = k.expr(Expr::Path(p));
    let s2 = k.stmt(ext);
    let body = k.block(&[s1, s2], None);
    let (hir, names) = k.finish_main(&[], body);
    let typed = static_check(&hir);
    // One diagnostic per root cause: the call of an unresolved callee is
    // not reported again.
    assert_eq!(
        messages(&typed, &names),
        [
            "T0003 unresolved name",
            "T0004 the type of `print` is not declared to the checker"
        ]
    );
    assert_eq!(typed.expr(call), Some(TypeId::ERROR));
}

#[test]
fn test_error_nodes_are_contained() {
    let mut k = Kit::new();
    let i32_ = k.prim(Prim::I32);
    let err = k.expr(Expr::Err);
    let (s1, x) = k.let_("x", None, Some(err));
    let use_x = k.use_(x);
    let one = k.int(1);
    let sum = k.op(OpKind::Add, &[use_x, one]);
    let (s2, _) = k.let_("y", Some(i32_), Some(sum));
    let use_x2 = k.use_(x);
    let fld = k.field_expr(use_x2, "anything");
    let call = k.b.call(fld, &[]);
    let s3 = k.stmt(call);
    let body = k.block(&[s1, s2, s3], None);
    let (hir, _) = k.finish_main(&[], body);
    let typed = static_check(&hir);
    assert!(typed.is_ok(), "{:?}", typed.diagnostics());
    assert_eq!(typed.binder(x), Some(TypeId::ERROR));
}

#[test]
fn test_cannot_infer_reports_once_at_the_binding() {
    let mut k = Kit::new();
    let (s1, x) = k.let_("x", None, None);
    let use_x = k.use_(x);
    let s2 = k.stmt(use_x);
    let body = k.block(&[s1, s2], None);
    let (hir, names) = k.finish_main(&[], body);
    let typed = static_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0023 cannot infer a type here; add an annotation"]
    );
    assert!(matches!(typed.diagnostics()[0].node, NodeRef::Pat(_)));
    assert_eq!(typed.binder(x), Some(TypeId::ERROR));
}

#[test]
fn test_deferred_initialization_is_inferred() {
    let mut k = Kit::new();
    let (s1, x) = k.let_("x", None, None);
    let target = k.use_(x);
    let v = k.bool(false);
    let assign = k.expr(Expr::Assign {
        target,
        op: None,
        value: v,
    });
    let s2 = k.stmt(assign);
    let body = k.block(&[s1, s2], None);
    let (hir, _) = k.finish_main(&[], body);
    let typed = static_check(&hir);
    assert!(typed.is_ok());
    assert_eq!(typed.binder(x), Some(BOOL));
    assert_eq!(typed.expr(assign), Some(TypeId::UNIT));
}

#[test]
fn test_literal_ranges_are_checked_after_inference() {
    let mut k = Kit::new();
    let u8_ = k.prim(Prim::U8);
    let big = k.int(300);
    let (s1, _) = k.let_("a", Some(u8_), Some(big));
    let u8b = k.prim(Prim::U8);
    let neg = k.int(-1);
    let (s2, _) = k.let_("b", Some(u8b), Some(neg));
    let body = k.block(&[s1, s2], None);
    let (hir, names) = k.finish_main(&[], body);
    let typed = static_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        [
            "T0022 literal out of range for `u8`",
            "T0022 literal out of range for `u8`"
        ]
    );
}

#[test]
fn test_casts() {
    let mut k = Kit::new();
    let f64_ = k.prim(Prim::F64);
    let one = k.int(1);
    let ok = k.expr(Expr::Cast {
        expr: one,
        ty: f64_,
        policy: hir_lang::Policy::CAST,
    });
    let s1 = k.stmt(ok);
    let bool_ = k.prim(Prim::Bool);
    let s = k.str("x");
    let bad = k.expr(Expr::Cast {
        expr: s,
        ty: bool_,
        policy: hir_lang::Policy::CAST,
    });
    let s2 = k.stmt(bad);
    let body = k.block(&[s1, s2], None);
    let (hir, names) = k.finish_main(&[], body);
    let typed = static_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0020 cannot cast `str` to `bool`"]
    );
    assert_eq!(typed.expr(ok), Some(F64));
}

#[test]
fn test_dynamic_forms_and_any_values_are_rejected_statically() {
    let mut k = Kit::new();
    let any = k.ty(Ty::Any);
    let (p, x) = k.param("x", Some(any), ParamKind::Normal, None);
    let use_x = k.use_(x);
    let one = k.int(1);
    let sum = k.op(OpKind::Add, &[use_x, one]);
    let s1 = k.stmt(sum);
    let name = k.str("n");
    let vv = k.expr(Expr::VarVar(name));
    let s2 = k.stmt(vv);
    let body = k.block(&[s1, s2], None);
    let f = k.func("f", &[p], None, body);
    let (hir, names) = k.finish_items(&[f]);
    let typed = static_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        [
            "T0024 operation on a dynamic `any` value; cast or type-test it first",
            "T0025 this dynamic form is not allowed under a static profile",
        ]
    );
}

#[test]
fn test_generics_are_reported_once_as_unsupported() {
    let mut k = Kit::new();
    let t = k.name("T");
    let tb = k.b.new_binder(t, hir_lang::BinderKind::TypeParam);
    let tpath =
        k.b.resolved_path(t, hir_lang::Ns::Type, hir_lang::Res::Local(tb));
    let tty = k.ty(Ty::Path(tpath));
    let (p, x) = k.param("x", Some(tty), ParamKind::Normal, None);
    let use_x = k.use_(x);
    let body = k.block(&[], Some(use_x));
    let tpath2 =
        k.b.resolved_path(t, hir_lang::Ns::Type, hir_lang::Res::Local(tb));
    let ret = k.ty(Ty::Path(tpath2));
    let n = k.name("id");
    let params = k.b.list(&[p]);
    let gp = k.b.list(&[hir_lang::GenericParam::new(tb)]);
    let id = k.b.item(hir_lang::Item::new(
        Some(n),
        hir_lang::ItemKind::Fn(hir_lang::FnDef {
            generics: hir_lang::Generics {
                params: gp,
                preds: hir_lang::List::EMPTY,
            },
            params,
            ret: Some(ret),
            body: Some(body),
            ..hir_lang::FnDef::default()
        }),
    ));
    // A use of the generic function is not a second diagnostic.
    let one = k.int(1);
    let call = k.call_item("id", id, &[one]);
    let s = k.stmt(call);
    let main_body = k.block(&[s], None);
    let (hir, names) = k.finish_main(&[id], main_body);
    let typed = static_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0028 generics are not supported by this profile in this version"]
    );
    // Inside the item, the parameter is a rigid type.
    assert!(matches!(typed.types().get(typed.binder(x).unwrap()), Type::Param(b) if b == tb));
}

#[test]
fn test_closures_effects_and_tasks() {
    let mut k = Kit::new();
    let i64_ = k.prim(Prim::I64);
    let (p, x) = k.param("x", Some(i64_), ParamKind::Normal, None);
    let use_x = k.use_(x);
    let params = k.b.list(&[p]);
    let clo = k.expr(Expr::Closure(hir_lang::Closure {
        params,
        ..hir_lang::Closure::new(use_x)
    }));
    let (s1, f) = k.let_("f", None, Some(clo));
    let use_f = k.use_(f);
    let two = k.int(2);
    let call = k.b.call(use_f, &[two]);
    let (s2, r) = k.let_("r", None, Some(call));
    // spawn(|| 1) then await the handle, in an async function
    let one = k.int(1);
    let thunk = k.expr(Expr::Closure(hir_lang::Closure::new(one)));
    let spawn = k.expr(Expr::Spawn(thunk));
    let wait = k.expr(Expr::Await(spawn));
    let (s3, w) = k.let_("w", None, Some(wait));
    let body = k.block(&[s1, s2, s3], None);
    let main = k.func_fx("main", &[], None, Effects::ASYNC, body);
    let (hir, _) = k.finish_items(&[main]);
    let typed = static_check(&hir);
    assert!(typed.is_ok(), "{:?}", typed.diagnostics());
    assert_eq!(typed.binder(r), Some(I64));
    assert_eq!(typed.binder(w), Some(I64));
    assert!(
        matches!(typed.types().get(typed.binder(f).unwrap()), Type::Fn { params: [p], ret, .. } if *p == I64 && ret == I64)
    );
}

#[test]
fn test_host_declarations() {
    let mut k = Kit::new();
    let vec_sym = k.sym("Vec");
    let len_sym = k.sym("len");
    let make_sym = k.sym("make");
    // let v = make(); v.len()
    let n = k.name("make");
    let p =
        k.b.resolved_path(n, hir_lang::Ns::Value, hir_lang::Res::Extern(make_sym));
    let callee = k.expr(Expr::Path(p));
    let call = k.b.call(callee, &[]);
    let (s1, v) = k.let_("v", None, Some(call));
    let use_v = k.use_(v);
    let len = k.method_call(use_v, "len", &[]);
    let body = k.block(&[s1], Some(len));
    let ret = k.prim(Prim::Usize);
    let f = k.func("f", &[], Some(ret), body);
    let (hir, _) = k.finish_items(&[f]);
    let mut checker = typeck_lang::Checker::new(&hir, Profile::static_explicit());
    let vec_ty = checker.types_mut().external(vec_sym);
    let make_ty = checker.types_mut().func(&[], vec_ty, Effects::NONE);
    let len_ty = checker
        .types_mut()
        .func(&[vec_ty], TypeId::prim(Prim::Usize), Effects::NONE);
    checker.declare_extern(make_sym, make_ty);
    checker.declare_member(vec_ty, len_sym, len_ty);
    let typed = checker.check().unwrap();
    assert!(typed.is_ok(), "{:?}", typed.diagnostics());
    assert_eq!(typed.expr(len), Some(TypeId::prim(Prim::Usize)));
}

#[test]
fn test_strings_compare_and_concatenate_per_profile() {
    let mut k = Kit::new();
    let (a, b) = (k.str("a"), k.str("b"));
    let cat = k.op(OpKind::Add, &[a, b]);
    let s1 = k.stmt(cat);
    let (c, d) = (k.str("c"), k.str("d"));
    let lt = k.op(OpKind::Lt, &[c, d]);
    let s2 = k.stmt(lt);
    let body = k.block(&[s1, s2], None);
    let (hir, names) = k.finish_main(&[], body);
    let typed = static_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0018 `add` is not defined for `str`"]
    );
    let with = check(&hir, &Profile::static_explicit().with_string_add(true)).unwrap();
    assert!(with.is_ok());
    assert_eq!(with.expr(cat), Some(STR));
    assert_eq!(with.op_class(cat), Some(OpClass::Str));
}

#[test]
fn test_let_else_must_diverge() {
    let mut k = Kit::new();
    let one = k.int(1);
    let (_, pat) = k.local("x");
    let unit = k.block(&[], None);
    let s = k.b.stmt(Stmt::Let {
        pat,
        ty: None,
        init: Some(one),
        else_: Some(unit),
    });
    let body = k.block(&[s], None);
    let (hir, names) = k.finish_main(&[], body);
    let typed = static_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0001 mismatched types: expected `!`, found `()`"]
    );
}
