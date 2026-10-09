//! The dynamic discipline, and the same programs under both disciplines.

mod common;

use common::{Kit, messages};
use hir_lang::{Arg, Expr, Op, OpKind, Overflow, ParamKind, Pat, Prim, Ty};
use typeck_lang::{CheckError, Discipline, OpClass, Profile, TypeId, check};

#[test]
fn test_everything_is_any_and_nothing_is_a_type_error() {
    let mut k = Kit::new();
    // fn main() { let x = 1 + true; x.foo(); promote(PHP_INT_MAX + 1) }
    let one = k.int(1);
    let yes = k.bool(true);
    let sum = k.op(OpKind::Add, &[one, yes]);
    let (s1, x) = k.let_("x", None, Some(sum));
    let use_x = k.use_(x);
    let call = k.method_call(use_x, "foo", &[]);
    let s2 = k.stmt(call);
    let (a, b) = (k.int(i64::MAX), k.int(1));
    let promote = k.b.op_with(
        Op::new(OpKind::Add).with_overflow(Overflow::Promote),
        &[a, b],
    );
    let s3 = k.stmt(promote);
    let body = k.block(&[s1, s2, s3], None);
    let (hir, _) = k.finish_main(&[], body);
    let typed = check(&hir, &Profile::dynamic()).unwrap();
    assert!(typed.is_ok(), "{:?}", typed.diagnostics());
    assert_eq!(typed.expr(sum), Some(TypeId::ANY));
    assert_eq!(typed.binder(x), Some(TypeId::ANY));
    assert_eq!(typed.op_class(promote), Some(OpClass::Dynamic));
    // Statically: `true` in `add`, and `promote` on a static result. `x` is
    // `{error}` after the first, so `x.foo()` is not reported again.
    let typed = check(&hir, &Profile::static_explicit()).unwrap();
    assert_eq!(typed.diagnostics().len(), 2, "{:?}", typed.diagnostics());
}

#[test]
fn test_certain_arity_errors_are_reported() {
    let mut k = Kit::new();
    let (x, _) = k.param("x", None, ParamKind::Normal, None);
    let body = k.block(&[], None);
    let f = k.func("f", &[x], None, body);
    let (one, two) = (k.int(1), k.int(2));
    let too_many = k.call_item("f", f, &[one, two]);
    let s1 = k.stmt(too_many);
    let three = k.int(3);
    let callee = k.item_expr("f", f);
    let named = k.named("nope", three);
    let unknown = k.call_args(callee, &[named]);
    let s2 = k.stmt(unknown);
    // With a spread, the count is not certain: nothing reported.
    let xs = k.int(0);
    let callee = k.item_expr("f", f);
    let spread = k.call_args(
        callee,
        &[Arg {
            kind: hir_lang::ArgKind::Spread,
            value: xs,
            place: false,
        }],
    );
    let s3 = k.stmt(spread);
    let body = k.block(&[s1, s2, s3], None);
    let (hir, names) = k.finish_main(&[f], body);
    let typed = check(&hir, &Profile::dynamic()).unwrap();
    assert_eq!(
        messages(&typed, &names),
        [
            "T0007 expected 1 arguments, found 2",
            "T0008 no parameter named `nope`",
            "T0010 missing argument for parameter `x`",
        ]
    );
    let quiet = check(&hir, &Profile::dynamic().with_certain_errors(false)).unwrap();
    assert!(quiet.is_ok());
}

#[test]
fn test_certain_shape_errors_on_constructors_and_records() {
    let mut k = Kit::new();
    let i64_ = k.prim(Prim::I64);
    let some = k.variant("Some", &[i64_]);
    let none = k.variant("None", &[]);
    let opt = k.sum("Opt", &[some, none]);
    let i64b = k.prim(Prim::I64);
    let rec = k.record("R", &[("a", i64b)]);
    // Some(1, 2)
    let (one, two) = (k.int(1), k.int(2));
    let callee = k.variant_expr("Some", some);
    let ctor = k.b.call(callee, &[one, two]);
    let s1 = k.stmt(ctor);
    // R { b: 1 }
    let n = k.name("R");
    let def = k.b.def(hir_lang::Def::Item(rec));
    let path =
        k.b.resolved_path(n, hir_lang::Ns::Type, hir_lang::Res::Def(def));
    let v = k.int(1);
    let bi = k.ident("b");
    let fields = k.b.list(&[hir_lang::FieldInit { name: bi, value: v }]);
    let lit = k.expr(Expr::Record {
        path: Some(path),
        fields,
        base: None,
    });
    let s2 = k.stmt(lit);
    // match 0 { Some(a, b) => () }
    let scrut = k.int(0);
    let n = k.name("Some");
    let def = k.b.def(hir_lang::Def::Variant(some));
    let ppath =
        k.b.resolved_path(n, hir_lang::Ns::Pattern, hir_lang::Res::Def(def));
    let (_, pa) = k.local("a");
    let (_, pb) = k.local("b");
    let elems = k.b.list(&[pa, pb]);
    let pat = k.b.pat(Pat::Ctor {
        path: ppath,
        elems,
        rest: None,
    });
    let unit = k.expr(Expr::Tuple(hir_lang::List::EMPTY));
    let arms = k.b.list(&[hir_lang::Arm {
        pat,
        guard: None,
        body: unit,
    }]);
    let m = k.expr(Expr::Match {
        scrutinee: scrut,
        arms,
    });
    let s3 = k.stmt(m);
    let body = k.block(&[s1, s2, s3], None);
    let (hir, names) = k.finish_main(&[opt, rec], body);
    let typed = check(&hir, &Profile::dynamic()).unwrap();
    assert_eq!(
        messages(&typed, &names),
        [
            "T0007 expected 1 arguments, found 2",
            "T0014 `R` has no field `b`",
            "T0007 expected 1 arguments, found 2",
        ]
    );
}

#[test]
fn test_annotations_are_hints_under_dynamic() {
    let mut k = Kit::new();
    // fn f(x) -> Missing { x }   : nothing is lowered, nothing reported
    let n = k.name("Missing");
    let p = k.b.name_path(n, hir_lang::Ns::Type);
    let ret = k.ty(Ty::Path(p));
    let (px, x) = k.param("x", None, ParamKind::Normal, None);
    let use_x = k.use_(x);
    let body = k.block(&[], Some(use_x));
    let f = k.func("f", &[px], Some(ret), body);
    let (hir, names) = k.finish_items(&[f]);
    let typed = check(&hir, &Profile::dynamic()).unwrap();
    assert!(typed.is_ok());
    let strict = check(&hir, &Profile::static_explicit()).unwrap();
    assert_eq!(
        messages(&strict, &names),
        [
            "T0002 a type annotation is required here",
            "T0003 unresolved name"
        ]
    );
}

#[test]
fn test_unimplemented_disciplines_and_invalid_profiles() {
    let mut k = Kit::new();
    let body = k.block(&[], None);
    let (hir, _) = k.finish_main(&[], body);
    for p in [
        Profile::gradual(),
        Profile::static_inferred(),
        Profile::hm(),
    ] {
        assert_eq!(
            check(&hir, &p),
            Err(CheckError::NotImplemented {
                discipline: p.discipline
            })
        );
    }
    let bad = Profile::static_explicit().with_literal_defaults(Prim::F64, Prim::F64);
    assert_eq!(check(&hir, &bad), Err(CheckError::InvalidProfile));
    assert!(Discipline::Dynamic.is_implemented());
    assert_eq!(
        CheckError::NotImplemented {
            discipline: Discipline::Hm
        }
        .to_string(),
        "the `hm` discipline is not implemented in this version"
    );
}

#[test]
fn test_partial_paths_resolve_under_dynamic_too() {
    let mut k = Kit::new();
    let circle = k.variant("Circle", &[]);
    let shape = k.sum("Shape", &[circle]);
    let ap = k.assoc_path("Shape", shape, "Circle");
    let e = k.expr(Expr::Path(ap));
    let s = k.stmt(e);
    let body = k.block(&[s], None);
    let (hir, _) = k.finish_main(&[shape], body);
    let typed = check(&hir, &Profile::dynamic()).unwrap();
    assert_eq!(typed.path_def(ap), Some(hir_lang::Def::Variant(circle)));
    let typed = check(&hir, &Profile::static_explicit()).unwrap();
    assert_eq!(typed.path_def(ap), Some(hir_lang::Def::Variant(circle)));
    assert!(
        matches!(typed.types().get(typed.expr(e).unwrap()), typeck_lang::Type::Adt(i) if i == shape)
    );
}
