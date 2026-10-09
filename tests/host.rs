//! Host declarations, including hostile ones: types naming items the unit
//! does not have, and ids from another type store.

mod common;

use common::Kit;
use hir_lang::{Arm, Effects, Expr, ItemId, Pat, Prim, Res};
use typeck_lang::{Checker, Profile, TypeId, Types};

/// `fn main() { let v = make(); v.m(); v.f; v[0]; match v { _ => () }; let w: i32 = v; }`
fn uses_of_make() -> (hir_lang::Hir, intern_lang::Interner, hir_lang::Symbol) {
    let mut k = Kit::new();
    let make = k.sym("make");
    let n = k.name("make");
    let p = k.b.resolved_path(n, hir_lang::Ns::Value, Res::Extern(make));
    let callee = k.expr(Expr::Path(p));
    let call = k.b.call(callee, &[]);
    let (s1, v) = k.let_("v", None, Some(call));
    let uv = k.use_(v);
    let m = k.method_call(uv, "m", &[]);
    let s2 = k.stmt(m);
    let uv = k.use_(v);
    let f = k.field_expr(uv, "f");
    let s3 = k.stmt(f);
    let uv = k.use_(v);
    let zero = k.int(0);
    let idx = k.expr(Expr::Index {
        base: uv,
        index: zero,
    });
    let s4 = k.stmt(idx);
    let uv = k.use_(v);
    let wild = k.b.pat(Pat::Wild);
    let unit = k.expr(Expr::Tuple(hir_lang::List::EMPTY));
    let arms = k.b.list(&[Arm {
        pat: wild,
        guard: None,
        body: unit,
    }]);
    let mt = k.expr(Expr::Match {
        scrutinee: uv,
        arms,
    });
    let s5 = k.stmt(mt);
    let uv = k.use_(v);
    let i32_ = k.prim(Prim::I32);
    let (s6, _) = k.let_("w", Some(i32_), Some(uv));
    let body = k.block(&[s1, s2, s3, s4, s5, s6], None);
    let (hir, names) = k.finish_main(&[], body);
    (hir, names, make)
}

#[test]
fn test_types_naming_foreign_items_are_harmless() {
    let (hir, _, make) = uses_of_make();
    let mut checker = Checker::new(&hir, Profile::static_explicit().with_subtyping(true));
    let bogus = checker
        .types_mut()
        .adt(ItemId::from_index(999_999).unwrap());
    let f = checker.types_mut().func(&[], bogus, Effects::NONE);
    checker.declare_extern(make, f);
    let typed = checker.check().unwrap();
    // Each use is judged on its own; nothing panics.
    assert!(!typed.is_ok());
}

#[test]
fn test_ids_from_another_store_read_as_error() {
    let (hir, _, make) = uses_of_make();
    let mut other = Types::new();
    let mut big = TypeId::UNIT;
    for _ in 0..10_000 {
        big = other.slice(big);
    }
    let mut checker = Checker::new(&hir, Profile::static_explicit());
    let f = checker.types_mut().func(&[], big, Effects::NONE);
    checker.declare_extern(make, f);
    let typed = checker.check().unwrap();
    // The foreign id is `{error}` here: no use of `v` is reported, and the
    // store did not grow to the other store's size.
    assert!(typed.is_ok(), "{:?}", typed.diagnostics());
    assert!(typed.stats().type_nodes < 1_000);
}

#[test]
fn test_declarations_replace_earlier_ones() {
    let (hir, _, make) = uses_of_make();
    let mut checker = Checker::new(&hir, Profile::static_explicit());
    let first = checker
        .types_mut()
        .func(&[], TypeId::prim(Prim::Bool), Effects::NONE);
    let second = checker
        .types_mut()
        .func(&[], TypeId::prim(Prim::I32), Effects::NONE);
    checker
        .declare_extern(make, first)
        .declare_extern(make, second);
    let typed = checker.check().unwrap();
    // `v: i32`: the method, field, and index uses are wrong, the `let` and
    // `match` fine.
    let codes: Vec<&str> = typed.diagnostics().iter().map(|d| d.kind.code()).collect();
    assert_eq!(codes, ["T0013", "T0012", "T0016"]);
}
