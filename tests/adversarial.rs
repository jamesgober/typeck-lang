//! Termination, budgets, and complexity on hostile and very large inputs.
//!
//! Complexity claims are checked with the checker's own step counter
//! (deterministic), not wall-clock time: doubling the input must at most
//! double the work, give or take a constant.

mod common;

use common::{Kit, static_check};
use hir_lang::{Expr, ExprId, OpKind, Pat, Prim, Ty};
use typeck_lang::{Budget, CheckError, Checker, Limit, Profile, Type, TypeId, check};

/// `let x0 = 1; let x1 = (x0, x0); ...; let y0; let y1 = (y0, y0); ...;
/// y_n = x_n;` The type of `x_n` is a tree of `2^n` leaves but a DAG of `n`
/// nodes; assigning it to `y_n` unifies two such DAGs (ISSUES M39).
fn doubling_chain(n: usize) -> (hir_lang::Hir, ExprId) {
    let mut k = Kit::new();
    let mut stmts = Vec::with_capacity(2 * n + 4);
    let one = k.int(1);
    let (s, mut x) = k.let_("x", None, Some(one));
    stmts.push(s);
    for _ in 0..n {
        let (a, b) = (k.use_(x), k.use_(x));
        let list = k.b.list(&[a, b]);
        let pair = k.expr(Expr::Tuple(list));
        let (s, next) = k.let_("x", None, Some(pair));
        stmts.push(s);
        x = next;
    }
    let (s, mut y) = k.let_("y", None, None);
    stmts.push(s);
    for _ in 0..n {
        let (a, b) = (k.use_(y), k.use_(y));
        let list = k.b.list(&[a, b]);
        let pair = k.expr(Expr::Tuple(list));
        let (s, next) = k.let_("y", None, Some(pair));
        stmts.push(s);
        y = next;
    }
    let target = k.use_(y);
    let value = k.use_(x);
    let assign = k.expr(Expr::Assign {
        target,
        op: None,
        value,
    });
    stmts.push(k.stmt(assign));
    let body = k.block(&stmts, None);
    let (hir, _) = k.finish_main(&[], body);
    (hir, value)
}

#[test]
fn test_doubling_chain_checks_in_linear_steps() {
    let (small, _) = doubling_chain(2_000);
    let (large, value) = doubling_chain(4_000);
    let a = static_check(&small);
    let b = static_check(&large);
    assert!(a.is_ok(), "{:?}", a.diagnostics());
    assert!(b.is_ok(), "{:?}", b.diagnostics());
    let (sa, sb) = (a.stats().steps, b.stats().steps);
    assert!(sb <= 2 * sa + 1_000, "steps {sa} -> {sb}: not linear");
    // The type itself is a DAG: the store grows linearly too.
    let (ta, tb) = (a.stats().type_nodes, b.stats().type_nodes);
    assert!(tb <= 2 * ta + 1_000, "type nodes {ta} -> {tb}");
    // Rendering a 2^4000-leaf type is capped.
    let names = intern_lang::Interner::new();
    let shown = b.display(b.expr(value).unwrap(), &names).to_string();
    assert!(shown.chars().count() < 300, "{}", shown.len());
}

#[test]
fn test_doubling_chain_at_scale() {
    let (hir, _) = doubling_chain(50_000);
    let typed = static_check(&hir);
    assert!(typed.is_ok());
}

#[test]
fn test_deep_expression_nesting_is_iterative() {
    // 1 + (1 + (1 + ... )) 100,000 deep, as the tail of a typed function.
    let mut k = Kit::new();
    let mut e = k.int(1);
    for _ in 0..100_000 {
        let one = k.int(1);
        e = k.op(OpKind::Add, &[one, e]);
    }
    let body = k.block(&[], Some(e));
    let ret = k.prim(Prim::I32);
    let f = k.func("f", &[], Some(ret), body);
    let (hir, _) = k.finish_items(&[f]);
    let typed = static_check(&hir);
    assert!(
        typed.is_ok(),
        "{:?}",
        &typed.diagnostics()[..1.min(typed.diagnostics().len())]
    );
    assert_eq!(typed.expr(e), Some(TypeId::prim(Prim::I32)));
}

#[test]
fn test_deep_blocks_and_ifs() {
    let mut k = Kit::new();
    let mut e = k.int(7);
    for i in 0..50_000 {
        if i % 2 == 0 {
            e = k.block(&[], Some(e));
        } else {
            let c = k.bool(true);
            let other = k.int(0);
            e = k.expr(Expr::If {
                cond: c,
                then: e,
                else_: Some(other),
            });
        }
    }
    let (s, x) = k.let_("x", None, Some(e));
    let body = k.block(&[s], None);
    let (hir, _) = k.finish_main(&[], body);
    let typed = static_check(&hir);
    assert!(typed.is_ok());
    assert_eq!(typed.binder(x), Some(TypeId::prim(Prim::I64)));
}

#[test]
fn test_deep_type_annotations_and_patterns() {
    let mut k = Kit::new();
    // let p: (((i32,),),...) = (((1,),),...);  with a matching pattern
    let depth = 30_000;
    let mut ty = k.prim(Prim::I32);
    let mut val = k.int(1);
    let (x, mut pat) = k.local("x");
    for _ in 0..depth {
        let tl = k.b.list(&[ty]);
        ty = k.ty(Ty::Tuple(tl));
        let vl = k.b.list(&[val]);
        val = k.expr(Expr::Tuple(vl));
        let pl = k.b.list(&[pat]);
        pat = k.b.pat(Pat::Tuple {
            elems: pl,
            rest: None,
        });
    }
    let s = k.let_pat(pat, Some(ty), Some(val));
    let body = k.block(&[s], None);
    let (hir, _) = k.finish_main(&[], body);
    let typed = static_check(&hir);
    assert!(typed.is_ok(), "{:?}", typed.diagnostics().first());
    assert_eq!(typed.binder(x), Some(TypeId::prim(Prim::I32)));
}

#[test]
fn test_long_alias_chains_lower_iteratively() {
    let mut k = Kit::new();
    // type A0 = i32; type A1 = A0; ... ; let x: A_n = 1;
    let n = 20_000;
    let mut prev_ty = k.prim(Prim::I32);
    let mut items = Vec::with_capacity(n + 1);
    for i in 0..n {
        let name = k.name("A");
        let item = k.b.item(hir_lang::Item::new(
            Some(name),
            hir_lang::ItemKind::Alias {
                generics: hir_lang::Generics::default(),
                ty: prev_ty,
            },
        ));
        items.push(item);
        let _ = i;
        prev_ty = k.item_ty("A", item);
    }
    let one = k.int(1);
    let (s, x) = k.let_("x", Some(prev_ty), Some(one));
    let body = k.block(&[s], None);
    let main = k.func("main", &[], None, body);
    items.push(main);
    let (hir, _) = k.finish_items(&items);
    let typed = static_check(&hir);
    assert!(typed.is_ok());
    assert_eq!(typed.binder(x), Some(TypeId::prim(Prim::I32)));
}

/// `n` functions, each `fn f(a: i64, b: i64) -> i64 { let c = a * b; c + a }`
/// and a `main` calling each.
fn many_functions(n: usize) -> hir_lang::Hir {
    let mut k = Kit::new();
    let mut items = Vec::with_capacity(n + 1);
    let mut calls = Vec::with_capacity(n);
    for _ in 0..n {
        let (t1, t2, t3) = (k.prim(Prim::I64), k.prim(Prim::I64), k.prim(Prim::I64));
        let (pa, a) = k.param("a", Some(t1), hir_lang::ParamKind::Normal, None);
        let (pb, b) = k.param("b", Some(t2), hir_lang::ParamKind::Normal, None);
        let (ua, ub) = (k.use_(a), k.use_(b));
        let mul = k.op(OpKind::Mul, &[ua, ub]);
        let (s, c) = k.let_("c", None, Some(mul));
        let (uc, ua2) = (k.use_(c), k.use_(a));
        let add = k.op(OpKind::Add, &[uc, ua2]);
        let body = k.block(&[s], Some(add));
        let f = k.func("f", &[pa, pb], Some(t3), body);
        items.push(f);
        let (x, y) = (k.int(2), k.int(3));
        let call = k.call_item("f", f, &[x, y]);
        calls.push(k.stmt(call));
    }
    let body = k.block(&calls, None);
    let main = k.func("main", &[], None, body);
    items.push(main);
    k.finish_items(&items).0
}

#[test]
fn test_work_scales_linearly_with_program_size() {
    let a = static_check(&many_functions(2_000));
    let b = static_check(&many_functions(20_000));
    assert!(a.is_ok() && b.is_ok());
    let (sa, sb) = (a.stats().steps, b.stats().steps);
    assert!(sb <= 10 * sa + 10_000, "steps {sa} -> {sb}");
    let dynamic_a = check(&many_functions(2_000), &Profile::dynamic()).unwrap();
    let dynamic_b = check(&many_functions(20_000), &Profile::dynamic()).unwrap();
    assert!(dynamic_b.stats().steps <= 10 * dynamic_a.stats().steps + 10_000);
}

#[test]
fn test_budgets_turn_hostile_input_into_errors() {
    let (hir, _) = doubling_chain(1_000);
    let mut checker = Checker::new(&hir, Profile::static_explicit());
    let _ = checker.set_budget(Budget {
        steps: 5_000,
        ..Budget::default()
    });
    assert_eq!(
        checker.check(),
        Err(CheckError::BudgetExceeded {
            limit: Limit::Steps
        })
    );
    let mut checker = Checker::new(&hir, Profile::static_explicit());
    let _ = checker.set_budget(Budget {
        type_nodes: 100,
        ..Budget::default()
    });
    assert_eq!(
        checker.check(),
        Err(CheckError::BudgetExceeded {
            limit: Limit::TypeNodes
        })
    );
    // The default budget is generous for real programs.
    assert!(check(&hir, &Profile::static_explicit()).is_ok());
}

#[test]
fn test_many_inference_failures_report_linearly() {
    let mut k = Kit::new();
    let mut stmts = Vec::new();
    for _ in 0..20_000 {
        let (s, _) = k.let_("x", None, None);
        stmts.push(s);
    }
    let body = k.block(&stmts, None);
    let (hir, _) = k.finish_main(&[], body);
    let typed = static_check(&hir);
    assert_eq!(typed.diagnostics().len(), 20_000);
}

#[test]
fn test_deep_inheritance_chain() {
    let mut k = Kit::new();
    // class C0 { fn m(self) -> i32 } class C1 : C0 ... C_n; c_n.m()
    let (recv, _) = k.receiver(None);
    let one = k.int(1);
    let body = k.block(&[], Some(one));
    let ret = k.prim(Prim::I32);
    let m = k.func("m", &[recv], Some(ret), body);
    let items_list = k.b.list(&[m]);
    let n0 = k.name("C");
    let mut prev = k.b.item(hir_lang::Item::new(
        Some(n0),
        hir_lang::ItemKind::Class(hir_lang::ClassDef {
            items: items_list,
            ..hir_lang::ClassDef::default()
        }),
    ));
    let mut all = vec![prev];
    for _ in 0..5_000 {
        let bt = k.item_ty("C", prev);
        let bases = k.b.list(&[bt]);
        let n = k.name("C");
        prev = k.b.item(hir_lang::Item::new(
            Some(n),
            hir_lang::ItemKind::Class(hir_lang::ClassDef {
                bases,
                ..hir_lang::ClassDef::default()
            }),
        ));
        all.push(prev);
    }
    let lt = k.item_ty("C", prev);
    let (p, c) = k.param("c", Some(lt), hir_lang::ParamKind::Normal, None);
    let use_c = k.use_(c);
    let call = k.method_call(use_c, "m", &[]);
    let body = k.block(&[], Some(call));
    let ret = k.prim(Prim::I32);
    let f = k.func("f", &[p], Some(ret), body);
    all.push(f);
    let (hir, _) = k.finish_items(&all);
    let typed = static_check(&hir);
    assert!(typed.is_ok(), "{:?}", typed.diagnostics());
    assert_eq!(typed.method(call), Some(m));
}

#[test]
fn test_huge_array_lengths_and_spreads_do_not_loop() {
    let mut k = Kit::new();
    // fn f(a: i64) {}  f(...[0; 1 << 40])   (an array type of 2^40 elements)
    let t = k.prim(Prim::I64);
    let (pa, _) = k.param("a", Some(t), hir_lang::ParamKind::Normal, None);
    let body = k.block(&[], None);
    let f = k.func("f", &[pa], None, body);
    let zero = k.int(0);
    let one = k.int(1);
    let forty = k.int(40);
    let count = k.op(OpKind::Shl, &[one, forty]);
    let rep = k.expr(Expr::Repeat { elem: zero, count });
    let callee = k.item_expr("f", f);
    let call = k.call_args(
        callee,
        &[hir_lang::Arg {
            kind: hir_lang::ArgKind::Spread,
            value: rep,
            place: false,
        }],
    );
    let s = k.stmt(call);
    let main_body = k.block(&[s], None);
    let (hir, _) = k.finish_main(&[f], main_body);
    let typed = static_check(&hir);
    assert!(matches!(
        typed.types().get(typed.expr(rep).unwrap()),
        Type::Array { len, .. } if len == 1 << 40
    ));
    assert_eq!(typed.diagnostics().len(), 1, "too many arguments, once");
}
