//! Exhaustiveness and usefulness through match-lang (ISSUES P17): missing
//! values are reported with witnesses, unreachable arms and redundant
//! or-alternatives as warnings, over sums (generic ones too), nested
//! tuples, booleans, integers with ranges, nullable types, and unions.

mod common;

use common::{Kit, inferred_check, messages, static_check};
use hir_lang::{Lit, NodeRef, ParamKind, Pat, Prim, Ty};
use typeck_lang::{DiagnosticKind, Profile, Severity, check};

/// `enum Opt<T> { None, Some(T) }`.
fn opt(k: &mut Kit) -> (hir_lang::ItemId, hir_lang::VariantId, hir_lang::VariantId) {
    let t = k.type_param("T");
    let gp = k.gparam(t, &[]);
    let g = k.generics(&[gp], &[]);
    let none = k.variant("None", &[]);
    let tt = k.tp("T", t);
    let some = k.variant("Some", &[tt]);
    (k.gsum("Opt", g, &[none, some]), none, some)
}

/// `fn f(x: <ty>) { <match x { arms }> }`, returning the match.
fn match_fn(
    k: &mut Kit,
    ty: hir_lang::TyId,
    arms: impl FnOnce(&mut Kit) -> Vec<(hir_lang::PatId, hir_lang::ExprId)>,
) -> (hir_lang::ItemId, hir_lang::ExprId) {
    let (p, x) = k.param("x", Some(ty), ParamKind::Normal, None);
    let ux = k.use_(x);
    let arms = arms(k);
    let m = k.match_(ux, &arms);
    let s = k.stmt(m);
    let body = k.block(&[s], None);
    (k.func("f", &[p], None, body), m)
}

fn unit(k: &mut Kit) -> hir_lang::ExprId {
    k.block(&[], None)
}

#[test]
fn test_nested_generic_sum_witness() {
    let mut k = Kit::new();
    let (o, none, some) = opt(&mut k);
    let b = k.prim(Prim::Bool);
    let ty = k.path_ty("Opt", o, &[b]);
    let (f, m) = match_fn(&mut k, ty, |k| {
        let t = k.lit_pat(Lit::Bool(true));
        let p1 = k.variant_pat("Some", some, &[t]);
        let p2 = k.unit_variant_pat("None", none);
        let (u1, u2) = (unit(k), unit(k));
        vec![(p1, u1), (p2, u2)]
    });
    let (hir, names) = k.finish_items(&[o, f]);
    let typed = static_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0027 non-exhaustive match: `Some(false)` not covered"]
    );
    assert_eq!(typed.witnesses(m, &names), ["Some(false)"]);
    assert_eq!(
        typed.diagnostics()[0].kind,
        DiagnosticKind::NonExhaustive {
            missing: Some(some)
        }
    );
}

#[test]
fn test_unreachable_arm_is_a_warning() {
    let mut k = Kit::new();
    let b = k.prim(Prim::Bool);
    let (f, _) = match_fn(&mut k, b, |k| {
        let w = k.wild();
        let t = k.lit_pat(Lit::Bool(true));
        let (u1, u2) = (unit(k), unit(k));
        vec![(w, u1), (t, u2)]
    });
    let (hir, names) = k.finish_items(&[f]);
    let typed = static_check(&hir);
    assert_eq!(messages(&typed, &names), ["T0040 unreachable match arm"]);
    assert_eq!(typed.diagnostics()[0].severity, Severity::Warning);
    assert!(matches!(typed.diagnostics()[0].node, NodeRef::Pat(_)));
    // Warnings do not make the result fail.
    assert!(typed.is_ok());
}

#[test]
fn test_redundant_or_alternative() {
    let mut k = Kit::new();
    let b = k.prim(Prim::Bool);
    let (f, _) = match_fn(&mut k, b, |k| {
        let t = k.lit_pat(Lit::Bool(true));
        let t2 = k.lit_pat(Lit::Bool(true));
        let fa = k.lit_pat(Lit::Bool(false));
        let alts = k.b.list(&[t, t2]);
        let or = k.b.pat(Pat::Or(alts));
        let (u1, u2) = (unit(k), unit(k));
        vec![(or, u1), (fa, u2)]
    });
    let (hir, names) = k.finish_items(&[f]);
    let typed = static_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0041 this alternative only matches values already matched"]
    );
}

#[test]
fn test_integer_ranges_cover_u8() {
    let mut k = Kit::new();
    let u8t = k.prim(Prim::U8);
    let range = |k: &mut Kit, lo: i64, hi: i64| {
        let a = k.lit_pat(Lit::Int(hir_lang::IntLit::new(lo as u64)));
        let b = k.lit_pat(Lit::Int(hir_lang::IntLit::new(hi as u64)));
        k.b.pat(Pat::Range {
            lo: Some(a),
            hi: Some(b),
            inclusive: true,
        })
    };
    let (f, _) = match_fn(&mut k, u8t, |k| {
        let a = range(k, 0, 127);
        let b = range(k, 128, 250);
        let (u1, u2) = (unit(k), unit(k));
        vec![(a, u1), (b, u2)]
    });
    let (hir, names) = k.finish_items(&[f]);
    let typed = static_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0027 non-exhaustive match: `251..=255` not covered"]
    );
}

#[test]
fn test_tuple_of_bools_and_nullable() {
    let mut k = Kit::new();
    let (b1, b2) = (k.prim(Prim::Bool), k.prim(Prim::Bool));
    let elems = k.b.list(&[b1, b2]);
    let tup = k.ty(Ty::Tuple(elems));
    let (f, m) = match_fn(&mut k, tup, |k| {
        let t = k.lit_pat(Lit::Bool(true));
        let w = k.wild();
        let e1 = k.b.list(&[t, w]);
        let p1 = k.b.pat(Pat::Tuple {
            elems: e1,
            rest: None,
        });
        let w2 = k.wild();
        let t2 = k.lit_pat(Lit::Bool(true));
        let e2 = k.b.list(&[w2, t2]);
        let p2 = k.b.pat(Pat::Tuple {
            elems: e2,
            rest: None,
        });
        let (u1, u2) = (unit(k), unit(k));
        vec![(p1, u1), (p2, u2)]
    });
    let i = k.prim(Prim::I32);
    let n = k.ty(Ty::Nullable(i));
    let (p, x) = k.param("y", Some(n), ParamKind::Normal, None);
    let ux = k.use_(x);
    let one = k.lit_pat(Lit::Int(hir_lang::IntLit::new(1)));
    let u = unit(&mut k);
    let m2 = k.match_(ux, &[(one, u)]);
    let s = k.stmt(m2);
    let body = k.block(&[s], None);
    let g = k.func("g", &[p], None, body);
    let (hir, names) = k.finish_items(&[f, g]);
    let typed = static_check(&hir);
    assert_eq!(typed.witnesses(m, &names), ["(false, false)"]);
    let ws = typed.witnesses(m2, &names);
    assert!(ws.contains(&"null".to_string()), "{ws:?}");
}

#[test]
fn test_union_matched_by_type_tests() {
    let mut k = Kit::new();
    let (i, s) = (k.prim(Prim::I64), k.prim(Prim::Str));
    let members = k.b.list(&[i, s]);
    let u = k.ty(Ty::Union(members));
    let (f, m) = match_fn(&mut k, u, |k| {
        let it = k.prim(Prim::I64);
        let p1 = k.b.pat(Pat::TypeTest { ty: it, pat: None });
        let u1 = unit(k);
        vec![(p1, u1)]
    });
    let (hir, names) = k.finish_items(&[f]);
    let typed = static_check(&hir);
    assert_eq!(typed.witnesses(m, &names), ["is str"]);
}

#[test]
fn test_exhaustive_matches_are_silent_and_toggle_off() {
    let mut k = Kit::new();
    let (o, none, some) = opt(&mut k);
    let i = k.prim(Prim::I64);
    let ty = k.path_ty("Opt", o, &[i]);
    let (f, _) = match_fn(&mut k, ty, |k| {
        let w = k.wild();
        let p1 = k.variant_pat("Some", some, &[w]);
        let p2 = k.unit_variant_pat("None", none);
        let (u1, u2) = (unit(k), unit(k));
        vec![(p1, u1), (p2, u2)]
    });
    let i2 = k.prim(Prim::I64);
    let ty2 = k.path_ty("Opt", o, &[i2]);
    let (p, x) = k.param("z", Some(ty2), ParamKind::Normal, None);
    let ux = k.use_(x);
    let w = k.wild();
    let p1 = k.variant_pat("Some", some, &[w]);
    let u = unit(&mut k);
    let m2 = k.match_(ux, &[(p1, u)]);
    let s = k.stmt(m2);
    let body = k.block(&[s], None);
    let g = k.func("g", &[p], None, body);
    let (hir, names) = k.finish_items(&[o, f, g]);
    let typed = inferred_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0027 non-exhaustive match: `None` not covered"]
    );
    let off = check(
        &hir,
        &Profile::static_inferred().with_exhaustive_match(false),
    )
    .unwrap();
    assert!(off.diagnostics().is_empty());
}
