//! More static-explicit forms: structural records, classes and
//! inheritance, aliases, collections, patterns, effects, and intrinsics.

mod common;

use common::{Kit, messages, static_check};
use hir_lang::{
    Arm, Effects, Expr, FieldPat, Intrinsic, ItemKind, MemOrder, NodeRef, OpKind, ParamKind, Pat,
    Prim, SliceRest, Ty,
};
use typeck_lang::{Coercion, DiagnosticKind, Profile, RecordTyping, Type, TypeId, check};

const I64: TypeId = TypeId::prim(Prim::I64);
const I32: TypeId = TypeId::prim(Prim::I32);
const BOOL: TypeId = TypeId::prim(Prim::Bool);

/// Two record declarations with the same fields, and a value of one used
/// where the other is expected.
fn twin_records() -> (hir_lang::Hir, intern_lang::Interner, hir_lang::ExprId) {
    let mut k = Kit::new();
    let (t1, t2) = (k.prim(Prim::I32), k.prim(Prim::I32));
    let a = k.record("A", &[("x", t1)]);
    let b = k.record("B", &[("x", t2)]);
    let at = k.item_ty("A", a);
    let (p, v) = k.param("v", Some(at), ParamKind::Normal, None);
    let use_v = k.use_(v);
    let bt = k.item_ty("B", b);
    let (s, _) = k.let_("w", Some(bt), Some(use_v));
    let body = k.block(&[s], None);
    let f = k.func("f", &[p], None, body);
    let (hir, names) = k.finish_items(&[a, b, f]);
    (hir, names, use_v)
}

#[test]
fn test_nominal_versus_structural_records() {
    let (hir, names, _) = twin_records();
    let nominal = static_check(&hir);
    assert_eq!(
        messages(&nominal, &names),
        ["T0001 mismatched types: expected `B`, found `A`"]
    );
    let structural = check(
        &hir,
        &Profile::static_explicit().with_records(RecordTyping::Structural),
    )
    .unwrap();
    assert!(structural.is_ok(), "{:?}", structural.diagnostics());
}

#[test]
fn test_structural_width_subtyping() {
    let mut k = Kit::new();
    let (t1, t2, t3) = (k.prim(Prim::I32), k.prim(Prim::I32), k.prim(Prim::Bool));
    let small = k.record("Small", &[("x", t1)]);
    let big = k.record("Big", &[("x", t2), ("flag", t3)]);
    let bt = k.item_ty("Big", big);
    let (p, v) = k.param("v", Some(bt), ParamKind::Normal, None);
    let use_v = k.use_(v);
    let st = k.item_ty("Small", small);
    let (s, _) = k.let_("w", Some(st), Some(use_v));
    let body = k.block(&[s], None);
    let f = k.func("f", &[p], None, body);
    let (hir, _) = k.finish_items(&[small, big, f]);
    let profile = Profile::static_explicit()
        .with_records(RecordTyping::Structural)
        .with_subtyping(true);
    let typed = check(&hir, &profile).unwrap();
    assert!(typed.is_ok(), "{:?}", typed.diagnostics());
    assert!(matches!(
        typed.coercion(use_v),
        Some((Coercion::RecordWidth, _))
    ));
    // Without subtyping, the extra field is a mismatch.
    let strict = check(&hir, &profile.with_subtyping(false)).unwrap();
    assert_eq!(strict.diagnostics().len(), 1);
}

/// `class Base { fn hello(self) -> i32 }`, `class Derived : Base`.
fn class_pair(k: &mut Kit) -> (hir_lang::ItemId, hir_lang::ItemId, hir_lang::ItemId) {
    let (recv, _) = k.receiver(None);
    let one = k.int(1);
    let body = k.block(&[], Some(one));
    let ret = k.prim(Prim::I32);
    let hello = k.func("hello", &[recv], Some(ret), body);
    let items = k.b.list(&[hello]);
    let n = k.name("Base");
    let base = k.b.item(hir_lang::Item::new(
        Some(n),
        ItemKind::Class(hir_lang::ClassDef {
            items,
            ..hir_lang::ClassDef::default()
        }),
    ));
    let base_ty = k.item_ty("Base", base);
    let bases = k.b.list(&[base_ty]);
    let n = k.name("Derived");
    let derived = k.b.item(hir_lang::Item::new(
        Some(n),
        ItemKind::Class(hir_lang::ClassDef {
            bases,
            ..hir_lang::ClassDef::default()
        }),
    ));
    (base, derived, hello)
}

#[test]
fn test_inherited_methods_and_subclass_subtyping() {
    let mut k = Kit::new();
    let (base, derived, hello) = class_pair(&mut k);
    let dt = k.item_ty("Derived", derived);
    let (p, d) = k.param("d", Some(dt), ParamKind::Normal, None);
    let use_d = k.use_(d);
    let call = k.method_call(use_d, "hello", &[]);
    let s1 = k.stmt(call);
    let use_d2 = k.use_(d);
    let bt = k.item_ty("Base", base);
    let (s2, _) = k.let_("b", Some(bt), Some(use_d2));
    let body = k.block(&[s1, s2], None);
    let f = k.func("f", &[p], None, body);
    let (hir, names) = k.finish_items(&[base, derived, f]);
    let strict = static_check(&hir);
    // Calling an inherited method is fine; using a Derived as a Base needs
    // subtyping.
    assert_eq!(
        messages(&strict, &names),
        ["T0001 mismatched types: expected `Base`, found `Derived`"]
    );
    assert_eq!(strict.method(call), Some(hello));
    assert_eq!(strict.expr(call), Some(I32));
    let sub = check(&hir, &Profile::static_explicit().with_subtyping(true)).unwrap();
    assert!(sub.is_ok(), "{:?}", sub.diagnostics());
    assert_eq!(sub.coercion(use_d2).map(|c| c.0), Some(Coercion::Subclass));
}

#[test]
fn test_inheritance_cycles_are_cut_and_reported() {
    let mut k = Kit::new();
    // class A : B {}  class B : A {}
    let a_placeholder = k.name("A");
    let n_b = k.name("B");
    let _ = (a_placeholder, n_b);
    let a = k.b.item(hir_lang::Item::new(None, ItemKind::Err));
    let _ = a;
    // Build B first referencing A's id, which is allocated next.
    let next_a = hir_lang::ItemId::from_index(2).unwrap();
    let a_ty = k.item_ty("A", next_a);
    let bases_b = k.b.list(&[a_ty]);
    let nb = k.name("B");
    let b = k.b.item(hir_lang::Item::new(
        Some(nb),
        ItemKind::Class(hir_lang::ClassDef {
            bases: bases_b,
            ..hir_lang::ClassDef::default()
        }),
    ));
    let b_ty = k.item_ty("B", b);
    let bases_a = k.b.list(&[b_ty]);
    let na = k.name("A");
    let a2 = k.b.item(hir_lang::Item::new(
        Some(na),
        ItemKind::Class(hir_lang::ClassDef {
            bases: bases_a,
            ..hir_lang::ClassDef::default()
        }),
    ));
    assert_eq!(a2, next_a);
    let root = k.b.module(None, &[b, a2]);
    let (hir, _) = k.b.finish_lenient(root).unwrap();
    let typed = static_check(&hir);
    let cycles = typed
        .diagnostics()
        .iter()
        .filter(|d| d.kind == DiagnosticKind::InheritanceCycle)
        .count();
    assert_eq!(cycles, 1);
}

#[test]
fn test_aliases_expand_and_cycles_are_reported() {
    let mut k = Kit::new();
    // type Num = i32; let x: Num = 1;
    let i32_ = k.prim(Prim::I32);
    let n = k.name("Num");
    let alias = k.b.item(hir_lang::Item::new(
        Some(n),
        ItemKind::Alias {
            generics: hir_lang::Generics::default(),
            ty: i32_,
        },
    ));
    let num = k.item_ty("Num", alias);
    let one = k.int(1);
    let (s, x) = k.let_("x", Some(num), Some(one));
    let body = k.block(&[s], None);
    // type Loop = (Loop,);
    let self_id = hir_lang::ItemId::from_index(1).unwrap();
    let inner = k.item_ty("Loop", self_id);
    let tup_list = k.b.list(&[inner]);
    let tup = k.ty(Ty::Tuple(tup_list));
    let ln = k.name("Loop");
    let lp = k.b.item(hir_lang::Item::new(
        Some(ln),
        ItemKind::Alias {
            generics: hir_lang::Generics::default(),
            ty: tup,
        },
    ));
    assert_eq!(lp, self_id);
    let main = k.func("main", &[], None, body);
    let (hir, names) = k.finish_items(&[alias, lp, main]);
    let typed = static_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0029 type alias expands to itself"]
    );
    assert_eq!(typed.binder(x), Some(I32));
}

#[test]
fn test_arrays_slices_indexing_and_unsizing() {
    let mut k = Kit::new();
    // let a = [1, 2, 3]; let s: &[i64] = &a; a[0]; a[true]
    let (x, y, z) = (k.int(1), k.int(2), k.int(3));
    let list = k.b.list(&[x, y, z]);
    let arr = k.expr(Expr::Array(list));
    let (s1, a) = k.let_("a", None, Some(arr));
    let use_a = k.use_(a);
    let borrow = k.expr(Expr::Borrow {
        kind: hir_lang::BorrowKind::Shared,
        expr: use_a,
    });
    let i64_ = k.prim(Prim::I64);
    let slice = k.ty(Ty::Slice(i64_));
    let sref = k.ty(Ty::Ref {
        mutable: false,
        region: None,
        inner: slice,
    });
    let (s2, _) = k.let_("s", Some(sref), Some(borrow));
    let use_a2 = k.use_(a);
    let zero = k.int(0);
    let idx = k.expr(Expr::Index {
        base: use_a2,
        index: zero,
    });
    let s3 = k.stmt(idx);
    let use_a3 = k.use_(a);
    let t = k.bool(true);
    let bad = k.expr(Expr::Index {
        base: use_a3,
        index: t,
    });
    let s4 = k.stmt(bad);
    let body = k.block(&[s1, s2, s3, s4], None);
    let (hir, names) = k.finish_main(&[], body);
    let typed = static_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0001 mismatched types: expected `usize`, found `bool`"]
    );
    assert_eq!(
        typed.types().get(typed.binder(a).unwrap()),
        Type::Array { elem: I64, len: 3 }
    );
    assert_eq!(typed.expr(idx), Some(I64));
    assert_eq!(typed.coercion(borrow).map(|c| c.0), Some(Coercion::Unsize));
}

#[test]
fn test_maps_and_named_rests() {
    let mut k = Kit::new();
    let s = k.str("k");
    let v = k.int(1);
    let entries = k.b.list(&[hir_lang::MapEntry {
        key: Some(s),
        value: v,
    }]);
    let m = k.expr(Expr::Map(entries));
    let (s1, mb) = k.let_("m", None, Some(m));
    let use_m = k.use_(mb);
    let key = k.str("k");
    let get = k.expr(Expr::Index {
        base: use_m,
        index: key,
    });
    let s2 = k.stmt(get);
    let body = k.block(&[s1, s2], None);
    let (hir, _) = k.finish_main(&[], body);
    let typed = static_check(&hir);
    assert!(typed.is_ok(), "{:?}", typed.diagnostics());
    assert_eq!(
        typed.types().get(typed.binder(mb).unwrap()),
        Type::Map {
            key: TypeId::prim(Prim::Str),
            value: I64
        }
    );
    assert_eq!(typed.expr(get), Some(I64));
}

#[test]
fn test_tuple_record_and_slice_patterns() {
    let mut k = Kit::new();
    // let (a, b) = (1, true);
    let (one, t) = (k.int(1), k.bool(true));
    let tl = k.b.list(&[one, t]);
    let tup = k.expr(Expr::Tuple(tl));
    let (a, pa) = k.local("a");
    let (b, pb) = k.local("b");
    let elems = k.b.list(&[pa, pb]);
    let tpat = k.b.pat(Pat::Tuple { elems, rest: None });
    let s1 = k.let_pat(tpat, None, Some(tup));
    // let [first, ..rest] = [1, 2, 3];
    let (x, y, z) = (k.int(1), k.int(2), k.int(3));
    let al = k.b.list(&[x, y, z]);
    let arr = k.expr(Expr::Array(al));
    let (first, pf) = k.local("first");
    let (rest, pr) = k.local("rest");
    let prefix = k.b.list(&[pf]);
    let spat = k.b.pat(Pat::Slice {
        prefix,
        rest: Some(SliceRest {
            bind: Some(pr),
            suffix: hir_lang::List::EMPTY,
        }),
    });
    let s2 = k.let_pat(spat, None, Some(arr));
    // let (c, d, e) = (1, 2);  -> arity
    let (u, w) = (k.int(1), k.int(2));
    let tl2 = k.b.list(&[u, w]);
    let tup2 = k.expr(Expr::Tuple(tl2));
    let (_, pc) = k.local("c");
    let (_, pd) = k.local("d");
    let (_, pe) = k.local("e");
    let elems2 = k.b.list(&[pc, pd, pe]);
    let bad = k.b.pat(Pat::Tuple {
        elems: elems2,
        rest: None,
    });
    let s3 = k.let_pat(bad, None, Some(tup2));
    let body = k.block(&[s1, s2, s3], None);
    let (hir, names) = k.finish_main(&[], body);
    let typed = static_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0007 expected 2 arguments, found 3"]
    );
    assert_eq!(typed.binder(a), Some(I64));
    assert_eq!(typed.binder(b), Some(BOOL));
    assert_eq!(typed.binder(first), Some(I64));
    assert_eq!(
        typed.types().get(typed.binder(rest).unwrap()),
        Type::Array { elem: I64, len: 2 }
    );
}

#[test]
fn test_record_patterns_and_or_patterns() {
    let mut k = Kit::new();
    let (t1, t2) = (k.prim(Prim::I32), k.prim(Prim::Bool));
    let rec = k.record("R", &[("n", t1), ("ok", t2)]);
    let rt = k.item_ty("R", rec);
    let (p, r) = k.param("r", Some(rt), ParamKind::Normal, None);
    // let R { n, .. } = r;
    let use_r = k.use_(r);
    let (n, pn) = k.local("n");
    let nid = k.ident("n");
    let fields = k.b.list(&[FieldPat { name: nid, pat: pn }]);
    let pn_ = k.name("R");
    let def = k.b.def(hir_lang::Def::Item(rec));
    let path =
        k.b.resolved_path(pn_, hir_lang::Ns::Type, hir_lang::Res::Def(def));
    let rpat = k.b.pat(Pat::Record {
        path: Some(path),
        fields,
        rest: true,
    });
    let s1 = k.let_pat(rpat, None, Some(use_r));
    // match 1 { x | x => x }  with the same binder in both alternatives
    let scrut = k.int(1);
    let xn = k.name("x");
    let xb = k.b.new_binder(xn, hir_lang::BinderKind::Local);
    let alt1 = k.b.bind(xb);
    let alt2 = k.b.bind(xb);
    let alts = k.b.list(&[alt1, alt2]);
    let orp = k.b.pat(Pat::Or(alts));
    let use_x = k.use_(xb);
    let arms = k.b.list(&[Arm {
        pat: orp,
        guard: None,
        body: use_x,
    }]);
    let m = k.expr(Expr::Match {
        scrutinee: scrut,
        arms,
    });
    let s2 = k.stmt(m);
    let body = k.block(&[s1, s2], None);
    let f = k.func("f", &[p], None, body);
    let (hir, _) = k.finish_items(&[rec, f]);
    let typed = static_check(&hir);
    assert!(typed.is_ok(), "{:?}", typed.diagnostics());
    assert_eq!(typed.binder(n), Some(I32));
    assert_eq!(typed.binder(xb), Some(I64));
}

#[test]
fn test_labelled_blocks_and_break_values() {
    let mut k = Kit::new();
    // let v = 'l: { if true { break 'l 1 }; 2 };
    let ln = k.name("l");
    let label = k.b.new_binder(ln, hir_lang::BinderKind::Label);
    let one = k.int(1);
    let brk = k.expr(Expr::Break {
        label: Some(label),
        value: Some(one),
    });
    let then = k.block(&[], Some(brk));
    let c = k.bool(true);
    let iff = k.expr(Expr::If {
        cond: c,
        then,
        else_: None,
    });
    let s = k.stmt(iff);
    let two = k.int(2);
    let stmts = k.b.list(&[s]);
    let blk = k.expr(Expr::Block(hir_lang::Block {
        stmts,
        tail: Some(two),
        label: Some(label),
        is_unsafe: false,
    }));
    let (s1, v) = k.let_("v", None, Some(blk));
    let body = k.block(&[s1], None);
    let (hir, _) = k.finish_main(&[], body);
    let typed = static_check(&hir);
    assert!(typed.is_ok(), "{:?}", typed.diagnostics());
    assert_eq!(typed.binder(v), Some(I64));
}

#[test]
fn test_try_catch_with_type_tests() {
    let mut k = Kit::new();
    // try { 1 } catch (e: str) { 2 }
    let one = k.int(1);
    let str_ = k.prim(Prim::Str);
    let (eb, ep) = k.local("e");
    let tt = k.b.pat(Pat::TypeTest {
        ty: str_,
        pat: Some(ep),
    });
    let two = k.int(2);
    let catches = k.b.list(&[Arm {
        pat: tt,
        guard: None,
        body: two,
    }]);
    let t = k.expr(Expr::Try {
        body: one,
        catches,
        finally: None,
    });
    let (s1, r) = k.let_("r", None, Some(t));
    // match 1 { (x: str) => () }  -> impossible type test
    let scrut = k.int(1);
    let str2 = k.prim(Prim::Str);
    let tt2 = k.b.pat(Pat::TypeTest {
        ty: str2,
        pat: None,
    });
    let unit = k.expr(Expr::Tuple(hir_lang::List::EMPTY));
    let wild = k.b.pat(Pat::Wild);
    let unit2 = k.expr(Expr::Tuple(hir_lang::List::EMPTY));
    let arms = k.b.list(&[
        Arm {
            pat: tt2,
            guard: None,
            body: unit,
        },
        Arm {
            pat: wild,
            guard: None,
            body: unit2,
        },
    ]);
    let m = k.expr(Expr::Match {
        scrutinee: scrut,
        arms,
    });
    let s2 = k.stmt(m);
    let body = k.block(&[s1, s2], None);
    let (hir, names) = k.finish_main(&[], body);
    let typed = static_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0032 a value of type `i64` can never be a `str`"]
    );
    assert_eq!(typed.binder(eb), Some(TypeId::prim(Prim::Str)));
    assert_eq!(typed.binder(r), Some(I64));
}

#[test]
fn test_generators_yield_their_declared_type() {
    let mut k = Kit::new();
    let i32_ = k.prim(Prim::I32);
    let one = k.int(1);
    let y = k.expr(Expr::Yield {
        key: None,
        value: Some(one),
    });
    let s = k.stmt(y);
    let t = k.bool(true);
    let bad = k.expr(Expr::Yield {
        key: None,
        value: Some(t),
    });
    let s2 = k.stmt(bad);
    let body = k.block(&[s, s2], None);
    let gen_fn = k.func_fx("count", &[], Some(i32_), Effects::YIELD, body);
    let call = k.call_item("count", gen_fn, &[]);
    let s3 = k.stmt(call);
    let main_body = k.block(&[s3], None);
    let (hir, names) = k.finish_main(&[gen_fn], main_body);
    let typed = static_check(&hir);
    assert_eq!(
        messages(&typed, &names),
        ["T0001 mismatched types: expected `i32`, found `bool`"]
    );
    assert_eq!(typed.expr(one), Some(I32));
    assert_eq!(
        typed.types().get(typed.expr(call).unwrap()),
        Type::Generator {
            item: I32,
            is_async: false
        }
    );
}

#[test]
fn test_atomics_and_named_intrinsics() {
    let mut k = Kit::new();
    let i64_ = k.prim(Prim::I64);
    let ptr = k.ty(Ty::Ptr {
        mutable: true,
        inner: i64_,
    });
    let (p, pb) = k.param("p", Some(ptr), ParamKind::Normal, None);
    let use_p = k.use_(pb);
    let args = k.b.list(&[use_p]);
    let load = k.expr(Expr::Intrinsic {
        kind: Intrinsic::AtomicLoad(MemOrder::Acquire),
        generic_args: hir_lang::List::EMPTY,
        args,
    });
    let s1 = k.stmt(load);
    let rdtsc = k.sym("rdtsc");
    let nargs = k.b.list(&[]);
    let named = k.expr(Expr::Intrinsic {
        kind: Intrinsic::Named(rdtsc),
        generic_args: hir_lang::List::EMPTY,
        args: nargs,
    });
    let s2 = k.stmt(named);
    let body = k.block(&[s1, s2], None);
    let f = k.func("f", &[p], None, body);
    let (hir, names) = k.finish_items(&[f]);
    let typed = static_check(&hir);
    assert_eq!(typed.expr(load), Some(I64));
    assert_eq!(
        messages(&typed, &names),
        ["T0004 the type of `rdtsc` is not declared to the checker"]
    );
    let mut checker = typeck_lang::Checker::new(&hir, Profile::static_explicit());
    let ty = checker
        .types_mut()
        .func(&[], TypeId::prim(Prim::U64), Effects::NONE);
    checker.declare_intrinsic(rdtsc, ty);
    let typed = checker.check().unwrap();
    assert!(typed.is_ok());
    assert_eq!(typed.expr(named), Some(TypeId::prim(Prim::U64)));
}

#[test]
fn test_dyn_bound_that_is_not_an_interface() {
    let mut k = Kit::new();
    let any = k.ty(Ty::Any);
    let bounds = k.b.list(&[hir_lang::Bound::Ty(any)]);
    let obj = k.ty(Ty::Object(bounds));
    let (p, _) = k.param("x", Some(obj), ParamKind::Normal, None);
    let body = k.block(&[], None);
    let f = k.func("f", &[p], None, body);
    let (hir, _) = k.finish_items(&[f]);
    let typed = static_check(&hir);
    assert_eq!(typed.diagnostics().len(), 1);
    assert_eq!(typed.diagnostics()[0].kind, DiagnosticKind::NotAnInterface);
}

#[test]
fn test_compound_assignment_and_assignability() {
    let mut k = Kit::new();
    let one = k.int(1);
    let (s1, x) = k.let_("x", None, Some(one));
    let target = k.use_(x);
    let two = k.int(2);
    let add = k.expr(Expr::Assign {
        target,
        op: Some(hir_lang::Op::new(OpKind::Add)),
        value: two,
    });
    let s2 = k.stmt(add);
    let body = k.block(&[], None);
    let g = k.func("g", &[], None, body);
    let target2 = k.item_expr("g", g);
    let three = k.int(3);
    let bad = k.expr(Expr::Assign {
        target: target2,
        op: None,
        value: three,
    });
    let s3 = k.stmt(bad);
    let main_body = k.block(&[s1, s2, s3], None);
    let (hir, names) = k.finish_main(&[g], main_body);
    let typed = static_check(&hir);
    let got = messages(&typed, &names);
    assert!(
        got.contains(&"T0038 cannot assign to this".to_string()),
        "{got:?}"
    );
    assert_eq!(typed.binder(x), Some(I64));
    assert_eq!(typed.diagnostics()[0].node, NodeRef::Expr(target2));
}
