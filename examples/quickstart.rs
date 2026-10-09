//! The Tier-1 path: build (or receive) a HIR unit, call `check` with a
//! profile, read the types and the diagnostics.
//!
//! ```text
//! cargo run --example quickstart
//! ```

use hir_lang::{
    BinderKind, Builder, FnDef, HirError, Item, ItemKind, Name, OpKind, Param, ParamKind, Prim, Ty,
};
use intern_lang::Interner;
use typeck_lang::{Profile, check};

fn main() -> Result<(), HirError> {
    let mut names = Interner::new();
    let mut b = Builder::new();

    // fn area(w: f64, h: f64) -> f64 { w * h }
    let param = |b: &mut Builder, names: &mut Interner, name: &str| {
        let binder = b.new_binder(Name::new(names.intern(name)), BinderKind::Param);
        let pat = b.bind(binder);
        let ty = b.ty(Ty::Prim(Prim::F64));
        let p = b.param(Param {
            pat,
            ty: Some(ty),
            default: None,
            kind: ParamKind::Normal,
            by_ref: false,
        });
        (p, binder)
    };
    let (pw, w) = param(&mut b, &mut names, "w");
    let (ph, h) = param(&mut b, &mut names, "h");
    let (uw, uh) = (b.use_binder(w), b.use_binder(h));
    let product = b.op(OpKind::Mul, &[uw, uh]);
    let body = b.block(&[], Some(product));
    let params = b.list(&[pw, ph]);
    let ret = b.ty(Ty::Prim(Prim::F64));
    let area = b.item(Item::new(
        Some(Name::new(names.intern("area"))),
        ItemKind::Fn(FnDef {
            params,
            ret: Some(ret),
            body: Some(body),
            ..FnDef::default()
        }),
    ));

    // fn main() { let ok = 2.0 * 3.0; let bad = 1 + true; }
    let (two, three) = (
        b.lit(hir_lang::Lit::Float(hir_lang::FloatLit::new(2.0))),
        b.lit(hir_lang::Lit::Float(hir_lang::FloatLit::new(3.0))),
    );
    let mul = b.op(OpKind::Mul, &[two, three]);
    let ok = b.new_binder(Name::new(names.intern("ok")), BinderKind::Local);
    let ok_pat = b.bind(ok);
    let s1 = b.let_stmt(ok_pat, Some(mul));
    let one = b.int(1);
    let yes = b.lit(hir_lang::Lit::Bool(true));
    let sum = b.op(OpKind::Add, &[one, yes]);
    let bad = b.new_binder(Name::new(names.intern("bad")), BinderKind::Local);
    let bad_pat = b.bind(bad);
    let s2 = b.let_stmt(bad_pat, Some(sum));
    let main_body = b.block(&[s1, s2], None);
    let main = b.func(Name::new(names.intern("main")), &[], main_body);

    let root = b.module(None, &[area, main]);
    let hir = b.finish(root)?;

    for profile in [Profile::static_explicit(), Profile::dynamic()] {
        let typed = check(&hir, &profile).expect("an implemented discipline");
        println!("== {} ==", profile.discipline.name());
        if let Some(t) = typed.expr(product) {
            println!("w * h : {}", typed.display(t, &names));
        }
        if let Some(t) = typed.binder(ok) {
            println!("ok    : {}", typed.display(t, &names));
        }
        for d in typed.diagnostics() {
            println!(
                "{} {} at {:?}",
                d.kind.code(),
                typed.message(d, &names),
                d.node
            );
        }
        if typed.is_ok() {
            println!("no diagnostics");
        }
    }
    Ok(())
}
