//! The Tier-2 path: a `Checker` with host declarations. A language's
//! standard library lives outside the unit (`Res::Extern` names); the host
//! tells the checker what those names are, including methods of host types.
//!
//! ```text
//! cargo run --example host
//! ```

use hir_lang::{
    Arg, BinderKind, Builder, Effects, Expr, HirError, Ident, List, Name, Ns, Prim, Res, Span,
};
use intern_lang::Interner;
use typeck_lang::{Budget, Checker, Profile, TypeId};

fn main() -> Result<(), HirError> {
    let mut names = Interner::new();
    let (vec, new, push, len) = (
        names.intern("Vec"),
        names.intern("vec_new"),
        names.intern("push"),
        names.intern("len"),
    );
    let mut b = Builder::new();

    // fn main() { let v = vec_new(); v.push(1); v.len() > 0 }
    let path = b.resolved_path(Name::new(new), Ns::Value, Res::Extern(new));
    let callee = b.expr(Expr::Path(path));
    let make = b.call(callee, &[]);
    let v = b.new_binder(Name::new(names.intern("v")), BinderKind::Local);
    let v_pat = b.bind(v);
    let s1 = b.let_stmt(v_pat, Some(make));
    let call = |b: &mut Builder, method, args: &[hir_lang::ExprId]| {
        let receiver = b.use_binder(v);
        let args: Vec<Arg> = args.iter().map(|&a| Arg::positional(a)).collect();
        let args = b.list(&args);
        b.expr(Expr::MethodCall {
            receiver,
            method: Ident::new(method, Span::empty(0)),
            generic_args: List::EMPTY,
            args,
        })
    };
    let one = b.int(1);
    let pushed = call(&mut b, push, &[one]);
    let s2 = b.expr_stmt(pushed);
    let length = call(&mut b, len, &[]);
    let s3 = b.expr_stmt(length);
    let body = b.block(&[s1, s2, s3], None);
    let main = b.func(Name::new(names.intern("main")), &[], body);
    let root = b.module(None, &[main]);
    let hir = b.finish(root)?;

    let mut checker = Checker::new(&hir, Profile::static_explicit());
    checker.set_budget(Budget::for_hir(&hir));
    // The host's view of its library: a nominal `Vec` with two methods
    // (receiver first) and a constructor function.
    let types = checker.types_mut();
    let vec_ty = types.external(vec);
    let new_ty = types.func(&[], vec_ty, Effects::NONE);
    let push_ty = types.func(
        &[vec_ty, TypeId::prim(Prim::I64)],
        TypeId::UNIT,
        Effects::NONE,
    );
    let len_ty = types.func(&[vec_ty], TypeId::prim(Prim::Usize), Effects::NONE);
    checker
        .declare_extern(new, new_ty)
        .declare_member(vec_ty, push, push_ty)
        .declare_member(vec_ty, len, len_ty);

    let typed = checker.check().expect("static-explicit is implemented");
    println!(
        "v.len() : {}",
        typed.display(typed.expr(length).unwrap_or(TypeId::ERROR), &names)
    );
    println!(
        "1       : {}",
        typed.display(typed.expr(one).unwrap_or(TypeId::ERROR), &names)
    );
    println!("diagnostics: {}", typed.diagnostics().len());
    Ok(())
}
