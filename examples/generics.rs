//! The `static-inferred` path: a generic container, an interface with a
//! generic implementation, a bounded generic function, and a closure whose
//! parameter is inferred; then the types, the method each call dispatches
//! to, and the monomorphization plan.
//!
//! ```text
//! cargo run --example generics
//! ```

use hir_lang::{
    BinderId, BinderKind, Bound, Builder, CaptureMode, Closure, Def, Expr, ExprId, FieldDef,
    FieldInit, FnDef, GenericArg, GenericParam, Generics, HirError, Ident, ImplDef, InterfaceDef,
    Item, ItemId, ItemKind, Member, Name, Ns, OpKind, Param, ParamId, ParamKind, Path, Prim,
    RecordDef, Res, Segment, Span, Ty, TyId,
};
use intern_lang::Interner;
use typeck_lang::{Profile, check};

struct Kit {
    b: Builder,
    names: Interner,
}

impl Kit {
    fn name(&mut self, s: &str) -> Name {
        Name::new(self.names.intern(s))
    }

    fn type_param(&mut self, s: &str) -> BinderId {
        let n = self.name(s);
        self.b.new_binder(n, BinderKind::TypeParam)
    }

    fn ident(&mut self, s: &str) -> Ident {
        Ident::new(self.names.intern(s), Span::empty(0))
    }

    /// A type path to a type parameter.
    fn tp(&mut self, s: &str, binder: BinderId) -> TyId {
        let n = self.name(s);
        let p = self.b.resolved_path(n, Ns::Type, Res::Local(binder));
        self.b.ty(Ty::Path(p))
    }

    /// A type path to an item, with generic arguments.
    fn item_ty(&mut self, s: &str, item: ItemId, args: &[TyId]) -> TyId {
        let n = self.name(s);
        let origin = self.b.origin();
        let ga: Vec<GenericArg> = args.iter().map(|&t| GenericArg::Ty(t)).collect();
        let args = self.b.list(&ga);
        let segments = self.b.list(&[Segment {
            args,
            ..Segment::new(n, origin)
        }]);
        let def = self.b.def(Def::Item(item));
        let p = self.b.path(Path {
            res: Res::Def(def),
            ..Path::new(segments, Ns::Type)
        });
        self.b.ty(Ty::Path(p))
    }

    fn param(&mut self, s: &str, ty: Option<TyId>, kind: ParamKind) -> (ParamId, BinderId) {
        let n = self.name(s);
        let binder = self.b.new_binder(n, BinderKind::Param);
        let pat = self.b.bind(binder);
        let p = self.b.param(Param {
            pat,
            ty,
            default: None,
            kind,
            by_ref: false,
        });
        (p, binder)
    }

    fn func(
        &mut self,
        s: &str,
        generics: Generics,
        params: &[ParamId],
        ret: Option<TyId>,
        body: Option<ExprId>,
    ) -> ItemId {
        let n = self.name(s);
        let params = self.b.list(params);
        self.b.item(Item::new(
            Some(n),
            ItemKind::Fn(FnDef {
                generics,
                params,
                ret,
                body,
                ..FnDef::default()
            }),
        ))
    }

    fn generics(&mut self, binder: BinderId, bound: Option<TyId>) -> Generics {
        let bounds: Vec<Bound> = bound.into_iter().map(Bound::Ty).collect();
        let gp = GenericParam {
            bounds: self.b.list(&bounds),
            ..GenericParam::new(binder)
        };
        Generics {
            params: self.b.list(&[gp]),
            preds: hir_lang::List::EMPTY,
        }
    }

    fn val(&mut self, base: ExprId) -> ExprId {
        let v = self.names.intern("val");
        self.b.expr(Expr::Field {
            base,
            member: Member::Named(v),
            span: Span::empty(0),
        })
    }

    fn method_call(&mut self, receiver: ExprId, s: &str) -> ExprId {
        let method = self.ident(s);
        self.b.expr(Expr::MethodCall {
            receiver,
            method,
            generic_args: hir_lang::List::EMPTY,
            args: hir_lang::List::EMPTY,
        })
    }

    fn call(&mut self, s: &str, item: ItemId, args: &[ExprId]) -> ExprId {
        let n = self.name(s);
        let def = self.b.def(Def::Item(item));
        let p = self.b.resolved_path(n, Ns::Value, Res::Def(def));
        let callee = self.b.expr(Expr::Path(p));
        self.b.call(callee, args)
    }
}

fn main() -> Result<(), HirError> {
    let mut k = Kit {
        b: Builder::new(),
        names: Interner::new(),
    };

    // struct Box<T> { val: T }
    let t = k.type_param("T");
    let g = k.generics(t, None);
    let tt = k.tp("T", t);
    let val = k.ident("val");
    let field = k.b.field(FieldDef {
        ty: Some(tt),
        ..FieldDef::named(val)
    });
    let fields = k.b.list(&[field]);
    let box_name = k.name("Box");
    let box_item = k.b.item(Item::new(
        Some(box_name),
        ItemKind::Record(RecordDef {
            generics: g,
            fields,
            ..RecordDef::default()
        }),
    ));

    // trait Show { fn show(self) -> i64; }
    let self_ty = k.b.ty(Ty::SelfTy);
    let (recv, _) = k.param("self", Some(self_ty), ParamKind::Receiver);
    let i64_ty = k.b.ty(Ty::Prim(Prim::I64));
    let show_decl = k.func("show", Generics::default(), &[recv], Some(i64_ty), None);
    let items = k.b.list(&[show_decl]);
    let show_name = k.name("Show");
    let show = k.b.item(Item::new(
        Some(show_name),
        ItemKind::Interface(InterfaceDef {
            items,
            ..InterfaceDef::default()
        }),
    ));

    // impl Show for i64 { fn show(self) -> i64 { self } }
    let self_ty = k.b.ty(Ty::SelfTy);
    let (recv, me) = k.param("self", Some(self_ty), ParamKind::Receiver);
    let body = {
        let m = k.b.use_binder(me);
        k.b.block(&[], Some(m))
    };
    let i64_ty = k.b.ty(Ty::Prim(Prim::I64));
    let show_i64 = k.func(
        "show",
        Generics::default(),
        &[recv],
        Some(i64_ty),
        Some(body),
    );
    let show_ty = k.item_ty("Show", show, &[]);
    let i64_self = k.b.ty(Ty::Prim(Prim::I64));
    let members = k.b.list(&[show_i64]);
    let impl_i64 = k.b.item(Item::new(
        None,
        ItemKind::Impl(ImplDef {
            interface: Some(show_ty),
            items: members,
            ..ImplDef::new(i64_self)
        }),
    ));

    // impl<V: Show> Show for Box<V> { fn show(self) -> i64 { self.val.show() } }
    let v = k.type_param("V");
    let bound = k.item_ty("Show", show, &[]);
    let g = k.generics(v, Some(bound));
    let vt = k.tp("V", v);
    let box_v = k.item_ty("Box", box_item, &[vt]);
    let self_ty = k.b.ty(Ty::SelfTy);
    let (recv, me) = k.param("self", Some(self_ty), ParamKind::Receiver);
    let m = k.b.use_binder(me);
    let inner = k.val(m);
    let call = k.method_call(inner, "show");
    let body = k.b.block(&[], Some(call));
    let i64_ty = k.b.ty(Ty::Prim(Prim::I64));
    let show_box = k.func(
        "show",
        Generics::default(),
        &[recv],
        Some(i64_ty),
        Some(body),
    );
    let show_ty = k.item_ty("Show", show, &[]);
    let members = k.b.list(&[show_box]);
    let impl_box = k.b.item(Item::new(
        None,
        ItemKind::Impl(ImplDef {
            generics: g,
            interface: Some(show_ty),
            items: members,
            ..ImplDef::new(box_v)
        }),
    ));

    // fn apply<U: Show>(f: fn(U) -> U, x: U) -> i64 { f(x).show() }
    let u = k.type_param("U");
    let bound = k.item_ty("Show", show, &[]);
    let g = k.generics(u, Some(bound));
    let (ua, ub, uc) = (k.tp("U", u), k.tp("U", u), k.tp("U", u));
    let fn_params = k.b.list(&[ua]);
    let fn_ty = k.b.ty(Ty::Fn {
        params: fn_params,
        ret: ub,
        effects: hir_lang::Effects::NONE,
        throws: None,
        abi: None,
    });
    let (pf, f) = k.param("f", Some(fn_ty), ParamKind::Normal);
    let (px, x) = k.param("x", Some(uc), ParamKind::Normal);
    let (uf, ux) = (k.b.use_binder(f), k.b.use_binder(x));
    let applied = k.b.call(uf, &[ux]);
    let shown = k.method_call(applied, "show");
    let body = k.b.block(&[], Some(shown));
    let i64_ty = k.b.ty(Ty::Prim(Prim::I64));
    let apply = k.func("apply", g, &[pf, px], Some(i64_ty), Some(body));

    // fn main() -> i64 {
    //     apply(|b| b, Box { val: Box { val: 7 } })
    // }
    let seven = k.b.int(7);
    let lit = |k: &mut Kit, value: ExprId| {
        let n = k.name("Box");
        let def = k.b.def(Def::Item(box_item));
        let path = k.b.resolved_path(n, Ns::Type, Res::Def(def));
        let name = k.ident("val");
        let fields = k.b.list(&[FieldInit { name, value }]);
        k.b.expr(Expr::Record {
            path: Some(path),
            fields,
            base: None,
        })
    };
    let inner = lit(&mut k, seven);
    let outer = lit(&mut k, inner);
    let (pb, bv) = k.param("b", None, ParamKind::Normal);
    let ub = k.b.use_binder(bv);
    let params = k.b.list(&[pb]);
    let closure = k.b.expr(Expr::Closure(Closure {
        params,
        implicit: Some(CaptureMode::ByRef),
        ..Closure::new(ub)
    }));
    let main_call = k.call("apply", apply, &[closure, outer]);
    let one = k.b.int(1);
    let sum = k.b.op(OpKind::Add, &[main_call, one]);
    let body = k.b.block(&[], Some(sum));
    let i64_ty = k.b.ty(Ty::Prim(Prim::I64));
    let main_fn = k.func("main", Generics::default(), &[], Some(i64_ty), Some(body));

    let root =
        k.b.module(None, &[box_item, show, impl_i64, impl_box, apply, main_fn]);
    let hir = k.b.finish(root)?;
    let names = k.names;

    let typed = check(&hir, &Profile::static_inferred()).expect("the check runs");
    for d in typed.diagnostics() {
        println!("{} {}", d.kind.code(), typed.message(d, &names));
    }
    println!("diagnostics: {}", typed.diagnostics().len());
    let shown = |t| typed.display(t, &names).to_string();
    println!(
        "closure parameter `b`: {}",
        shown(typed.binder(bv).expect("typed"))
    );
    println!(
        "`apply(..)`: {}",
        shown(typed.expr(main_call).expect("typed"))
    );
    for instance in typed.mono_plan().instances() {
        let args: Vec<String> = instance.args.iter().map(|&a| shown(a)).collect();
        println!(
            "instance of item {:?}: [{}] ({:?})",
            instance.item,
            args.join(", "),
            instance.strategy
        );
    }
    Ok(())
}
