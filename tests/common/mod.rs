//! Shared helpers: a builder plus an interner, with short constructors for
//! the HIR shapes the tests use.

#![allow(dead_code)]

use hir_lang::{
    Arg, ArgKind, Arm, BinderId, BinderKind, Bound, Builder, CaptureMode, ClassDef, Closure, Def,
    Effects, Expr, ExprId, FieldDef, FieldId, FnDef, GenericArg, GenericParam, Generics, Hir,
    Ident, ImplDef, InterfaceDef, Item, ItemId, ItemKind, Lit, Name, Ns, Param, ParamId, ParamKind,
    Pat, PatId, Path, PathId, PathRoot, Prim, RecordDef, Res, Segment, Shape, Span, Stmt, StmtId,
    SumDef, Symbol, Ty, TyId, Variant, VariantId, WherePred,
};
use intern_lang::Interner;
use typeck_lang::{Profile, Typed, check};

pub struct Kit {
    pub names: Interner,
    pub b: Builder,
}

impl Default for Kit {
    fn default() -> Self {
        Self::new()
    }
}

impl Kit {
    pub fn new() -> Self {
        Self {
            names: Interner::new(),
            b: Builder::new(),
        }
    }

    pub fn sym(&mut self, s: &str) -> Symbol {
        self.names.intern(s)
    }

    pub fn name(&mut self, s: &str) -> Name {
        Name::new(self.sym(s))
    }

    pub fn ident(&mut self, s: &str) -> Ident {
        Ident::new(self.sym(s), Span::empty(0))
    }

    // ------------------------------------------------------------- types

    pub fn prim(&mut self, p: Prim) -> TyId {
        self.b.ty(Ty::Prim(p))
    }

    pub fn ty(&mut self, t: Ty) -> TyId {
        self.b.ty(t)
    }

    /// A type path naming an item of this unit.
    pub fn item_ty(&mut self, name: &str, item: ItemId) -> TyId {
        let n = self.name(name);
        let def = self.b.def(Def::Item(item));
        let p = self.b.resolved_path(n, Ns::Type, Res::Def(def));
        self.b.ty(Ty::Path(p))
    }

    // ------------------------------------------------------- expressions

    pub fn int(&mut self, v: i64) -> ExprId {
        self.b.int(v)
    }

    pub fn bool(&mut self, v: bool) -> ExprId {
        self.b.lit(Lit::Bool(v))
    }

    pub fn str(&mut self, s: &str) -> ExprId {
        self.b.str_lit(s)
    }

    pub fn float(&mut self, v: f64) -> ExprId {
        self.b.lit(Lit::Float(hir_lang::FloatLit::new(v)))
    }

    pub fn null(&mut self) -> ExprId {
        self.b.lit(Lit::Null)
    }

    pub fn use_(&mut self, binder: BinderId) -> ExprId {
        self.b.use_binder(binder)
    }

    /// A value path to an item of this unit.
    pub fn item_expr(&mut self, name: &str, item: ItemId) -> ExprId {
        let n = self.name(name);
        let def = self.b.def(Def::Item(item));
        let p = self.b.resolved_path(n, Ns::Value, Res::Def(def));
        self.b.expr(Expr::Path(p))
    }

    pub fn variant_expr(&mut self, name: &str, v: VariantId) -> ExprId {
        let n = self.name(name);
        let def = self.b.def(Def::Variant(v));
        let p = self.b.resolved_path(n, Ns::Value, Res::Def(def));
        self.b.expr(Expr::Path(p))
    }

    pub fn call_item(&mut self, name: &str, item: ItemId, args: &[ExprId]) -> ExprId {
        let callee = self.item_expr(name, item);
        self.b.call(callee, args)
    }

    pub fn call_args(&mut self, callee: ExprId, args: &[Arg]) -> ExprId {
        let args = self.b.list(args);
        self.b.expr(Expr::Call { callee, args })
    }

    pub fn named(&mut self, name: &str, value: ExprId) -> Arg {
        Arg {
            kind: ArgKind::Named(self.ident(name)),
            value,
            place: false,
        }
    }

    pub fn op(&mut self, kind: hir_lang::OpKind, args: &[ExprId]) -> ExprId {
        self.b.op(kind, args)
    }

    pub fn block(&mut self, stmts: &[StmtId], tail: Option<ExprId>) -> ExprId {
        self.b.block(stmts, tail)
    }

    pub fn expr(&mut self, e: Expr) -> ExprId {
        self.b.expr(e)
    }

    pub fn stmt(&mut self, e: ExprId) -> StmtId {
        self.b.expr_stmt(e)
    }

    // -------------------------------------------------------- statements

    /// `let name[: ty] = init;`, returning the statement and the binder.
    pub fn let_(
        &mut self,
        name: &str,
        ty: Option<TyId>,
        init: Option<ExprId>,
    ) -> (StmtId, BinderId) {
        let n = self.name(name);
        let binder = self.b.new_binder(n, BinderKind::Local);
        let pat = self.b.bind(binder);
        let s = self.b.stmt(Stmt::Let {
            pat,
            ty,
            init,
            else_: None,
        });
        (s, binder)
    }

    pub fn let_pat(&mut self, pat: PatId, ty: Option<TyId>, init: Option<ExprId>) -> StmtId {
        self.b.stmt(Stmt::Let {
            pat,
            ty,
            init,
            else_: None,
        })
    }

    /// A `Local` binder with its binding pattern.
    pub fn local(&mut self, name: &str) -> (BinderId, PatId) {
        let n = self.name(name);
        let binder = self.b.new_binder(n, BinderKind::Local);
        let pat = self.b.bind(binder);
        (binder, pat)
    }

    // ------------------------------------------------------------- items

    /// A parameter `name: ty` of the given kind.
    pub fn param(
        &mut self,
        name: &str,
        ty: Option<TyId>,
        kind: ParamKind,
        default: Option<ExprId>,
    ) -> (ParamId, BinderId) {
        let n = self.name(name);
        let binder = self.b.new_binder(n, BinderKind::Param);
        let pat = self.b.bind(binder);
        let p = self.b.param(Param {
            pat,
            ty,
            default,
            kind,
            by_ref: false,
        });
        (p, binder)
    }

    /// `fn name(params) -> ret { body }`.
    pub fn func(
        &mut self,
        name: &str,
        params: &[ParamId],
        ret: Option<TyId>,
        body: ExprId,
    ) -> ItemId {
        self.func_fx(name, params, ret, Effects::NONE, body)
    }

    pub fn func_fx(
        &mut self,
        name: &str,
        params: &[ParamId],
        ret: Option<TyId>,
        effects: Effects,
        body: ExprId,
    ) -> ItemId {
        let n = self.name(name);
        let params = self.b.list(params);
        self.b.item(Item::new(
            Some(n),
            ItemKind::Fn(FnDef {
                params,
                ret,
                effects,
                body: Some(body),
                ..FnDef::default()
            }),
        ))
    }

    pub fn field(&mut self, name: &str, ty: Option<TyId>) -> FieldId {
        let id = self.ident(name);
        self.b.field(FieldDef {
            ty,
            ..FieldDef::named(id)
        })
    }

    /// `struct name { fields }`.
    pub fn record(&mut self, name: &str, fields: &[(&str, TyId)]) -> ItemId {
        let ids: Vec<FieldId> = fields
            .iter()
            .map(|&(n, t)| self.field(n, Some(t)))
            .collect();
        let fields = self.b.list(&ids);
        let n = self.name(name);
        self.b.item(Item::new(
            Some(n),
            ItemKind::Record(RecordDef {
                fields,
                ..RecordDef::default()
            }),
        ))
    }

    /// `struct name(types);`.
    pub fn tuple_record(&mut self, name: &str, types: &[TyId]) -> ItemId {
        let ids: Vec<FieldId> = types
            .iter()
            .map(|&t| {
                self.b.field(FieldDef {
                    name: None,
                    vis: hir_lang::Vis::Private,
                    ty: Some(t),
                    default: None,
                })
            })
            .collect();
        let fields = self.b.list(&ids);
        let n = self.name(name);
        self.b.item(Item::new(
            Some(n),
            ItemKind::Record(RecordDef {
                fields,
                shape: Shape::Tuple,
                ..RecordDef::default()
            }),
        ))
    }

    /// A variant: tuple-shaped with `types`, or unit when empty.
    pub fn variant(&mut self, name: &str, types: &[TyId]) -> VariantId {
        let ids: Vec<FieldId> = types
            .iter()
            .map(|&t| {
                self.b.field(FieldDef {
                    name: None,
                    vis: hir_lang::Vis::Private,
                    ty: Some(t),
                    default: None,
                })
            })
            .collect();
        let fields = self.b.list(&ids);
        let name = self.ident(name);
        self.b.variant(Variant {
            name,
            shape: if types.is_empty() {
                Shape::Unit
            } else {
                Shape::Tuple
            },
            fields,
            discriminant: None,
        })
    }

    pub fn sum(&mut self, name: &str, variants: &[VariantId]) -> ItemId {
        let variants = self.b.list(variants);
        let n = self.name(name);
        self.b.item(Item::new(
            Some(n),
            ItemKind::Sum(SumDef {
                variants,
                ..SumDef::default()
            }),
        ))
    }

    pub fn impl_(&mut self, self_ty: TyId, items: &[ItemId]) -> ItemId {
        let items = self.b.list(items);
        self.b.item(Item::new(
            None,
            ItemKind::Impl(ImplDef {
                items,
                ..ImplDef::new(self_ty)
            }),
        ))
    }

    /// A receiver parameter `self` (type `Self` when `ty` is `None`).
    pub fn receiver(&mut self, ty: Option<TyId>) -> (ParamId, BinderId) {
        self.param("self", ty, ParamKind::Receiver, None)
    }

    pub fn method_call(&mut self, receiver: ExprId, name: &str, args: &[ExprId]) -> ExprId {
        let method = self.ident(name);
        let args: Vec<Arg> = args.iter().map(|&a| Arg::positional(a)).collect();
        let args = self.b.list(&args);
        self.b.expr(Expr::MethodCall {
            receiver,
            method,
            generic_args: hir_lang::List::EMPTY,
            args,
        })
    }

    pub fn field_expr(&mut self, base: ExprId, name: &str) -> ExprId {
        let sym = self.sym(name);
        self.b.expr(Expr::Field {
            base,
            member: hir_lang::Member::Named(sym),
            span: Span::empty(0),
        })
    }

    /// A partial value path `Owner::name` whose prefix resolves to `owner`.
    pub fn assoc_path(&mut self, owner_name: &str, owner: ItemId, name: &str) -> PathId {
        let a = self.name(owner_name);
        let n = self.name(name);
        let origin = self.b.origin();
        let segments = self.b.list(&[
            hir_lang::Segment::new(a, origin),
            hir_lang::Segment::new(n, origin),
        ]);
        let def = self.b.def(Def::Item(owner));
        self.b.path(hir_lang::Path {
            res: Res::Def(def),
            unresolved: 1,
            ..hir_lang::Path::new(segments, Ns::Value)
        })
    }

    // -------------------------------------------------------------- finish

    /// Wraps `body` in `fn main()` in a root module, with `items` beside it.
    pub fn finish_main(mut self, items: &[ItemId], body: ExprId) -> (Hir, Interner) {
        let main = self.func("main", &[], None, body);
        let mut all = items.to_vec();
        all.push(main);
        self.finish_items(&all)
    }

    pub fn finish_items(mut self, items: &[ItemId]) -> (Hir, Interner) {
        let root = self.b.module(None, items);
        match self.b.finish(root) {
            Ok(hir) => (hir, self.names),
            Err(e) => panic!("test HIR does not validate: {e:?}"),
        }
    }
}

/// Checks under the static-explicit preset.
pub fn static_check(hir: &Hir) -> Typed {
    check(hir, &Profile::static_explicit()).expect("check runs")
}

/// Every diagnostic, rendered as `code message`.
pub fn messages(typed: &Typed, names: &Interner) -> Vec<String> {
    typed
        .diagnostics()
        .iter()
        .map(|d| format!("{} {}", d.kind.code(), typed.message(d, names)))
        .collect()
}

// ---------------------------------------------------------------- generics
//
// Every HIR node has one parent, so each use of a type parameter, interface,
// or generic type is a fresh path node: the helpers build one per call.

impl Kit {
    /// A type-parameter binder named `name`.
    pub fn type_param(&mut self, name: &str) -> BinderId {
        let n = self.name(name);
        self.b.new_binder(n, BinderKind::TypeParam)
    }

    /// A constant-parameter binder named `name`.
    pub fn const_param(&mut self, name: &str) -> BinderId {
        let n = self.name(name);
        self.b.new_binder(n, BinderKind::ConstParam)
    }

    /// A type path naming type parameter `b` (written `name`).
    pub fn tp(&mut self, name: &str, b: BinderId) -> TyId {
        let n = self.name(name);
        let p = self.b.resolved_path(n, Ns::Type, Res::Local(b));
        self.b.ty(Ty::Path(p))
    }

    /// A value path naming constant parameter `b`.
    pub fn cp_expr(&mut self, name: &str, b: BinderId) -> ExprId {
        let n = self.name(name);
        let p = self.b.resolved_path(n, Ns::Value, Res::Local(b));
        self.b.expr(Expr::Path(p))
    }

    /// A generic parameter with interface bounds.
    pub fn gparam(&mut self, b: BinderId, bounds: &[TyId]) -> GenericParam {
        let bs: Vec<Bound> = bounds.iter().map(|&t| Bound::Ty(t)).collect();
        GenericParam {
            bounds: self.b.list(&bs),
            ..GenericParam::new(b)
        }
    }

    /// A generic parameter with a default type.
    pub fn gparam_default(&mut self, b: BinderId, default: TyId) -> GenericParam {
        GenericParam {
            default: Some(GenericArg::Ty(default)),
            ..GenericParam::new(b)
        }
    }

    /// A constant generic parameter of type `ty`.
    pub fn gconst(&mut self, b: BinderId, ty: TyId) -> GenericParam {
        GenericParam {
            ty: Some(ty),
            ..GenericParam::new(b)
        }
    }

    pub fn generics(&mut self, params: &[GenericParam], preds: &[WherePred]) -> Generics {
        Generics {
            params: self.b.list(params),
            preds: self.b.list(preds),
        }
    }

    /// `where subject: bounds`.
    pub fn where_(&mut self, subject: TyId, bounds: &[TyId]) -> WherePred {
        let bs: Vec<Bound> = bounds.iter().map(|&t| Bound::Ty(t)).collect();
        WherePred {
            subject: Bound::Ty(subject),
            bounds: self.b.list(&bs),
        }
    }

    /// A type path to item `item` with generic type arguments.
    pub fn path_ty(&mut self, name: &str, item: ItemId, args: &[TyId]) -> TyId {
        let ga: Vec<GenericArg> = args.iter().map(|&t| GenericArg::Ty(t)).collect();
        self.path_ty_args(name, item, &ga)
    }

    /// A type path to item `item` with arbitrary generic arguments.
    pub fn path_ty_args(&mut self, name: &str, item: ItemId, args: &[GenericArg]) -> TyId {
        let n = self.name(name);
        let origin = self.b.origin();
        let args = self.b.list(args);
        let seg = Segment {
            args,
            ..Segment::new(n, origin)
        };
        let segments = self.b.list(&[seg]);
        let def = self.b.def(Def::Item(item));
        let p = self.b.path(Path {
            res: Res::Def(def),
            ..Path::new(segments, Ns::Type)
        });
        self.b.ty(Ty::Path(p))
    }

    /// `Iface<args, Name = ty, ...>`: an interface path with bindings.
    pub fn iface_ty_bind(
        &mut self,
        name: &str,
        iface: ItemId,
        args: &[TyId],
        bindings: &[(&str, TyId)],
    ) -> TyId {
        let mut ga: Vec<GenericArg> = args.iter().map(|&t| GenericArg::Ty(t)).collect();
        for &(n, t) in bindings {
            let id = self.ident(n);
            ga.push(GenericArg::Binding { name: id, ty: t });
        }
        self.path_ty_args(name, iface, &ga)
    }

    /// A value path to item `item` with generic arguments (`f::<i32>`).
    pub fn item_expr_args(&mut self, name: &str, item: ItemId, args: &[TyId]) -> ExprId {
        let n = self.name(name);
        let origin = self.b.origin();
        let ga: Vec<GenericArg> = args.iter().map(|&t| GenericArg::Ty(t)).collect();
        let args = self.b.list(&ga);
        let seg = Segment {
            args,
            ..Segment::new(n, origin)
        };
        let segments = self.b.list(&[seg]);
        let def = self.b.def(Def::Item(item));
        let p = self.b.path(Path {
            res: Res::Def(def),
            ..Path::new(segments, Ns::Value)
        });
        self.b.expr(Expr::Path(p))
    }

    /// `Prefix::name` in a type, with the prefix resolved to `res`
    /// (`T::Item`).
    pub fn assoc_ty(&mut self, prefix: &str, res: Res, name: &str) -> TyId {
        let a = self.name(prefix);
        let n = self.name(name);
        let origin = self.b.origin();
        let segments = self
            .b
            .list(&[Segment::new(a, origin), Segment::new(n, origin)]);
        let p = self.b.path(Path {
            res,
            unresolved: 1,
            ..Path::new(segments, Ns::Type)
        });
        self.b.ty(Ty::Path(p))
    }

    /// `Self::name` in a type.
    pub fn self_assoc_ty(&mut self, name: &str) -> TyId {
        let n = self.name(name);
        let origin = self.b.origin();
        let segments = self.b.list(&[Segment::new(n, origin)]);
        let p = self.b.path(Path {
            res: Res::Unresolved,
            unresolved: 1,
            root: PathRoot::SelfType,
            ..Path::new(segments, Ns::Type)
        });
        self.b.ty(Ty::Path(p))
    }

    /// `Prefix::name` as a value, with the prefix resolved to `res`
    /// (`T::new`, `Show::show`).
    pub fn assoc_expr(&mut self, prefix: &str, res: Res, name: &str) -> ExprId {
        let a = self.name(prefix);
        let n = self.name(name);
        let origin = self.b.origin();
        let segments = self
            .b
            .list(&[Segment::new(a, origin), Segment::new(n, origin)]);
        let p = self.b.path(Path {
            res,
            unresolved: 1,
            ..Path::new(segments, Ns::Value)
        });
        self.b.expr(Expr::Path(p))
    }

    /// A resolution naming item `item`.
    pub fn res(&mut self, item: ItemId) -> Res {
        Res::Def(self.b.def(Def::Item(item)))
    }

    pub fn self_ty(&mut self) -> TyId {
        self.b.ty(Ty::SelfTy)
    }

    pub fn ref_ty(&mut self, mutable: bool, inner: TyId) -> TyId {
        self.b.ty(Ty::Ref {
            mutable,
            region: None,
            inner,
        })
    }

    /// A generic function.
    pub fn gfunc(
        &mut self,
        name: &str,
        generics: Generics,
        params: &[ParamId],
        ret: Option<TyId>,
        body: ExprId,
    ) -> ItemId {
        let n = self.name(name);
        let params = self.b.list(params);
        self.b.item(Item::new(
            Some(n),
            ItemKind::Fn(FnDef {
                generics,
                params,
                ret,
                body: Some(body),
                ..FnDef::default()
            }),
        ))
    }

    /// A function declaration without a body (an interface method).
    pub fn decl(&mut self, name: &str, params: &[ParamId], ret: Option<TyId>) -> ItemId {
        let n = self.name(name);
        let params = self.b.list(params);
        self.b.item(Item::new(
            Some(n),
            ItemKind::Fn(FnDef {
                params,
                ret,
                body: None,
                ..FnDef::default()
            }),
        ))
    }

    /// A generic record with named fields.
    pub fn grecord(&mut self, name: &str, generics: Generics, fields: &[(&str, TyId)]) -> ItemId {
        let ids: Vec<FieldId> = fields
            .iter()
            .map(|&(n, t)| self.field(n, Some(t)))
            .collect();
        let fields = self.b.list(&ids);
        let n = self.name(name);
        self.b.item(Item::new(
            Some(n),
            ItemKind::Record(RecordDef {
                generics,
                fields,
                ..RecordDef::default()
            }),
        ))
    }

    /// A generic sum.
    pub fn gsum(&mut self, name: &str, generics: Generics, variants: &[VariantId]) -> ItemId {
        let variants = self.b.list(variants);
        let n = self.name(name);
        self.b.item(Item::new(
            Some(n),
            ItemKind::Sum(SumDef { generics, variants }),
        ))
    }

    /// An interface.
    pub fn iface(
        &mut self,
        name: &str,
        generics: Generics,
        supers: &[TyId],
        items: &[ItemId],
    ) -> ItemId {
        let n = self.name(name);
        let supers = self.b.list(supers);
        let items = self.b.list(items);
        self.b.item(Item::new(
            Some(n),
            ItemKind::Interface(InterfaceDef {
                generics,
                supers,
                items,
            }),
        ))
    }

    /// `impl<generics> [iface for] self_ty { items }`.
    pub fn impl_of(
        &mut self,
        generics: Generics,
        iface: Option<TyId>,
        self_ty: TyId,
        items: &[ItemId],
    ) -> ItemId {
        let items = self.b.list(items);
        self.b.item(Item::new(
            None,
            ItemKind::Impl(ImplDef {
                generics,
                interface: iface,
                self_ty,
                items,
            }),
        ))
    }

    /// An associated type declaration.
    pub fn assoc(&mut self, name: &str, bounds: &[TyId], default: Option<TyId>) -> ItemId {
        let n = self.name(name);
        let bs: Vec<Bound> = bounds.iter().map(|&t| Bound::Ty(t)).collect();
        let bounds = self.b.list(&bs);
        self.b
            .item(Item::new(Some(n), ItemKind::AssocType { bounds, default }))
    }

    /// `type name = ty;` (an alias, or an associated type's value in an
    /// impl).
    pub fn alias(&mut self, name: &str, generics: Generics, ty: TyId) -> ItemId {
        let n = self.name(name);
        self.b
            .item(Item::new(Some(n), ItemKind::Alias { generics, ty }))
    }

    /// A class.
    pub fn class(
        &mut self,
        name: &str,
        generics: Generics,
        bases: &[TyId],
        interfaces: &[TyId],
        fields: &[(&str, TyId)],
        items: &[ItemId],
    ) -> ItemId {
        let ids: Vec<FieldId> = fields
            .iter()
            .map(|&(n, t)| self.field(n, Some(t)))
            .collect();
        let n = self.name(name);
        let def = ClassDef {
            generics,
            bases: self.b.list(bases),
            interfaces: self.b.list(interfaces),
            fields: self.b.list(&ids),
            items: self.b.list(items),
            ..ClassDef::default()
        };
        self.b.item(Item::new(Some(n), ItemKind::Class(def)))
    }

    /// A closure over `params` (implicit captures by reference).
    pub fn closure(&mut self, params: &[ParamId], ret: Option<TyId>, body: ExprId) -> ExprId {
        let params = self.b.list(params);
        self.b.expr(Expr::Closure(Closure {
            params,
            ret,
            implicit: Some(CaptureMode::ByRef),
            ..Closure::new(body)
        }))
    }

    /// `match scrutinee { pat => body, ... }`.
    pub fn match_(&mut self, scrutinee: ExprId, arms: &[(PatId, ExprId)]) -> ExprId {
        let arms: Vec<Arm> = arms
            .iter()
            .map(|&(pat, body)| Arm {
                pat,
                guard: None,
                body,
            })
            .collect();
        let arms = self.b.list(&arms);
        self.b.expr(Expr::Match { scrutinee, arms })
    }

    pub fn wild(&mut self) -> PatId {
        self.b.pat(Pat::Wild)
    }

    pub fn lit_pat(&mut self, lit: Lit) -> PatId {
        self.b.pat(Pat::Lit(lit))
    }

    /// `Name(elems...)` naming variant `v`.
    pub fn variant_pat(&mut self, name: &str, v: VariantId, elems: &[PatId]) -> PatId {
        let n = self.name(name);
        let def = self.b.def(Def::Variant(v));
        let path = self.b.resolved_path(n, Ns::Pattern, Res::Def(def));
        let elems = self.b.list(elems);
        self.b.pat(Pat::Ctor {
            path,
            elems,
            rest: None,
        })
    }

    /// A unit variant pattern.
    pub fn unit_variant_pat(&mut self, name: &str, v: VariantId) -> PatId {
        let n = self.name(name);
        let def = self.b.def(Def::Variant(v));
        let path = self.b.resolved_path(n, Ns::Pattern, Res::Def(def));
        self.b.pat(Pat::Path(path))
    }

    /// A method `name(self[: recv]) -> ret { body }` building block: the
    /// receiver parameter and binder.
    pub fn method(
        &mut self,
        name: &str,
        recv: Option<TyId>,
        params: &[ParamId],
        ret: Option<TyId>,
        body_of: impl FnOnce(&mut Kit, BinderId) -> ExprId,
    ) -> ItemId {
        let (r, me) = self.receiver(recv);
        let body = body_of(self, me);
        let mut all = alloc_vec(r);
        all.extend_from_slice(params);
        self.func(name, &all, ret, body)
    }
}

fn alloc_vec(first: ParamId) -> Vec<ParamId> {
    vec![first]
}

/// Checks under the static-inferred preset.
pub fn inferred_check(hir: &Hir) -> Typed {
    check(hir, &Profile::static_inferred()).expect("check runs")
}
