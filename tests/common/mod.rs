//! Shared helpers: a builder plus an interner, with short constructors for
//! the HIR shapes the tests use.

#![allow(dead_code)]

use hir_lang::{
    Arg, ArgKind, BinderId, BinderKind, Builder, Def, Effects, Expr, ExprId, FieldDef, FieldId,
    FnDef, Hir, Ident, ImplDef, Item, ItemId, ItemKind, Lit, Name, Ns, Param, ParamId, ParamKind,
    PatId, PathId, Prim, RecordDef, Res, Shape, Span, Stmt, StmtId, SumDef, Symbol, Ty, TyId,
    Variant, VariantId,
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
