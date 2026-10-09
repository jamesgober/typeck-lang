//! What value paths name, including the unresolved tails of partial paths
//! (`Shape::Circle`, `Point::new`, `T::default`, `<T as Show>::show`), and
//! the instantiation of the generic items they name.

use alloc::vec::Vec;

use hir_lang::{
    BinderId, Def, GenericArg, ItemId, ItemKind, NodeRef, PathId, PathRoot, Res, Shape, Symbol,
    VariantId,
};

use super::{
    Ctx,
    lower::Sig,
    traits::{MemberLookup, Pick},
};
use crate::{
    diag::{DiagnosticKind, Feature},
    error::CheckError,
    infer::GENERAL,
    mono::Dispatch,
    types::{Tag, Type, TypeId},
};

/// What a value path refers to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ValueRef {
    Local(BinderId),
    /// A function item, with its (instantiated) signature.
    Fn {
        item: ItemId,
        sig: u32,
    },
    /// A `const` or `global` item, with its (instantiated) type.
    Decl {
        item: ItemId,
        ty: TypeId,
    },
    /// A tuple-shaped record's constructor, building `adt`.
    RecordCtor {
        item: ItemId,
        adt: TypeId,
    },
    /// A tuple variant's constructor, building `adt`.
    VariantCtor {
        v: VariantId,
        adt: TypeId,
    },
    /// A value of a known type: unit records and variants, host values.
    Typed(TypeId),
    /// Already reported, or nothing to report: `{error}`.
    Error,
}

/// What a record literal or record pattern constructs or matches.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RecordRef {
    /// A record or class item.
    Item(ItemId),
    /// A variant with fields.
    Variant(VariantId),
}

impl Ctx<'_> {
    /// Resolves a value path (`Value` or `Pattern` namespace), reporting what
    /// is wrong with it at `at`, and instantiating a generic item it names.
    pub(crate) fn value_path(&mut self, p: PathId, at: NodeRef) -> Result<ValueRef, CheckError> {
        let path = *self.hir.path(p);
        if path.res == Res::Err {
            return Ok(ValueRef::Error);
        }
        if path.unresolved != 0 || path.qself.is_some() {
            return self.path_tail(p, at);
        }
        let written = self.last_args(p);
        Ok(match path.res {
            Res::Local(b) => {
                if self
                    .hir
                    .binder(b)
                    .is_some_and(|x| x.kind == hir_lang::BinderKind::ConstParam)
                {
                    // A constant parameter used as a value: its declared
                    // type.
                    return Ok(ValueRef::Typed(self.const_param_type(b)?));
                }
                ValueRef::Local(b)
            }
            Res::Def(d) if d.unit() == self.hir.unit() => match d.def() {
                Def::Item(i) => self.item_value(i, &written, at)?,
                Def::Variant(v) => self.variant_value(v, None, &written, at)?,
            },
            Res::Def(d) => match self.host_foreign(d) {
                Some(t) => ValueRef::Typed(t),
                None => {
                    let name = self.last_segment(p);
                    self.report(at, DiagnosticKind::UnknownExtern { name });
                    ValueRef::Error
                }
            },
            Res::Extern(sym) => match self.host_extern(sym) {
                Some(t) => ValueRef::Typed(t),
                None => {
                    self.report(at, DiagnosticKind::UnknownExtern { name: Some(sym) });
                    ValueRef::Error
                }
            },
            Res::Prim(_) => {
                self.report(at, DiagnosticKind::NotAValue);
                ValueRef::Error
            }
            Res::Unresolved => {
                self.report(at, DiagnosticKind::Unresolved);
                ValueRef::Error
            }
            Res::Err => ValueRef::Error,
        })
    }

    /// The declared type of a constant generic parameter.
    fn const_param_type(&mut self, b: BinderId) -> Result<TypeId, CheckError> {
        let Some(item) = self.env_item() else {
            return Ok(TypeId::ERROR);
        };
        // The parameter's declaration is on the item or its owner.
        let mut owners = alloc::vec![item];
        if let Some(o) = self.idx.owner_of(item) {
            owners.push(o);
        }
        for it in owners {
            let Some(g) = super::generics::generics_of(&self.item_kind(it)) else {
                continue;
            };
            let found = self
                .hir
                .list(g.params)
                .iter()
                .find(|gp| gp.binder == b)
                .and_then(|gp| gp.ty);
            if let Some(t) = found {
                let saved = self.lower_ctx.replace(it);
                let r = self.lower_ty(t, None, true);
                self.lower_ctx = saved;
                return r;
            }
        }
        Ok(TypeId::ERROR)
    }

    fn last_segment(&self, p: PathId) -> Option<Symbol> {
        let path = self.hir.path(p);
        self.hir.list(path.segments).last().map(|s| s.name.sym)
    }

    /// The positional generic arguments of a path's last segment.
    fn last_args(&self, p: PathId) -> Vec<GenericArg> {
        let path = self.hir.path(p);
        match self.hir.list(path.segments).last() {
            Some(s) => self.written_args(s.args),
            None => Vec::new(),
        }
    }

    /// The positional generic arguments of the segment before the last.
    fn prefix_args(&self, p: PathId) -> Vec<GenericArg> {
        let path = self.hir.path(p);
        let segs = self.hir.list(path.segments);
        match segs.len().checked_sub(2).and_then(|i| segs.get(i)) {
            Some(s) => self.written_args(s.args),
            None => Vec::new(),
        }
    }

    fn item_value(
        &mut self,
        i: ItemId,
        written: &[GenericArg],
        at: NodeRef,
    ) -> Result<ValueRef, CheckError> {
        Ok(match self.item_kind(i) {
            ItemKind::Fn(_) => self.fn_ref(i, None, written, at)?,
            ItemKind::Const { .. } | ItemKind::Global { .. } => ValueRef::Decl {
                item: i,
                ty: self.decl_type(i)?,
            },
            ItemKind::Record(def) => match def.shape {
                Shape::Tuple => ValueRef::RecordCtor {
                    item: i,
                    adt: self.adt_use(i, written, at)?,
                },
                Shape::Unit => ValueRef::Typed(self.adt_use(i, written, at)?),
                Shape::Named => {
                    self.report(at, DiagnosticKind::NotAValue);
                    ValueRef::Error
                }
            },
            ItemKind::Err => ValueRef::Error,
            _ => {
                self.report(at, DiagnosticKind::NotAValue);
                ValueRef::Error
            }
        })
    }

    /// The nominal type of `item` at a use: written arguments, else fresh
    /// variables.
    pub(crate) fn adt_use(
        &mut self,
        item: ItemId,
        written: &[GenericArg],
        at: NodeRef,
    ) -> Result<TypeId, CheckError> {
        if !self.profile.is_static() {
            return Ok(self.adt_type(item));
        }
        let t = if written.is_empty() {
            self.adt_fresh(item)
        } else {
            self.name_item(item);
            let args = self.fill_args(item, written, at, false, None)?;
            self.types.adt_with(item, &args)
        };
        // Constructing a value of a bounded generic type needs the bounds.
        let args = self.types.kids(t).to_vec();
        self.push_bounds(item, &args, at)?;
        Ok(t)
    }

    /// A variant used as a value: `owner` is the sum's instance when the
    /// path's prefix gave it.
    fn variant_value(
        &mut self,
        v: VariantId,
        owner: Option<TypeId>,
        written: &[GenericArg],
        at: NodeRef,
    ) -> Result<ValueRef, CheckError> {
        let Some(sum) = self.hir.variant_owner(v) else {
            return Ok(ValueRef::Error);
        };
        let adt = match owner {
            Some(t) => t,
            None => self.adt_use(sum, written, at)?,
        };
        Ok(match self.hir.variant(v).map(|x| x.shape) {
            Some(Shape::Tuple) => ValueRef::VariantCtor { v, adt },
            Some(Shape::Unit) => ValueRef::Typed(adt),
            // A variant with named fields is built by a record literal; as a
            // bare value it is not one.
            _ => ValueRef::Error,
        })
    }

    /// A function item used at `at`: instantiated (owner placeholders from
    /// `inherited`, own from `written`, the rest fresh), its bounds queued,
    /// the use recorded.
    pub(crate) fn fn_ref(
        &mut self,
        item: ItemId,
        inherited: Option<&[TypeId]>,
        written: &[GenericArg],
        at: NodeRef,
    ) -> Result<ValueRef, CheckError> {
        let own = if written.is_empty() {
            None
        } else {
            Some(self.fill_args(item, written, at, false, None)?)
        };
        let args = self.instantiate(item, inherited, own.as_deref());
        let Some(sig) = self.inst_sig(item, &args, at)? else {
            return Ok(ValueRef::Error);
        };
        if !args.is_empty() {
            self.push_bounds(item, &args, at)?;
        }
        if let NodeRef::Expr(e) = at {
            self.record_use(e, item, &args, Dispatch::Static);
        }
        Ok(ValueRef::Fn { item, sig })
    }

    /// The signature of `item` with its placeholders replaced by `args` (the
    /// template itself when there are none).
    pub(crate) fn inst_sig(
        &mut self,
        item: ItemId,
        args: &[TypeId],
        at: NodeRef,
    ) -> Result<Option<u32>, CheckError> {
        let Some(template) = self.sig(item)? else {
            return Ok(None);
        };
        if args.is_empty() {
            return Ok(Some(u32::try_from(template).unwrap_or(u32::MAX)));
        }
        let Some(mut s) = self.sig_arena.get(template).cloned() else {
            return Ok(None);
        };
        let params = self.placeholders(item);
        for p in &mut s.params {
            let t = self.subst(p.ty, &params, args)?;
            p.ty = self.normalize(t, at)?;
        }
        let ret = self.subst(s.ret, &params, args)?;
        s.ret = self.normalize(ret, at)?;
        if let Some(t) = s.throws {
            let t = self.subst(t, &params, args)?;
            s.throws = Some(self.normalize(t, at)?);
        }
        Ok(Some(self.push_sig(s)))
    }

    pub(crate) fn push_sig(&mut self, s: Sig) -> u32 {
        let index = u32::try_from(self.sig_arena.len()).unwrap_or(u32::MAX);
        self.sig_arena.push(s);
        index
    }

    /// The type a value path has.
    pub(crate) fn value_type(&mut self, r: ValueRef) -> Result<TypeId, CheckError> {
        Ok(match r {
            ValueRef::Local(b) => match self.binder_type(b) {
                Some(t) => t,
                None => {
                    // A binder with no binding site seen yet (or never
                    // bound): a fresh variable, inferred from its uses.
                    let v = self.fresh(GENERAL);
                    if let Some(slot) = self.binder_ty.get_mut(b.index()) {
                        *slot = v.raw();
                    }
                    v
                }
            },
            ValueRef::Fn { sig, .. } => self.fn_value_type(sig as usize),
            ValueRef::Decl { ty, .. } => ty,
            ValueRef::RecordCtor { item, adt } => {
                let fields = self.record_field_ids(item);
                self.ctor_type(&fields, adt)?
            }
            ValueRef::VariantCtor { v, adt } => {
                let fields: Vec<_> = self
                    .hir
                    .variant(v)
                    .map(|x| self.hir.list(x.fields).to_vec())
                    .unwrap_or_default();
                self.ctor_type(&fields, adt)?
            }
            ValueRef::Typed(t) => t,
            ValueRef::Error => TypeId::ERROR,
        })
    }

    pub(crate) fn record_field_ids(&self, i: ItemId) -> Vec<hir_lang::FieldId> {
        match self.item_kind(i) {
            ItemKind::Record(def) => self.hir.list(def.fields).to_vec(),
            ItemKind::Class(def) => self.hir.list(def.fields).to_vec(),
            _ => Vec::new(),
        }
    }

    /// A field's declared type inside an instance `adt` of its owner.
    pub(crate) fn field_type_in(
        &mut self,
        f: hir_lang::FieldId,
        adt: TypeId,
    ) -> Result<TypeId, CheckError> {
        let t = self.field_type(f)?;
        match self.adt_subst(adt) {
            Some((_, params, args)) if !params.is_empty() => self.subst(t, &params, &args),
            _ => Ok(t),
        }
    }

    fn ctor_type(
        &mut self,
        fields: &[hir_lang::FieldId],
        result: TypeId,
    ) -> Result<TypeId, CheckError> {
        let mut params = Vec::with_capacity(fields.len());
        for &f in fields {
            params.push(self.field_type_in(f, result)?);
        }
        Ok(self.types.func(&params, result, hir_lang::Effects::NONE))
    }

    /// Resolves the unresolved tail of a partial path by type.
    fn path_tail(&mut self, p: PathId, at: NodeRef) -> Result<ValueRef, CheckError> {
        let path = *self.hir.path(p);
        if path.unresolved > 1 {
            self.report(
                at,
                DiagnosticKind::Unsupported {
                    feature: Feature::LongAssocPaths,
                },
            );
            return Ok(ValueRef::Error);
        }
        let segments = self.hir.list(path.segments);
        let Some(&last) = segments.last() else {
            return Ok(ValueRef::Error);
        };
        let name = last.name.sym;
        let own = self.written_args(last.args);
        // `<T as Iface>::m` and `Iface::m`: an interface member with a
        // known (or fresh) `Self`.
        if let Some(q) = path.qself {
            let qt = self.lower_ty(q.ty, self.cur_self, false)?;
            if q.trait_len > 0 {
                let Some(iface) = self
                    .local_item(path.res)
                    .filter(|&i| matches!(self.item_kind(i), ItemKind::Interface(_)))
                else {
                    if path.res != Res::Err {
                        self.report(at, DiagnosticKind::NotAnInterface);
                    }
                    return Ok(ValueRef::Error);
                };
                let trait_seg = segments
                    .get(q.trait_len.saturating_sub(1) as usize)
                    .copied();
                let written = trait_seg.map_or_else(Vec::new, |s| self.written_args(s.args));
                return self.iface_member_value(p, iface, qt, &written, name, &own, at);
            }
            return self.member_value(p, qt, name, &own, at);
        }
        let prefix_len = segments.len().saturating_sub(1);
        if prefix_len > 0 {
            if let Some(iface) = self
                .local_item(path.res)
                .filter(|&i| matches!(self.item_kind(i), ItemKind::Interface(_)))
            {
                let self_ty = self.fresh(GENERAL);
                let written = self.prefix_args(p);
                return self.iface_member_value(p, iface, self_ty, &written, name, &own, at);
            }
        }
        let Some(owner) = self.prefix_type(p, &path, prefix_len, at)? else {
            return Ok(ValueRef::Error);
        };
        let owner = self.resolve(owner);
        if let Type::Adt { item, .. } = self.types.get(owner) {
            if matches!(self.item_kind(item), ItemKind::Sum(_)) {
                if let Some(v) = self.idx.variant_named(item, name) {
                    self.record_path_def(p, Def::Variant(v));
                    return self.variant_value(v, Some(owner), &own, at);
                }
            }
        }
        self.member_value(p, owner, name, &own, at)
    }

    /// An interface's member `name` with `Self` = `self_ty`.
    #[allow(clippy::too_many_arguments)]
    fn iface_member_value(
        &mut self,
        p: PathId,
        iface: ItemId,
        self_ty: TypeId,
        written: &[GenericArg],
        name: Symbol,
        own: &[GenericArg],
        at: NodeRef,
    ) -> Result<ValueRef, CheckError> {
        let tr_args = self.fill_args(iface, written, at, false, Some(self_ty))?;
        let s = self.types.self_of(iface);
        let own_params = self.own_params(iface);
        let root = self.types.trait_ref(iface, &own_params);
        // The member may come from a supertrait.
        let mut found = None;
        for tr in self.elaborate(root, s)? {
            let Some(i) = self.trait_item(tr) else {
                continue;
            };
            if let Some(m) = self.iface_member(i, name) {
                let mut from = alloc::vec![s];
                from.extend(own_params.iter().copied());
                let mut to = alloc::vec![self_ty];
                to.extend(tr_args.iter().copied());
                let tr = self.subst(tr, &from, &to)?;
                found = Some((m, self.trait_args(tr)));
                break;
            }
        }
        let Some((member, args)) = found else {
            let ty = self.types.trait_ref(iface, &tr_args);
            self.report(at, DiagnosticKind::NoMethod { ty, name });
            return Ok(ValueRef::Error);
        };
        let pick = Pick::Iface {
            member,
            self_ty,
            tr_args: args,
            dynamic: false,
        };
        self.use_pick(p, &pick, own, at)
    }

    /// Member `name` of type `owner`, as a value.
    fn member_value(
        &mut self,
        p: PathId,
        owner: TypeId,
        name: Symbol,
        own: &[GenericArg],
        at: NodeRef,
    ) -> Result<ValueRef, CheckError> {
        match self.member(owner, name, at)? {
            Some(pick) => self.use_pick(p, &pick, own, at),
            None => Ok(ValueRef::Error),
        }
    }

    /// A picked member, instantiated and recorded.
    pub(crate) fn use_pick(
        &mut self,
        p: PathId,
        pick: &Pick,
        own: &[GenericArg],
        at: NodeRef,
    ) -> Result<ValueRef, CheckError> {
        if let Pick::Host(t) = *pick {
            return Ok(ValueRef::Typed(t));
        }
        let member = match pick {
            Pick::Rec { member, .. } | Pick::Iface { member, .. } => *member,
            Pick::Host(_) => return Ok(ValueRef::Error),
        };
        self.record_path_def(p, Def::Item(member));
        let own_args = if own.is_empty() {
            None
        } else {
            Some(self.fill_args(member, own, at, false, None)?)
        };
        let Some((member, args)) = self.pick_args(pick, own_args.as_deref()) else {
            return Ok(ValueRef::Error);
        };
        let dispatch = match pick {
            Pick::Iface { dynamic: true, .. } => Dispatch::Dynamic,
            Pick::Iface { .. } => Dispatch::Bound,
            _ => Dispatch::Static,
        };
        match self.item_kind(member) {
            ItemKind::Fn(_) => {
                let Some(sig) = self.inst_sig(member, &args, at)? else {
                    return Ok(ValueRef::Error);
                };
                self.push_bounds(member, &args, at)?;
                if let NodeRef::Expr(e) = at {
                    self.record_use(e, member, &args, dispatch);
                }
                Ok(ValueRef::Fn { item: member, sig })
            }
            ItemKind::Const { .. } | ItemKind::Global { .. } => {
                let t = self.decl_type(member)?;
                let params = self.placeholders(member);
                let t = self.subst(t, &params, &args)?;
                let t = self.normalize(t, at)?;
                self.push_bounds(member, &args, at)?;
                Ok(ValueRef::Decl {
                    item: member,
                    ty: t,
                })
            }
            _ => Ok(ValueRef::Error),
        }
    }

    /// The type the resolved prefix of a partial path names.
    fn prefix_type(
        &mut self,
        p: PathId,
        path: &hir_lang::Path,
        prefix_len: usize,
        at: NodeRef,
    ) -> Result<Option<TypeId>, CheckError> {
        if prefix_len == 0 {
            return Ok(match path.root {
                PathRoot::SelfType | PathRoot::StaticType => self.cur_self,
                PathRoot::ParentType => self.cur_parent()?,
                _ => None,
            });
        }
        let written = self.prefix_args(p);
        Ok(match path.res {
            Res::Def(d) if d.unit() == self.hir.unit() => match d.def() {
                Def::Item(i) => match self.item_kind(i) {
                    ItemKind::Record(_) | ItemKind::Sum(_) | ItemKind::Class(_) => {
                        Some(self.adt_use(i, &written, at)?)
                    }
                    ItemKind::Alias { ty, .. } => {
                        let self_ty = self.item_self(i);
                        let saved = self.lower_ctx.replace(i);
                        let body = self.lower_ty(ty, self_ty, true);
                        self.lower_ctx = saved;
                        let body = body?;
                        let args = self.fill_args(i, &written, at, false, None)?;
                        let params = self.own_params(i);
                        Some(self.subst(body, &params, &args)?)
                    }
                    ItemKind::Err => None,
                    _ => {
                        self.report(at, DiagnosticKind::NotAType);
                        None
                    }
                },
                Def::Variant(_) => None,
            },
            Res::Def(d) => Some(self.types.foreign(d)),
            Res::Prim(p) => Some(TypeId::prim(p)),
            Res::Extern(sym) => Some(self.types.external(sym)),
            Res::Local(b) => match self.hir.binder(b) {
                Some(x) if x.kind == hir_lang::BinderKind::TypeParam => {
                    self.types.name_binder(b, x.name.sym);
                    Some(self.types.param(b))
                }
                _ => {
                    self.report(at, DiagnosticKind::NotAType);
                    None
                }
            },
            Res::Unresolved => {
                self.report(at, DiagnosticKind::Unresolved);
                None
            }
            Res::Err => None,
        })
    }

    /// The first base class of the current class (`parent::`).
    fn cur_parent(&mut self) -> Result<Option<TypeId>, CheckError> {
        let Some(t) = self.cur_self else {
            return Ok(None);
        };
        Ok(self.base_types(t)?.first().copied())
    }

    /// Looks up a member (method, associated function, constant) of a type.
    /// Reports `NoMethod` or `AmbiguousMethod` at `at` (`NoMethod` only when
    /// the type's members are complete); `None` after reporting.
    pub(crate) fn member(
        &mut self,
        owner: TypeId,
        name: Symbol,
        at: NodeRef,
    ) -> Result<Option<Pick>, CheckError> {
        Ok(match self.lookup_member(owner, name, at)? {
            MemberLookup::Found(m) => Some(m),
            MemberLookup::Ambiguous => {
                let ty = self.resolve(owner);
                self.report(at, DiagnosticKind::AmbiguousMethod { ty, name });
                None
            }
            MemberLookup::NotFound { incomplete } => {
                if !incomplete && self.tag(owner) != Tag::Var {
                    let ty = self.resolve(owner);
                    self.report(at, DiagnosticKind::NoMethod { ty, name });
                }
                None
            }
        })
    }

    /// What a record literal's or record pattern's path constructs.
    pub(crate) fn record_ref(
        &mut self,
        p: PathId,
        at: NodeRef,
    ) -> Result<Option<RecordRef>, CheckError> {
        let path = *self.hir.path(p);
        if path.res == Res::Err {
            return Ok(None);
        }
        if path.unresolved != 0 || path.qself.is_some() {
            // `Shape::Rect { .. }`: a variant by type.
            let _ = self.path_tail(p, at)?;
            return Ok(match self.path_def.get(p.index()).copied().flatten() {
                Some(Def::Variant(v)) => Some(RecordRef::Variant(v)),
                _ => None,
            });
        }
        Ok(match path.res {
            Res::Def(d) if d.unit() == self.hir.unit() => match d.def() {
                Def::Item(i) => match self.item_kind(i) {
                    ItemKind::Record(_) | ItemKind::Class(_) => Some(RecordRef::Item(i)),
                    ItemKind::Alias { ty, .. } => {
                        let self_ty = self.item_self(i);
                        let t = self.lower_ty(ty, self_ty, true)?;
                        match self.types.get(self.resolve(t)) {
                            Type::Adt { item: r, .. }
                                if matches!(
                                    self.item_kind(r),
                                    ItemKind::Record(_) | ItemKind::Class(_)
                                ) =>
                            {
                                Some(RecordRef::Item(r))
                            }
                            Type::Error => None,
                            _ => {
                                self.report(at, DiagnosticKind::NotAType);
                                None
                            }
                        }
                    }
                    ItemKind::Err => None,
                    _ => {
                        self.report(at, DiagnosticKind::NotAType);
                        None
                    }
                },
                Def::Variant(v) => Some(RecordRef::Variant(v)),
            },
            Res::Unresolved => {
                self.report(at, DiagnosticKind::Unresolved);
                None
            }
            Res::Err => None,
            _ => {
                // Another unit's or the host's record: its fields are not
                // known here.
                let name = self.last_segment(p);
                self.report(at, DiagnosticKind::UnknownExtern { name });
                None
            }
        })
    }

    /// The nominal type a record reference constructs, at a use (fresh
    /// arguments for a generic item, or the ones written on the path).
    pub(crate) fn record_ref_type(&mut self, r: RecordRef, p: Option<PathId>) -> TypeId {
        let written = p.map_or_else(Vec::new, |p| self.last_args(p));
        let item = match r {
            RecordRef::Item(i) => Some(i),
            RecordRef::Variant(v) => self.hir.variant_owner(v),
        };
        match item {
            Some(i) => self
                .adt_use(i, &written, p.map_or(NodeRef::Item(i), NodeRef::Path))
                .unwrap_or(TypeId::ERROR),
            None => TypeId::ERROR,
        }
    }
}
