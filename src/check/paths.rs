//! What value paths name, including the unresolved tails of partial paths
//! (`Shape::Circle`, `Point::new`), and member lookup on nominal types.

use alloc::vec::Vec;

use hir_lang::{
    BinderId, Def, ItemId, ItemKind, NodeRef, PathId, PathRoot, Res, Shape, Symbol, VariantId,
};

use super::{Ctx, call::Lookup};
use crate::{
    diag::{DiagnosticKind, Feature},
    error::CheckError,
    types::{Tag, Type, TypeId},
};

/// What a value path refers to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ValueRef {
    Local(BinderId),
    /// A function item (its signature drives calls).
    Fn(ItemId),
    /// A `const` or `global` item.
    Decl(ItemId),
    /// A tuple-shaped record's constructor.
    RecordCtor(ItemId),
    /// A tuple variant's constructor.
    VariantCtor(VariantId),
    /// A value of a known type: unit records and variants, host values.
    Typed(TypeId),
    /// Already reported, or nothing to report: `{error}`.
    Error,
}

/// A member found on a type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MemberRef {
    Item(ItemId),
    /// A host-declared member's type.
    Host(TypeId),
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
    /// is wrong with it at `at`.
    pub(crate) fn value_path(&mut self, p: PathId, at: NodeRef) -> Result<ValueRef, CheckError> {
        let path = *self.hir.path(p);
        if path.res == Res::Err {
            return Ok(ValueRef::Error);
        }
        if path.unresolved != 0 || path.qself.is_some() {
            return self.path_tail(p, at);
        }
        let generic_args = self
            .hir
            .list(path.segments)
            .iter()
            .any(|s| !s.args.is_empty());
        Ok(match path.res {
            Res::Local(b) => ValueRef::Local(b),
            Res::Def(d) if d.unit() == self.hir.unit() => match d.def() {
                Def::Item(i) => {
                    if self.idx.is_generic(i) {
                        // Reported once, at the generic item.
                        return Ok(ValueRef::Error);
                    }
                    if generic_args {
                        self.report(at, unsupported(Feature::Generics));
                        return Ok(ValueRef::Error);
                    }
                    self.item_value(i, at)
                }
                Def::Variant(v) => self.variant_value(v),
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

    fn last_segment(&self, p: PathId) -> Option<Symbol> {
        let path = self.hir.path(p);
        self.hir.list(path.segments).last().map(|s| s.name.sym)
    }

    fn item_value(&mut self, i: ItemId, at: NodeRef) -> ValueRef {
        match self.item_kind(i) {
            ItemKind::Fn(_) => ValueRef::Fn(i),
            ItemKind::Const { .. } | ItemKind::Global { .. } => ValueRef::Decl(i),
            ItemKind::Record(def) => match def.shape {
                Shape::Tuple => ValueRef::RecordCtor(i),
                Shape::Unit => ValueRef::Typed(self.adt_type(i)),
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
        }
    }

    fn variant_value(&mut self, v: VariantId) -> ValueRef {
        let Some(sum) = self.hir.variant_owner(v) else {
            return ValueRef::Error;
        };
        if self.idx.is_generic(sum) {
            return ValueRef::Error;
        }
        match self.hir.variant(v).map(|x| x.shape) {
            Some(Shape::Tuple) => ValueRef::VariantCtor(v),
            Some(Shape::Unit) => ValueRef::Typed(self.adt_type(sum)),
            // A variant with named fields is built by a record literal; as a
            // bare value it is not one.
            _ => ValueRef::Error,
        }
    }

    /// The type a value path has.
    pub(crate) fn value_type(&mut self, r: ValueRef) -> Result<TypeId, CheckError> {
        Ok(match r {
            ValueRef::Local(b) => match self.binder_type(b) {
                Some(t) => t,
                None => {
                    // A binder with no binding site seen yet (or never
                    // bound): a fresh variable, inferred from its uses.
                    let v = self.fresh(crate::infer::GENERAL);
                    if let Some(slot) = self.binder_ty.get_mut(b.index()) {
                        *slot = v.raw();
                    }
                    v
                }
            },
            ValueRef::Fn(i) => match self.sig(i)? {
                Some(s) => self.fn_value_type(s),
                None => TypeId::ERROR,
            },
            ValueRef::Decl(i) => self.decl_type(i)?,
            ValueRef::RecordCtor(i) => {
                let fields = self.record_field_ids(i);
                let result = self.adt_type(i);
                self.ctor_type(&fields, result)?
            }
            ValueRef::VariantCtor(v) => {
                let fields: Vec<_> = self
                    .hir
                    .variant(v)
                    .map(|x| self.hir.list(x.fields).to_vec())
                    .unwrap_or_default();
                let result = self
                    .hir
                    .variant_owner(v)
                    .map_or(TypeId::ERROR, |s| self.adt_type(s));
                self.ctor_type(&fields, result)?
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

    fn ctor_type(
        &mut self,
        fields: &[hir_lang::FieldId],
        result: TypeId,
    ) -> Result<TypeId, CheckError> {
        let mut params = Vec::with_capacity(fields.len());
        for &f in fields {
            params.push(self.field_type(f)?);
        }
        Ok(self.types.func(&params, result, hir_lang::Effects::NONE))
    }

    /// Resolves the unresolved tail of a partial path by type.
    fn path_tail(&mut self, p: PathId, at: NodeRef) -> Result<ValueRef, CheckError> {
        let path = *self.hir.path(p);
        if path.qself.is_some() {
            self.report(at, unsupported(Feature::Traits));
            return Ok(ValueRef::Error);
        }
        if path.unresolved > 1 {
            self.report(at, unsupported(Feature::AssociatedTypes));
            return Ok(ValueRef::Error);
        }
        let segments = self.hir.list(path.segments);
        let Some(&last) = segments.last() else {
            return Ok(ValueRef::Error);
        };
        if !last.args.is_empty() {
            self.report(at, unsupported(Feature::Generics));
            return Ok(ValueRef::Error);
        }
        let prefix_len = segments.len().saturating_sub(1);
        let Some(owner) = self.prefix_type(&path, prefix_len, at)? else {
            return Ok(ValueRef::Error);
        };
        let owner = self.resolve(owner);
        let name = last.name.sym;
        if let Type::Adt(item) = self.types.get(owner) {
            if matches!(self.item_kind(item), ItemKind::Sum(_)) {
                if let Some(v) = self.idx.variant_named(item, name) {
                    self.record_path_def(p, Def::Variant(v));
                    return Ok(self.variant_value(v));
                }
            }
        }
        match self.member(owner, name, at)? {
            Some(MemberRef::Item(m)) => {
                self.record_path_def(p, Def::Item(m));
                Ok(match self.item_kind(m) {
                    ItemKind::Fn(_) if self.idx.is_generic(m) => ValueRef::Error,
                    ItemKind::Fn(_) => ValueRef::Fn(m),
                    _ => ValueRef::Decl(m),
                })
            }
            Some(MemberRef::Host(t)) => Ok(ValueRef::Typed(t)),
            None => Ok(ValueRef::Error),
        }
    }

    /// The type the resolved prefix of a partial path names.
    fn prefix_type(
        &mut self,
        path: &hir_lang::Path,
        prefix_len: usize,
        at: NodeRef,
    ) -> Result<Option<TypeId>, CheckError> {
        if prefix_len == 0 {
            return Ok(match path.root {
                PathRoot::SelfType | PathRoot::StaticType => self.cur_self,
                PathRoot::ParentType => self.cur_parent(),
                _ => None,
            });
        }
        Ok(match path.res {
            Res::Def(d) if d.unit() == self.hir.unit() => match d.def() {
                Def::Item(i) => match self.item_kind(i) {
                    ItemKind::Record(_) | ItemKind::Sum(_) | ItemKind::Class(_) => {
                        if self.idx.is_generic(i) {
                            None
                        } else {
                            Some(self.adt_type(i))
                        }
                    }
                    ItemKind::Alias { ty, .. } if !self.idx.is_generic(i) => {
                        let self_ty = self.item_self(i);
                        Some(self.lower_ty(ty, self_ty, true)?)
                    }
                    ItemKind::Interface(_) => {
                        self.report(at, unsupported(Feature::Traits));
                        None
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
            Res::Local(_) => {
                // `T::new` on a type parameter needs trait bounds.
                self.report(at, unsupported(Feature::Traits));
                None
            }
            Res::Unresolved => {
                self.report(at, DiagnosticKind::Unresolved);
                None
            }
            Res::Err => None,
        })
    }

    /// The first base class of the current class (`parent::`).
    fn cur_parent(&mut self) -> Option<TypeId> {
        let t = self.cur_self?;
        let Type::Adt(class) = self.types.get(self.resolve(t)) else {
            return None;
        };
        let base = *self.idx.bases_of(class).first()?;
        Some(self.adt_type(base))
    }

    /// Looks up a member (method, associated function, constant) of a type,
    /// walking base classes in order. Reports `NoMethod` or
    /// `AmbiguousMethod` at `at` (`NoMethod` only when the type's members
    /// are complete); `None` after reporting.
    pub(crate) fn member(
        &mut self,
        owner: TypeId,
        name: Symbol,
        at: NodeRef,
    ) -> Result<Option<MemberRef>, CheckError> {
        Ok(match self.member_lookup(owner, name)? {
            Lookup::Found(m) => Some(m),
            Lookup::Ambiguous => {
                let ty = self.resolve(owner);
                self.report(at, DiagnosticKind::AmbiguousMethod { ty, name });
                None
            }
            Lookup::NotFound { incomplete } => {
                if !incomplete {
                    let ty = self.resolve(owner);
                    self.report(at, DiagnosticKind::NoMethod { ty, name });
                }
                None
            }
        })
    }

    /// [`member`](Self::member) without reporting.
    pub(crate) fn member_lookup(
        &mut self,
        owner: TypeId,
        name: Symbol,
    ) -> Result<Lookup, CheckError> {
        let owner = self.resolve(owner);
        if self.types.node(owner).tag == Tag::Error {
            return Ok(Lookup::NotFound { incomplete: true });
        }
        let mut incomplete = false;
        self.new_visit();
        let mut queue: Vec<TypeId> = alloc::vec![owner];
        let mut qi = 0;
        while let Some(&t) = queue.get(qi) {
            qi += 1;
            self.meter.tick(1)?;
            let found = self.idx.members_named(t, name);
            if !found.is_empty() {
                let mut inherent = found.iter().filter(|m| !m.via_interface);
                let pick = match (inherent.next(), inherent.next(), found) {
                    (Some(one), None, _) => Some(one.item),
                    (None, _, [one]) => Some(one.item),
                    _ => None,
                };
                return Ok(match pick {
                    Some(m) => Lookup::Found(MemberRef::Item(m)),
                    None => Lookup::Ambiguous,
                });
            }
            if let Some(h) = self.host_member(t, name) {
                return Ok(Lookup::Found(MemberRef::Host(h)));
            }
            if let Type::Adt(item) = self.types.get(t) {
                if !self.visit(item) {
                    continue;
                }
                incomplete |= self.idx.is_incomplete(item);
                let bases = self.idx.bases_of(item).to_vec();
                for base in bases {
                    let bt = self.adt_type(base);
                    queue.push(bt);
                }
            }
        }
        Ok(Lookup::NotFound { incomplete })
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
                    _ if self.idx.is_generic(i) => None,
                    ItemKind::Record(_) | ItemKind::Class(_) => Some(RecordRef::Item(i)),
                    ItemKind::Alias { ty, .. } => {
                        let self_ty = self.item_self(i);
                        let t = self.lower_ty(ty, self_ty, true)?;
                        match self.types.get(self.resolve(t)) {
                            Type::Adt(r)
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
                Def::Variant(v) => {
                    let generic = self
                        .hir
                        .variant_owner(v)
                        .is_some_and(|s| self.idx.is_generic(s));
                    (!generic).then_some(RecordRef::Variant(v))
                }
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

    /// The nominal type a record reference constructs.
    pub(crate) fn record_ref_type(&mut self, r: RecordRef) -> TypeId {
        match r {
            RecordRef::Item(i) => self.adt_type(i),
            RecordRef::Variant(v) => self
                .hir
                .variant_owner(v)
                .map_or(TypeId::ERROR, |s| self.adt_type(s)),
        }
    }
}

fn unsupported(feature: Feature) -> DiagnosticKind {
    DiagnosticKind::Unsupported { feature }
}
