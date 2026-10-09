//! The pre-pass: one walk over the live tree, then the lookup tables every
//! later phase uses (all sorted vectors searched by binary search, so no
//! lookup is linear in a declaration's size).

use alloc::vec::Vec;

use hir_lang::{
    Bound, Control, Event, ExprId, FieldId, GenericArg, IdKind, Item, ItemId, ItemKind, NodeRef,
    PatId, Shape, Symbol, Ty, TyId, VariantId,
};

use super::Ctx;
use crate::{
    diag::DiagnosticKind,
    error::CheckError,
    typed::NONE,
    types::{Field, Tag, TypeId},
};

/// What a member-table entry names.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct MemberEntry {
    /// The owning type (an impl's self type, a class, an interface's `Self`).
    pub(crate) owner: TypeId,
    pub(crate) name: Symbol,
    /// The function, constant, or alias item.
    pub(crate) item: ItemId,
    /// Declared in an interface implementation rather than inherently.
    pub(crate) via_interface: bool,
}

/// Where a field lives: a record or class item, or a sum variant.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum FieldOwner {
    Item(u32),
    Variant(u32),
}

#[derive(Debug, Default)]
pub(crate) struct Index {
    /// Live items in preorder.
    pub(crate) items: Vec<ItemId>,
    /// Per item: the enclosing item (`NONE` for the root).
    pub(crate) owner: Vec<u32>,
    /// Per item: declares generic parameters, or sits inside an item that
    /// does.
    pub(crate) generic: Vec<bool>,
    /// Live expressions and patterns, in preorder.
    pub(crate) exprs: Vec<ExprId>,
    pub(crate) pats: Vec<PatId>,
    /// Members of nominal types, sorted by (owner, name).
    pub(crate) members: Vec<MemberEntry>,
    /// Variants of sums, sorted by (sum item, name).
    pub(crate) variants: Vec<(u32, Symbol, VariantId)>,
    /// Fields by (owner, name), with their position and id.
    pub(crate) fields: Vec<(FieldOwner, Symbol, u32, FieldId)>,
    /// Per field: the item that owns it (the sum, for variant fields).
    pub(crate) field_owner: Vec<u32>,
    /// Per class item: its base classes, a range of `base_pool` (and of
    /// `base_type_pool`, their types in the class's placeholders).
    pub(crate) bases: Vec<(u32, u32)>,
    pub(crate) base_pool: Vec<ItemId>,
    pub(crate) base_type_pool: Vec<TypeId>,
    /// Per item: members may be missing from the tables (a class using a
    /// mixin, which resolve-lang expands), so a failed lookup is silent.
    pub(crate) incomplete: Vec<bool>,
    /// Per item: its `Self` type, once computed (`NONE`: none or unknown).
    pub(crate) self_ty: Vec<u32>,
}

impl Index {
    pub(crate) fn owner_of(&self, item: ItemId) -> Option<ItemId> {
        self.owner
            .get(item.index())
            .copied()
            .filter(|&o| o != NONE)
            .and_then(|o| ItemId::from_index(o as usize))
    }

    pub(crate) fn is_generic(&self, item: ItemId) -> bool {
        self.generic.get(item.index()).copied().unwrap_or(false)
    }

    pub(crate) fn is_incomplete(&self, item: ItemId) -> bool {
        self.incomplete.get(item.index()).copied().unwrap_or(false)
    }

    /// The members named `name` of `owner`.
    pub(crate) fn members_named(&self, owner: TypeId, name: Symbol) -> &[MemberEntry] {
        let key = (owner, name);
        let lo = self.members.partition_point(|m| (m.owner, m.name) < key);
        let hi = self.members.partition_point(|m| (m.owner, m.name) <= key);
        self.members.get(lo..hi).unwrap_or(&[])
    }

    pub(crate) fn variant_named(&self, sum: ItemId, name: Symbol) -> Option<VariantId> {
        let key = (u32::try_from(sum.index()).unwrap_or(NONE), name);
        self.variants
            .binary_search_by(|&(s, n, _)| (s, n).cmp(&key))
            .ok()
            .and_then(|i| self.variants.get(i))
            .map(|&(_, _, v)| v)
    }

    /// The position and id of field `name` of `owner`.
    pub(crate) fn field_named(&self, owner: FieldOwner, name: Symbol) -> Option<(u32, FieldId)> {
        self.fields
            .binary_search_by(|&(o, n, _, _)| (o, n).cmp(&(owner, name)))
            .ok()
            .and_then(|i| self.fields.get(i))
            .map(|&(_, _, pos, id)| (pos, id))
    }

    pub(crate) fn bases_of(&self, class: ItemId) -> &[ItemId] {
        let Some(&(start, len)) = self.bases.get(class.index()) else {
            return &[];
        };
        self.base_pool
            .get(start as usize..(start as usize).saturating_add(len as usize))
            .unwrap_or(&[])
    }

    /// The base classes' types, in the class's placeholders.
    pub(crate) fn base_types_of(&self, class: ItemId) -> &[TypeId] {
        let Some(&(start, len)) = self.bases.get(class.index()) else {
            return &[];
        };
        self.base_type_pool
            .get(start as usize..(start as usize).saturating_add(len as usize))
            .unwrap_or(&[])
    }
}

impl Ctx<'_> {
    pub(crate) fn build_index(&mut self) -> Result<(), CheckError> {
        self.walk_live()?;
        let items = core::mem::take(&mut self.idx.items);
        if self.profile.is_static() {
            for &item in &items {
                self.collect_impl_tys(item)?;
            }
            self.impl_tys.sort_by_key(|&(t, o, _)| (o, t));
            self.impl_ty_index = self
                .impl_tys
                .iter()
                .enumerate()
                .map(|(k, &(t, _, _))| (t, u32::try_from(k).unwrap_or(NONE)))
                .collect();
            self.impl_ty_index.sort_unstable();
        }
        for &item in &items {
            self.meter.tick(1)?;
            self.index_item(item)?;
        }
        self.idx.members.sort_by_key(|m| (m.owner, m.name, m.item));
        self.idx.variants.sort_unstable();
        self.idx.fields.sort_unstable();
        if self.profile.is_static() {
            // Interfaces first (their member tables answer associated-type
            // bindings in impl headers), then implementations.
            for &item in &items {
                if matches!(self.item_kind(item), ItemKind::Interface(_)) {
                    self.meter.tick(1)?;
                    self.index_impls(item)?;
                }
            }
            self.tr
                .iface_members
                .sort_unstable_by_key(|&(r, n, i)| (r, n, i));
            self.finish_trait_index();
        }
        self.idx.items = items;
        self.index_bases()?;
        if self.profile.is_static() {
            let items = core::mem::take(&mut self.idx.items);
            for &item in &items {
                if matches!(self.item_kind(item), ItemKind::Impl(_) | ItemKind::Class(_)) {
                    self.meter.tick(1)?;
                    self.index_impls(item)?;
                }
            }
            self.idx.items = items;
            self.finish_trait_index();
        }
        self.index_record_shapes()?;
        if self.profile.is_static() {
            self.check_coherence()?;
        }
        Ok(())
    }

    /// Records the `impl Trait` type nodes of a function's signature: in a
    /// parameter type, an anonymous generic parameter; in the result type,
    /// an opaque type.
    fn collect_impl_tys(&mut self, item: ItemId) -> Result<(), CheckError> {
        let ItemKind::Fn(def) = self.item_kind(item) else {
            return Ok(());
        };
        let hir = self.hir;
        let mut roots: Vec<(TyId, bool)> = hir
            .list(def.params)
            .iter()
            .filter_map(|&p| hir.param(p).ty)
            .map(|t| (t, false))
            .collect();
        if let Some(r) = def.ret {
            roots.push((r, true));
        }
        for (root, rpit) in roots {
            let mut stack = alloc::vec![root];
            while let Some(t) = stack.pop() {
                self.meter.tick(1)?;
                let node = *hir.ty(t);
                if let Ty::Impl(_) = node {
                    self.impl_tys.push((t, item, rpit));
                    continue;
                }
                type_children_all(&node, hir, &mut stack);
            }
        }
        Ok(())
    }

    /// Collects the live nodes and the item tree.
    fn walk_live(&mut self) -> Result<(), CheckError> {
        let hir = self.hir;
        let n_items = hir.count(IdKind::Item);
        let idx = &mut self.idx;
        idx.owner = alloc::vec![NONE; n_items];
        idx.generic = alloc::vec![false; n_items];
        idx.incomplete = alloc::vec![false; n_items];
        idx.self_ty = alloc::vec![NONE; n_items];
        idx.bases = alloc::vec![(0, 0); n_items];
        idx.field_owner = alloc::vec![NONE; hir.count(IdKind::Field)];
        // One walk: live nodes in preorder, and the size of each item's own
        // part (nodes not inside a nested item), for the plan.
        let mut steps = 0u64;
        let sizes = &mut self.item_size;
        let mut open: Vec<ItemId> = Vec::new();
        hir.walk_from(NodeRef::Item(hir.root()), |event| {
            match event {
                Event::Enter(node) => {
                    steps += 1;
                    if let Some(&top) = open.last() {
                        if let Some(n) = sizes.get_mut(top.index()) {
                            *n = n.saturating_add(1);
                        }
                    }
                    match node {
                        NodeRef::Item(i) => {
                            idx.items.push(i);
                            open.push(i);
                        }
                        NodeRef::Expr(e) => idx.exprs.push(e),
                        NodeRef::Pat(p) => idx.pats.push(p),
                        _ => {}
                    }
                }
                Event::Leave(NodeRef::Item(_)) => {
                    let _ = open.pop();
                }
                _ => {}
            }
            Control::Continue
        });
        // Members see their owner's generic parameters (and `Self`).
        for &i in &idx.items {
            let members = match hir.item(i).kind {
                ItemKind::Module { items, .. } => items,
                ItemKind::Class(d) => d.items,
                ItemKind::Interface(d) => d.items,
                ItemKind::Impl(d) => d.items,
                _ => continue,
            };
            let raw = u32::try_from(i.index()).unwrap_or(NONE);
            for &m in hir.list(members) {
                if let Some(slot) = idx.owner.get_mut(m.index()) {
                    *slot = raw;
                }
            }
        }
        // Preorder visits owners before members, so one pass suffices.
        for &i in &idx.items {
            let own = item_generics_nonempty(hir.item(i));
            let inherited = idx
                .owner
                .get(i.index())
                .copied()
                .filter(|&o| o != NONE)
                .and_then(|o| ItemId::from_index(o as usize))
                .is_some_and(|o| {
                    is_member_owner(hir.item(o))
                        && idx.generic.get(o.index()).copied().unwrap_or(false)
                });
            if let Some(slot) = idx.generic.get_mut(i.index()) {
                *slot = own || inherited;
            }
        }
        self.meter.tick(steps)
    }

    fn index_item(&mut self, item: ItemId) -> Result<(), CheckError> {
        let it = *self.hir.item(item);
        let raw = u32::try_from(item.index()).unwrap_or(NONE);
        match it.kind {
            ItemKind::Record(def) => {
                self.name_item(item);
                for (pos, &f) in self.hir.list(def.fields).iter().enumerate() {
                    self.add_field(FieldOwner::Item(raw), raw, pos, f, def.shape);
                }
            }
            ItemKind::Sum(def) => {
                self.name_item(item);
                for &v in self.hir.list(def.variants) {
                    let Some(variant) = self.hir.variant(v).copied() else {
                        continue;
                    };
                    self.idx.variants.push((raw, variant.name.sym, v));
                    let vraw = u32::try_from(v.index()).unwrap_or(NONE);
                    for (pos, &f) in self.hir.list(variant.fields).iter().enumerate() {
                        self.add_field(FieldOwner::Variant(vraw), raw, pos, f, variant.shape);
                    }
                }
            }
            ItemKind::Class(def) => {
                self.name_item(item);
                for (pos, &f) in self.hir.list(def.fields).iter().enumerate() {
                    self.add_field(FieldOwner::Item(raw), raw, pos, f, Shape::Named);
                }
                let owner = if self.profile.is_static() {
                    self.adt_identity(item)
                } else {
                    self.types.adt(item)
                };
                self.set_self(item, owner);
                for &m in self.hir.list(def.items) {
                    if matches!(self.item_kind(m), ItemKind::MixinUse(_)) {
                        // Mixed-in members arrive when resolve-lang expands
                        // the use; until then lookups on this class are
                        // silent rather than wrong.
                        self.mark_incomplete(item);
                    }
                    self.add_member(owner, m, false);
                }
            }
            ItemKind::Interface(_) => {
                let owner = self.types.self_of(item);
                self.set_self(item, owner);
            }
            ItemKind::Impl(def) if !self.profile.is_static() => {
                // Nothing is lowered under `Dynamic`; impls on a named
                // declaration are indexed for path tails. (Static profiles
                // index every impl in the trait index.)
                if let Some(head) = self.ty_head_item(def.self_ty) {
                    let owner = self.types.adt(head);
                    self.set_self(item, owner);
                    let via_interface = def.interface.is_some();
                    for &m in self.hir.list(def.items) {
                        self.add_member(owner, m, via_interface);
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }

    /// The item a type annotation's path names, if it names one directly.
    fn ty_head_item(&self, ty: hir_lang::TyId) -> Option<ItemId> {
        let Ty::Path(p) = *self.hir.ty(ty) else {
            return None;
        };
        match self.hir.path(p).res {
            hir_lang::Res::Def(d) if d.unit() == self.hir.unit() => match d.def() {
                hir_lang::Def::Item(i) => Some(i),
                hir_lang::Def::Variant(_) => None,
            },
            _ => None,
        }
    }

    fn mark_incomplete(&mut self, item: ItemId) {
        if let Some(slot) = self.idx.incomplete.get_mut(item.index()) {
            *slot = true;
        }
    }

    fn set_self(&mut self, item: ItemId, ty: TypeId) {
        if let Some(slot) = self.idx.self_ty.get_mut(item.index()) {
            *slot = ty.raw();
        }
    }

    fn add_member(&mut self, owner: TypeId, member: ItemId, via_interface: bool) {
        let it = self.hir.item(member);
        let Some(name) = it.name else { return };
        if matches!(
            it.kind,
            ItemKind::Fn(_) | ItemKind::Const { .. } | ItemKind::Global { .. }
        ) {
            self.idx.members.push(MemberEntry {
                owner,
                name: name.sym,
                item: member,
                via_interface,
            });
        }
    }

    fn add_field(&mut self, owner: FieldOwner, item: u32, pos: usize, f: FieldId, shape: Shape) {
        if let Some(slot) = self.idx.field_owner.get_mut(f.index()) {
            *slot = item;
        }
        let pos = u32::try_from(pos).unwrap_or(NONE);
        if shape == Shape::Named {
            if let Some(name) = self.hir.field(f).name {
                self.idx.fields.push((owner, name.sym, pos, f));
            }
        }
    }

    /// Lowers each class's base list and breaks inheritance cycles.
    fn index_bases(&mut self) -> Result<(), CheckError> {
        let items = core::mem::take(&mut self.idx.items);
        for &item in &items {
            let ItemKind::Class(def) = self.item_kind(item) else {
                continue;
            };
            let start = u32::try_from(self.idx.base_pool.len()).unwrap_or(NONE);
            let mut len = 0u32;
            for &b in self.hir.list(def.bases) {
                self.meter.tick(1)?;
                let t = if self.profile.is_static() {
                    let saved = self.lower_ctx.replace(item);
                    let t = self.lower_ty(b, None, true);
                    self.lower_ctx = saved;
                    t?
                } else {
                    self.ty_head_item(b)
                        .map_or(TypeId::ERROR, |i| self.types.adt(i))
                };
                let t = self.resolve(t);
                let n = self.types.node(t);
                let base = (n.tag == Tag::Adt)
                    .then(|| ItemId::from_index(n.x as usize))
                    .flatten()
                    .filter(|&i| matches!(self.item_kind(i), ItemKind::Class(_)));
                match base {
                    Some(base) => {
                        self.idx.base_pool.push(base);
                        self.idx.base_type_pool.push(t);
                        len += 1;
                    }
                    None if n.tag == Tag::Error => {}
                    None => self.report(NodeRef::Ty(b), DiagnosticKind::NotAType),
                }
            }
            if let Some(slot) = self.idx.bases.get_mut(item.index()) {
                *slot = (start, len);
            }
        }
        // Cycle detection: iterative DFS with colours (0 white, 1 grey,
        // 2 black). A back edge reports at its source class and cuts that
        // class's base list, so every later walk over bases terminates.
        let mut colour = alloc::vec![0u8; self.hir.count(IdKind::Item)];
        for &start in &items {
            if !matches!(self.item_kind(start), ItemKind::Class(_))
                || colour.get(start.index()).copied() != Some(0)
            {
                continue;
            }
            let mut stack: Vec<(ItemId, usize)> = alloc::vec![(start, 0)];
            if let Some(c) = colour.get_mut(start.index()) {
                *c = 1;
            }
            while let Some(&mut (node, ref mut next)) = stack.last_mut() {
                self.meter.tick(1)?;
                let bases = self.idx.bases_of(node);
                if let Some(&base) = bases.get(*next) {
                    *next += 1;
                    match colour.get(base.index()).copied() {
                        Some(0) => {
                            if let Some(c) = colour.get_mut(base.index()) {
                                *c = 1;
                            }
                            stack.push((base, 0));
                        }
                        Some(1) => {
                            self.report(NodeRef::Item(node), DiagnosticKind::InheritanceCycle);
                            if let Some(slot) = self.idx.bases.get_mut(node.index()) {
                                *slot = (0, 0);
                            }
                            // The base list is gone: finish this node.
                            if let Some(top) = stack.last_mut() {
                                top.1 = usize::MAX;
                            }
                        }
                        _ => {}
                    }
                } else {
                    if let Some(c) = colour.get_mut(node.index()) {
                        *c = 2;
                    }
                    let _ = stack.pop();
                }
            }
        }
        self.idx.items = items;
        Ok(())
    }

    /// Sorted field lists of named-field records: structural unification
    /// and record literals compare them.
    fn index_record_shapes(&mut self) -> Result<(), CheckError> {
        if !self.profile.is_static() {
            return Ok(());
        }
        let items = core::mem::take(&mut self.idx.items);
        for &item in &items {
            let ItemKind::Record(def) = self.item_kind(item) else {
                continue;
            };
            if def.shape != Shape::Named || def.is_union || self.is_generic_item(item) {
                continue;
            }
            let mut fields = Vec::new();
            for &f in self.hir.list(def.fields) {
                self.meter.tick(1)?;
                let Some(name) = self.hir.field(f).name else {
                    continue;
                };
                let ty = self.field_type(f)?;
                fields.push(Field { name: name.sym, ty });
            }
            fields.sort_by_key(|f| f.name);
            fields.dedup_by_key(|f| f.name);
            let start = u32::try_from(self.field_pool.len()).unwrap_or(NONE);
            let len = u32::try_from(fields.len()).unwrap_or(0);
            self.field_pool.extend_from_slice(&fields);
            if let Some(slot) = self.record_fields.get_mut(item.index()) {
                *slot = Some((start, len));
            }
        }
        self.idx.items = items;
        Ok(())
    }
}

fn item_generics_nonempty(item: &Item) -> bool {
    let g = match item.kind {
        ItemKind::Fn(d) => d.generics,
        ItemKind::Record(d) => d.generics,
        ItemKind::Sum(d) => d.generics,
        ItemKind::Class(d) => d.generics,
        ItemKind::Interface(d) => d.generics,
        ItemKind::Impl(d) => d.generics,
        ItemKind::Alias { generics, .. } => generics,
        _ => return false,
    };
    !g.params.is_empty()
}

/// Items whose generic parameters are visible to their members.
fn is_member_owner(item: &Item) -> bool {
    matches!(
        item.kind,
        ItemKind::Impl(_) | ItemKind::Class(_) | ItemKind::Interface(_)
    )
}

/// The type children of a type node, including the types inside a path's
/// generic arguments and a bound list's interface paths.
pub(crate) fn type_children_all(node: &Ty, hir: &hir_lang::Hir, out: &mut Vec<TyId>) {
    let path_args = |p: hir_lang::PathId, out: &mut Vec<TyId>| {
        let path = hir.path(p);
        if let Some(q) = path.qself {
            out.push(q.ty);
        }
        for seg in hir.list(path.segments) {
            for a in hir.list(seg.args) {
                match *a {
                    GenericArg::Ty(t) | GenericArg::Binding { ty: t, .. } => out.push(t),
                    GenericArg::Constraint { bounds, .. } => {
                        out.extend(hir.list(bounds).iter().filter_map(|b| match *b {
                            Bound::Ty(t) => Some(t),
                            Bound::Region(_) => None,
                        }));
                    }
                    _ => {}
                }
            }
        }
    };
    match *node {
        Ty::Tuple(list) | Ty::Union(list) | Ty::Intersection(list) => {
            out.extend_from_slice(hir.list(list));
        }
        Ty::Array { elem, .. } => out.push(elem),
        Ty::Slice(t) | Ty::Ref { inner: t, .. } | Ty::Ptr { inner: t, .. } | Ty::Nullable(t) => {
            out.push(t);
        }
        Ty::Fn {
            params,
            ret,
            throws,
            ..
        } => {
            out.extend_from_slice(hir.list(params));
            out.push(ret);
            out.extend(throws);
        }
        Ty::Path(p) => path_args(p, out),
        Ty::Object(bounds) | Ty::Impl(bounds) => {
            out.extend(hir.list(bounds).iter().filter_map(|b| match *b {
                Bound::Ty(t) => Some(t),
                Bound::Region(_) => None,
            }));
        }
        _ => {}
    }
}
