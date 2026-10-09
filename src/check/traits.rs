//! Interfaces (traits): the impl index, obligations and their solver,
//! associated-type normalization, member lookup, coherence, and
//! conformance.
//!
//! **Index.** Every `impl` block, and every class (its own members and each
//! interface it declares), is an *implementation record*: a self type, an
//! optional interface reference, and members. Records are indexed by the
//! head of their self type (`Vec`, `i32`, a tuple of three, a reference...)
//! with a separate bucket for blanket impls (`impl<T> Show for T`), so a
//! lookup only tests the records that could match; a generic record matches
//! by unifying its self type, instantiated with fresh variables, with the
//! type at hand, inside a snapshot that is rolled back (ISSUES P17: generic
//! impls are indexed, so member lookups on generic types are never silently
//! skipped).
//!
//! **Obligations.** `T: Iface<A>` and `<T as Iface<A>>::Item == U` goals are
//! queued where they arise (instantiating a generic item, coercing to `dyn`,
//! returning an `impl Trait`) and solved when their self type is known:
//! placeholders by the bounds in scope (with supertraits), everything else
//! by selecting the one matching record, whose own bounds become nested
//! goals. Nesting is capped by [`Budget::trait_depth`](crate::Budget), so a
//! cyclic or ever-growing resolution is a budget error, never a hang.
//!
//! **Coherence.** Two impls of one interface whose heads unify overlap: the
//! later one is reported (selection would otherwise be ambiguous). Orphan
//! rules are a property of crates, which a unit does not see; they are not
//! checked here.

use alloc::vec::Vec;

use hir_lang::{ItemId, ItemKind, NodeRef, Symbol};

use super::Ctx;
use crate::{
    diag::DiagnosticKind,
    error::{CheckError, Limit},
    infer::GENERAL,
    typed::NONE,
    types::{Tag, Type, TypeId},
};

/// The head of a self type: what a value's type must start with for a
/// record to apply. `BLANKET` is the bucket of records whose self type is a
/// placeholder.
pub(crate) type HeadKey = (u8, u32, u32);

/// Associated-type bindings: (associated type, value).
pub(crate) type Bindings = Vec<(ItemId, TypeId)>;
pub(crate) const BLANKET: HeadKey = (u8::MAX, 0, 0);

/// One implementation record.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ImplRec {
    /// The `impl` item, or the class.
    pub(crate) item: ItemId,
    /// The implementing type, in the record's placeholders.
    pub(crate) self_ty: TypeId,
    /// The implemented interface (a `Trait` node); `None` for inherent
    /// members.
    pub(crate) tr: Option<TypeId>,
    /// A class's declaration of an interface: the class's own members
    /// implement it (they are found through the class's inherent record).
    pub(crate) class_decl: bool,
}

#[derive(Debug, Default)]
pub(crate) struct TraitIndex {
    pub(crate) recs: Vec<ImplRec>,
    /// (interface, head, record), sorted.
    pub(crate) by_trait: Vec<(u32, HeadKey, u32)>,
    /// (head, record) of interface records, sorted.
    pub(crate) trait_by_head: Vec<(HeadKey, u32)>,
    /// (head, record) of inherent records, sorted.
    pub(crate) inherent: Vec<(HeadKey, u32)>,
    /// Record members: (record, name, item), sorted.
    pub(crate) members: Vec<(u32, Symbol, ItemId)>,
    /// Interface members (functions, constants, associated types):
    /// (interface, name, item), sorted.
    pub(crate) iface_members: Vec<(u32, Symbol, ItemId)>,
    /// Per item: its supertraits, an index into `super_lists` (`NONE`:
    /// not computed, `BUSY`: being computed).
    pub(crate) supers_memo: Vec<u32>,
    pub(crate) super_lists: Vec<Vec<TypeId>>,
    /// Every live interface, in preorder.
    pub(crate) ifaces: Vec<ItemId>,
}

const BUSY: u32 = u32::MAX - 1;

fn bucket<K: Ord + Copy, V: Copy>(table: &[(K, V)], key: K) -> impl Iterator<Item = V> + '_ {
    let lo = table.partition_point(|&(k, _)| k < key);
    let hi = table.partition_point(|&(k, _)| k <= key);
    table.get(lo..hi).unwrap_or(&[]).iter().map(|&(_, v)| v)
}

/// A pending goal.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Goal {
    /// `ty` implements `tr`.
    Impl { ty: TypeId, tr: TypeId },
    /// `<ty as tr>::assoc` is `out`.
    Project {
        ty: TypeId,
        tr: TypeId,
        assoc: ItemId,
        out: TypeId,
    },
}

/// A goal, where it arose, the item whose bounds are in scope there, and how
/// deep in nested resolution it is.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Obligation {
    pub(crate) goal: Goal,
    pub(crate) at: NodeRef,
    pub(crate) env: Option<ItemId>,
    pub(crate) depth: u32,
}

/// The outcome of one solving attempt.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Step {
    Done,
    Stuck,
}

/// What a member lookup found.
#[derive(Clone, Debug)]
pub(crate) enum Pick {
    /// A member of an implementation record; `inst` instantiates the
    /// record's placeholders (unified with the looked-up type).
    Rec { member: ItemId, inst: Vec<TypeId> },
    /// An interface's member used through a record that does not override
    /// it (a default method, a default constant), or through a bound.
    Iface {
        member: ItemId,
        self_ty: TypeId,
        tr_args: Vec<TypeId>,
        dynamic: bool,
    },
    /// A host-declared member.
    Host(TypeId),
}

/// The outcome of a member lookup.
#[derive(Clone, Debug)]
pub(crate) enum MemberLookup {
    Found(Pick),
    Ambiguous,
    NotFound { incomplete: bool },
}

impl Ctx<'_> {
    // ------------------------------------------------------------- heads

    /// The head of `t` (`None` for variables, placeholders, projections,
    /// opaque types, and `{error}`).
    pub(crate) fn head_of(&self, t: TypeId) -> Option<HeadKey> {
        let r = self.resolve(t);
        let n = self.types.node(r);
        let k = |c: u8, a: u32, b: u32| Some((c, a, b));
        match n.tag {
            Tag::Adt => k(1, n.x, 0),
            Tag::Foreign => k(2, n.x, n.y.wrapping_mul(2).wrapping_add(u32::from(n.small))),
            Tag::Extern => k(3, n.x, 0),
            Tag::Prim => k(4, u32::from(n.small), 0),
            Tag::Tuple => k(5, n.len, 0),
            Tag::Array => k(6, 0, 0),
            Tag::Slice => k(7, 0, 0),
            Tag::Ref => k(8, u32::from(n.small), 0),
            Tag::Ptr => k(9, u32::from(n.small), 0),
            Tag::Fn => k(10, n.len, u32::from(n.small)),
            Tag::Nullable => k(11, 0, 0),
            Tag::Map => k(12, 0, 0),
            Tag::Record => k(13, 0, 0),
            Tag::Dyn => k(14, 0, 0),
            Tag::Never => k(15, 0, 0),
            Tag::Null => k(16, 0, 0),
            Tag::Any => k(17, 0, 0),
            Tag::Union => k(18, n.len, 0),
            Tag::Inter => k(19, n.len, 0),
            Tag::Async => k(20, 0, 0),
            Tag::Task => k(21, 0, 0),
            Tag::Gen => k(22, 0, 0),
            Tag::AsyncGen => k(23, 0, 0),
            Tag::Trait | Tag::Const => k(24, n.x, 0),
            Tag::Error
            | Tag::Var
            | Tag::Param
            | Tag::ImplParam
            | Tag::SelfOf
            | Tag::Proj
            | Tag::Opaque => None,
        }
    }

    // ------------------------------------------------------------- index

    /// Registers the implementation records of `item` (an impl or a class).
    /// Called once per live item by the index pass, static profiles only.
    pub(crate) fn index_impls(&mut self, item: ItemId) -> Result<(), CheckError> {
        let hir = self.hir;
        match self.item_kind(item) {
            ItemKind::Impl(def) => {
                let saved = self.lower_ctx.replace(item);
                let self_ty = self.lower_ty(def.self_ty, None, true);
                self.lower_ctx = saved;
                let self_ty = self.resolve(self_ty?);
                self.set_self_ty(item, self_ty);
                if self.is_err(self_ty) {
                    return Ok(());
                }
                let tr = match def.interface {
                    Some(t) => {
                        let saved = self.lower_ctx.replace(item);
                        let lb = self.lower_bound(t, self_ty);
                        self.lower_ctx = saved;
                        match lb? {
                            Some(lb) => Some(lb.tr),
                            // Reported; the members are still checked.
                            None => return Ok(()),
                        }
                    }
                    None => None,
                };
                let rec = self.add_rec(ImplRec {
                    item,
                    self_ty,
                    tr,
                    class_decl: false,
                });
                for &m in hir.list(def.items) {
                    self.add_rec_member(rec, m);
                }
            }
            ItemKind::Class(def) => {
                let self_ty = self.adt_identity(item);
                self.set_self_ty(item, self_ty);
                let rec = self.add_rec(ImplRec {
                    item,
                    self_ty,
                    tr: None,
                    class_decl: false,
                });
                for &m in hir.list(def.items) {
                    self.add_rec_member(rec, m);
                }
                for &i in hir.list(def.interfaces) {
                    let saved = self.lower_ctx.replace(item);
                    let lb = self.lower_bound(i, self_ty);
                    self.lower_ctx = saved;
                    if let Some(lb) = lb? {
                        let _ = self.add_rec(ImplRec {
                            item,
                            self_ty,
                            tr: Some(lb.tr),
                            class_decl: true,
                        });
                    }
                }
            }
            ItemKind::Interface(def) => {
                let s = self.types.self_of(item);
                self.set_self_ty(item, s);
                self.name_item(item);
                self.tr.ifaces.push(item);
                let raw = u32::try_from(item.index()).unwrap_or(NONE);
                for &m in hir.list(def.items) {
                    if let Some(name) = self.hir.get_item(m).and_then(|it| it.name) {
                        if matches!(
                            self.item_kind(m),
                            ItemKind::Fn(_) | ItemKind::Const { .. } | ItemKind::AssocType { .. }
                        ) {
                            self.tr.iface_members.push((raw, name.sym, m));
                        }
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn set_self_ty(&mut self, item: ItemId, ty: TypeId) {
        if let Some(slot) = self.idx.self_ty.get_mut(item.index()) {
            *slot = ty.raw();
        }
    }

    fn add_rec(&mut self, rec: ImplRec) -> u32 {
        let id = u32::try_from(self.tr.recs.len()).unwrap_or(NONE);
        let head = self.head_of(rec.self_ty).unwrap_or(BLANKET);
        match rec.tr {
            Some(tr) => {
                let iface = self.types.node(tr).x;
                self.tr.by_trait.push((iface, head, id));
                self.tr.trait_by_head.push((head, id));
            }
            None => self.tr.inherent.push((head, id)),
        }
        self.tr.recs.push(rec);
        id
    }

    fn add_rec_member(&mut self, rec: u32, m: ItemId) {
        let Some(name) = self.hir.get_item(m).and_then(|it| it.name) else {
            return;
        };
        if matches!(
            self.item_kind(m),
            ItemKind::Fn(_)
                | ItemKind::Const { .. }
                | ItemKind::Global { .. }
                | ItemKind::Alias { .. }
        ) {
            self.tr.members.push((rec, name.sym, m));
        }
    }

    /// Sorts the index tables once every record is registered.
    pub(crate) fn finish_trait_index(&mut self) {
        let t = &mut self.tr;
        t.by_trait.sort_unstable();
        t.trait_by_head.sort_unstable();
        t.inherent.sort_unstable();
        t.members.sort_unstable_by_key(|&(r, n, i)| (r, n, i));
        t.iface_members.sort_unstable_by_key(|&(r, n, i)| (r, n, i));
        t.supers_memo = alloc::vec![NONE; self.hir.count(hir_lang::IdKind::Item)];
    }

    /// The members of record `rec` named `name`.
    pub(crate) fn rec_members(&self, rec: u32, name: Symbol) -> Vec<ItemId> {
        let lo = self
            .tr
            .members
            .partition_point(|&(r, n, _)| (r, n) < (rec, name));
        let hi = self
            .tr
            .members
            .partition_point(|&(r, n, _)| (r, n) <= (rec, name));
        self.tr
            .members
            .get(lo..hi)
            .unwrap_or(&[])
            .iter()
            .map(|&(_, _, i)| i)
            .collect()
    }

    /// The member of interface `iface` itself named `name`.
    pub(crate) fn iface_member(&self, iface: ItemId, name: Symbol) -> Option<ItemId> {
        let key = (u32::try_from(iface.index()).unwrap_or(NONE), name);
        let lo = self
            .tr
            .iface_members
            .partition_point(|&(r, n, _)| (r, n) < key);
        self.tr
            .iface_members
            .get(lo)
            .filter(|&&(r, n, _)| (r, n) == key)
            .map(|&(_, _, i)| i)
    }

    /// The associated type named `name` of `iface` or one of its
    /// supertraits: (declaring interface, associated type).
    pub(crate) fn assoc_named(
        &mut self,
        iface: ItemId,
        name: Symbol,
    ) -> Result<Option<(ItemId, ItemId)>, CheckError> {
        let s = self.types.self_of(iface);
        let own = self.own_params(iface);
        let root = self.types.trait_ref(iface, &own);
        for tr in self.elaborate(root, s)? {
            let Some(i) = ItemId::from_index(self.types.node(tr).x as usize) else {
                continue;
            };
            if let Some(m) = self.iface_member(i, name) {
                if matches!(self.item_kind(m), ItemKind::AssocType { .. }) {
                    return Ok(Some((i, m)));
                }
            }
        }
        Ok(None)
    }

    /// The associated types of `iface` in declaration order.
    pub(crate) fn assoc_types(&self, iface: ItemId) -> Vec<ItemId> {
        match self.item_kind(iface) {
            ItemKind::Interface(d) => self
                .hir
                .list(d.items)
                .iter()
                .copied()
                .filter(|&m| matches!(self.item_kind(m), ItemKind::AssocType { .. }))
                .collect(),
            _ => Vec::new(),
        }
    }

    /// The direct supertraits of `iface` (in its placeholders).
    fn supers_of(&mut self, iface: ItemId) -> Result<Vec<TypeId>, CheckError> {
        if let Some(&v) = self.tr.supers_memo.get(iface.index()) {
            if v == BUSY {
                return Ok(Vec::new());
            }
            if v != NONE {
                return Ok(self
                    .tr
                    .super_lists
                    .get(v as usize)
                    .cloned()
                    .unwrap_or_default());
            }
        }
        let ItemKind::Interface(def) = self.item_kind(iface) else {
            return Ok(Vec::new());
        };
        if let Some(slot) = self.tr.supers_memo.get_mut(iface.index()) {
            *slot = BUSY;
        }
        let s = self.types.self_of(iface);
        let mut out = Vec::new();
        let saved = self.lower_ctx.replace(iface);
        let mut result = Ok(());
        for &t in self.hir.list(def.supers) {
            match self.lower_bound(t, s) {
                Ok(Some(lb)) => out.push(lb.tr),
                Ok(None) => {}
                Err(e) => {
                    result = Err(e);
                    break;
                }
            }
        }
        self.lower_ctx = saved;
        result?;
        let index = u32::try_from(self.tr.super_lists.len()).unwrap_or(NONE);
        self.tr.super_lists.push(out.clone());
        if let Some(slot) = self.tr.supers_memo.get_mut(iface.index()) {
            *slot = index;
        }
        Ok(out)
    }

    /// The generic arguments of an interface reference (without the
    /// associated-type slots a `dyn` reference carries).
    pub(crate) fn trait_args(&mut self, tr: TypeId) -> Vec<TypeId> {
        let n = self.types.node(tr);
        let Some(iface) = ItemId::from_index(n.x as usize) else {
            return Vec::new();
        };
        let explicit = {
            let pl = self.params_of(iface);
            self.plist(pl).explicit
        };
        let kids = self.types.kids(tr);
        kids.get(..explicit.min(kids.len())).unwrap_or(&[]).to_vec()
    }

    pub(crate) fn trait_item(&self, tr: TypeId) -> Option<ItemId> {
        let n = self.types.node(self.resolve(tr));
        (n.tag == Tag::Trait)
            .then(|| ItemId::from_index(n.x as usize))
            .flatten()
    }

    /// `tr` and every supertrait it implies for `subject`, each once.
    pub(crate) fn elaborate(
        &mut self,
        tr: TypeId,
        subject: TypeId,
    ) -> Result<Vec<TypeId>, CheckError> {
        let first = {
            let Some(i) = self.trait_item(tr) else {
                return Ok(Vec::new());
            };
            let args = self.trait_args(tr);
            self.types.trait_ref(i, &args)
        };
        let mut out = alloc::vec![first];
        let mut qi = 0;
        while let Some(&t) = out.get(qi) {
            qi += 1;
            self.meter.tick(1)?;
            let Some(i) = self.trait_item(t) else {
                continue;
            };
            let args = self.types.kids(t).to_vec();
            let mut from = alloc::vec![self.types.self_of(i)];
            from.extend(self.own_params(i));
            let mut to = alloc::vec![subject];
            to.extend(args);
            for sup in self.supers_of(i)? {
                let s = self.subst(sup, &from, &to)?;
                if !out.contains(&s) {
                    out.push(s);
                }
            }
        }
        Ok(out)
    }

    // ----------------------------------------------------- bounds in scope

    /// The item whose bounds are in scope.
    pub(crate) fn env_item(&self) -> Option<ItemId> {
        self.lower_ctx.or(self.cur_item)
    }

    /// The interface references (elaborated with supertraits) that the
    /// bounds in scope, an opaque type's bounds, or a `dyn` type give
    /// `subject`, each with its associated-type bindings.
    pub(crate) fn bounds_on(
        &mut self,
        subject: TypeId,
        env: Option<ItemId>,
    ) -> Result<Vec<(TypeId, Bindings)>, CheckError> {
        let subject = self.resolve(subject);
        let mut direct: Vec<(TypeId, Bindings)> = Vec::new();
        match self.types.get(subject) {
            Type::Dyn(traits) => {
                for &t in traits.to_vec().iter() {
                    let Some(i) = self.trait_item(t) else {
                        continue;
                    };
                    let args = self.trait_args(t);
                    let slots: Vec<TypeId> =
                        self.types.kids(t).get(args.len()..).unwrap_or(&[]).to_vec();
                    let binds: Vec<(ItemId, TypeId)> =
                        self.assoc_types(i).into_iter().zip(slots).collect();
                    let tr = self.types.trait_ref(i, &args);
                    direct.push((tr, binds));
                }
            }
            Type::Opaque { origin, args } => {
                let args = args.to_vec();
                if let Some((f, _)) = self.impl_ty_owner(origin) {
                    let params = self.placeholders(f);
                    let me = self.types.opaque(origin, &params);
                    let bl = self.bounds_of(f)?;
                    let entries = self.blist(bl).bounds.clone();
                    for b in entries {
                        if b.subject != me {
                            continue;
                        }
                        let tr = self.subst(b.tr, &params, &args)?;
                        let mut binds = Vec::new();
                        let pairs = self.blist(bl).bindings_of(&b).to_vec();
                        for (a, v) in pairs {
                            binds.push((a, self.subst(v, &params, &args)?));
                        }
                        direct.push((tr, binds));
                    }
                }
            }
            _ => {
                if let Some(item) = env {
                    let bl = self.bounds_of(item)?;
                    let entries = self.blist(bl).bounds.clone();
                    for b in entries {
                        if self.resolve(b.subject) == subject {
                            let binds = self.blist(bl).bindings_of(&b).to_vec();
                            direct.push((b.tr, binds));
                        }
                    }
                }
                // An interface's `Self` implements the interface even where
                // the interface's own bounds are not in scope.
                if let Type::SelfOf(i) = self.types.get(subject) {
                    let own = self.own_params(i);
                    let tr = self.types.trait_ref(i, &own);
                    if !direct.iter().any(|(t, _)| *t == tr) {
                        direct.push((tr, Vec::new()));
                    }
                }
            }
        }
        let mut out = Vec::new();
        for (tr, binds) in direct {
            for e in self.elaborate(tr, subject)? {
                out.push((e, binds.clone()));
            }
        }
        Ok(out)
    }

    // -------------------------------------------------------- obligations

    pub(crate) fn oblige_impl(&mut self, ty: TypeId, tr: TypeId, at: NodeRef) {
        let ob = Obligation {
            goal: Goal::Impl { ty, tr },
            at,
            env: self.env_item(),
            depth: self.solve_depth,
        };
        self.pending.push(ob);
    }

    pub(crate) fn oblige_projection(
        &mut self,
        ty: TypeId,
        tr: TypeId,
        assoc: ItemId,
        out: TypeId,
        at: NodeRef,
    ) {
        let ob = Obligation {
            goal: Goal::Project { ty, tr, assoc, out },
            at,
            env: self.env_item(),
            depth: self.solve_depth,
        };
        self.pending.push(ob);
    }

    /// Solves every pending obligation that can be decided now; the rest
    /// stay pending.
    pub(crate) fn solve(&mut self) -> Result<(), CheckError> {
        loop {
            let batch = core::mem::take(&mut self.pending);
            if batch.is_empty() {
                return Ok(());
            }
            let mut progress = false;
            let mut keep = Vec::new();
            for ob in batch {
                match self.solve_one(ob)? {
                    Step::Done => progress = true,
                    Step::Stuck => keep.push(ob),
                }
            }
            keep.append(&mut self.pending);
            self.pending = keep;
            if !progress {
                return Ok(());
            }
        }
    }

    /// End of an item: solve, give unconstrained literals their defaults
    /// where a goal waits on them, solve again, and keep what is left for
    /// the final report.
    pub(crate) fn solve_item_end(&mut self) -> Result<(), CheckError> {
        self.solve()?;
        if self.pending.is_empty() {
            return Ok(());
        }
        let pending = self.pending.clone();
        for ob in &pending {
            let ty = match ob.goal {
                Goal::Impl { ty, .. } | Goal::Project { ty, .. } => ty,
            };
            let _ = self.settle_literal(ty)?;
        }
        self.solve()?;
        let rest = core::mem::take(&mut self.pending);
        self.stuck.extend(rest);
        Ok(())
    }

    fn solve_one(&mut self, ob: Obligation) -> Result<Step, CheckError> {
        self.meter.tick(1)?;
        if ob.depth > self.meter.budget.trait_depth {
            return Err(CheckError::BudgetExceeded {
                limit: Limit::TraitDepth,
            });
        }
        let saved_depth = core::mem::replace(&mut self.solve_depth, ob.depth.saturating_add(1));
        let saved_ctx = self.lower_ctx;
        let saved_item = self.cur_item;
        self.lower_ctx = None;
        self.cur_item = ob.env;
        let r = match ob.goal {
            Goal::Impl { ty, tr } => self.solve_impl(ty, tr, ob.at),
            Goal::Project { ty, tr, assoc, out } => match self.project(ty, tr, assoc, ob.at)? {
                Some(v) => {
                    if !self.unify(out, v)? && !self.is_err(v) && !self.is_err(out) {
                        self.report(
                            ob.at,
                            DiagnosticKind::Mismatch {
                                expected: out,
                                found: v,
                            },
                        );
                    }
                    Ok(Step::Done)
                }
                None => Ok(Step::Stuck),
            },
        };
        self.solve_depth = saved_depth;
        self.lower_ctx = saved_ctx;
        self.cur_item = saved_item;
        r
    }

    fn solve_impl(&mut self, ty: TypeId, tr: TypeId, at: NodeRef) -> Result<Step, CheckError> {
        let t = self.resolve(ty);
        match self.tag(t) {
            Tag::Error | Tag::Never | Tag::Any => return Ok(Step::Done),
            Tag::Var => return Ok(Step::Stuck),
            _ => {}
        }
        if self.is_err(tr) {
            return Ok(Step::Done);
        }
        if self.is_rigid(t) || self.tag(t) == Tag::Dyn {
            if self.bound_satisfies(t, tr)? {
                return Ok(Step::Done);
            }
            if self.tag(t) != Tag::Dyn {
                self.report_unsatisfied(t, tr, at);
                return Ok(Step::Done);
            }
        }
        match self.select(t, tr)? {
            Selection::One(rec) => {
                let _ = self.commit_rec(rec, t, Some(tr), at)?;
                Ok(Step::Done)
            }
            Selection::None => {
                // A subclass implements what its base classes declare.
                for base in self.base_types(t)? {
                    if let Selection::One(rec) = self.select(base, tr)? {
                        let _ = self.commit_rec(rec, base, Some(tr), at)?;
                        return Ok(Step::Done);
                    }
                }
                if self.has_unbound(t)? || self.has_unbound(tr)? {
                    // A later binding may still make a record apply.
                    return Ok(Step::Stuck);
                }
                self.report_unsatisfied(t, tr, at);
                Ok(Step::Done)
            }
            Selection::Many => {
                if self.has_unbound(t)? || self.has_unbound(tr)? {
                    return Ok(Step::Stuck);
                }
                self.report(
                    at,
                    DiagnosticKind::AmbiguousImpl {
                        ty: t,
                        interface: tr,
                    },
                );
                Ok(Step::Done)
            }
        }
    }

    /// Whether a node of kind `tag` is reachable from `t` through variable
    /// bindings (node flags only describe the stored node).
    fn reaches(&mut self, t: TypeId, tag: Tag) -> Result<bool, CheckError> {
        let n = self.types.node(t);
        let flag = |n: &crate::types::Node| match tag {
            Tag::Proj => n.has_proj,
            _ => n.has_param,
        };
        if !flag(&n) && !n.has_var {
            return Ok(false);
        }
        self.walk_epoch = self.walk_epoch.wrapping_add(1);
        if self.walk_epoch == 0 {
            self.walk_stamp.iter_mut().for_each(|s| *s = 0);
            self.walk_epoch = 1;
        }
        if self.walk_stamp.len() < self.types.len() {
            self.walk_stamp.resize(self.types.len(), 0);
        }
        let epoch = self.walk_epoch;
        let mut stack = alloc::vec![t];
        while let Some(x) = stack.pop() {
            self.meter.tick(1)?;
            let rep = self.resolve(x);
            let n = self.types.node(rep);
            if n.tag == tag {
                return Ok(true);
            }
            if !flag(&n) && !n.has_var {
                continue;
            }
            match self.walk_stamp.get_mut(rep.index()) {
                Some(s) if *s == epoch => continue,
                Some(s) => *s = epoch,
                None => {}
            }
            self.types.for_each_child(rep, |k| stack.push(k));
        }
        Ok(false)
    }

    /// Whether `t` mentions a variable that is still unbound (the node
    /// flags alone cannot say: a class may be represented by a node whose
    /// variables are all bound).
    pub(crate) fn has_unbound(&mut self, t: TypeId) -> Result<bool, CheckError> {
        // Each class representative once (epoch-stamped visited marks), so
        // shared structure costs its DAG size, never its tree size.
        self.walk_epoch = self.walk_epoch.wrapping_add(1);
        if self.walk_epoch == 0 {
            self.walk_stamp.iter_mut().for_each(|s| *s = 0);
            self.walk_epoch = 1;
        }
        if self.walk_stamp.len() < self.types.len() {
            self.walk_stamp.resize(self.types.len(), 0);
        }
        let epoch = self.walk_epoch;
        let mut stack = alloc::vec![t];
        while let Some(x) = stack.pop() {
            self.meter.tick(1)?;
            let rep = self.resolve(x);
            let n = self.types.node(rep);
            if n.tag == Tag::Var {
                return Ok(true);
            }
            if !n.has_var {
                continue;
            }
            match self.walk_stamp.get_mut(rep.index()) {
                Some(s) if *s == epoch => continue,
                Some(s) => *s = epoch,
                None => {}
            }
            self.types.for_each_child(rep, |k| stack.push(k));
        }
        Ok(false)
    }

    fn report_unsatisfied(&mut self, ty: TypeId, tr: TypeId, at: NodeRef) {
        self.report(at, DiagnosticKind::Unsatisfied { ty, interface: tr });
    }

    /// Whether the bounds on a rigid type (or a `dyn` type's interfaces)
    /// give `tr`; unifies the arguments of the first that fits.
    fn bound_satisfies(&mut self, t: TypeId, tr: TypeId) -> Result<bool, CheckError> {
        let Some(want) = self.trait_item(tr) else {
            return Ok(true);
        };
        let want_args = self.trait_args(tr);
        let env = self.env_item();
        for (have, _) in self.bounds_on(t, env)? {
            if self.trait_item(have) != Some(want) {
                continue;
            }
            let have_args = self.trait_args(have);
            if have_args.len() != want_args.len() {
                continue;
            }
            let snap = self.infer.snapshot();
            let mut ok = true;
            for (&a, &b) in have_args.iter().zip(&want_args) {
                if !self.unify(a, b)? {
                    ok = false;
                    break;
                }
            }
            if ok {
                self.infer.commit();
                return Ok(true);
            }
            self.infer.rollback(snap);
        }
        Ok(false)
    }

    /// The records of `tr`'s interface that apply to `t`.
    fn select(&mut self, t: TypeId, tr: TypeId) -> Result<Selection, CheckError> {
        let Some(iface) = self.trait_item(tr) else {
            return Ok(Selection::None);
        };
        let raw = u32::try_from(iface.index()).unwrap_or(NONE);
        let head = self.head_of(t).unwrap_or(BLANKET);
        let mut cands: Vec<u32> = Vec::new();
        let lo = self
            .tr
            .by_trait
            .partition_point(|&(i, h, _)| (i, h) < (raw, head));
        let hi = self
            .tr
            .by_trait
            .partition_point(|&(i, h, _)| (i, h) <= (raw, head));
        cands.extend(
            self.tr
                .by_trait
                .get(lo..hi)
                .unwrap_or(&[])
                .iter()
                .map(|&(_, _, r)| r),
        );
        if head != BLANKET {
            let lo = self
                .tr
                .by_trait
                .partition_point(|&(i, h, _)| (i, h) < (raw, BLANKET));
            let hi = self
                .tr
                .by_trait
                .partition_point(|&(i, h, _)| (i, h) <= (raw, BLANKET));
            cands.extend(
                self.tr
                    .by_trait
                    .get(lo..hi)
                    .unwrap_or(&[])
                    .iter()
                    .map(|&(_, _, r)| r),
            );
        }
        let want_args = self.trait_args(tr);
        let mut found = Vec::new();
        for rec in cands {
            if self.rec_matches(rec, t, Some(&want_args))? {
                found.push(rec);
                if found.len() > 1 {
                    return Ok(Selection::Many);
                }
            }
        }
        Ok(match found.first() {
            Some(&r) => Selection::One(r),
            None => Selection::None,
        })
    }

    /// The one record of `tr` that applies to `t` (or to one of its base
    /// classes), if exactly one does.
    pub(crate) fn select_one(
        &mut self,
        t: TypeId,
        tr: TypeId,
    ) -> Result<Option<(u32, TypeId)>, CheckError> {
        if let Selection::One(r) = self.select(t, tr)? {
            return Ok(Some((r, t)));
        }
        for base in self.base_types(t)? {
            if let Selection::One(r) = self.select(base, tr)? {
                return Ok(Some((r, base)));
            }
        }
        Ok(None)
    }

    /// Whether record `rec` applies to `t` (and, for an interface record, to
    /// the interface arguments `args`). Changes nothing.
    fn rec_matches(
        &mut self,
        rec: u32,
        t: TypeId,
        args: Option<&[TypeId]>,
    ) -> Result<bool, CheckError> {
        self.meter.tick(1)?;
        let Some(r) = self.tr.recs.get(rec as usize).copied() else {
            return Ok(false);
        };
        let snap = self.infer.snapshot();
        let inst = self.instantiate_rec(r.item);
        let ok = self.rec_unify(r, &inst, t, args)?;
        self.infer.rollback(snap);
        Ok(ok)
    }

    /// The record's placeholders, instantiated with fresh variables.
    fn instantiate_rec(&mut self, item: ItemId) -> Vec<TypeId> {
        self.instantiate(item, None, None)
    }

    fn rec_unify(
        &mut self,
        r: ImplRec,
        inst: &[TypeId],
        t: TypeId,
        args: Option<&[TypeId]>,
    ) -> Result<bool, CheckError> {
        let params = self.placeholders(r.item);
        let self_ty = self.subst(r.self_ty, &params, inst)?;
        if !self.unify(self_ty, t)? {
            return Ok(false);
        }
        if let (Some(want), Some(tr)) = (args, r.tr) {
            let tr = self.subst(tr, &params, inst)?;
            let have = self.trait_args(tr);
            if have.len() != want.len() {
                return Ok(false);
            }
            for (&a, &b) in have.iter().zip(want) {
                if !self.unify(a, b)? {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }

    /// Commits to record `rec` for `t`: unifies, and queues the record's
    /// bounds as nested goals. Returns the record's instantiation.
    pub(crate) fn commit_rec(
        &mut self,
        rec: u32,
        t: TypeId,
        tr: Option<TypeId>,
        at: NodeRef,
    ) -> Result<Vec<TypeId>, CheckError> {
        let inst = self.commit_rec_quiet(rec, t, tr)?;
        if let Some(r) = self.tr.recs.get(rec as usize).copied() {
            self.push_bounds(r.item, &inst, at)?;
        }
        Ok(inst)
    }

    /// [`commit_rec`](Self::commit_rec) without queuing the record's bounds
    /// (the caller instantiates a member whose own bounds include them).
    fn commit_rec_quiet(
        &mut self,
        rec: u32,
        t: TypeId,
        tr: Option<TypeId>,
    ) -> Result<Vec<TypeId>, CheckError> {
        let Some(r) = self.tr.recs.get(rec as usize).copied() else {
            return Ok(Vec::new());
        };
        let inst = self.instantiate_rec(r.item);
        let want = tr.map(|tr| self.trait_args(tr));
        let _ = self.rec_unify(r, &inst, t, want.as_deref())?;
        Ok(inst)
    }

    /// The base-class types of a class type, transitively, with the
    /// subclass's arguments substituted (breadth first, each class once).
    pub(crate) fn base_types(&mut self, t: TypeId) -> Result<Vec<TypeId>, CheckError> {
        let mut out: Vec<TypeId> = Vec::new();
        let mut queue = alloc::vec![self.resolve(t)];
        let mut qi = 0;
        self.new_visit();
        while let Some(&c) = queue.get(qi) {
            qi += 1;
            self.meter.tick(1)?;
            let Some((item, params, args)) = self.adt_subst(c) else {
                continue;
            };
            if !self.visit(item) {
                continue;
            }
            let bases = self.idx.base_types_of(item).to_vec();
            for b in bases {
                let bt = self.subst(b, &params, &args)?;
                out.push(bt);
                queue.push(bt);
            }
        }
        Ok(out)
    }

    // ------------------------------------------------------ normalization

    /// Replaces every projection in `t` that can be resolved now: through a
    /// record's associated type, a binding in scope, or a `dyn` type's
    /// value; one whose self type is still unknown becomes a variable with a
    /// pending goal; one on a placeholder without a binding stays a rigid
    /// projection.
    pub(crate) fn normalize(&mut self, t: TypeId, at: NodeRef) -> Result<TypeId, CheckError> {
        let n = self.types.node(t);
        if !n.has_var && !n.has_proj {
            return Ok(t);
        }
        let r = self.resolve(t);
        if !self.reaches(r, Tag::Proj)? {
            return Ok(r);
        }
        self.norm_depth = self.norm_depth.saturating_add(1);
        let out = if self.norm_depth > self.nest_limit() {
            Err(CheckError::BudgetExceeded {
                limit: Limit::TraitDepth,
            })
        } else {
            self.normalize_inner(r, at)
        };
        self.norm_depth = self.norm_depth.saturating_sub(1);
        out
    }

    fn normalize_inner(&mut self, root: TypeId, at: NodeRef) -> Result<TypeId, CheckError> {
        // Post-order over the projection-bearing part of the DAG, with a
        // local memo (normalization of nested projections may recurse
        // through `normalize`, so the shared substitution memo is not
        // used).
        let mut memo: alloc::collections::BTreeMap<TypeId, TypeId> =
            alloc::collections::BTreeMap::new();
        let find =
            |memo: &alloc::collections::BTreeMap<TypeId, TypeId>, k: TypeId| memo.get(&k).copied();
        let mut stack: Vec<(TypeId, bool)> = alloc::vec![(root, false)];
        let mut kids: Vec<TypeId> = Vec::new();
        while let Some((x, expanded)) = stack.pop() {
            self.meter.tick(1)?;
            if !expanded && find(&memo, x).is_some() {
                continue;
            }
            let rep = self.resolve(x);
            let n = self.types.node(rep);
            if (!n.has_proj && !n.has_var) || n.tag == Tag::Var {
                let _ = memo.insert(x, rep);
                continue;
            }
            if !expanded {
                stack.push((x, true));
                let m = &memo;
                self.types.for_each_child(rep, |k| {
                    if find(m, k).is_none() {
                        stack.push((k, false));
                    }
                });
                continue;
            }
            kids.clear();
            let m = &memo;
            let infer = &self.infer;
            self.types.for_each_child(rep, |k| {
                kids.push(find(m, k).unwrap_or_else(|| infer.resolve(k)))
            });
            let rebuilt = self.types.rebuild(rep, &kids);
            let value = if n.tag == Tag::Proj {
                self.resolve_projection(rebuilt, at)?
            } else {
                rebuilt
            };
            let _ = memo.insert(x, value);
        }
        Ok(find(&memo, root).unwrap_or(root))
    }

    /// One projection node, with normalized children.
    fn resolve_projection(&mut self, p: TypeId, at: NodeRef) -> Result<TypeId, CheckError> {
        let n = self.types.node(p);
        let (Some(iface), Some(assoc)) = (
            ItemId::from_index(n.x as usize),
            ItemId::from_index(n.y as usize),
        ) else {
            return Ok(TypeId::ERROR);
        };
        let kids = self.types.kids(p).to_vec();
        let Some((&self_ty, args)) = kids.split_first() else {
            return Ok(TypeId::ERROR);
        };
        let tr = self.types.trait_ref(iface, args);
        match self.project(self_ty, tr, assoc, at)? {
            Some(v) => Ok(v),
            None => {
                let v = self.fresh(GENERAL);
                self.oblige_projection(self_ty, tr, assoc, v, at);
                Ok(v)
            }
        }
    }

    /// `<ty as tr>::assoc` if it can be decided now (`None`: the self type,
    /// or the choice of record, still depends on variables).
    fn project(
        &mut self,
        ty: TypeId,
        tr: TypeId,
        assoc: ItemId,
        at: NodeRef,
    ) -> Result<Option<TypeId>, CheckError> {
        let t = self.resolve(ty);
        let Some(iface) = self.trait_item(tr) else {
            return Ok(Some(TypeId::ERROR));
        };
        match self.tag(t) {
            Tag::Error | Tag::Never | Tag::Any => return Ok(Some(TypeId::ERROR)),
            Tag::Var => return Ok(None),
            _ => {}
        }
        let args = self.trait_args(tr);
        if self.is_rigid(t) || self.tag(t) == Tag::Dyn {
            let env = self.env_item();
            for (have, binds) in self.bounds_on(t, env)? {
                if self.trait_item(have) != Some(iface) {
                    continue;
                }
                if let Some(&(_, v)) = binds.iter().find(|&&(a, _)| a == assoc) {
                    return Ok(Some(v));
                }
            }
            if self.tag(t) != Tag::Dyn {
                let mut pargs = alloc::vec![t];
                pargs.extend_from_slice(&args);
                self.name_item(assoc);
                return Ok(Some(self.types.projection(iface, assoc, &pargs)));
            }
        }
        let rec = match self.select(t, tr)? {
            Selection::One(rec) => rec,
            Selection::None => {
                let mut via_base = None;
                for base in self.base_types(t)? {
                    if let Selection::One(rec) = self.select(base, tr)? {
                        via_base = Some(rec);
                        break;
                    }
                }
                match via_base {
                    Some(rec) => rec,
                    None if self.has_unbound(t)? => return Ok(None),
                    None => {
                        self.report_unsatisfied(t, tr, at);
                        return Ok(Some(TypeId::ERROR));
                    }
                }
            }
            Selection::Many => {
                if self.has_unbound(t)? {
                    return Ok(None);
                }
                self.report(
                    at,
                    DiagnosticKind::AmbiguousImpl {
                        ty: t,
                        interface: tr,
                    },
                );
                return Ok(Some(TypeId::ERROR));
            }
        };
        let inst = self.commit_rec(rec, t, Some(tr), at)?;
        self.assoc_value(rec, &inst, t, &args, assoc, at).map(Some)
    }

    /// The value of associated type `assoc` in record `rec` (instantiated
    /// with `inst`, for self type `t` and interface arguments `args`): the
    /// record's alias of that name, else the interface's default.
    fn assoc_value(
        &mut self,
        rec: u32,
        inst: &[TypeId],
        t: TypeId,
        args: &[TypeId],
        assoc: ItemId,
        at: NodeRef,
    ) -> Result<TypeId, CheckError> {
        let Some(r) = self.tr.recs.get(rec as usize).copied() else {
            return Ok(TypeId::ERROR);
        };
        let name = self.item_symbol(assoc);
        let alias = name.and_then(|n| {
            self.rec_members(rec, n)
                .into_iter()
                .find(|&m| matches!(self.item_kind(m), ItemKind::Alias { .. }))
        });
        if let Some(alias) = alias {
            let ItemKind::Alias { ty, .. } = self.item_kind(alias) else {
                return Ok(TypeId::ERROR);
            };
            let self_ty = self.item_self(alias);
            let saved = self.lower_ctx.replace(alias);
            let v = self.lower_ty(ty, self_ty, true);
            self.lower_ctx = saved;
            let params = self.placeholders(r.item);
            let v = self.subst(v?, &params, inst)?;
            return self.normalize(v, at);
        }
        if let ItemKind::AssocType {
            default: Some(d), ..
        } = self.item_kind(assoc)
        {
            let Some(owner) = self.idx.owner_of(assoc) else {
                return Ok(TypeId::ERROR);
            };
            let s = self.types.self_of(owner);
            let saved = self.lower_ctx.replace(owner);
            let v = self.lower_ty(d, Some(s), true);
            self.lower_ctx = saved;
            let mut from = alloc::vec![s];
            from.extend(self.own_params(owner));
            let mut to = alloc::vec![t];
            to.extend_from_slice(args);
            let v = self.subst(v?, &from, &to)?;
            return self.normalize(v, at);
        }
        // Reported by conformance at the record.
        Ok(TypeId::ERROR)
    }

    /// `X::name` in a type: the associated type `name` of type `t`.
    pub(crate) fn assoc_type_of(
        &mut self,
        t: TypeId,
        name: Symbol,
        at: NodeRef,
    ) -> Result<TypeId, CheckError> {
        let t = self.resolve(t);
        if self.is_err(t) {
            return Ok(TypeId::ERROR);
        }
        // Inside an impl of an interface, `Self::Item` is that interface's.
        let mut found: Vec<(ItemId, ItemId, Vec<TypeId>)> = Vec::new();
        if let Some(ctx) = self.env_item() {
            let impl_item = if matches!(self.item_kind(ctx), ItemKind::Impl(_)) {
                Some(ctx)
            } else {
                self.idx
                    .owner_of(ctx)
                    .filter(|&o| matches!(self.item_kind(o), ItemKind::Impl(_)))
            };
            if let Some(imp) = impl_item {
                let rec = self
                    .tr
                    .recs
                    .iter()
                    .find(|r| r.item == imp && r.tr.is_some())
                    .copied();
                if let Some(ImplRec {
                    tr: Some(tr),
                    self_ty,
                    ..
                }) = rec
                {
                    if self.resolve(self_ty) == t {
                        if let Some(i) = self.trait_item(tr) {
                            if let Some((decl, assoc)) = self.assoc_named(i, name)? {
                                let args = self.trait_args(tr);
                                found.push((decl, assoc, args));
                            }
                        }
                    }
                }
            }
        }
        if found.is_empty() {
            if self.is_rigid(t) || self.tag(t) == Tag::Dyn {
                let env = self.env_item();
                for (tr, _) in self.bounds_on(t, env)? {
                    let Some(i) = self.trait_item(tr) else {
                        continue;
                    };
                    if let Some(m) = self.iface_member(i, name) {
                        if matches!(self.item_kind(m), ItemKind::AssocType { .. })
                            && !found.iter().any(|&(d, a, _)| (d, a) == (i, m))
                        {
                            let args = self.trait_args(tr);
                            found.push((i, m, args));
                        }
                    }
                }
            } else if let Some(head) = self.head_of(t) {
                let recs: Vec<u32> = bucket(&self.tr.trait_by_head, head)
                    .chain(bucket(&self.tr.trait_by_head, BLANKET))
                    .collect();
                for rec in recs {
                    let Some(r) = self.tr.recs.get(rec as usize).copied() else {
                        continue;
                    };
                    let Some(tr) = r.tr else { continue };
                    let Some(i) = self.trait_item(tr) else {
                        continue;
                    };
                    let Some(m) = self.iface_member(i, name) else {
                        continue;
                    };
                    if !matches!(self.item_kind(m), ItemKind::AssocType { .. })
                        || found.iter().any(|&(d, _, _)| d == i)
                    {
                        continue;
                    }
                    if self.rec_matches(rec, t, None)? {
                        let inst = self.instantiate_rec(r.item);
                        let params = self.placeholders(r.item);
                        let tr = self.subst(tr, &params, &inst)?;
                        let args = self.trait_args(tr);
                        found.push((i, m, args));
                    }
                }
            }
        }
        match found.len() {
            0 => {
                self.report(at, DiagnosticKind::NoAssocType { name });
                Ok(TypeId::ERROR)
            }
            1 => {
                let Some((decl, assoc, args)) = found.pop() else {
                    return Ok(TypeId::ERROR);
                };
                let mut pargs = alloc::vec![t];
                pargs.extend(args);
                self.name_item(assoc);
                let p = self.types.projection(decl, assoc, &pargs);
                self.normalize(p, at)
            }
            _ => {
                self.report(at, DiagnosticKind::AmbiguousAssocType { name });
                Ok(TypeId::ERROR)
            }
        }
    }

    // ------------------------------------------------------ member lookup

    /// Looks up member `name` (method, associated function, constant) of a
    /// value or type `t`: bounds and `dyn` interfaces for rigid types, then
    /// inherent members (walking base classes), host members, and members
    /// of interfaces `t` implements.
    pub(crate) fn lookup_member(
        &mut self,
        t: TypeId,
        name: Symbol,
        at: NodeRef,
    ) -> Result<MemberLookup, CheckError> {
        let t = self.resolve(t);
        let tag = self.tag(t);
        if tag == Tag::Error {
            return Ok(MemberLookup::NotFound { incomplete: true });
        }
        // Rigid types and `dyn`: what their bounds say.
        if self.is_rigid(t) || tag == Tag::Dyn {
            let env = self.env_item();
            let mut picks: Vec<(ItemId, ItemId, Vec<TypeId>)> = Vec::new();
            for (tr, _) in self.bounds_on(t, env)? {
                let Some(i) = self.trait_item(tr) else {
                    continue;
                };
                if let Some(m) = self.iface_member(i, name) {
                    if !matches!(self.item_kind(m), ItemKind::AssocType { .. })
                        && !picks.iter().any(|&(d, _, _)| d == i)
                    {
                        let args = self.trait_args(tr);
                        picks.push((i, m, args));
                    }
                }
            }
            match picks.len() {
                0 => {}
                1 => {
                    if let Some((_, member, tr_args)) = picks.pop() {
                        return Ok(MemberLookup::Found(Pick::Iface {
                            member,
                            self_ty: t,
                            tr_args,
                            dynamic: tag == Tag::Dyn,
                        }));
                    }
                }
                _ => return Ok(MemberLookup::Ambiguous),
            }
        }
        // Inherent members, walking base classes level by level.
        let mut level = alloc::vec![t];
        let mut incomplete = false;
        // Each class once (epoch-stamped marks: deep hierarchies stay linear).
        self.new_visit();
        while !level.is_empty() {
            let mut found: Vec<(u32, ItemId, TypeId)> = Vec::new();
            let mut next = Vec::new();
            for &lt in &level {
                self.meter.tick(1)?;
                if let Some(head) = self.head_of(lt) {
                    let recs: Vec<u32> = bucket(&self.tr.inherent, head)
                        .chain(bucket(&self.tr.inherent, BLANKET))
                        .collect();
                    for rec in recs {
                        let ms = self.rec_members(rec, name);
                        if ms.is_empty() || !self.rec_matches(rec, lt, None)? {
                            continue;
                        }
                        for m in ms {
                            found.push((rec, m, lt));
                        }
                    }
                }
                if let Some(h) = self.host_member_of(lt, name) {
                    return Ok(MemberLookup::Found(Pick::Host(h)));
                }
                if let Some((item, params, args)) = self.adt_subst(lt) {
                    if !self.visit(item) {
                        continue;
                    }
                    incomplete |= self.idx.is_incomplete(item);
                    let bases = self.idx.base_types_of(item).to_vec();
                    for b in bases {
                        next.push(self.subst(b, &params, &args)?);
                    }
                }
            }
            match found.len() {
                0 => level = next,
                1 => {
                    let Some((rec, member, lt)) = found.pop() else {
                        break;
                    };
                    let inst = self.commit_rec_quiet(rec, lt, None)?;
                    return Ok(MemberLookup::Found(Pick::Rec { member, inst }));
                }
                _ => return Ok(MemberLookup::Ambiguous),
            }
        }
        // Interface members through the records `t` (or a base) matches.
        let mut cands: Vec<(u32, ItemId, TypeId)> = Vec::new();
        let mut levels = alloc::vec![t];
        levels.extend(self.base_types(t)?);
        for lt in levels {
            let Some(head) = self.head_of(lt) else {
                continue;
            };
            let recs: Vec<u32> = bucket(&self.tr.trait_by_head, head)
                .chain(bucket(&self.tr.trait_by_head, BLANKET))
                .collect();
            for rec in recs {
                let Some(r) = self.tr.recs.get(rec as usize).copied() else {
                    continue;
                };
                let Some(tr) = r.tr else { continue };
                let Some(i) = self.trait_item(tr) else {
                    continue;
                };
                let Some(m) = self.iface_member(i, name) else {
                    continue;
                };
                if matches!(self.item_kind(m), ItemKind::AssocType { .. })
                    || cands.iter().any(|&(c, _, _)| c == rec)
                {
                    continue;
                }
                if self.rec_matches(rec, lt, None)? {
                    cands.push((rec, m, lt));
                }
            }
            if !cands.is_empty() {
                break;
            }
        }
        let mut ifaces: Vec<ItemId> = cands
            .iter()
            .filter_map(|&(rec, _, _)| {
                self.tr
                    .recs
                    .get(rec as usize)
                    .and_then(|r| r.tr)
                    .and_then(|tr| self.trait_item(tr))
            })
            .collect();
        ifaces.sort_unstable();
        ifaces.dedup();
        if ifaces.len() > 1 || cands.len() > 1 {
            return Ok(MemberLookup::Ambiguous);
        }
        if let Some((rec, decl, lt)) = cands.pop() {
            let Some(r) = self.tr.recs.get(rec as usize).copied() else {
                return Ok(MemberLookup::NotFound { incomplete });
            };
            let own_member = if r.class_decl {
                None
            } else {
                self.rec_members(rec, name)
                    .into_iter()
                    .find(|&m| !matches!(self.item_kind(m), ItemKind::Alias { .. }))
            };
            // An overriding member's bounds include the record's; a default
            // reached through the record needs the record's bounds queued.
            let inst = if own_member.is_some() {
                self.commit_rec_quiet(rec, lt, None)?
            } else {
                self.commit_rec(rec, lt, None, at)?
            };
            // The record's own member of that name overrides the default.
            if !r.class_decl {
                if let Some(m) = self
                    .rec_members(rec, name)
                    .into_iter()
                    .find(|&m| !matches!(self.item_kind(m), ItemKind::Alias { .. }))
                {
                    return Ok(MemberLookup::Found(Pick::Rec { member: m, inst }));
                }
            }
            let params = self.placeholders(r.item);
            let tr = match r.tr {
                Some(tr) => self.subst(tr, &params, &inst)?,
                None => TypeId::ERROR,
            };
            let tr_args = self.trait_args(tr);
            return Ok(MemberLookup::Found(Pick::Iface {
                member: decl,
                self_ty: lt,
                tr_args,
                dynamic: false,
            }));
        }
        Ok(MemberLookup::NotFound { incomplete })
    }

    /// A host-declared member of `t`: declared on exactly `t`, or on its
    /// head without arguments (`Vec` for `Vec<i32>`).
    fn host_member_of(&mut self, t: TypeId, name: Symbol) -> Option<TypeId> {
        if let Some(h) = self.host_member(t, name) {
            return Some(h);
        }
        let n = self.types.node(t);
        let bare = match n.tag {
            Tag::Extern if n.len > 0 => {
                let sym = Symbol::from_u32(n.x)?;
                self.types.external(sym)
            }
            Tag::Adt if n.len > 0 => self.types.adt(ItemId::from_index(n.x as usize)?),
            _ => return None,
        };
        self.host_member(bare, name)
    }

    /// The arguments for a picked member's placeholders: the record's (or
    /// the interface's `Self` and arguments), then the member's own (from
    /// `own`, else fresh), then fresh `impl Trait` parameters.
    pub(crate) fn pick_args(
        &mut self,
        pick: &Pick,
        own: Option<&[TypeId]>,
    ) -> Option<(ItemId, Vec<TypeId>)> {
        Some(match pick {
            Pick::Rec { member, inst, .. } => {
                let args = self.instantiate(*member, Some(inst), own);
                (*member, args)
            }
            Pick::Iface {
                member,
                self_ty,
                tr_args,
                ..
            } => {
                let mut inherited = alloc::vec![*self_ty];
                inherited.extend_from_slice(tr_args);
                let args = self.instantiate(*member, Some(&inherited), own);
                (*member, args)
            }
            // Host members have no placeholders.
            Pick::Host(_) => return None,
        })
    }

    // ---------------------------------------------------------- coherence

    /// Reports impls of one interface that overlap (their self types and
    /// arguments unify): selection between them would be ambiguous.
    pub(crate) fn check_coherence(&mut self) -> Result<(), CheckError> {
        let groups = self.tr.by_trait.clone();
        let mut i = 0;
        while i < groups.len() {
            let Some(&(iface, _, _)) = groups.get(i) else {
                break;
            };
            let end = groups.partition_point(|&(x, _, _)| x <= iface);
            let group = groups.get(i..end).unwrap_or(&[]);
            // Records of one head, and blanket records against all.
            let blanket: Vec<u32> = group
                .iter()
                .filter(|&&(_, h, _)| h == BLANKET)
                .map(|&(_, _, r)| r)
                .collect();
            let mut j = 0;
            while j < group.len() {
                let Some(&(_, head, _)) = group.get(j) else {
                    break;
                };
                let k = j + group
                    .get(j..)
                    .unwrap_or(&[])
                    .iter()
                    .take_while(|&&(_, h, _)| h == head)
                    .count();
                let same: Vec<u32> = group
                    .get(j..k)
                    .unwrap_or(&[])
                    .iter()
                    .map(|&(_, _, r)| r)
                    .collect();
                for (a_pos, &a) in same.iter().enumerate() {
                    let others: Vec<u32> = if head == BLANKET {
                        same.get(..a_pos).unwrap_or(&[]).to_vec()
                    } else {
                        let mut o = same.get(..a_pos).unwrap_or(&[]).to_vec();
                        o.extend(blanket.iter().copied());
                        o
                    };
                    for b in others {
                        if self.overlap(a, b)? {
                            let (first, later) = if a < b { (a, b) } else { (b, a) };
                            let item = self.tr.recs.get(later as usize).map(|r| r.item);
                            let other = self.tr.recs.get(first as usize).map(|r| r.item);
                            if let (Some(item), Some(other)) = (item, other) {
                                self.report(
                                    NodeRef::Item(item),
                                    DiagnosticKind::OverlappingImpls { other },
                                );
                            }
                            break;
                        }
                    }
                }
                j = k;
            }
            i = end;
        }
        Ok(())
    }

    fn overlap(&mut self, a: u32, b: u32) -> Result<bool, CheckError> {
        self.meter.tick(1)?;
        let (Some(ra), Some(rb)) = (
            self.tr.recs.get(a as usize).copied(),
            self.tr.recs.get(b as usize).copied(),
        ) else {
            return Ok(false);
        };
        let snap = self.infer.snapshot();
        let ia = self.instantiate_rec(ra.item);
        let ib = self.instantiate_rec(rb.item);
        let pa = self.placeholders(ra.item);
        let pb = self.placeholders(rb.item);
        let sa = self.subst(ra.self_ty, &pa, &ia)?;
        let sb = self.subst(rb.self_ty, &pb, &ib)?;
        let mut ok = self.unify(sa, sb)?;
        if ok {
            if let (Some(ta), Some(tb)) = (ra.tr, rb.tr) {
                let ta = self.subst(ta, &pa, &ia)?;
                let tb = self.subst(tb, &pb, &ib)?;
                ok = self.unify(ta, tb)?;
            }
        }
        self.infer.rollback(snap);
        Ok(ok)
    }

    // -------------------------------------------------------- conformance

    /// An implementation of an interface provides every member without a
    /// default, nothing the interface does not declare, and methods whose
    /// signatures match the interface's with `Self` and the interface's
    /// arguments substituted.
    pub(crate) fn check_conformance(&mut self, rec: u32) -> Result<(), CheckError> {
        let Some(r) = self.tr.recs.get(rec as usize).copied() else {
            return Ok(());
        };
        let Some(tr) = r.tr else { return Ok(()) };
        let Some(iface) = self.trait_item(tr) else {
            return Ok(());
        };
        let ItemKind::Interface(idef) = self.item_kind(iface) else {
            return Ok(());
        };
        let at = NodeRef::Item(r.item);
        let tr_args = self.trait_args(tr);
        // The record's own members (for a class: its members and those of
        // its base classes).
        let own_rec = if r.class_decl {
            self.tr
                .recs
                .iter()
                .position(|x| x.item == r.item && x.tr.is_none())
                .and_then(|p| u32::try_from(p).ok())
        } else {
            Some(rec)
        };
        let mut missing: Vec<Symbol> = Vec::new();
        for &m in self.hir.list(idef.items) {
            self.meter.tick(1)?;
            let Some(name) = self.item_symbol(m) else {
                continue;
            };
            let provided: Vec<ItemId> = match own_rec {
                Some(o) => self.rec_members(o, name),
                None => Vec::new(),
            };
            let provided = match (provided.first(), r.class_decl) {
                (Some(&p), _) => Some(p),
                (None, true) => self.inherited_member(r.self_ty, name)?,
                (None, false) => None,
            };
            let has_default = match self.item_kind(m) {
                ItemKind::Fn(d) => d.body.is_some(),
                ItemKind::Const { value, .. } => value.is_some(),
                ItemKind::AssocType { default, .. } => default.is_some(),
                _ => true,
            };
            match provided {
                None if !has_default => missing.push(name),
                None => {}
                Some(p) => {
                    if let (ItemKind::Fn(_), ItemKind::Fn(_)) =
                        (self.item_kind(m), self.item_kind(p))
                    {
                        self.compare_method(r, m, p, &tr_args)?;
                    }
                }
            }
        }
        if let Some(&first) = missing.first() {
            self.report(
                at,
                DiagnosticKind::MissingMember {
                    name: first,
                    count: u32::try_from(missing.len()).unwrap_or(u32::MAX),
                },
            );
        }
        // Associated types with parameters of their own are not checked.
        if !r.class_decl {
            let aliases: Vec<ItemId> = self
                .tr
                .members
                .iter()
                .filter(|&&(x, _, _)| x == rec)
                .map(|&(_, _, i)| i)
                .filter(|&i| {
                    matches!(self.item_kind(i), ItemKind::Alias { generics, .. } if !generics.params.is_empty())
                })
                .collect();
            for a in aliases {
                self.report(
                    NodeRef::Item(a),
                    DiagnosticKind::Unsupported {
                        feature: crate::diag::Feature::GenericAssocTypes,
                    },
                );
            }
        }
        if !r.class_decl {
            let members: Vec<(Symbol, ItemId)> = self
                .tr
                .members
                .iter()
                .filter(|&&(x, _, _)| x == rec)
                .map(|&(_, n, i)| (n, i))
                .collect();
            for (name, m) in members {
                if self.iface_member_any(iface, name)?.is_none() {
                    self.report(
                        NodeRef::Item(m),
                        DiagnosticKind::NotAMember {
                            interface: tr,
                            name,
                        },
                    );
                }
            }
        }
        Ok(())
    }

    /// A member named `name` of `iface` or a supertrait.
    fn iface_member_any(
        &mut self,
        iface: ItemId,
        name: Symbol,
    ) -> Result<Option<ItemId>, CheckError> {
        if let Some(m) = self.iface_member(iface, name) {
            return Ok(Some(m));
        }
        let s = self.types.self_of(iface);
        let own = self.own_params(iface);
        let root = self.types.trait_ref(iface, &own);
        for tr in self.elaborate(root, s)? {
            if let Some(i) = self.trait_item(tr) {
                if let Some(m) = self.iface_member(i, name) {
                    return Ok(Some(m));
                }
            }
        }
        Ok(None)
    }

    /// A member a class inherits from a base class.
    fn inherited_member(&mut self, t: TypeId, name: Symbol) -> Result<Option<ItemId>, CheckError> {
        for base in self.base_types(t)? {
            let Some((item, _, _)) = self.adt_subst(base) else {
                continue;
            };
            let rec = self
                .tr
                .recs
                .iter()
                .position(|x| x.item == item && x.tr.is_none())
                .and_then(|p| u32::try_from(p).ok());
            if let Some(rec) = rec {
                if let Some(&m) = self.rec_members(rec, name).first() {
                    return Ok(Some(m));
                }
            }
        }
        Ok(None)
    }

    /// Compares an implementing method `p` with the interface's method `m`.
    fn compare_method(
        &mut self,
        r: ImplRec,
        m: ItemId,
        p: ItemId,
        tr_args: &[TypeId],
    ) -> Result<(), CheckError> {
        let (Some(ms), Some(ps)) = (self.sig(m)?, self.sig(p)?) else {
            return Ok(());
        };
        let (Some(msig), Some(psig)) = (
            self.sig_arena.get(ms).cloned(),
            self.sig_arena.get(ps).cloned(),
        ) else {
            return Ok(());
        };
        let at = NodeRef::Item(p);
        if msig.params.len() != psig.params.len() {
            self.report(
                at,
                DiagnosticKind::Arity {
                    min: u32::try_from(msig.params.len()).unwrap_or(u32::MAX),
                    max: Some(u32::try_from(msig.params.len()).unwrap_or(u32::MAX)),
                    found: u32::try_from(psig.params.len()).unwrap_or(u32::MAX),
                },
            );
            return Ok(());
        }
        // The interface method's placeholders: `Self`, the interface's
        // parameters, then its own, which map to the implementing method's
        // own parameters in order.
        let mparams = self.placeholders(m);
        let pparams = self.placeholders(p);
        let iface_own = {
            let pl = self.params_of(m);
            (self.plist(pl).own, self.plist(pl).explicit)
        };
        let impl_own = {
            let pl = self.params_of(p);
            let l = self.plist(pl);
            l.own_params().to_vec()
        };
        if iface_own.1 != impl_own.len() {
            self.report(
                at,
                DiagnosticKind::GenericArity {
                    expected: u32::try_from(iface_own.1).unwrap_or(u32::MAX),
                    found: u32::try_from(impl_own.len()).unwrap_or(u32::MAX),
                },
            );
            return Ok(());
        }
        let mut to = alloc::vec![r.self_ty];
        to.extend_from_slice(tr_args);
        to.extend_from_slice(&impl_own);
        // Anything left (`impl Trait` parameters) maps to itself.
        while to.len() < mparams.len() {
            if let Some(&x) = mparams.get(to.len()) {
                to.push(x);
            }
        }
        let _ = pparams;
        let saved = self.cur_item.replace(p);
        let mut bad: Option<(NodeRef, TypeId, TypeId)> = None;
        let pairs: Vec<(TypeId, TypeId, usize)> = msig
            .params
            .iter()
            .zip(&psig.params)
            .enumerate()
            .map(|(i, (a, b))| (a.ty, b.ty, i))
            .chain(core::iter::once((msig.ret, psig.ret, usize::MAX)))
            .collect();
        let def = match self.item_kind(p) {
            ItemKind::Fn(d) => Some(d),
            _ => None,
        };
        for (want, have, i) in pairs {
            let want = self.subst(want, &mparams, &to)?;
            let want = self.normalize(want, at)?;
            if !self.unify(want, have)? && !self.is_err(want) && !self.is_err(have) {
                let node = match (i, def) {
                    (usize::MAX, Some(d)) => d.ret.map_or(at, NodeRef::Ty),
                    (i, Some(d)) => self
                        .hir
                        .list(d.params)
                        .get(i)
                        .map_or(at, |&pid| NodeRef::Param(pid)),
                    _ => at,
                };
                bad = Some((node, want, have));
                break;
            }
        }
        self.cur_item = saved;
        if let Some((node, expected, found)) = bad {
            self.report(node, DiagnosticKind::Mismatch { expected, found });
        }
        Ok(())
    }
}

/// The outcome of record selection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Selection {
    None,
    One(u32),
    Many,
}
