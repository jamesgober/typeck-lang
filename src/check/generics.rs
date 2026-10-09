//! Generic items: their parameters and bounds, substitution, and
//! instantiation.
//!
//! An item's generic parameters are *placeholders*: rigid types inside the
//! item ([`Type::Param`], [`Type::ImplParam`] for `impl Trait` parameters, and
//! [`Type::SelfOf`] for an interface's `Self`). A member of an impl, class, or
//! interface sees its owner's placeholders first, then its own. Using a
//! generic item instantiates it: each placeholder is replaced by an explicit
//! argument or a fresh inference variable, by a memoized rebuild of the
//! types that mention placeholders (linear in the type DAG, like zonking;
//! placeholder-free subterms are skipped in constant time).
//!
//! The parameter list of an item is read straight from the HIR (nothing is
//! lowered), so lowering a type never needs another item's bounds; bounds are
//! lowered lazily, once per item.

use alloc::vec::Vec;

use hir_lang::{
    Bound, Expr, ExprId, GenericArg, Generics, ItemId, ItemKind, NodeRef, Res, Symbol, Ty, TyId,
    WherePred,
};

use super::Ctx;
use crate::{
    diag::DiagnosticKind,
    error::CheckError,
    infer::GENERAL,
    typed::NONE,
    types::{Tag, Type, TypeId},
};

/// The placeholders an item sees, in instantiation order.
#[derive(Clone, Debug, Default)]
pub(crate) struct ParamList {
    /// Owner placeholders (interface `Self`, the owner's parameters), then
    /// this item's own type and constant parameters, then its `impl Trait`
    /// parameters.
    pub(crate) params: Vec<TypeId>,
    /// Where this item's own explicit parameters start in `params`.
    pub(crate) own: usize,
    /// How many own explicit parameters there are.
    pub(crate) explicit: usize,
    /// Per own explicit parameter: its default.
    pub(crate) defaults: Vec<Option<GenericArg>>,
}

impl ParamList {
    pub(crate) fn own_params(&self) -> &[TypeId] {
        self.params
            .get(self.own..self.own.saturating_add(self.explicit))
            .unwrap_or(&[])
    }
}

/// One bound in an item's environment: `subject: tr` with associated-type
/// bindings.
#[derive(Clone, Copy, Debug)]
pub(crate) struct BoundEntry {
    /// The bounded type (a placeholder, a projection, or an opaque type).
    pub(crate) subject: TypeId,
    /// The interface reference (a `Trait` node).
    pub(crate) tr: TypeId,
    /// Bindings `Item = T`: a range of [`BoundList::bindings`].
    pub(crate) bind: (u32, u32),
    /// Where the bound is written.
    pub(crate) at: NodeRef,
}

/// The bounds an item's body may rely on.
#[derive(Clone, Debug, Default)]
pub(crate) struct BoundList {
    pub(crate) bounds: Vec<BoundEntry>,
    /// Associated-type bindings: (associated type item, its value).
    pub(crate) bindings: Vec<(ItemId, TypeId)>,
}

impl BoundList {
    pub(crate) fn bindings_of(&self, b: &BoundEntry) -> &[(ItemId, TypeId)] {
        let (start, len) = b.bind;
        self.bindings
            .get(start as usize..(start as usize).saturating_add(len as usize))
            .unwrap_or(&[])
    }
}

/// `bounds_memo` state while an item's bounds are being lowered.
const BUSY: u32 = u32::MAX - 1;

/// A lowered bound before it is stored: the interface reference, bindings,
/// and constraints on associated types (`Iterator<Item: Show>`).
pub(crate) struct LoweredBound {
    pub(crate) tr: TypeId,
    pub(crate) bindings: Vec<(ItemId, TypeId)>,
    pub(crate) constraints: Vec<(ItemId, hir_lang::List<Bound>)>,
}

/// The generics of an item kind, if it has any.
pub(crate) fn generics_of(kind: &ItemKind) -> Option<Generics> {
    Some(match *kind {
        ItemKind::Fn(d) => d.generics,
        ItemKind::Record(d) => d.generics,
        ItemKind::Sum(d) => d.generics,
        ItemKind::Class(d) => d.generics,
        ItemKind::Interface(d) => d.generics,
        ItemKind::Impl(d) => d.generics,
        ItemKind::Alias { generics, .. } => generics,
        _ => return None,
    })
}

impl Ctx<'_> {
    // ------------------------------------------------------------ params

    /// The placeholders of `item` (memoized; read from the HIR only).
    pub(crate) fn params_of(&mut self, item: ItemId) -> u32 {
        if let Some(&v) = self.params_memo.get(item.index()) {
            if v != NONE {
                return v;
            }
        }
        let hir = self.hir;
        let mut chain: Vec<ItemId> = alloc::vec![item];
        if let Some(o) = self.idx.owner_of(item) {
            if is_member_owner(&self.item_kind(o)) {
                chain.push(o);
            }
        }
        let mut list = ParamList::default();
        for &it in chain.iter().rev() {
            let kind = self.item_kind(it);
            if matches!(kind, ItemKind::Interface(_)) {
                let s = self.types.self_of(it);
                list.params.push(s);
            }
            if it == item {
                list.own = list.params.len();
            }
            if let Some(g) = generics_of(&kind) {
                for gp in hir.list(g.params) {
                    let Some(binder) = hir.binder(gp.binder) else {
                        continue;
                    };
                    if !matches!(
                        binder.kind,
                        hir_lang::BinderKind::TypeParam | hir_lang::BinderKind::ConstParam
                    ) {
                        continue;
                    }
                    self.types.name_binder(gp.binder, binder.name.sym);
                    let p = self.types.param(gp.binder);
                    list.params.push(p);
                    if it == item {
                        list.explicit += 1;
                        list.defaults.push(gp.default);
                    }
                }
            }
        }
        if matches!(self.item_kind(item), ItemKind::Fn(_)) {
            for (ty, owner, rpit) in self.impl_tys_of(item) {
                if !rpit && owner == item {
                    let p = self.types.impl_param(ty);
                    list.params.push(p);
                }
            }
        }
        let index = u32::try_from(self.param_lists.len()).unwrap_or(NONE);
        self.param_lists.push(list);
        if let Some(slot) = self.params_memo.get_mut(item.index()) {
            *slot = index;
        }
        index
    }

    pub(crate) fn plist(&self, index: u32) -> &ParamList {
        static EMPTY: ParamList = ParamList {
            params: Vec::new(),
            own: 0,
            explicit: 0,
            defaults: Vec::new(),
        };
        self.param_lists.get(index as usize).unwrap_or(&EMPTY)
    }

    /// The placeholders of `item`, copied out.
    pub(crate) fn placeholders(&mut self, item: ItemId) -> Vec<TypeId> {
        let i = self.params_of(item);
        self.plist(i).params.clone()
    }

    /// Whether `item` (or its owner) has placeholders.
    pub(crate) fn is_generic_item(&mut self, item: ItemId) -> bool {
        let i = self.params_of(item);
        !self.plist(i).params.is_empty()
    }

    /// The `impl Trait` type nodes in `item`'s signature: (type node, owning
    /// function, return position).
    pub(crate) fn impl_tys_of(&self, item: ItemId) -> Vec<(TyId, ItemId, bool)> {
        let lo = self.impl_tys.partition_point(|&(_, o, _)| o < item);
        let hi = self.impl_tys.partition_point(|&(_, o, _)| o <= item);
        self.impl_tys
            .get(lo..hi)
            .map(<[_]>::to_vec)
            .unwrap_or_default()
    }

    /// The function an `impl Trait` type node belongs to, and whether it is
    /// in return position.
    pub(crate) fn impl_ty_owner(&self, ty: TyId) -> Option<(ItemId, bool)> {
        self.impl_ty_index
            .binary_search_by(|&(t, _)| t.cmp(&ty))
            .ok()
            .and_then(|i| self.impl_ty_index.get(i))
            .and_then(|&(_, k)| self.impl_tys.get(k as usize))
            .map(|&(_, o, r)| (o, r))
    }

    // ------------------------------------------------------------ bounds

    /// The bounds `item`'s body may rely on (memoized). While an item's own
    /// bounds are being lowered, a request for them sees the part lowered
    /// so far (so `T: Iterator, T::Item: Show` works in either order of
    /// the two kinds: plain parameter bounds are lowered first).
    pub(crate) fn bounds_of(&mut self, item: ItemId) -> Result<u32, CheckError> {
        if let Some(&v) = self.bounds_memo.get(item.index()) {
            if v != NONE && v != BUSY {
                return Ok(v);
            }
            if v == BUSY {
                return Ok(self
                    .bounds_partial
                    .get(item.index())
                    .copied()
                    .unwrap_or(NONE));
            }
        }
        let index = u32::try_from(self.bound_lists.len()).unwrap_or(NONE);
        self.bound_lists.push(BoundList::default());
        if let Some(slot) = self.bounds_memo.get_mut(item.index()) {
            *slot = BUSY;
        }
        if let Some(slot) = self.bounds_partial.get_mut(item.index()) {
            *slot = index;
        }
        let saved = self.lower_ctx.replace(item);
        let r = self.build_bounds(item, index);
        self.lower_ctx = saved;
        r?;
        if let Some(slot) = self.bounds_memo.get_mut(item.index()) {
            *slot = index;
        }
        Ok(index)
    }

    pub(crate) fn blist(&self, index: u32) -> &BoundList {
        static EMPTY: BoundList = BoundList {
            bounds: Vec::new(),
            bindings: Vec::new(),
        };
        self.bound_lists.get(index as usize).unwrap_or(&EMPTY)
    }

    /// Stores a lowered bound, and the bounds its associated-type
    /// constraints (`Iterator<Item: Show>`) put on projections, on an
    /// explicit worklist (constraints nest to any depth).
    fn push_bound_entry(
        &mut self,
        list: u32,
        subject: TypeId,
        lowered: LoweredBound,
        at: NodeRef,
    ) -> Result<(), CheckError> {
        let mut work: Vec<(TypeId, LoweredBound, NodeRef)> = alloc::vec![(subject, lowered, at)];
        while let Some((subject, lowered, at)) = work.pop() {
            self.meter.tick(1)?;
            let Some(bl) = self.bound_lists.get_mut(list as usize) else {
                return Ok(());
            };
            let start = u32::try_from(bl.bindings.len()).unwrap_or(NONE);
            let len = u32::try_from(lowered.bindings.len()).unwrap_or(0);
            bl.bindings.extend_from_slice(&lowered.bindings);
            bl.bounds.push(BoundEntry {
                subject,
                tr: lowered.tr,
                bind: (start, len),
                at,
            });
            for (assoc, bounds) in lowered.constraints {
                let iface = self.types.node(lowered.tr).x;
                let Some(iface) = ItemId::from_index(iface as usize) else {
                    continue;
                };
                let mut args = alloc::vec![subject];
                args.extend_from_slice(self.types.kids(lowered.tr));
                let proj = self.types.projection(iface, assoc, &args);
                self.name_item(assoc);
                for &b in self.hir.list(bounds) {
                    if let Bound::Ty(t) = b {
                        if let Some(inner) = self.lower_bound(t, proj)? {
                            work.push((proj, inner, NodeRef::Ty(t)));
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn build_bounds(&mut self, item: ItemId, list: u32) -> Result<(), CheckError> {
        let hir = self.hir;
        // The owner's bounds come first (members rely on them).
        if let Some(o) = self.idx.owner_of(item) {
            if is_member_owner(&self.item_kind(o)) {
                let ob = self.bounds_of(o)?;
                let copy = self.blist(ob).clone();
                if let Some(bl) = self.bound_lists.get_mut(list as usize) {
                    let shift = u32::try_from(bl.bindings.len()).unwrap_or(0);
                    bl.bindings.extend_from_slice(&copy.bindings);
                    bl.bounds.extend(copy.bounds.iter().map(|b| BoundEntry {
                        bind: (b.bind.0.saturating_add(shift), b.bind.1),
                        ..*b
                    }));
                }
            }
        }
        let kind = self.item_kind(item);
        // An interface's `Self` implements the interface.
        if let ItemKind::Interface(_) = kind {
            let own = self.own_params(item);
            let tr = self.types.trait_ref(item, &own);
            let s = self.types.self_of(item);
            self.name_item(item);
            if let Some(bl) = self.bound_lists.get_mut(list as usize) {
                bl.bounds.push(BoundEntry {
                    subject: s,
                    tr,
                    bind: (0, 0),
                    at: NodeRef::Item(item),
                });
            }
        }
        let generics = generics_of(&kind).unwrap_or_default();
        let mut later: Vec<(TypeId, TyId)> = Vec::new();
        let mut later_preds: Vec<WherePred> = Vec::new();
        // Pass 1: bounds on plain parameters.
        for gp in hir.list(generics.params) {
            self.meter.tick(1)?;
            let p = self.types.param(gp.binder);
            for &b in hir.list(gp.bounds) {
                if let Bound::Ty(t) = b {
                    if let Some(lb) = self.lower_bound(t, p)? {
                        self.push_bound_entry(list, p, lb, NodeRef::Ty(t))?;
                    }
                }
            }
        }
        for pred in hir.list(generics.preds) {
            self.meter.tick(1)?;
            match pred.subject {
                Bound::Ty(subj) if self.is_param_path(subj) => {
                    let s = self.lower_ty(subj, None, true)?;
                    for &b in hir.list(pred.bounds) {
                        if let Bound::Ty(t) = b {
                            if let Some(lb) = self.lower_bound(t, s)? {
                                self.push_bound_entry(list, s, lb, NodeRef::Ty(t))?;
                            }
                        }
                    }
                }
                Bound::Ty(_) => later_preds.push(*pred),
                Bound::Region(_) => {}
            }
        }
        if matches!(kind, ItemKind::Fn(_)) {
            for (ty, owner, rpit) in self.impl_tys_of(item) {
                if owner != item {
                    continue;
                }
                if rpit {
                    let params = self.placeholders(item);
                    let o = self.types.opaque(ty, &params);
                    later.push((o, ty));
                } else {
                    let p = self.types.impl_param(ty);
                    if let Ty::Impl(bounds) = *hir.ty(ty) {
                        for &b in hir.list(bounds) {
                            if let Bound::Ty(t) = b {
                                if let Some(lb) = self.lower_bound(t, p)? {
                                    self.remember_impl_name(ty, lb.tr);
                                    self.push_bound_entry(list, p, lb, NodeRef::Ty(t))?;
                                }
                            }
                        }
                    }
                }
            }
        }
        // Pass 2: bounds whose subject needs pass 1 (projections, other
        // types), and the bounds of opaque results.
        for pred in later_preds {
            let Bound::Ty(subj) = pred.subject else {
                continue;
            };
            let s = self.lower_ty(subj, self.item_self(item), true)?;
            for &b in hir.list(pred.bounds) {
                if let Bound::Ty(t) = b {
                    if let Some(lb) = self.lower_bound(t, s)? {
                        self.push_bound_entry(list, s, lb, NodeRef::Ty(t))?;
                    }
                }
            }
        }
        for (o, ty) in later {
            if let Ty::Impl(bounds) = *hir.ty(ty) {
                for &b in hir.list(bounds) {
                    if let Bound::Ty(t) = b {
                        if let Some(lb) = self.lower_bound(t, o)? {
                            self.remember_impl_name(ty, lb.tr);
                            self.push_bound_entry(list, o, lb, NodeRef::Ty(t))?;
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Remembers the first interface of an `impl` type for display.
    fn remember_impl_name(&mut self, ty: TyId, tr: TypeId) {
        let n = self.types.node(tr);
        if let Some(name) = ItemId::from_index(n.x as usize)
            .and_then(|i| self.hir.get_item(i))
            .and_then(|it| it.name)
        {
            self.types.name_impl(ty, name.sym);
        }
    }

    /// Whether a type annotation is a plain path to a type parameter.
    fn is_param_path(&self, ty: TyId) -> bool {
        let Ty::Path(p) = *self.hir.ty(ty) else {
            return false;
        };
        let path = self.hir.path(p);
        path.unresolved == 0
            && matches!(path.res, Res::Local(b) if self.hir.binder(b).is_some_and(|x| x.kind == hir_lang::BinderKind::TypeParam))
    }

    /// An item's own explicit parameters (the arguments of its identity
    /// instance).
    pub(crate) fn own_params(&mut self, item: ItemId) -> Vec<TypeId> {
        let i = self.params_of(item);
        self.plist(i).own_params().to_vec()
    }

    /// Lowers a bound `ty` on `subject` to an interface reference. Reports
    /// and returns `None` when `ty` does not name an interface.
    pub(crate) fn lower_bound(
        &mut self,
        ty: TyId,
        subject: TypeId,
    ) -> Result<Option<LoweredBound>, CheckError> {
        let at = NodeRef::Ty(ty);
        let Ty::Path(p) = *self.hir.ty(ty) else {
            if !matches!(self.hir.ty(ty), Ty::Err) {
                self.report(at, DiagnosticKind::NotAnInterface);
            }
            return Ok(None);
        };
        let path = *self.hir.path(p);
        if path.res == Res::Err {
            return Ok(None);
        }
        let iface = match (path.unresolved, self.local_item(path.res)) {
            (0, Some(i)) if matches!(self.item_kind(i), ItemKind::Interface(_)) => i,
            (0, Some(i)) if matches!(self.item_kind(i), ItemKind::Err) => return Ok(None),
            _ => {
                if path.res == Res::Unresolved {
                    self.report(NodeRef::Path(p), DiagnosticKind::Unresolved);
                } else {
                    self.report(at, DiagnosticKind::NotAnInterface);
                }
                return Ok(None);
            }
        };
        self.name_item(iface);
        let args = self
            .hir
            .list(path.segments)
            .last()
            .map_or(hir_lang::List::EMPTY, |s| s.args);
        let mut positional: Vec<GenericArg> = Vec::new();
        let mut bindings = Vec::new();
        let mut constraints = Vec::new();
        for &a in self.hir.list(args) {
            match a {
                GenericArg::Ty(_) | GenericArg::Const(_) => positional.push(a),
                GenericArg::Region(_) => {}
                GenericArg::Binding { name, ty: bty } => {
                    match self.assoc_named(iface, name.sym)? {
                        Some((_, assoc)) => {
                            let t = self.lower_ty(bty, None, false)?;
                            bindings.push((assoc, t));
                        }
                        None => self.report(
                            NodeRef::Ty(bty),
                            DiagnosticKind::NoAssocType { name: name.sym },
                        ),
                    }
                }
                GenericArg::Constraint { name, bounds } => {
                    match self.assoc_named(iface, name.sym)? {
                        Some((_, assoc)) => constraints.push((assoc, bounds)),
                        None => self.report(at, DiagnosticKind::NoAssocType { name: name.sym }),
                    }
                }
            }
        }
        let filled = self.fill_args(iface, &positional, at, true, Some(subject))?;
        let tr = self.types.trait_ref(iface, &filled);
        Ok(Some(LoweredBound {
            tr,
            bindings,
            constraints,
        }))
    }

    // ------------------------------------------------------ explicit args

    /// Lowers one generic argument to a type (a constant argument to a
    /// [`Type::Const`], a constant parameter to its placeholder).
    pub(crate) fn lower_arg(&mut self, a: GenericArg, sig: bool) -> Result<TypeId, CheckError> {
        Ok(match a {
            GenericArg::Ty(t) => self.lower_ty(t, None, sig)?,
            GenericArg::Const(e) => self.const_arg(e)?,
            _ => TypeId::ERROR,
        })
    }

    /// A constant generic argument: a constant parameter, or a compile-time
    /// integer.
    pub(crate) fn const_arg(&mut self, e: ExprId) -> Result<TypeId, CheckError> {
        if let Expr::Path(p) = *self.hir.expr(e) {
            let path = self.hir.path(p);
            if let (0, Res::Local(b)) = (path.unresolved, path.res) {
                if self
                    .hir
                    .binder(b)
                    .is_some_and(|x| x.kind == hir_lang::BinderKind::ConstParam)
                {
                    return Ok(self.types.param(b));
                }
            }
        }
        Ok(match self.const_eval(e)? {
            Some(v) => match i64::try_from(v) {
                Ok(v) => self.types.constant(v),
                Err(_) => {
                    self.report(NodeRef::Expr(e), DiagnosticKind::NotConstant);
                    TypeId::ERROR
                }
            },
            None => {
                self.report(NodeRef::Expr(e), DiagnosticKind::NotConstant);
                TypeId::ERROR
            }
        })
    }

    /// The arguments for `item`'s own explicit parameters, from the
    /// positional generic arguments written at a use. Missing trailing
    /// arguments take their defaults, else (outside signatures) fresh
    /// variables; a wrong count is reported at `at` and the arguments become
    /// `{error}`. `self_ty` substitutes an interface's `Self` in defaults.
    pub(crate) fn fill_args(
        &mut self,
        item: ItemId,
        written: &[GenericArg],
        at: NodeRef,
        sig: bool,
        self_ty: Option<TypeId>,
    ) -> Result<Vec<TypeId>, CheckError> {
        let pl = self.params_of(item);
        let (explicit, own_params, defaults) = {
            let l = self.plist(pl);
            (l.explicit, l.own_params().to_vec(), l.defaults.clone())
        };
        let mut out: Vec<TypeId> = Vec::with_capacity(explicit);
        if written.len() > explicit {
            self.report(
                at,
                DiagnosticKind::GenericArity {
                    expected: u32::try_from(explicit).unwrap_or(u32::MAX),
                    found: u32::try_from(written.len()).unwrap_or(u32::MAX),
                },
            );
            return Ok(alloc::vec![TypeId::ERROR; explicit]);
        }
        for &w in written {
            out.push(self.lower_arg(w, sig)?);
        }
        let mut missing = false;
        while out.len() < explicit {
            let i = out.len();
            match defaults.get(i).copied().flatten() {
                Some(d) => {
                    let t = self.lower_arg(d, true)?;
                    // A default may mention earlier parameters (and `Self`).
                    let mut from: Vec<TypeId> = own_params.get(..i).unwrap_or(&[]).to_vec();
                    let mut to: Vec<TypeId> = out.clone();
                    if let (Some(s), ItemKind::Interface(_)) = (self_ty, self.item_kind(item)) {
                        from.push(self.types.self_of(item));
                        to.push(s);
                    }
                    let t = self.subst(t, &from, &to)?;
                    out.push(t);
                }
                None if !sig => {
                    let v = self.fresh(GENERAL);
                    out.push(v);
                }
                None => {
                    missing = true;
                    out.push(TypeId::ERROR);
                }
            }
        }
        if missing {
            self.report(
                at,
                DiagnosticKind::GenericArity {
                    expected: u32::try_from(explicit).unwrap_or(u32::MAX),
                    found: u32::try_from(written.len()).unwrap_or(u32::MAX),
                },
            );
        }
        Ok(out)
    }

    /// The positional generic arguments written on a path segment.
    pub(crate) fn written_args(&self, args: hir_lang::List<GenericArg>) -> Vec<GenericArg> {
        self.hir
            .list(args)
            .iter()
            .copied()
            .filter(|a| matches!(a, GenericArg::Ty(_) | GenericArg::Const(_)))
            .collect()
    }

    /// Instantiates `item`: `inherited` gives the owner's placeholders (fresh
    /// variables when `None`), `own` the item's own explicit arguments (fresh
    /// variables when `None`); `impl Trait` parameters always get fresh
    /// variables. Returns the arguments in placeholder order.
    pub(crate) fn instantiate(
        &mut self,
        item: ItemId,
        inherited: Option<&[TypeId]>,
        own: Option<&[TypeId]>,
    ) -> Vec<TypeId> {
        let pl = self.params_of(item);
        let (n, own_start, explicit) = {
            let l = self.plist(pl);
            (l.params.len(), l.own, l.explicit)
        };
        let mut args = Vec::with_capacity(n);
        for i in 0..n {
            let t = if i < own_start {
                inherited.and_then(|v| v.get(i).copied())
            } else if i < own_start + explicit {
                own.and_then(|v| v.get(i - own_start).copied())
            } else {
                None
            };
            let t = match t {
                Some(t) => t,
                None => self.fresh(GENERAL),
            };
            args.push(t);
        }
        args
    }

    /// Pushes the bounds of `item`, instantiated with `args`, as obligations
    /// checked at `at`.
    pub(crate) fn push_bounds(
        &mut self,
        item: ItemId,
        args: &[TypeId],
        at: NodeRef,
    ) -> Result<(), CheckError> {
        let bl = self.bounds_of(item)?;
        if self.blist(bl).bounds.is_empty() {
            return Ok(());
        }
        let params = self.placeholders(item);
        let entries = self.blist(bl).bounds.clone();
        for b in entries {
            let subject = self.subst(b.subject, &params, args)?;
            let subject = self.normalize(subject, at)?;
            let tr = self.subst(b.tr, &params, args)?;
            let tr = self.normalize(tr, at)?;
            self.oblige_impl(subject, tr, at);
            let binds = self.blist(bl).bindings_of(&b).to_vec();
            for (assoc, value) in binds {
                let value = self.subst(value, &params, args)?;
                let value = self.normalize(value, at)?;
                self.oblige_projection(subject, tr, assoc, value, at);
            }
        }
        Ok(())
    }

    // ------------------------------------------------------- substitution

    /// Replaces every placeholder `from[i]` in `t` by `to[i]`. Memoized per
    /// call: linear in the part of the type DAG that mentions placeholders.
    pub(crate) fn subst(
        &mut self,
        t: TypeId,
        from: &[TypeId],
        to: &[TypeId],
    ) -> Result<TypeId, CheckError> {
        if from.is_empty() {
            return Ok(t);
        }
        let root = self.resolve(t);
        let mut map: Vec<(TypeId, TypeId)> = from.iter().copied().zip(to.iter().copied()).collect();
        map.sort_unstable_by_key(|&(f, _)| f);
        // Only placeholders are mapped (the common case): placeholder-free
        // subterms are skipped in O(1). Otherwise every node is visited.
        let gated = map
            .iter()
            .all(|&(f, _)| self.types.node(f).tag.is_placeholder());
        // A class may be represented by a node whose variables are bound
        // to placeholders: only a node free of both is skipped.
        let skip = |n: &crate::types::Node| gated && !n.has_param && !n.has_var;
        if skip(&self.types.node(root)) {
            return Ok(root);
        }
        let limit = self.types.len();
        self.subst_epoch = self.subst_epoch.wrapping_add(1);
        if self.subst_epoch == 0 {
            self.subst_stamp.iter_mut().for_each(|s| *s = 0);
            self.subst_epoch = 1;
        }
        if self.subst_stamp.len() < limit {
            self.subst_stamp.resize(limit, 0);
            self.subst_memo.resize(limit, NONE);
        }
        let epoch = self.subst_epoch;
        let mut stack: Vec<(TypeId, bool)> = alloc::vec![(root, false)];
        let mut kids: Vec<TypeId> = Vec::new();
        while let Some((x, expanded)) = stack.pop() {
            self.meter.tick(1)?;
            if x.index() >= limit {
                continue;
            }
            let done = self.subst_stamp.get(x.index()) == Some(&epoch)
                && self.subst_memo.get(x.index()) != Some(&NONE);
            if done && !expanded {
                continue;
            }
            let rep = self.resolve(x);
            let n = self.types.node(rep);
            // Any node in the map is replaced (placeholders, and the opaque
            // results a function body sees as their hidden types).
            let mapped = map
                .binary_search_by_key(&rep, |&(f, _)| f)
                .ok()
                .and_then(|i| map.get(i))
                .map(|&(_, r)| r);
            let value = if let Some(r) = mapped {
                Some(r)
            } else if skip(&n)
                || n.tag.is_placeholder()
                || (!expanded && !has_children(&self.types, rep))
            {
                Some(rep)
            } else if !expanded {
                stack.push((x, true));
                let stamp = &self.subst_stamp;
                let memo = &self.subst_memo;
                self.types.for_each_child(rep, |k| {
                    let seen = k.index() < limit
                        && stamp.get(k.index()) == Some(&epoch)
                        && memo.get(k.index()) != Some(&NONE);
                    if !seen {
                        stack.push((k, false));
                    }
                });
                None
            } else {
                kids.clear();
                let stamp = &self.subst_stamp;
                let memo = &self.subst_memo;
                let infer = &self.infer;
                let types = &self.types;
                types.for_each_child(rep, |k| {
                    let v = if k.index() < limit && stamp.get(k.index()) == Some(&epoch) {
                        memo.get(k.index()).copied().unwrap_or(NONE)
                    } else {
                        NONE
                    };
                    kids.push(if v == NONE {
                        // Placeholder-free (never pushed) or out of range.
                        infer.resolve(k)
                    } else {
                        TypeId::from_raw(v)
                    });
                });
                Some(self.types.rebuild(rep, &kids))
            };
            if let Some(v) = value {
                if let (Some(s), Some(m)) = (
                    self.subst_stamp.get_mut(x.index()),
                    self.subst_memo.get_mut(x.index()),
                ) {
                    *s = epoch;
                    *m = v.raw();
                }
            }
        }
        let out = if root.index() < limit && self.subst_stamp.get(root.index()) == Some(&epoch) {
            self.subst_memo
                .get(root.index())
                .copied()
                .filter(|&v| v != NONE)
                .map_or(root, TypeId::from_raw)
        } else {
            root
        };
        Ok(out)
    }

    /// The fields' substitution for an instance `Adt(item, args)`: the
    /// item's placeholders and the instance's arguments.
    pub(crate) fn adt_subst(&mut self, t: TypeId) -> Option<(ItemId, Vec<TypeId>, Vec<TypeId>)> {
        let r = self.resolve(t);
        let n = self.types.node(r);
        if n.tag != Tag::Adt {
            return None;
        }
        let item = ItemId::from_index(n.x as usize)?;
        let args = self.types.kids(r).to_vec();
        let params = self.placeholders(item);
        Some((item, params, args))
    }

    /// The nominal type of `item` with fresh arguments (a use: a constructor,
    /// a record literal, a pattern).
    pub(crate) fn adt_fresh(&mut self, item: ItemId) -> TypeId {
        self.name_item(item);
        let args = self.instantiate(item, None, None);
        self.types.adt_with(item, &args)
    }

    /// The nominal type of `item` applied to its own placeholders (inside
    /// the item).
    pub(crate) fn adt_identity(&mut self, item: ItemId) -> TypeId {
        self.name_item(item);
        let params = self.placeholders(item);
        self.types.adt_with(item, &params)
    }

    /// Whether `t` is a placeholder of the item being checked (or of an
    /// opaque type, a rigid projection): a type only bounds describe.
    pub(crate) fn is_rigid(&self, t: TypeId) -> bool {
        matches!(
            self.types.get(self.resolve(t)),
            Type::Param(_)
                | Type::ImplParam(_)
                | Type::SelfOf(_)
                | Type::Projection { .. }
                | Type::Opaque { .. }
        )
    }

    /// The display name of a symbol-bearing item.
    pub(crate) fn item_symbol(&self, item: ItemId) -> Option<Symbol> {
        self.hir
            .get_item(item)
            .and_then(|it| it.name)
            .map(|n| n.sym)
    }
}

/// Items whose generic parameters (and bounds) their members see.
pub(crate) fn is_member_owner(kind: &ItemKind) -> bool {
    matches!(
        kind,
        ItemKind::Impl(_) | ItemKind::Class(_) | ItemKind::Interface(_)
    )
}

/// Whether a node has children (leaves are their own substitution).
fn has_children(types: &crate::types::Types, t: TypeId) -> bool {
    let mut any = false;
    types.for_each_child(t, |_| any = true);
    any
}
