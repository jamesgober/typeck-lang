//! The monomorphization plan (see [`crate::MonoPlan`]).
//!
//! Every use of a generic item was recorded with its arguments, in the
//! placeholders of the item containing the use. The plan starts from the
//! uses in non-generic code (whose arguments are concrete), and walks each
//! reached instance's own uses with its arguments substituted: a
//! breadth-first closure over (item, arguments), each pair once. Interface
//! methods called on placeholders are resolved to the implementing method
//! of each concrete instance. A shared (dictionary-passing) item is walked
//! once with its own placeholders; the call sites that reach it with
//! concrete arguments add the implementations its bounds need (the
//! dictionaries' methods). Instance chains longer than the budget's trait
//! depth (polymorphic recursion) are reported and cut.

use alloc::{collections::BTreeMap, vec::Vec};

use hir_lang::{ItemId, ItemKind, NodeRef};

use super::Ctx;
use crate::{
    diag::DiagnosticKind,
    error::CheckError,
    mono::{Dispatch, MonoPlan, Strategy},
    typed::NONE,
    types::TypeId,
};

/// A queued instance: the item, its arguments, its chain depth.
struct Work {
    item: ItemId,
    args: Vec<TypeId>,
    depth: u32,
    strategy: Strategy,
}

impl Ctx<'_> {
    /// How the plan compiles `item`: an attribute declared to the checker
    /// wins, then the profile's policy.
    fn strategy_of(&self, item: ItemId) -> Strategy {
        let mut items = alloc::vec![item];
        if let Some(o) = self.idx.owner_of(item) {
            items.push(o);
        }
        for it in items {
            for attr in self.hir.attrs(NodeRef::Item(it)) {
                if let Some(&(_, s)) = self
                    .host
                    .mono_attrs
                    .iter()
                    .find(|&&(n, _)| n == attr.name.sym)
                {
                    return s;
                }
            }
        }
        match self.profile.mono {
            crate::mono::MonoPolicy::Copy => Strategy::Copy,
            crate::mono::MonoPolicy::Shared => Strategy::Shared,
            crate::mono::MonoPolicy::Selective { max_nodes } => {
                if self.item_size.get(item.index()).copied().unwrap_or(0) <= max_nodes {
                    Strategy::Copy
                } else {
                    Strategy::Shared
                }
            }
        }
    }

    /// Builds the plan. Runs after zonking: recorded arguments are
    /// variable-free.
    pub(crate) fn build_plan(&mut self) -> Result<MonoPlan, CheckError> {
        let mark = self.diags.len();
        let plan = self.build_plan_inner();
        // Re-resolving goals on concrete instances may meet problems the
        // check already reported at their call sites: only the plan's own
        // finding (unbounded instantiation) is kept.
        let mut i = 0usize;
        self.diags.retain(|d| {
            i += 1;
            i <= mark || d.kind == DiagnosticKind::RecursiveInstantiation
        });
        plan
    }

    fn build_plan_inner(&mut self) -> Result<MonoPlan, CheckError> {
        let mut plan = MonoPlan::default();
        if self.uses.is_empty() {
            return Ok(plan);
        }
        // Uses by owner.
        let mut order: Vec<(u32, u32)> = self
            .uses
            .iter()
            .enumerate()
            .map(|(i, u)| {
                (
                    u.owner
                        .map_or(NONE, |o| u32::try_from(o.index()).unwrap_or(NONE)),
                    u32::try_from(i).unwrap_or(NONE),
                )
            })
            .collect();
        order.sort_unstable();
        let mut seen: BTreeMap<(ItemId, Vec<TypeId>), ()> = BTreeMap::new();
        let mut queue: Vec<Work> = Vec::new();
        // Roots: owners with no placeholders (and constant contexts).
        let mut owners: Vec<u32> = order.iter().map(|&(o, _)| o).collect();
        owners.dedup();
        let mut roots: Vec<Option<ItemId>> = Vec::new();
        for o in owners {
            let item = if o == NONE {
                None
            } else {
                ItemId::from_index(o as usize)
            };
            match item {
                None => roots.push(None),
                Some(i) if !self.is_generic_item(i) => roots.push(Some(i)),
                Some(_) => {}
            }
        }
        for root in roots {
            self.meter.tick(1)?;
            self.walk_uses(root, &[], 0, &order, &mut seen, &mut queue, &mut plan)?;
        }
        let mut qi = 0;
        while let Some(w) = queue.get(qi) {
            qi += 1;
            self.meter.tick(1)?;
            let (item, args, depth, strategy) = (w.item, w.args.clone(), w.depth, w.strategy);
            if strategy == Strategy::Shared && self.types_have_params(&args) {
                // The shared body itself.
                self.walk_uses(
                    Some(item),
                    &args,
                    depth,
                    &order,
                    &mut seen,
                    &mut queue,
                    &mut plan,
                )?;
            } else if strategy == Strategy::Shared {
                // A call site with concrete arguments: the dictionaries.
                self.dictionaries(item, &args, depth, &mut seen, &mut queue, &mut plan)?;
            } else {
                self.walk_uses(
                    Some(item),
                    &args,
                    depth,
                    &order,
                    &mut seen,
                    &mut queue,
                    &mut plan,
                )?;
            }
        }
        Ok(plan)
    }

    fn types_have_params(&self, args: &[TypeId]) -> bool {
        args.iter().any(|&t| self.types.node(t).has_param)
    }

    /// Walks the uses inside `owner`, instantiated with `args`.
    #[allow(clippy::too_many_arguments)]
    fn walk_uses(
        &mut self,
        owner: Option<ItemId>,
        args: &[TypeId],
        depth: u32,
        order: &[(u32, u32)],
        seen: &mut BTreeMap<(ItemId, Vec<TypeId>), ()>,
        queue: &mut Vec<Work>,
        plan: &mut MonoPlan,
    ) -> Result<(), CheckError> {
        let key = owner.map_or(NONE, |o| u32::try_from(o.index()).unwrap_or(NONE));
        let lo = order.partition_point(|&(o, _)| o < key);
        let hi = order.partition_point(|&(o, _)| o <= key);
        let params = match owner {
            Some(o) => self.placeholders(o),
            None => Vec::new(),
        };
        let saved = self.cur_item;
        self.cur_item = owner;
        for &(_, ui) in order.get(lo..hi).unwrap_or(&[]) {
            self.meter.tick(1)?;
            let Some(u) = self.uses.get(ui as usize).copied() else {
                continue;
            };
            if u.dispatch == Dispatch::Dynamic {
                continue;
            }
            let raw: Vec<TypeId> = self
                .use_args
                .get(u.args.0 as usize..(u.args.0 as usize).saturating_add(u.args.1 as usize))
                .unwrap_or(&[])
                .to_vec();
            let at = NodeRef::Expr(u.at);
            let mut cargs = Vec::with_capacity(raw.len());
            for t in raw {
                let t = self.subst(t, &params, args)?;
                cargs.push(self.normalize(t, at)?);
            }
            let (callee, cargs) = if u.dispatch == Dispatch::Bound {
                self.resolve_bound_call(u.callee, cargs, at)?
            } else {
                (u.callee, cargs)
            };
            if !matches!(self.item_kind(callee), ItemKind::Fn(_)) || !self.is_generic_item(callee) {
                continue;
            }
            self.add_instance(callee, cargs, depth + 1, at, seen, queue, plan)?;
        }
        // Values coerced to `dyn` here: their implementations' methods are
        // the vtable.
        let dyns: Vec<(TypeId, TypeId)> = self
            .dyn_uses
            .iter()
            .filter(|&&(o, _, _)| o == owner)
            .map(|&(_, t, tr)| (t, tr))
            .collect();
        let at = owner.map_or(NodeRef::Item(self.hir.root()), NodeRef::Item);
        for (t, tr) in dyns {
            self.meter.tick(1)?;
            let t = self.subst(t, &params, args)?;
            let tr = self.subst(tr, &params, args)?;
            self.impl_methods(t, tr, depth, at, seen, queue, plan)?;
        }
        self.cur_item = saved;
        Ok(())
    }

    /// Every method of the implementation of `tr` for a concrete `t` (a
    /// dictionary or a vtable).
    #[allow(clippy::too_many_arguments)]
    fn impl_methods(
        &mut self,
        t: TypeId,
        tr: TypeId,
        depth: u32,
        at: NodeRef,
        seen: &mut BTreeMap<(ItemId, Vec<TypeId>), ()>,
        queue: &mut Vec<Work>,
        plan: &mut MonoPlan,
    ) -> Result<(), CheckError> {
        if self.types.node(t).has_param || self.is_rigid(t) || self.is_err(t) {
            return Ok(());
        }
        let Some((rec, matched)) = self.select_one(t, tr)? else {
            return Ok(());
        };
        let inst = self.commit_rec(rec, matched, Some(tr), at)?;
        let inst = self.zonk_list(&inst)?;
        let members: Vec<ItemId> = self
            .tr
            .members
            .iter()
            .filter(|&&(r, _, m)| r == rec && matches!(self.item_kind(m), ItemKind::Fn(_)))
            .map(|&(_, _, m)| m)
            .collect();
        for m in members {
            if !self.is_generic_item(m) {
                continue;
            }
            // Methods with parameters of their own are instantiated where
            // called; the table holds the rest.
            let pl = self.params_of(m);
            if self.plist(pl).explicit > 0 {
                continue;
            }
            self.add_instance(m, inst.clone(), depth + 1, at, seen, queue, plan)?;
        }
        Ok(())
    }

    /// An interface method called through a bound: on a concrete `Self`,
    /// the implementing method (or the interface's default).
    fn resolve_bound_call(
        &mut self,
        decl: ItemId,
        args: Vec<TypeId>,
        at: NodeRef,
    ) -> Result<(ItemId, Vec<TypeId>), CheckError> {
        let Some(iface) = self.idx.owner_of(decl) else {
            return Ok((decl, args));
        };
        let Some(&self_ty) = args.first() else {
            return Ok((decl, args));
        };
        if self.types.node(self_ty).has_param || self.is_rigid(self_ty) || self.is_err(self_ty) {
            return Ok((decl, args));
        }
        let explicit = {
            let pl = self.params_of(iface);
            self.plist(pl).explicit
        };
        let tr_args: Vec<TypeId> = args.get(1..1 + explicit).unwrap_or(&[]).to_vec();
        let own: Vec<TypeId> = args.get(1 + explicit..).unwrap_or(&[]).to_vec();
        let tr = self.types.trait_ref(iface, &tr_args);
        let Some(name) = self.item_symbol(decl) else {
            return Ok((decl, args));
        };
        let Some((rec, matched)) = self.select_one(self_ty, tr)? else {
            return Ok((decl, args));
        };
        let inst = self.commit_rec(rec, matched, Some(tr), at)?;
        let inst = self.zonk_list(&inst)?;
        let overriding = self
            .rec_members(rec, name)
            .into_iter()
            .find(|&m| matches!(self.item_kind(m), ItemKind::Fn(_)));
        Ok(match overriding {
            Some(m) => {
                let mut a = inst;
                a.extend(own);
                (m, a)
            }
            None => (decl, args),
        })
    }

    /// Variable-free forms of `ts` (after the plan's own unifications).
    fn zonk_list(&mut self, ts: &[TypeId]) -> Result<Vec<TypeId>, CheckError> {
        let mut memo = Vec::new();
        let mut out = Vec::with_capacity(ts.len());
        for &t in ts {
            out.push(
                self.infer
                    .zonk(&mut self.types, &mut memo, &mut self.meter, t)?,
            );
        }
        Ok(out)
    }

    #[allow(clippy::too_many_arguments)]
    fn add_instance(
        &mut self,
        item: ItemId,
        args: Vec<TypeId>,
        depth: u32,
        at: NodeRef,
        seen: &mut BTreeMap<(ItemId, Vec<TypeId>), ()>,
        queue: &mut Vec<Work>,
        plan: &mut MonoPlan,
    ) -> Result<(), CheckError> {
        let mut strategy = self.strategy_of(item);
        let mut args = args;
        if self.types_have_params(&args) {
            // Reached from shared code: the callee is shared too.
            strategy = Strategy::Shared;
            args = self.placeholders(item);
        }
        let key = (item, args.clone());
        if seen.contains_key(&key) {
            return Ok(());
        }
        if depth > self.meter.budget.trait_depth {
            self.report(at, DiagnosticKind::RecursiveInstantiation);
            return Ok(());
        }
        let _ = seen.insert(key, ());
        let start = u32::try_from(plan.args.len()).unwrap_or(NONE);
        plan.args.extend_from_slice(&args);
        plan.instances.push((
            item,
            start,
            u32::try_from(args.len()).unwrap_or(0),
            strategy,
        ));
        if strategy == Strategy::Shared && !self.types_have_params(&args) {
            // The shared body, once (it has placeholders: one level).
            let body = self.placeholders(item);
            self.add_instance(item, body, depth, at, seen, queue, plan)?;
        }
        queue.push(Work {
            item,
            args,
            depth,
            strategy,
        });
        Ok(())
    }

    /// The implementations a shared item's bounds need for concrete `args`:
    /// every method of each selected implementation.
    fn dictionaries(
        &mut self,
        item: ItemId,
        args: &[TypeId],
        depth: u32,
        seen: &mut BTreeMap<(ItemId, Vec<TypeId>), ()>,
        queue: &mut Vec<Work>,
        plan: &mut MonoPlan,
    ) -> Result<(), CheckError> {
        let bl = self.bounds_of(item)?;
        let params = self.placeholders(item);
        let entries = self.blist(bl).bounds.clone();
        let at = NodeRef::Item(item);
        for b in entries {
            self.meter.tick(1)?;
            let subject = self.subst(b.subject, &params, args)?;
            let tr = self.subst(b.tr, &params, args)?;
            if self.types.node(subject).has_param || self.is_rigid(subject) {
                continue;
            }
            self.impl_methods(subject, tr, depth, at, seen, queue, plan)?;
        }
        Ok(())
    }
}
