//! The static driver: every live item is checked on its own (items cannot
//! see each other's locals, HIR §3.2), then any live expression no item
//! reached (array lengths and constant arguments inside annotations) is
//! checked as a root of its own. Each item's pending interface goals are
//! solved when the item is done.

use alloc::vec::Vec;

use hir_lang::{Effects, ItemId, ItemKind};

use super::Ctx;
use crate::{
    error::CheckError,
    infer::{GENERAL, INT},
    types::TypeId,
};

impl Ctx<'_> {
    pub(crate) fn check_static(&mut self) -> Result<(), CheckError> {
        let items = core::mem::take(&mut self.idx.items);
        for &item in &items {
            self.meter.tick(1)?;
            self.cur_item = Some(item);
            self.check_item(item)?;
            self.solve_item_end()?;
        }
        self.cur_item = None;
        self.idx.items = items;
        // Expressions inside annotations (array lengths, constant generic
        // arguments) that no item checked.
        let exprs = core::mem::take(&mut self.idx.exprs);
        for &e in &exprs {
            if !self.typed(e) {
                self.cur_self = None;
                self.frames.push(self.const_frame());
                self.run(e)?;
                let _ = self.frames.pop();
            }
        }
        self.idx.exprs = exprs;
        self.solve_item_end()
    }

    /// The frame of a constant context: nothing returns from it.
    fn const_frame(&self) -> super::Frame {
        super::Frame {
            declared: TypeId::ERROR,
            ret: TypeId::ERROR,
            throws: None,
            yields: None,
        }
    }

    fn check_item(&mut self, item: ItemId) -> Result<(), CheckError> {
        let hir = self.hir;
        let it = *hir.item(item);
        self.cur_self = self.item_self(item);
        match it.kind {
            ItemKind::Fn(def) => self.check_fn(item, def)?,
            ItemKind::Const { value, .. } | ItemKind::Global { init: value, .. } => {
                let t = self.decl_type(item)?;
                if let Some(v) = value {
                    self.set_expect(v, t);
                    self.run_in(v, self.const_frame())?;
                }
            }
            ItemKind::Record(def) => {
                self.cur_self = Some(self.adt_identity(item));
                let _ = self.bounds_of(item)?;
                self.check_fields(hir.list(def.fields))?;
            }
            ItemKind::Class(def) => {
                self.cur_self = Some(self.adt_identity(item));
                let _ = self.bounds_of(item)?;
                self.check_fields(hir.list(def.fields))?;
                self.check_records_of(item)?;
            }
            ItemKind::Sum(def) => {
                self.cur_self = Some(self.adt_identity(item));
                let _ = self.bounds_of(item)?;
                for &v in hir.list(def.variants) {
                    let Some(variant) = hir.variant(v).copied() else {
                        continue;
                    };
                    self.check_fields(hir.list(variant.fields))?;
                    if let Some(d) = variant.discriminant {
                        let int = self.fresh(INT);
                        self.set_expect(d, int);
                        self.run_in(d, self.const_frame())?;
                    }
                }
            }
            ItemKind::Module {
                body: Some(body),
                effects,
                ..
            } => {
                // Top-level code (scripts, REPL entries): `return` values
                // are inferred.
                let ret = self.fresh(GENERAL);
                let frame = self.frame_for(ret, None, effects);
                self.run_in(body, frame)?;
            }
            ItemKind::Alias { ty, .. } => {
                let self_ty = self.cur_self;
                let saved = self.lower_ctx.replace(item);
                let r = self.lower_ty(ty, self_ty, true);
                self.lower_ctx = saved;
                let _ = r?;
            }
            ItemKind::Interface(_) => {
                // Bounds and supertraits are lowered (and reported) once.
                let _ = self.bounds_of(item)?;
                let s = self.types.self_of(item);
                let own = self.own_params(item);
                let tr = self.types.trait_ref(item, &own);
                let _ = self.elaborate(tr, s)?;
            }
            ItemKind::AssocType { default, .. } => {
                if let (Some(d), Some(owner)) = (default, self.idx.owner_of(item)) {
                    let s = self.types.self_of(owner);
                    let saved = self.lower_ctx.replace(owner);
                    let r = self.lower_ty(d, Some(s), true);
                    self.lower_ctx = saved;
                    let _ = r?;
                }
            }
            ItemKind::Impl(_) => {
                let _ = self.bounds_of(item)?;
                self.check_records_of(item)?;
            }
            ItemKind::Module { body: None, .. }
            | ItemKind::MixinUse(_)
            | ItemKind::Import { .. }
            | ItemKind::Err => {}
        }
        Ok(())
    }

    /// Conformance of the interface implementations an impl or class
    /// declares.
    fn check_records_of(&mut self, item: ItemId) -> Result<(), CheckError> {
        let recs: Vec<u32> = self
            .tr
            .recs
            .iter()
            .enumerate()
            .filter(|(_, r)| r.item == item && r.tr.is_some())
            .filter_map(|(i, _)| u32::try_from(i).ok())
            .collect();
        for rec in recs {
            self.check_conformance(rec)?;
        }
        Ok(())
    }

    /// Runs `root` inside `frame`.
    fn run_in(&mut self, root: hir_lang::ExprId, frame: super::Frame) -> Result<(), CheckError> {
        self.frames.push(frame);
        let r = self.run(root);
        let _ = self.frames.pop();
        r
    }

    fn check_fields(&mut self, fields: &[hir_lang::FieldId]) -> Result<(), CheckError> {
        for &f in fields {
            let t = self.field_type(f)?;
            if let Some(d) = self.hir.field(f).default {
                self.set_expect(d, t);
                self.run_in(d, self.const_frame())?;
            }
        }
        Ok(())
    }

    fn check_fn(&mut self, item: ItemId, def: hir_lang::FnDef) -> Result<(), CheckError> {
        let hir = self.hir;
        // Bounds are lowered (and reported) once, before the body relies on
        // them.
        let _ = self.bounds_of(item)?;
        let Some(sig) = self.sig(item)? else {
            return Ok(());
        };
        let (ret, throws) = match self.sig_arena.get(sig) {
            Some(s) => (s.ret, s.throws),
            None => (TypeId::ERROR, None),
        };
        for (i, &pid) in hir.list(def.params).iter().enumerate() {
            let param = *hir.param(pid);
            let ty = self
                .sig_arena
                .get(sig)
                .and_then(|s| s.params.get(i))
                .map_or(TypeId::ERROR, |p| p.ty);
            self.bind_param(param.pat, param.kind, ty)?;
            if let Some(d) = param.default {
                self.set_expect(d, ty);
                self.run_in(d, self.const_frame())?;
            }
        }
        if let Some(body) = def.body {
            // Inside the function, an `impl Trait` result is its hidden
            // type, inferred from the body.
            let (ret, hidden) = self.open_opaques(item, ret)?;
            let frame = self.frame_for(ret, throws, def.effects);
            let want = if def.effects.contains(Effects::YIELD) {
                TypeId::UNIT
            } else {
                ret
            };
            self.set_expect(body, want);
            self.run_in(body, frame)?;
            self.close_opaques(item, &hidden)?;
        }
        Ok(())
    }

    /// Replaces the opaque results of `item` in `ret` by fresh variables:
    /// (rewritten result, (opaque, its variable) pairs).
    fn open_opaques(
        &mut self,
        item: ItemId,
        ret: TypeId,
    ) -> Result<(TypeId, Vec<(TypeId, TypeId)>), CheckError> {
        let rpits: Vec<hir_lang::TyId> = self
            .impl_tys_of(item)
            .into_iter()
            .filter(|&(_, o, rpit)| o == item && rpit)
            .map(|(t, _, _)| t)
            .collect();
        if rpits.is_empty() {
            return Ok((ret, Vec::new()));
        }
        let params = self.placeholders(item);
        let mut pairs = Vec::new();
        for t in rpits {
            let o = self.types.opaque(t, &params);
            let v = self.fresh(GENERAL);
            pairs.push((o, v));
            self.hidden.push((t, v));
        }
        let (from, to): (Vec<TypeId>, Vec<TypeId>) = pairs.iter().copied().unzip();
        let ret = self.subst(ret, &from, &to)?;
        Ok((ret, pairs))
    }

    /// The hidden types of `item`'s opaque results must satisfy their
    /// bounds.
    fn close_opaques(
        &mut self,
        item: ItemId,
        pairs: &[(TypeId, TypeId)],
    ) -> Result<(), CheckError> {
        if pairs.is_empty() {
            return Ok(());
        }
        let bl = self.bounds_of(item)?;
        let entries = self.blist(bl).bounds.clone();
        for b in entries {
            let Some(&(_, hidden)) = pairs.iter().find(|&&(o, _)| o == b.subject) else {
                continue;
            };
            self.oblige_impl(hidden, b.tr, b.at);
            let binds = self.blist(bl).bindings_of(&b).to_vec();
            for (assoc, value) in binds {
                self.oblige_projection(hidden, b.tr, assoc, value, b.at);
            }
        }
        Ok(())
    }
}
