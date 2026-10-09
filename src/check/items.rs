//! The static driver: every live item is checked on its own (items cannot
//! see each other's locals, HIR §3.2), then any live expression no item
//! reached (array lengths and constant arguments inside annotations) is
//! checked as a root of its own.

use hir_lang::{Effects, ItemId, ItemKind, NodeRef};

use super::{Ctx, Frame};
use crate::{
    diag::{DiagnosticKind, Feature},
    error::CheckError,
    infer::{GENERAL, INT},
    types::TypeId,
};

impl Ctx<'_> {
    pub(crate) fn check_static(&mut self) -> Result<(), CheckError> {
        let items = core::mem::take(&mut self.idx.items);
        for &item in &items {
            self.meter.tick(1)?;
            self.check_item(item)?;
        }
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
        Ok(())
    }

    /// The frame of a constant context: nothing returns from it.
    fn const_frame(&self) -> Frame {
        Frame {
            ret: TypeId::ERROR,
            throws: None,
            yields: None,
        }
    }

    fn report_generic(&mut self, item: ItemId, own_generics: bool) {
        if own_generics {
            self.report(
                NodeRef::Item(item),
                DiagnosticKind::Unsupported {
                    feature: Feature::Generics,
                },
            );
        }
    }

    fn check_item(&mut self, item: ItemId) -> Result<(), CheckError> {
        let hir = self.hir;
        let it = *hir.item(item);
        self.cur_self = self.item_self(item);
        match it.kind {
            ItemKind::Fn(def) => {
                self.report_generic(item, !def.generics.params.is_empty());
                self.check_fn(item, def)?;
            }
            ItemKind::Const { value, .. } | ItemKind::Global { init: value, .. } => {
                let t = self.decl_type(item)?;
                if let Some(v) = value {
                    self.set_expect(v, t);
                    self.run_in(v, self.const_frame())?;
                }
            }
            ItemKind::Record(def) => {
                self.report_generic(item, !def.generics.params.is_empty());
                self.cur_self = Some(self.types.adt(item));
                self.check_fields(hir.list(def.fields))?;
            }
            ItemKind::Class(def) => {
                self.report_generic(item, !def.generics.params.is_empty());
                self.cur_self = Some(self.types.adt(item));
                self.check_fields(hir.list(def.fields))?;
            }
            ItemKind::Sum(def) => {
                self.report_generic(item, !def.generics.params.is_empty());
                self.cur_self = Some(self.types.adt(item));
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
            ItemKind::Alias { generics, ty } => {
                if generics.params.is_empty() {
                    let self_ty = self.cur_self;
                    let _ = self.lower_ty(ty, self_ty, true)?;
                } else {
                    self.report_generic(item, true);
                }
            }
            ItemKind::Interface(def) => {
                self.report_generic(item, !def.generics.params.is_empty());
            }
            ItemKind::Impl(def) => {
                // Interface conformance is checked with traits (0.5); an
                // impl's members are checked as items.
                self.report_generic(item, !def.generics.params.is_empty());
            }
            ItemKind::Module { body: None, .. }
            | ItemKind::AssocType { .. }
            | ItemKind::MixinUse(_)
            | ItemKind::Import { .. }
            | ItemKind::Err => {}
        }
        Ok(())
    }

    /// Runs `root` inside `frame`.
    fn run_in(&mut self, root: hir_lang::ExprId, frame: Frame) -> Result<(), CheckError> {
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
            let frame = self.frame_for(ret, throws, def.effects);
            let want = if def.effects.contains(Effects::YIELD) {
                TypeId::UNIT
            } else {
                ret
            };
            self.set_expect(body, want);
            self.run_in(body, frame)?;
        }
        Ok(())
    }
}
