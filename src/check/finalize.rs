//! After checking: literal defaults, late operand checks, literal ranges,
//! inference failures, and replacing every recorded type by its resolved,
//! variable-free form.

use alloc::vec::Vec;

use hir_lang::{Expr, ExprId, NodeRef, PathId};

use super::Ctx;
use crate::{
    diag::DiagnosticKind,
    error::CheckError,
    infer::{FLOAT, GENERAL, INT},
    mono::MonoPlan,
    typed::{NONE, OpClass, Stats, Typed, WKind},
    types::{Tag, Type, TypeId},
};

impl Ctx<'_> {
    pub(crate) fn into_typed(mut self) -> Result<Typed, CheckError> {
        let mut op_classes = Vec::new();
        let mut plan = MonoPlan::default();
        if self.profile.is_static() {
            self.solve()?;
            self.default_literals();
            // Goals that waited on literals.
            let stuck = core::mem::take(&mut self.stuck);
            self.pending.extend(stuck);
            self.solve()?;
            let rest = core::mem::take(&mut self.pending);
            self.stuck = rest;
            self.recheck_deferred_ops()?;
            self.check_literal_ranges();
            self.report_unresolved()?;
            self.zonk_all()?;
            self.check_matches()?;
            plan = self.build_plan()?;
            self.collect_op_classes(&mut op_classes);
        } else {
            for &e in &self.idx.exprs {
                if matches!(self.hir.expr(e), Expr::Op { .. }) {
                    op_classes.push((e, OpClass::Dynamic));
                }
            }
        }
        op_classes.sort_by_key(|&(e, _)| e);
        // Source order: by span start, then discovery (the sort is stable).
        self.diags.sort_by_key(|d| d.origin.span.start());
        self.coercions.sort_by_key(|&(e, _, _)| e);
        self.coercions.dedup_by_key(|c| c.0);
        self.methods.sort_by_key(|&(e, _)| e);
        self.methods.dedup_by_key(|m| m.0);
        // Uses by expression (the first recorded wins).
        let mut insts = Vec::with_capacity(self.uses.len());
        let mut inst_args = Vec::new();
        let mut uses = core::mem::take(&mut self.uses);
        uses.sort_by_key(|u| u.at);
        uses.dedup_by_key(|u| u.at);
        for u in &uses {
            let args = self
                .use_args
                .get(u.args.0 as usize..(u.args.0 as usize).saturating_add(u.args.1 as usize))
                .unwrap_or(&[]);
            let start = u32::try_from(inst_args.len()).unwrap_or(NONE);
            inst_args.extend_from_slice(args);
            insts.push((u.at, u.callee, start, u.args.1, u.dispatch));
        }
        // Witnesses: by match, then in the order found; with the names of
        // the variants and records they mention.
        self.witnesses.sort_by_key(|&(e, _, _)| e);
        let mut wnames = Vec::new();
        let mut witems = Vec::new();
        for n in &self.wnodes {
            match n.kind {
                WKind::Variant(v) => {
                    if let Some(var) = self.hir.variant(v) {
                        wnames.push((u32::try_from(v.index()).unwrap_or(NONE), var.name.sym));
                    }
                }
                WKind::Item(i) => {
                    if let Some(sym) = self.item_symbol(i) {
                        witems.push((u32::try_from(i.index()).unwrap_or(NONE), sym));
                    }
                }
                _ => {}
            }
        }
        wnames.sort_unstable();
        wnames.dedup_by_key(|w| w.0);
        witems.sort_unstable();
        witems.dedup_by_key(|w| w.0);
        let mut opaque = core::mem::take(&mut self.hidden);
        opaque.sort_by_key(|&(t, _)| t);
        let path_defs = self
            .path_def
            .iter()
            .enumerate()
            .filter_map(|(i, d)| Some((PathId::from_index(i)?, (*d)?)))
            .collect();
        Ok(Typed {
            stats: Stats {
                steps: self.meter.used,
                type_nodes: self.types.footprint(),
            },
            types: self.types,
            exprs: self.expr_ty,
            pats: self.pat_ty,
            binders: self.binder_ty,
            path_defs,
            methods: self.methods,
            coercions: self.coercions,
            op_classes,
            insts,
            inst_args,
            mono: plan,
            opaque,
            witnesses: self.witnesses,
            wnodes: self.wnodes,
            wsyms: self.wsyms,
            wnames,
            witems,
            diagnostics: self.diags,
            profile: self.profile,
        })
    }

    /// Unconstrained literals take the profile's default types.
    fn default_literals(&mut self) {
        let vars = core::mem::take(&mut self.infer.vars);
        for &v in &vars {
            let r = self.resolve(v);
            if self.types.node(r).tag != Tag::Var {
                continue;
            }
            let default = match self.infer.class_of(r) {
                INT => self.profile.default_int,
                FLOAT => self.profile.default_float,
                _ => continue,
            };
            self.infer.force(&self.types, r, TypeId::prim(default));
        }
        self.infer.vars = vars;
    }

    fn check_literal_ranges(&mut self) {
        let lits = core::mem::take(&mut self.int_lits);
        for &(at, var, lit) in &lits {
            if let Some(p) = self.prim_of(var) {
                if p.is_int() && !lit.fits(p) {
                    self.report(
                        at,
                        DiagnosticKind::LiteralOutOfRange {
                            ty: TypeId::prim(p),
                        },
                    );
                }
            }
        }
        self.int_lits = lits;
    }

    /// Reports each variable that nothing determined, once, at the first
    /// binder (else expression) whose type mentions it, then gives up on it.
    fn report_unresolved(&mut self) -> Result<(), CheckError> {
        let mut memo: Vec<u32> = Vec::new();
        let mut reported: Vec<bool> = alloc::vec![false; self.types.len()];
        for i in 0..self.binder_ty.len() {
            let raw = self.binder_ty.get(i).copied().unwrap_or(NONE);
            let site = self.binder_site.get(i).copied().unwrap_or(NONE);
            if raw == NONE || site == NONE {
                continue;
            }
            if let Some(root) = self.infer.first_free(
                &self.types,
                &mut memo,
                &mut self.meter,
                TypeId::from_raw(raw),
            )? {
                if first_report(&mut reported, root) {
                    if let Some(p) = hir_lang::PatId::from_index(site as usize) {
                        self.report(NodeRef::Pat(p), DiagnosticKind::CannotInfer);
                    }
                }
            }
        }
        let exprs = core::mem::take(&mut self.idx.exprs);
        for &e in &exprs {
            let raw = self.expr_ty.get(e.index()).copied().unwrap_or(NONE);
            if raw == NONE {
                continue;
            }
            if let Some(root) = self.infer.first_free(
                &self.types,
                &mut memo,
                &mut self.meter,
                TypeId::from_raw(raw),
            )? {
                if first_report(&mut reported, root) {
                    self.report(NodeRef::Expr(e), DiagnosticKind::CannotInfer);
                }
            }
        }
        self.idx.exprs = exprs;
        // Interface goals that never got a known type.
        let stuck = core::mem::take(&mut self.stuck);
        for ob in &stuck {
            let ty = match ob.goal {
                super::traits::Goal::Impl { ty, .. } | super::traits::Goal::Project { ty, .. } => {
                    ty
                }
            };
            if let Some(root) =
                self.infer
                    .first_free(&self.types, &mut memo, &mut self.meter, ty)?
            {
                if first_report(&mut reported, root) {
                    self.report(ob.at, DiagnosticKind::CannotInfer);
                }
            }
        }
        // Everything still unknown becomes `{error}`.
        let vars = core::mem::take(&mut self.infer.vars);
        for &v in &vars {
            let r = self.resolve(v);
            if self.types.node(r).tag == Tag::Var && self.infer.class_of(r) == GENERAL {
                self.infer.force(&self.types, r, TypeId::ERROR);
            }
        }
        self.infer.vars = vars;
        Ok(())
    }

    /// Resolves every recorded type, sharing one memo: linear in the types'
    /// DAG, however many nodes mention the same type.
    fn zonk_all(&mut self) -> Result<(), CheckError> {
        let mut memo: Vec<u32> = Vec::new();
        let mut tables = [
            core::mem::take(&mut self.expr_ty),
            core::mem::take(&mut self.pat_ty),
            core::mem::take(&mut self.binder_ty),
        ];
        for table in &mut tables {
            for slot in table.iter_mut() {
                if *slot != NONE {
                    let z = self.infer.zonk(
                        &mut self.types,
                        &mut memo,
                        &mut self.meter,
                        TypeId::from_raw(*slot),
                    )?;
                    *slot = z.raw();
                }
            }
        }
        let [exprs, pats, binders] = tables;
        self.expr_ty = exprs;
        self.pat_ty = pats;
        self.binder_ty = binders;
        let mut coercions = core::mem::take(&mut self.coercions);
        for c in &mut coercions {
            c.2 = self
                .infer
                .zonk(&mut self.types, &mut memo, &mut self.meter, c.2)?;
        }
        self.coercions = coercions;
        let mut args = core::mem::take(&mut self.use_args);
        for a in &mut args {
            *a = self
                .infer
                .zonk(&mut self.types, &mut memo, &mut self.meter, *a)?;
        }
        self.use_args = args;
        let mut hidden = core::mem::take(&mut self.hidden);
        for h in &mut hidden {
            h.1 = self
                .infer
                .zonk(&mut self.types, &mut memo, &mut self.meter, h.1)?;
        }
        self.hidden = hidden;
        let mut dyn_uses = core::mem::take(&mut self.dyn_uses);
        for d in &mut dyn_uses {
            d.1 = self
                .infer
                .zonk(&mut self.types, &mut memo, &mut self.meter, d.1)?;
            d.2 = self
                .infer
                .zonk(&mut self.types, &mut memo, &mut self.meter, d.2)?;
        }
        self.dyn_uses = dyn_uses;
        let mut diags = core::mem::take(&mut self.diags);
        for d in &mut diags {
            let mut err = None;
            d.kind.types_mut(|t| {
                if err.is_none() {
                    match self
                        .infer
                        .zonk(&mut self.types, &mut memo, &mut self.meter, *t)
                    {
                        Ok(z) => *t = z,
                        Err(e) => err = Some(e),
                    }
                }
            });
            if let Some(e) = err {
                return Err(e);
            }
        }
        self.diags = diags;
        crate::infer::Infer::check_size(&self.types, &self.meter)
    }

    fn collect_op_classes(&self, out: &mut Vec<(ExprId, OpClass)>) {
        let mut nulls = self.null_checks.clone();
        nulls.sort_unstable();
        for &e in &self.idx.exprs {
            let Expr::Op { args, .. } = *self.hir.expr(e) else {
                continue;
            };
            if nulls.binary_search(&e).is_ok() {
                out.push((e, OpClass::NullCheck));
                continue;
            }
            let Some(&first) = self.hir.list(args).first() else {
                continue;
            };
            let t = self.expr_ty.get(first.index()).copied().unwrap_or(NONE);
            if t == NONE {
                continue;
            }
            let class = match self.types.get(TypeId::from_raw(t)) {
                Type::Prim(p) if p.is_int() => OpClass::Int(p),
                Type::Prim(p) if p.is_float() => OpClass::Float(p),
                Type::Prim(hir_lang::Prim::Bool) => OpClass::Bool,
                Type::Prim(hir_lang::Prim::Char) => OpClass::Char,
                Type::Prim(hir_lang::Prim::Str) => OpClass::Str,
                _ => continue,
            };
            out.push((e, class));
        }
    }
}

/// Marks variable root `root` reported; `true` the first time.
fn first_report(reported: &mut [bool], root: u32) -> bool {
    match reported.get_mut(root as usize) {
        Some(seen) if !*seen => {
            *seen = true;
            true
        }
        _ => false,
    }
}
