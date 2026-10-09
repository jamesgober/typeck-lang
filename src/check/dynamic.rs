//! The `Dynamic` discipline: every value is `any`; the only errors are the
//! ones that are certain whatever the run-time values (profile toggle
//! `certain_errors`): calling a function of this unit with arguments that
//! cannot match its parameters, a constructor or constructor pattern of the
//! wrong length, and a record literal naming a field its record does not
//! declare.
//!
//! No annotation is lowered (annotations are hints for the runtime), so a
//! dynamic check never reports a type error.

use hir_lang::{
    ArgKind, Def, Expr, ExprId, ItemKind, NodeRef, Pat, PathId, Res, Shape, Stmt, VariantId,
};

use super::{Ctx, call::CallTarget, index::FieldOwner};
use crate::{diag::DiagnosticKind, error::CheckError, typed::NONE, types::TypeId};

/// What a call's callee names, when that is certain.
enum Known {
    Fn(hir_lang::ItemId),
    /// A tuple-shaped record or variant constructor with this many fields.
    Ctor(usize),
}

impl Ctx<'_> {
    pub(crate) fn check_dynamic(&mut self) -> Result<(), CheckError> {
        let any = TypeId::ANY.raw();
        let hir = self.hir;
        let exprs = core::mem::take(&mut self.idx.exprs);
        let pats = core::mem::take(&mut self.idx.pats);
        for &e in &exprs {
            self.meter.tick(1)?;
            if let Some(slot) = self.expr_ty.get_mut(e.index()) {
                *slot = any;
            }
            // Binders that are not bound by patterns.
            let mut bind = |b: hir_lang::BinderId| {
                if let Some(slot) = self.binder_ty.get_mut(b.index()) {
                    *slot = any;
                }
            };
            match *hir.expr(e) {
                Expr::Closure(c) => {
                    hir.list(c.captures).iter().for_each(|cap| bind(cap.binder));
                    c.self_binder.into_iter().for_each(&mut bind);
                }
                Expr::Block(b) => {
                    for &s in hir.list(b.stmts) {
                        if let Stmt::Static { binder, .. } | Stmt::Global { binder, .. } =
                            *hir.stmt(s)
                        {
                            bind(binder);
                        }
                    }
                }
                _ => {}
            }
        }
        for &p in &pats {
            self.meter.tick(1)?;
            if let Some(slot) = self.pat_ty.get_mut(p.index()) {
                *slot = any;
            }
            if let Pat::Bind { binder, .. } | Pat::Ident { binder, .. } = *hir.pat(p) {
                if let Some(slot) = self.binder_ty.get_mut(binder.index()) {
                    *slot = any;
                }
            }
        }
        // Tails of partial paths still resolve by type where the prefix is
        // a declaration of this unit (`Shape::Circle`, `Point::new`).
        for &e in &exprs {
            if let Expr::Path(p) = *hir.expr(e) {
                self.dynamic_tail(p);
            }
        }
        for &p in &pats {
            if let Pat::Ctor { path, .. }
            | Pat::Path(path)
            | Pat::Record {
                path: Some(path), ..
            } = *hir.pat(p)
            {
                self.dynamic_tail(path);
            }
        }
        if self.profile.certain_errors {
            for &e in &exprs {
                self.meter.tick(1)?;
                self.certain_expr(e)?;
            }
            for &p in &pats {
                self.meter.tick(1)?;
                self.certain_pat(p);
            }
        }
        self.idx.exprs = exprs;
        self.idx.pats = pats;
        Ok(())
    }

    /// Resolves a partial path's tail silently, when its prefix is a sum,
    /// record, or class of this unit.
    fn dynamic_tail(&mut self, p: PathId) {
        let path = *self.hir.path(p);
        if path.unresolved != 1 || path.qself.is_some() {
            return;
        }
        let Some(owner) = self.local_item(path.res) else {
            return;
        };
        let Some(last) = self.hir.list(path.segments).last().copied() else {
            return;
        };
        let name = last.name.sym;
        if matches!(self.item_kind(owner), ItemKind::Sum(_)) {
            if let Some(v) = self.idx.variant_named(owner, name) {
                self.record_path_def(p, Def::Variant(v));
                return;
            }
        }
        let t = self.types.adt(owner);
        if let [one] = self.idx.members_named(t, name) {
            let item = one.item;
            self.record_path_def(p, Def::Item(item));
        }
    }

    /// The variant or tuple record a path certainly names.
    fn certain_ctor(&self, p: PathId) -> Option<usize> {
        let path = self.hir.path(p);
        let variant = |v: VariantId| {
            self.hir
                .variant(v)
                .filter(|x| x.shape == Shape::Tuple)
                .map(|x| x.fields.len())
        };
        if path.unresolved != 0 {
            return match self.path_def.get(p.index()).copied().flatten() {
                Some(Def::Variant(v)) => variant(v),
                _ => None,
            };
        }
        match path.res {
            Res::Def(d) if d.unit() == self.hir.unit() => match d.def() {
                Def::Variant(v) => variant(v),
                Def::Item(i) => match self.item_kind(i) {
                    ItemKind::Record(r) if r.shape == Shape::Tuple => Some(r.fields.len()),
                    _ => None,
                },
            },
            _ => None,
        }
    }

    fn certain_callee(&self, callee: ExprId) -> Option<Known> {
        let Expr::Path(p) = *self.hir.expr(callee) else {
            return None;
        };
        if let Some(n) = self.certain_ctor(p) {
            return Some(Known::Ctor(n));
        }
        let path = self.hir.path(p);
        let item = if path.unresolved == 0 {
            self.local_item(path.res)?
        } else {
            match self.path_def.get(p.index()).copied().flatten()? {
                Def::Item(i) => i,
                Def::Variant(_) => return None,
            }
        };
        (matches!(self.item_kind(item), ItemKind::Fn(_)) && !self.idx.is_generic(item))
            .then_some(Known::Fn(item))
    }

    fn certain_expr(&mut self, e: ExprId) -> Result<(), CheckError> {
        match *self.hir.expr(e) {
            Expr::Call { callee, args } => {
                let list = self.hir.list(args);
                // A spread supplies an unknown number of arguments.
                if list
                    .iter()
                    .any(|a| matches!(a.kind, ArgKind::Spread | ArgKind::SpreadNamed))
                {
                    return Ok(());
                }
                match self.certain_callee(callee) {
                    Some(Known::Fn(item)) => {
                        if let Some(sig) = self.sig(item)? {
                            let target = CallTarget::Sig {
                                sig: u32::try_from(sig).unwrap_or(NONE),
                                skip: 0,
                                method: None,
                                deref: 0,
                            };
                            self.match_args(e, target, args, true)?;
                        }
                    }
                    Some(Known::Ctor(n)) => {
                        let mut positional = 0u32;
                        for a in list {
                            match a.kind {
                                ArgKind::Named(id) => self.report(
                                    NodeRef::Expr(a.value),
                                    DiagnosticKind::UnknownNamedArg { name: id.sym },
                                ),
                                _ => positional += 1,
                            }
                        }
                        let n = u32::try_from(n).unwrap_or(NONE);
                        if positional != n {
                            self.report(
                                NodeRef::Expr(e),
                                DiagnosticKind::Arity {
                                    min: n,
                                    max: Some(n),
                                    found: positional,
                                },
                            );
                        }
                    }
                    None => {}
                }
            }
            Expr::Record {
                path: Some(p),
                fields,
                ..
            } => {
                let owner = match self.certain_record(p) {
                    Some(o) => o,
                    None => return Ok(()),
                };
                for fi in self.hir.list(fields) {
                    if self.idx.field_named(owner.0, fi.name.sym).is_none() {
                        self.report(
                            NodeRef::Expr(e),
                            DiagnosticKind::UnknownField {
                                ty: owner.1,
                                name: fi.name.sym,
                            },
                        );
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }

    /// A record (not a class: classes take dynamic properties) or variant
    /// with named fields that a path certainly names.
    fn certain_record(&mut self, p: PathId) -> Option<(FieldOwner, TypeId)> {
        let path = *self.hir.path(p);
        let def = if path.unresolved == 0 {
            match path.res {
                Res::Def(d) if d.unit() == self.hir.unit() => d.def(),
                _ => return None,
            }
        } else {
            self.path_def.get(p.index()).copied().flatten()?
        };
        match def {
            Def::Item(i) => match self.item_kind(i) {
                ItemKind::Record(r) if r.shape == Shape::Named && !self.idx.is_generic(i) => {
                    let raw = u32::try_from(i.index()).ok()?;
                    self.name_item(i);
                    Some((FieldOwner::Item(raw), self.types.adt(i)))
                }
                _ => None,
            },
            Def::Variant(v) => {
                let named = self.hir.variant(v).is_some_and(|x| x.shape == Shape::Named);
                let sum = self.hir.variant_owner(v)?;
                let raw = u32::try_from(v.index()).ok()?;
                self.name_item(sum);
                named.then(|| (FieldOwner::Variant(raw), self.types.adt(sum)))
            }
        }
    }

    fn certain_pat(&mut self, p: hir_lang::PatId) {
        let Pat::Ctor { path, elems, rest } = *self.hir.pat(p) else {
            return;
        };
        let Some(n) = self.certain_ctor(path) else {
            return;
        };
        let k = elems.len();
        let fits = if rest.is_some() { k <= n } else { k == n };
        if !fits {
            let want = u32::try_from(n).unwrap_or(NONE);
            self.report(
                NodeRef::Pat(p),
                DiagnosticKind::Arity {
                    min: want,
                    max: Some(want),
                    found: u32::try_from(k).unwrap_or(NONE),
                },
            );
        }
    }
}
