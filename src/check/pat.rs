//! Patterns under a static profile, checked iteratively against the type of
//! the value they match. Patterns contain no expressions (HIR §6), so one
//! explicit stack covers a whole pattern of any depth.

use alloc::vec::Vec;

use hir_lang::{BindMode, BinderId, Lit, NodeRef, Pat, PatId, PathId, Prim, Res};

use super::{
    Ctx,
    index::FieldOwner,
    paths::{RecordRef, ValueRef},
};
use crate::{
    diag::DiagnosticKind,
    error::CheckError,
    infer::{FLOAT, GENERAL, INT},
    types::{Tag, Type, TypeId},
};

impl Ctx<'_> {
    fn set_pat(&mut self, p: PatId, t: TypeId) {
        if let Some(slot) = self.pat_ty.get_mut(p.index()) {
            *slot = t.raw();
        }
    }

    /// The type of a literal (in an expression or a pattern). Unsuffixed
    /// numbers get a literal variable, range-checked once resolved.
    pub(crate) fn lit_type(&mut self, at: NodeRef, lit: Lit) -> TypeId {
        match lit {
            Lit::Null => TypeId::NULL,
            Lit::Bool(_) => TypeId::prim(Prim::Bool),
            Lit::Int(l) => match l.suffix {
                Some(p) => TypeId::prim(p),
                None => {
                    let v = self.fresh(INT);
                    self.int_lits.push((at, v, l));
                    v
                }
            },
            Lit::Float(f) => match f.suffix {
                Some(p) => TypeId::prim(p),
                None => self.fresh(FLOAT),
            },
            Lit::Char(_) => TypeId::prim(Prim::Char),
            Lit::Str(_) => TypeId::prim(Prim::Str),
            Lit::Bytes(_) => self.types.slice(TypeId::prim(Prim::U8)),
            Lit::BigInt(_) => {
                // Wider than 64 bits: no integer type of a static profile
                // holds it.
                let ty = TypeId::prim(self.profile.default_int);
                self.report(at, DiagnosticKind::LiteralOutOfRange { ty });
                TypeId::ERROR
            }
        }
    }

    fn bind_pat_binder(&mut self, b: BinderId, t: TypeId, p: PatId) -> Result<(), CheckError> {
        match self.binder_type(b) {
            // Another alternative of an or-pattern bound it already.
            Some(existing) => {
                if !self.unify(existing, t)? {
                    self.report(
                        NodeRef::Pat(p),
                        DiagnosticKind::Mismatch {
                            expected: existing,
                            found: t,
                        },
                    );
                }
            }
            None => self.set_binder(b, t, p),
        }
        Ok(())
    }

    /// A pattern of value type `value` matches a scrutinee of type `scrut`.
    fn pat_fit(&mut self, p: PatId, value: TypeId, scrut: TypeId) -> Result<bool, CheckError> {
        if self.coerce(value, scrut)? != super::coerce::Fit::No {
            return Ok(true);
        }
        self.report(
            NodeRef::Pat(p),
            DiagnosticKind::Mismatch {
                expected: scrut,
                found: value,
            },
        );
        Ok(false)
    }

    /// The value a constant pattern path denotes (`None`: reported or
    /// `{error}`).
    fn pattern_value(&mut self, path: PathId, at: NodeRef) -> Result<Option<TypeId>, CheckError> {
        let r = self.value_path(path, at)?;
        Ok(match r {
            ValueRef::Error => None,
            ValueRef::Decl(_) | ValueRef::Typed(_) => Some(self.value_type(r)?),
            _ => {
                self.report(at, DiagnosticKind::NotAValue);
                None
            }
        })
    }

    /// Checks pattern `root` against `expected`, typing its binders.
    pub(crate) fn check_pat(&mut self, root: PatId, expected: TypeId) -> Result<(), CheckError> {
        let mut stack: Vec<(PatId, TypeId)> = alloc::vec![(root, expected)];
        while let Some((p, t)) = stack.pop() {
            self.meter.tick(1)?;
            self.set_pat(p, t);
            let at = NodeRef::Pat(p);
            match *self.hir.pat(p) {
                Pat::Wild | Pat::Err => {}
                Pat::Bind { binder, mode, sub } => {
                    let bt = match mode {
                        BindMode::Value => t,
                        BindMode::Ref => self.types.reference(false, t),
                        BindMode::RefMut => self.types.reference(true, t),
                    };
                    self.bind_pat_binder(binder, bt, p)?;
                    if let Some(s) = sub {
                        stack.push((s, t));
                    }
                }
                Pat::Ident { binder, path } => {
                    let ph = *self.hir.path(path);
                    // An unresolved bare name binds; a resolved one is a
                    // constant, unit variant, or unit record to compare with.
                    if ph.res != Res::Unresolved || ph.unresolved != 0 {
                        if let Some(vt) = self.pattern_value(path, at)? {
                            let _ = self.pat_fit(p, vt, t)?;
                        }
                    }
                    self.bind_pat_binder(binder, t, p)?;
                }
                Pat::Lit(lit) => {
                    let lt = self.lit_type(at, lit);
                    if !self.is_err(lt) {
                        let _ = self.pat_fit(p, lt, t)?;
                    }
                }
                Pat::Range { lo, hi, .. } => {
                    stack.extend(lo.map(|b| (b, t)));
                    stack.extend(hi.map(|b| (b, t)));
                }
                Pat::Path(path) => {
                    if let Some(vt) = self.pattern_value(path, at)? {
                        let _ = self.pat_fit(p, vt, t)?;
                    }
                }
                Pat::Or(alts) => {
                    let alts = self.hir.list(alts);
                    stack.extend(alts.iter().rev().map(|&a| (a, t)));
                }
                Pat::Ref { mutable, inner } => {
                    let r = self.resolve(t);
                    let inner_ty = match self.types.get(r) {
                        Type::Ref {
                            mutable: m,
                            inner: u,
                        } if m == mutable => u,
                        Type::Error => TypeId::ERROR,
                        _ => {
                            let u = self.fresh(GENERAL);
                            let want = self.types.reference(mutable, u);
                            if !self.pat_fit(p, want, t)? {
                                stack.push((inner, TypeId::ERROR));
                                continue;
                            }
                            u
                        }
                    };
                    stack.push((inner, inner_ty));
                }
                Pat::TypeTest { ty, pat } => {
                    let target = self.lower_ty(ty, self.cur_self, false)?;
                    self.type_test(p, t, target)?;
                    if let Some(sub) = pat {
                        stack.push((sub, target));
                    }
                }
                Pat::Tuple { elems, rest } => self.tuple_pat(p, t, elems, rest, &mut stack)?,
                Pat::Ctor { path, elems, rest } => {
                    self.ctor_pat(p, t, path, elems, rest, &mut stack)?
                }
                Pat::Record { path, fields, rest } => {
                    self.record_pat(p, t, path, fields, rest, &mut stack)?;
                }
                Pat::Slice { prefix, rest } => self.slice_pat(p, t, prefix, rest, &mut stack)?,
            }
        }
        Ok(())
    }

    /// Pushes `elems` (with an optional rest at `rest`) against `types`.
    fn push_with_rest(
        &mut self,
        p: PatId,
        elems: &[PatId],
        rest: Option<u32>,
        types: &[TypeId],
        stack: &mut Vec<(PatId, TypeId)>,
    ) {
        let n = types.len();
        let k = elems.len();
        let fits = match rest {
            None => k == n,
            Some(_) => k <= n,
        };
        if !fits {
            let found = u32::try_from(k).unwrap_or(u32::MAX);
            let want = u32::try_from(n).unwrap_or(u32::MAX);
            self.report(
                NodeRef::Pat(p),
                DiagnosticKind::Arity {
                    min: want,
                    max: Some(want),
                    found,
                },
            );
            stack.extend(elems.iter().map(|&e| (e, TypeId::ERROR)));
            return;
        }
        let split = rest.map_or(k, |r| (r as usize).min(k));
        for (i, &e) in elems.iter().enumerate() {
            let ty = if i < split {
                types.get(i)
            } else {
                types.get(n - (k - i))
            };
            stack.push((e, ty.copied().unwrap_or(TypeId::ERROR)));
        }
    }

    fn tuple_pat(
        &mut self,
        p: PatId,
        t: TypeId,
        elems: hir_lang::List<PatId>,
        rest: Option<u32>,
        stack: &mut Vec<(PatId, TypeId)>,
    ) -> Result<(), CheckError> {
        let elems = self.hir.list(elems);
        let r = self.resolve(t);
        match self.types.get(r) {
            Type::Tuple(ts) => {
                let ts = ts.to_vec();
                self.push_with_rest(p, elems, rest, &ts, stack);
            }
            Type::Error => stack.extend(elems.iter().map(|&e| (e, TypeId::ERROR))),
            _ => {
                let fresh: Vec<TypeId> = elems.iter().map(|_| self.fresh(GENERAL)).collect();
                let shape = self.types.tuple(&fresh);
                if rest.is_none() && self.unify(t, shape)? {
                    stack.extend(elems.iter().copied().zip(fresh));
                } else {
                    self.report(
                        NodeRef::Pat(p),
                        DiagnosticKind::Mismatch {
                            expected: t,
                            found: shape,
                        },
                    );
                    stack.extend(elems.iter().map(|&e| (e, TypeId::ERROR)));
                }
            }
        }
        Ok(())
    }

    fn ctor_pat(
        &mut self,
        p: PatId,
        t: TypeId,
        path: PathId,
        elems: hir_lang::List<PatId>,
        rest: Option<u32>,
        stack: &mut Vec<(PatId, TypeId)>,
    ) -> Result<(), CheckError> {
        let at = NodeRef::Pat(p);
        let elems = self.hir.list(elems);
        let (fields, adt) = match self.value_path(path, at)? {
            ValueRef::RecordCtor(i) => (self.record_field_ids(i), self.adt_type(i)),
            ValueRef::VariantCtor(v) => {
                let fields = self
                    .hir
                    .variant(v)
                    .map(|x| self.hir.list(x.fields).to_vec())
                    .unwrap_or_default();
                let adt = self
                    .hir
                    .variant_owner(v)
                    .map_or(TypeId::ERROR, |s| self.adt_type(s));
                (fields, adt)
            }
            ValueRef::Error => {
                stack.extend(elems.iter().map(|&e| (e, TypeId::ERROR)));
                return Ok(());
            }
            ValueRef::Typed(adt) if self.tag(adt) == Tag::Adt => {
                // A unit variant or record written with parentheses.
                let _ = self.pat_fit(p, adt, t)?;
                (Vec::new(), TypeId::ERROR)
            }
            _ => {
                self.report(at, DiagnosticKind::NotAValue);
                stack.extend(elems.iter().map(|&e| (e, TypeId::ERROR)));
                return Ok(());
            }
        };
        if adt != TypeId::ERROR && !self.pat_fit(p, adt, t)? {
            stack.extend(elems.iter().map(|&e| (e, TypeId::ERROR)));
            return Ok(());
        }
        let mut types = Vec::with_capacity(fields.len());
        for f in fields {
            types.push(self.field_type(f)?);
        }
        self.push_with_rest(p, elems, rest, &types, stack);
        Ok(())
    }

    fn record_pat(
        &mut self,
        p: PatId,
        t: TypeId,
        path: Option<PathId>,
        fields: hir_lang::List<hir_lang::FieldPat>,
        rest: bool,
        stack: &mut Vec<(PatId, TypeId)>,
    ) -> Result<(), CheckError> {
        let at = NodeRef::Pat(p);
        let fps = self.hir.list(fields);
        let error_out = |stack: &mut Vec<(PatId, TypeId)>| {
            stack.extend(fps.iter().map(|fp| (fp.pat, TypeId::ERROR)));
        };
        // Named targets: a record, class, or variant item.
        if let Some(path) = path {
            let Some(target) = self.record_ref(path, at)? else {
                error_out(stack);
                return Ok(());
            };
            let adt = self.record_ref_type(target);
            if !self.pat_fit(p, adt, t)? {
                error_out(stack);
                return Ok(());
            }
            let owner = match target {
                RecordRef::Item(i) => {
                    FieldOwner::Item(u32::try_from(i.index()).unwrap_or(u32::MAX))
                }
                RecordRef::Variant(v) => {
                    FieldOwner::Variant(u32::try_from(v.index()).unwrap_or(u32::MAX))
                }
            };
            let mut mentioned = 0usize;
            for fp in fps {
                match self.idx.field_named(owner, fp.name.sym) {
                    Some((_, f)) => {
                        mentioned += 1;
                        let ft = self.field_type(f)?;
                        stack.push((fp.pat, ft));
                    }
                    None => {
                        self.report(
                            at,
                            DiagnosticKind::UnknownField {
                                ty: adt,
                                name: fp.name.sym,
                            },
                        );
                        stack.push((fp.pat, TypeId::ERROR));
                    }
                }
            }
            if !rest {
                self.missing_pattern_fields(p, target, fps, mentioned);
            }
            return Ok(());
        }
        // Anonymous: the scrutinee's own fields.
        let r = self.resolve(t);
        let Some(declared) = self.record_fields_of(r) else {
            if !self.is_err(r) {
                self.report(
                    at,
                    DiagnosticKind::Mismatch {
                        expected: t,
                        found: TypeId::ERROR,
                    },
                );
            }
            error_out(stack);
            return Ok(());
        };
        for fp in fps {
            match declared.iter().find(|f| f.name == fp.name.sym) {
                Some(f) => stack.push((fp.pat, f.ty)),
                None => {
                    self.report(
                        at,
                        DiagnosticKind::UnknownField {
                            ty: r,
                            name: fp.name.sym,
                        },
                    );
                    stack.push((fp.pat, TypeId::ERROR));
                }
            }
        }
        if !rest {
            let missing: Vec<_> = declared
                .iter()
                .filter(|f| !fps.iter().any(|fp| fp.name.sym == f.name))
                .collect();
            if let Some(first) = missing.first() {
                self.report(
                    at,
                    DiagnosticKind::MissingFields {
                        first: first.name,
                        count: u32::try_from(missing.len()).unwrap_or(u32::MAX),
                    },
                );
            }
        }
        Ok(())
    }

    fn missing_pattern_fields(
        &mut self,
        p: PatId,
        target: RecordRef,
        fps: &[hir_lang::FieldPat],
        mentioned: usize,
    ) {
        let declared: Vec<hir_lang::FieldId> = match target {
            RecordRef::Item(i) => self.record_field_ids(i),
            RecordRef::Variant(v) => self
                .hir
                .variant(v)
                .map(|x| self.hir.list(x.fields).to_vec())
                .unwrap_or_default(),
        };
        if mentioned >= declared.len() {
            return;
        }
        let mut first = None;
        let mut count = 0u32;
        // Names in the pattern are unique (validated), so a sorted copy
        // makes the membership test logarithmic.
        let mut names: Vec<_> = fps.iter().map(|fp| fp.name.sym).collect();
        names.sort_unstable();
        for f in declared {
            if let Some(name) = self.hir.field(f).name {
                if names.binary_search(&name.sym).is_err() {
                    count += 1;
                    let _ = first.get_or_insert(name.sym);
                }
            }
        }
        if let Some(first) = first {
            self.report(
                NodeRef::Pat(p),
                DiagnosticKind::MissingFields { first, count },
            );
        }
    }

    fn slice_pat(
        &mut self,
        p: PatId,
        t: TypeId,
        prefix: hir_lang::List<PatId>,
        rest: Option<hir_lang::SliceRest>,
        stack: &mut Vec<(PatId, TypeId)>,
    ) -> Result<(), CheckError> {
        let prefix = self.hir.list(prefix);
        let suffix = rest.map_or(&[][..], |r| self.hir.list(r.suffix));
        let count = prefix.len() + suffix.len();
        let r = self.resolve(t);
        let (elem, len) = match self.types.get(r) {
            Type::Array { elem, len } => (elem, Some(len)),
            Type::Slice(elem) => (elem, None),
            Type::Error => (TypeId::ERROR, None),
            _ => {
                let v = self.fresh(GENERAL);
                let want = self.types.slice(v);
                if self.unify(t, want)? {
                    (v, None)
                } else {
                    self.report(
                        NodeRef::Pat(p),
                        DiagnosticKind::Mismatch {
                            expected: t,
                            found: want,
                        },
                    );
                    (TypeId::ERROR, None)
                }
            }
        };
        if let Some(len) = len {
            let count64 = count as u64;
            let ok = if rest.is_some() {
                count64 <= len
            } else {
                count64 == len
            };
            if !ok {
                let want = u32::try_from(len).unwrap_or(u32::MAX);
                self.report(
                    NodeRef::Pat(p),
                    DiagnosticKind::Arity {
                        min: want,
                        max: Some(want),
                        found: u32::try_from(count).unwrap_or(u32::MAX),
                    },
                );
            }
        }
        stack.extend(prefix.iter().chain(suffix).map(|&e| (e, elem)));
        if let Some(bind) = rest.and_then(|r| r.bind) {
            let rest_ty = match len {
                Some(len) if (count as u64) <= len => self.types.array(elem, len - count as u64),
                _ => self.types.slice(elem),
            };
            stack.push((bind, rest_ty));
        }
        Ok(())
    }

    /// Whether a run-time test of a `scrut` value for type `target` can ever
    /// succeed.
    fn type_test(&mut self, p: PatId, scrut: TypeId, target: TypeId) -> Result<(), CheckError> {
        let s = self.resolve(scrut);
        let ok = match self.types.get(s) {
            _ if self.is_err(target) => true,
            // An unknown type may be anything; a literal's class still
            // rules types out.
            _ if self.tag(s) == Tag::Var => {
                self.infer.class_of(s) == GENERAL || self.unify(s, target)?
            }
            Type::Any | Type::Error => true,
            Type::Nullable(inner) => {
                let snap = self.infer.snapshot();
                let ok = self.unify(inner, target)? || self.unify(s, target)?;
                if ok {
                    self.infer.commit()
                } else {
                    self.infer.rollback(snap)
                }
                ok
            }
            Type::Adt(a) => match self.types.get(self.resolve(target)) {
                Type::Adt(b) => a == b || self.is_subclass(b, a)?,
                _ => false,
            },
            _ => self.unify(s, target)?,
        };
        if !ok {
            self.report(
                NodeRef::Pat(p),
                DiagnosticKind::ImpossibleTypeTest {
                    from: s,
                    to: target,
                },
            );
        }
        Ok(())
    }
}

/// One step of the irrefutability evaluation.
enum Step {
    Visit(PatId),
    All(usize),
    Any(usize),
}

impl Ctx<'_> {
    /// The variant a pattern path names (directly, or through the tail the
    /// checker resolved).
    pub(crate) fn variant_of_path(&self, path: PathId) -> Option<hir_lang::VariantId> {
        let p = self.hir.path(path);
        if p.unresolved == 0 {
            if let Res::Def(d) = p.res {
                if d.unit() == self.hir.unit() {
                    if let hir_lang::Def::Variant(v) = d.def() {
                        return Some(v);
                    }
                }
            }
            return None;
        }
        match self.path_def.get(path.index()).copied().flatten() {
            Some(hir_lang::Def::Variant(v)) => Some(v),
            _ => None,
        }
    }

    /// A bare identifier pattern that binds (its path never resolved).
    fn ident_binds(&self, path: PathId) -> bool {
        let p = self.hir.path(path);
        p.res == Res::Unresolved && p.unresolved == 0
    }

    /// Whether a pattern matches every value of its type. Conservative: a
    /// pattern on a sum variant is refutable even when the sum has one
    /// variant.
    pub(crate) fn irrefutable(&mut self, root: PatId) -> Result<bool, CheckError> {
        let hir = self.hir;
        let mut steps = alloc::vec![Step::Visit(root)];
        let mut vals: Vec<bool> = Vec::new();
        while let Some(step) = steps.pop() {
            self.meter.tick(1)?;
            match step {
                Step::Visit(p) => match *hir.pat(p) {
                    Pat::Wild | Pat::Err | Pat::Bind { sub: None, .. } => vals.push(true),
                    Pat::Bind { sub: Some(s), .. } | Pat::Ref { inner: s, .. } => {
                        steps.push(Step::Visit(s));
                    }
                    Pat::Ident { path, .. } => vals.push(self.ident_binds(path)),
                    Pat::Lit(_) | Pat::Range { .. } | Pat::Path(_) | Pat::TypeTest { .. } => {
                        vals.push(false);
                    }
                    Pat::Tuple { elems, .. } => {
                        let elems = hir.list(elems);
                        steps.push(Step::All(elems.len()));
                        steps.extend(elems.iter().map(|&e| Step::Visit(e)));
                    }
                    Pat::Ctor { path, elems, .. } => {
                        if self.variant_of_path(path).is_some() {
                            vals.push(false);
                        } else {
                            let elems = hir.list(elems);
                            steps.push(Step::All(elems.len()));
                            steps.extend(elems.iter().map(|&e| Step::Visit(e)));
                        }
                    }
                    Pat::Record { path, fields, .. } => {
                        if path.is_some_and(|p| self.variant_of_path(p).is_some()) {
                            vals.push(false);
                        } else {
                            let fields = hir.list(fields);
                            steps.push(Step::All(fields.len()));
                            steps.extend(fields.iter().map(|f| Step::Visit(f.pat)));
                        }
                    }
                    Pat::Slice { prefix, rest } => {
                        vals.push(prefix.is_empty() && rest.is_some_and(|r| r.suffix.is_empty()))
                    }
                    Pat::Or(alts) => {
                        let alts = hir.list(alts);
                        steps.push(Step::Any(alts.len()));
                        steps.extend(alts.iter().map(|&a| Step::Visit(a)));
                    }
                },
                Step::All(n) | Step::Any(n) => {
                    let at = vals.len().saturating_sub(n);
                    let all = matches!(step, Step::All(_));
                    let v = if all {
                        vals.get(at..).is_none_or(|s| s.iter().all(|&b| b))
                    } else {
                        vals.get(at..).is_some_and(|s| s.iter().any(|&b| b))
                    };
                    vals.truncate(at);
                    vals.push(v);
                }
            }
        }
        Ok(vals.pop().unwrap_or(false))
    }

    /// How much of variant `v` a top-level arm pattern covers.
    pub(crate) fn covers_variant(
        &mut self,
        root: PatId,
        v: hir_lang::VariantId,
    ) -> Result<super::engine::Cover, CheckError> {
        use super::engine::Cover;
        let hir = self.hir;
        let mut best = Cover::None;
        let mut stack = alloc::vec![root];
        while let Some(p) = stack.pop() {
            self.meter.tick(1)?;
            let this = match *hir.pat(p) {
                Pat::Wild | Pat::Err | Pat::Bind { sub: None, .. } => Cover::All,
                Pat::Bind { sub: Some(s), .. } => {
                    stack.push(s);
                    continue;
                }
                Pat::Or(alts) => {
                    stack.extend(hir.list(alts).iter().copied());
                    continue;
                }
                Pat::Ident { path, .. } => {
                    if self.ident_binds(path) || self.variant_of_path(path) == Some(v) {
                        Cover::All
                    } else {
                        Cover::None
                    }
                }
                Pat::Path(path) => {
                    if self.variant_of_path(path) == Some(v) {
                        Cover::All
                    } else {
                        Cover::None
                    }
                }
                Pat::Ctor { path, elems, .. } => {
                    if self.variant_of_path(path) == Some(v) {
                        let mut all = true;
                        for &e in hir.list(elems) {
                            all &= self.irrefutable(e)?;
                        }
                        if all { Cover::All } else { Cover::Some }
                    } else {
                        Cover::None
                    }
                }
                Pat::Record {
                    path: Some(path),
                    fields,
                    ..
                } => {
                    if self.variant_of_path(path) == Some(v) {
                        let mut all = true;
                        for f in hir.list(fields) {
                            all &= self.irrefutable(f.pat)?;
                        }
                        if all { Cover::All } else { Cover::Some }
                    } else {
                        Cover::None
                    }
                }
                Pat::TypeTest { .. } => Cover::Some,
                _ => Cover::None,
            };
            best = match (best, this) {
                (Cover::All, _) | (_, Cover::All) => Cover::All,
                (Cover::Some, _) | (_, Cover::Some) => Cover::Some,
                _ => Cover::None,
            };
        }
        Ok(best)
    }
}
