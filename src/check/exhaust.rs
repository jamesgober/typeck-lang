//! Exhaustiveness and usefulness through match-lang (ISSUES P17).
//!
//! After inference, each `match` is handed to match-lang with a [`Model`]
//! over this checker's types: sums are sums, records, classes, tuples, and
//! references are products, `T?` is a sum of `null` and a value, a union is
//! a sum of its members (matched by type tests), integers and characters
//! carry their exact domains, and everything else (floats, strings, host and
//! generic types) is opaque. Missing values come back as witnesses and are
//! reported with the `match`; unreachable arms and redundant or-pattern
//! alternatives are warnings.
//!
//! A pattern this translation cannot express precisely (a type test against
//! a class, a range of floats, a byte-string literal) makes its arm count as
//! guarded: it never contributes coverage, so no match is ever declared
//! exhaustive on its account.

use alloc::vec::Vec;
use core::cell::{Cell, RefCell};

use hir_lang::{Arm, Expr, ExprId, ItemKind, Lit, NodeRef, Pat, PatId, Prim, Shape, VariantId};
use match_lang::{Checker as MatchChecker, Ctor, Error as MatchError, Model, Signature};

use super::Ctx;
use crate::{
    diag::{DiagnosticKind, Severity},
    error::{CheckError, Limit},
    typed::{NONE, WKind, WNode},
    types::{Field, Tag, Type, TypeId},
};

/// Witnesses kept per match (the rest are counted only).
const WITNESS_LIMIT: usize = 8;

/// The constructor model over the checker's types. Field types of generic
/// sums are substituted on demand, which needs the checker mutably; the
/// model is only ever used by one match-lang check at a time.
struct HirModel<'c, 'h> {
    cx: RefCell<&'c mut Ctx<'h>>,
    failed: Cell<Option<CheckError>>,
}

impl HirModel<'_, '_> {
    fn note(&self, r: Result<(), CheckError>) {
        if let Err(e) = r {
            self.failed.set(Some(e));
        }
    }
}

/// How a type is matched.
enum Shape2 {
    Sum(u32),
    Product,
    Bool,
    Int(i128, i128),
    Char,
    Opaque,
    Array(u32, TypeId),
    Slice(TypeId),
}

fn shape_of(cx: &Ctx<'_>, t: TypeId) -> Shape2 {
    let t = cx.resolve(t);
    match cx.types.get(t) {
        Type::Adt { item, .. } => match cx.item_kind(item) {
            ItemKind::Sum(d) => Shape2::Sum(u32::try_from(d.variants.len()).unwrap_or(u32::MAX)),
            ItemKind::Record(d) if d.is_union => Shape2::Opaque,
            ItemKind::Record(_) => Shape2::Product,
            _ => Shape2::Opaque,
        },
        Type::Prim(p) => match p {
            Prim::Bool => Shape2::Bool,
            Prim::Char => Shape2::Char,
            p if p.is_int() => {
                let (lo, hi) = int_domain(p);
                Shape2::Int(lo, hi)
            }
            _ => Shape2::Opaque,
        },
        Type::Tuple(_) | Type::Ref { .. } | Type::Record(_) => Shape2::Product,
        Type::Array { elem, len } => match u32::try_from(len) {
            Ok(n) => Shape2::Array(n, elem),
            Err(_) => Shape2::Slice(elem),
        },
        Type::ParamArray { elem, .. } | Type::Slice(elem) => Shape2::Slice(elem),
        Type::Nullable(_) => Shape2::Sum(2),
        Type::Union(ms) => Shape2::Sum(u32::try_from(ms.len()).unwrap_or(u32::MAX)),
        Type::Never => Shape2::Sum(0),
        _ => Shape2::Opaque,
    }
}

/// The values of an integer type.
fn int_domain(p: Prim) -> (i128, i128) {
    let bits = p.bits();
    if p.is_signed() {
        let half = 1i128 << (bits - 1);
        (-half, half - 1)
    } else {
        (0, (1i128 << bits) - 1)
    }
}

impl Model for HirModel<'_, '_> {
    type Ty = TypeId;

    fn signature(&self, ty: &TypeId) -> Signature<TypeId> {
        let cx = self.cx.borrow();
        match shape_of(&cx, *ty) {
            Shape2::Sum(count) => Signature::Sum { count },
            Shape2::Product => Signature::Product,
            Shape2::Bool => Signature::Bool,
            Shape2::Int(min, max) => Signature::Int { min, max },
            Shape2::Char => Signature::Char,
            Shape2::Opaque => Signature::Opaque,
            Shape2::Array(len, elem) => Signature::Array { len, elem },
            Shape2::Slice(elem) => Signature::Slice { elem },
        }
    }

    fn fields(&self, ty: &TypeId, variant: u32, out: &mut Vec<TypeId>) {
        let mut cx = self.cx.borrow_mut();
        let r = cx.match_fields(*ty, variant, out);
        drop(cx);
        self.note(r);
    }

    fn is_empty(&self, ty: &TypeId) -> bool {
        let cx = self.cx.borrow();
        matches!(shape_of(&cx, *ty), Shape2::Sum(0))
    }
}

/// One node of the shadow tree built beside each translated pattern: the
/// HIR pattern it came from (or none for synthetic wildcards and wrappers)
/// and its child count, in post-order.
#[derive(Clone, Copy)]
struct Shadow {
    origin: Option<PatId>,
    arity: u32,
}

enum Task {
    Visit(PatId, TypeId),
    /// A wildcard standing for an omitted field or a rest.
    Wild,
    /// Pops `n` patterns and builds one constructor around them.
    Build(BuildKind, u32, Option<PatId>),
}

#[derive(Clone, Copy)]
enum BuildKind {
    Variant(u32),
    Product,
    Or,
    Slice,
    SliceRest(u32),
}

impl Ctx<'_> {
    /// The field types of `variant` of `ty`, as the model reports them.
    fn match_fields(
        &mut self,
        ty: TypeId,
        variant: u32,
        out: &mut Vec<TypeId>,
    ) -> Result<(), CheckError> {
        let t = self.resolve(ty);
        match self.types.get(t) {
            Type::Adt { item, .. } => {
                let fields: Vec<hir_lang::FieldId> = match self.item_kind(item) {
                    ItemKind::Sum(d) => self
                        .hir
                        .list(d.variants)
                        .get(variant as usize)
                        .and_then(|&v| self.hir.variant(v))
                        .map(|v| self.hir.list(v.fields).to_vec())
                        .unwrap_or_default(),
                    ItemKind::Record(d) => self.hir.list(d.fields).to_vec(),
                    _ => Vec::new(),
                };
                let (params, args) = match self.adt_subst(t) {
                    Some((_, p, a)) => (p, a),
                    None => (Vec::new(), Vec::new()),
                };
                for f in fields {
                    let ft = self.field_type(f)?;
                    out.push(self.subst(ft, &params, &args)?);
                }
            }
            Type::Tuple(elems) => out.extend_from_slice(elems),
            Type::Ref { inner, .. } => out.push(inner),
            Type::Record(fields) => out.extend(fields.iter().map(|f| f.ty)),
            Type::Nullable(inner) if variant == 1 => out.push(inner),
            Type::Union(ms) => {
                if let Some(&m) = ms.get(variant as usize) {
                    out.push(m);
                }
            }
            _ => {}
        }
        Ok(())
    }

    /// Checks every recorded `match` with match-lang.
    pub(crate) fn check_matches(&mut self) -> Result<(), CheckError> {
        let matches = core::mem::take(&mut self.matches);
        for &m in &matches {
            self.check_match(m)?;
        }
        self.matches = matches;
        Ok(())
    }

    fn check_match(&mut self, e: ExprId) -> Result<(), CheckError> {
        let Expr::Match { scrutinee, arms } = *self.hir.expr(e) else {
            return Ok(());
        };
        let scrut = self.ety(scrutinee);
        if matches!(self.tag(scrut), Tag::Error | Tag::Any | Tag::Var) {
            return Ok(());
        }
        let arms: Vec<Arm> = self.hir.list(arms).to_vec();
        // Anything already reported inside a pattern: no second opinion.
        for arm in &arms {
            if self.pattern_has_error(arm.pat)? {
                return Ok(());
            }
        }
        let mut translated: Vec<match_lang::Arm> = Vec::with_capacity(arms.len());
        let mut shadows: Vec<Vec<Shadow>> = Vec::with_capacity(arms.len());
        for arm in &arms {
            self.meter.tick(1)?;
            let (pat, shadow, exact) = self.translate(arm.pat, scrut)?;
            translated.push(if arm.guard.is_some() || !exact {
                match_lang::Arm::guarded(pat)
            } else {
                match_lang::Arm::new(pat)
            });
            shadows.push(shadow);
        }
        let remaining = self.meter.budget.steps.saturating_sub(self.meter.used);
        let result = {
            let model = HirModel {
                cx: RefCell::new(self),
                failed: Cell::new(None),
            };
            let r = MatchChecker::new()
                .with_step_limit(remaining.max(1))
                .with_witness_limit(WITNESS_LIMIT)
                .check(&model, &scrut, &translated);
            if let Some(err) = model.failed.take() {
                return Err(err);
            }
            r
        };
        let report = match result {
            Ok(r) => r,
            Err(MatchError::StepLimit { .. } | MatchError::TooLarge) => {
                return Err(CheckError::BudgetExceeded {
                    limit: Limit::Steps,
                });
            }
            // A pattern that does not fit its type was reported by the
            // checker already; an inconsistent model would be a bug here,
            // and the match is then left unjudged rather than misjudged.
            Err(_) => return Ok(()),
        };
        self.meter.tick(report.steps())?;
        if !report.is_exhaustive() && self.profile.exhaustive_match {
            let start = u32::try_from(self.witnesses.len()).unwrap_or(NONE);
            let mut first_variant = None;
            for w in report.missing() {
                let before = self.wnodes.len();
                self.convert_witness(w)?;
                if first_variant.is_none() {
                    if let Some(WNode {
                        kind: WKind::Variant(v),
                        ..
                    }) = self.wnodes.get(before)
                    {
                        first_variant = Some(*v);
                    }
                }
                let len = u32::try_from(self.wnodes.len() - before).unwrap_or(0);
                self.witnesses
                    .push((e, u32::try_from(before).unwrap_or(NONE), len));
            }
            let _ = start;
            self.report(
                NodeRef::Expr(e),
                DiagnosticKind::NonExhaustive {
                    missing: first_variant,
                },
            );
        }
        for &i in report.unreachable() {
            if let Some(arm) = arms.get(i) {
                self.report_with(
                    NodeRef::Pat(arm.pat),
                    DiagnosticKind::UnreachableArm,
                    Severity::Warning,
                );
            }
        }
        for r in report.redundant() {
            let origin = shadows
                .get(r.arm)
                .and_then(|s| preorder_origin(s, r.node))
                .or_else(|| arms.get(r.arm).map(|a| a.pat));
            if let Some(p) = origin {
                self.report_with(
                    NodeRef::Pat(p),
                    DiagnosticKind::RedundantAlternative,
                    Severity::Warning,
                );
            }
        }
        Ok(())
    }

    fn pattern_has_error(&mut self, root: PatId) -> Result<bool, CheckError> {
        let mut stack = alloc::vec![root];
        while let Some(p) = stack.pop() {
            self.meter.tick(1)?;
            if matches!(self.hir.pat(p), Pat::Err) {
                return Ok(true);
            }
            let t = self
                .pat_ty
                .get(p.index())
                .copied()
                .filter(|&v| v != NONE)
                .map_or(TypeId::ERROR, TypeId::from_raw);
            if self.is_err(t) {
                return Ok(true);
            }
            pat_children(self.hir, p, &mut stack);
        }
        Ok(false)
    }

    /// Translates an arm pattern matched against `ty`. Returns the pattern,
    /// its shadow tree, and whether the translation is exact.
    fn translate(
        &mut self,
        root: PatId,
        ty: TypeId,
    ) -> Result<(match_lang::Pat, Vec<Shadow>, bool), CheckError> {
        let hir = self.hir;
        let mut tasks: Vec<Task> = alloc::vec![Task::Visit(root, ty)];
        let mut vals: Vec<match_lang::Pat> = Vec::new();
        let mut shadow: Vec<Shadow> = Vec::new();
        let mut exact = true;
        let wild = |vals: &mut Vec<match_lang::Pat>, shadow: &mut Vec<Shadow>, o: Option<PatId>| {
            vals.push(match_lang::Pat::wild());
            shadow.push(Shadow {
                origin: o,
                arity: 0,
            });
        };
        while let Some(task) = tasks.pop() {
            self.meter.tick(1)?;
            match task {
                Task::Wild => wild(&mut vals, &mut shadow, None),
                Task::Build(kind, n, origin) => {
                    let at = vals.len().saturating_sub(n as usize);
                    let kids: Vec<match_lang::Pat> = vals.drain(at..).collect();
                    vals.push(match kind {
                        BuildKind::Variant(i) => match_lang::Pat::variant(i, kids),
                        BuildKind::Product => match_lang::Pat::product(kids),
                        BuildKind::Or => match_lang::Pat::or(kids),
                        BuildKind::Slice => match_lang::Pat::slice(kids),
                        BuildKind::SliceRest(prefix) => {
                            let mut kids = kids;
                            let suffix = kids.split_off((prefix as usize).min(kids.len()));
                            match_lang::Pat::slice_rest(kids, suffix)
                        }
                    });
                    shadow.push(Shadow { origin, arity: n });
                }
                Task::Visit(p, t) => {
                    let t = self.resolve(t);
                    let pat = *hir.pat(p);
                    // `T?`: `null` is variant 0; anything else that can fail
                    // tests a present value (variant 1).
                    if let Type::Nullable(inner) = self.types.get(t) {
                        match pat {
                            Pat::Wild | Pat::Err | Pat::Bind { sub: None, .. } => {
                                wild(&mut vals, &mut shadow, Some(p));
                            }
                            Pat::Ident { path, .. } if self.ident_binds(path) => {
                                wild(&mut vals, &mut shadow, Some(p));
                            }
                            Pat::Bind { sub: Some(s), .. } => tasks.push(Task::Visit(s, t)),
                            Pat::Or(alts) => {
                                let alts = hir.list(alts);
                                tasks.push(Task::Build(
                                    BuildKind::Or,
                                    u32::try_from(alts.len()).unwrap_or(0),
                                    Some(p),
                                ));
                                tasks.extend(alts.iter().rev().map(|&a| Task::Visit(a, t)));
                            }
                            Pat::Lit(Lit::Null) => {
                                vals.push(match_lang::Pat::variant(0, []));
                                shadow.push(Shadow {
                                    origin: Some(p),
                                    arity: 0,
                                });
                            }
                            _ => {
                                tasks.push(Task::Build(BuildKind::Variant(1), 1, None));
                                tasks.push(Task::Visit(p, inner));
                            }
                        }
                        continue;
                    }
                    match pat {
                        Pat::Wild | Pat::Err | Pat::Bind { sub: None, .. } => {
                            wild(&mut vals, &mut shadow, Some(p));
                        }
                        Pat::Bind { sub: Some(s), .. } => tasks.push(Task::Visit(s, t)),
                        Pat::Or(alts) => {
                            let alts = hir.list(alts);
                            tasks.push(Task::Build(
                                BuildKind::Or,
                                u32::try_from(alts.len()).unwrap_or(0),
                                Some(p),
                            ));
                            tasks.extend(alts.iter().rev().map(|&a| Task::Visit(a, t)));
                        }
                        Pat::Ident { path, .. } if self.ident_binds(path) => {
                            wild(&mut vals, &mut shadow, Some(p));
                        }
                        Pat::Ident { path, .. } | Pat::Path(path) => {
                            match self.constant_pattern(path, t)? {
                                Some(c) => {
                                    vals.push(c);
                                    shadow.push(Shadow {
                                        origin: Some(p),
                                        arity: 0,
                                    });
                                }
                                None => {
                                    exact = false;
                                    wild(&mut vals, &mut shadow, Some(p));
                                }
                            }
                        }
                        Pat::Lit(lit) => match self.literal_pattern(lit, t) {
                            Some(c) => {
                                vals.push(c);
                                shadow.push(Shadow {
                                    origin: Some(p),
                                    arity: 0,
                                });
                            }
                            None => {
                                // A literal of one union member.
                                if let Some((i, m)) = self.union_member_for_lit(lit, t) {
                                    tasks.push(Task::Build(BuildKind::Variant(i), 1, Some(p)));
                                    tasks.push(Task::Visit(p, m));
                                    continue;
                                }
                                exact = false;
                                wild(&mut vals, &mut shadow, Some(p));
                            }
                        },
                        Pat::Range { lo, hi, inclusive } => {
                            match self.range_pattern(lo, hi, inclusive, t)? {
                                Some(c) => {
                                    vals.push(c);
                                    shadow.push(Shadow {
                                        origin: Some(p),
                                        arity: 0,
                                    });
                                }
                                None => {
                                    exact = false;
                                    wild(&mut vals, &mut shadow, Some(p));
                                }
                            }
                        }
                        Pat::Ref { inner, .. } => match self.types.get(t) {
                            Type::Ref { inner: it, .. } => {
                                tasks.push(Task::Build(BuildKind::Product, 1, Some(p)));
                                tasks.push(Task::Visit(inner, it));
                            }
                            _ => {
                                exact = false;
                                wild(&mut vals, &mut shadow, Some(p));
                            }
                        },
                        Pat::TypeTest { ty: tt, pat: sub } => {
                            let target = self.lower_ty(tt, self.cur_self, false)?;
                            let target = self.resolve(target);
                            let member = match self.types.get(t) {
                                Type::Union(ms) => {
                                    ms.iter().position(|&m| m == target).map(|i| (i, target))
                                }
                                _ => None,
                            };
                            match (member, sub) {
                                (Some((i, m)), _) => {
                                    tasks.push(Task::Build(
                                        BuildKind::Variant(u32::try_from(i).unwrap_or(0)),
                                        1,
                                        Some(p),
                                    ));
                                    match sub {
                                        Some(s) => tasks.push(Task::Visit(s, m)),
                                        None => {
                                            vals.push(match_lang::Pat::wild());
                                            shadow.push(Shadow {
                                                origin: None,
                                                arity: 0,
                                            });
                                        }
                                    }
                                }
                                (None, Some(s)) if target == t => tasks.push(Task::Visit(s, t)),
                                (None, None) if target == t => {
                                    wild(&mut vals, &mut shadow, Some(p));
                                }
                                _ => {
                                    exact = false;
                                    wild(&mut vals, &mut shadow, Some(p));
                                }
                            }
                        }
                        Pat::Tuple { elems, rest } => {
                            let elems = hir.list(elems).to_vec();
                            let mut fields = Vec::new();
                            self.match_fields(t, 0, &mut fields)?;
                            if !matches!(self.types.get(t), Type::Tuple(_)) {
                                exact = false;
                                wild(&mut vals, &mut shadow, Some(p));
                                continue;
                            }
                            self.push_positional(
                                p,
                                &elems,
                                rest,
                                &fields,
                                BuildKind::Product,
                                &mut tasks,
                            );
                        }
                        Pat::Ctor { path, elems, rest } => {
                            let elems = hir.list(elems).to_vec();
                            match self.ctor_target(path, t)? {
                                Some((kind, fields)) => {
                                    self.push_positional(
                                        p, &elems, rest, &fields, kind, &mut tasks,
                                    );
                                }
                                None => {
                                    exact = false;
                                    wild(&mut vals, &mut shadow, Some(p));
                                }
                            }
                        }
                        Pat::Record { path, fields, .. } => {
                            let fps = hir.list(fields).to_vec();
                            match self.record_target(path, t)? {
                                Some((kind, decl)) => {
                                    // Each declared field: the pattern naming
                                    // it, or `_`.
                                    let n = u32::try_from(decl.len()).unwrap_or(0);
                                    tasks.push(Task::Build(kind, n, Some(p)));
                                    for f in decl.iter().rev() {
                                        match fps.iter().find(|fp| fp.name.sym == f.name) {
                                            Some(fp) => tasks.push(Task::Visit(fp.pat, f.ty)),
                                            None => tasks.push(Task::Wild),
                                        }
                                    }
                                }
                                None => {
                                    exact = false;
                                    wild(&mut vals, &mut shadow, Some(p));
                                }
                            }
                        }
                        Pat::Slice { prefix, rest } => {
                            let elem = match self.types.get(t) {
                                Type::Array { elem, .. }
                                | Type::ParamArray { elem, .. }
                                | Type::Slice(elem) => Some(elem),
                                _ => None,
                            };
                            let Some(elem) = elem else {
                                exact = false;
                                wild(&mut vals, &mut shadow, Some(p));
                                continue;
                            };
                            let prefix = hir.list(prefix).to_vec();
                            let suffix =
                                rest.map_or_else(Vec::new, |r| hir.list(r.suffix).to_vec());
                            let n = u32::try_from(prefix.len() + suffix.len()).unwrap_or(0);
                            let kind = if rest.is_some() {
                                BuildKind::SliceRest(u32::try_from(prefix.len()).unwrap_or(0))
                            } else {
                                BuildKind::Slice
                            };
                            tasks.push(Task::Build(kind, n, Some(p)));
                            for &x in prefix.iter().chain(&suffix).rev() {
                                tasks.push(Task::Visit(x, elem));
                            }
                        }
                    }
                }
            }
        }
        let pat = vals.pop().unwrap_or_else(match_lang::Pat::wild);
        Ok((pat, shadow, exact))
    }
}

/// The HIR origin of the node at preorder index `index` of a translated
/// pattern, from its post-order shadow tree.
fn preorder_origin(shadow: &[Shadow], index: usize) -> Option<PatId> {
    let n = shadow.len();
    // Subtree sizes in post-order.
    let mut size = alloc::vec![1usize; n];
    for k in 0..n {
        let arity = shadow.get(k).map_or(0, |s| s.arity as usize);
        let mut child = k;
        let mut total = 1;
        for _ in 0..arity {
            if child == 0 {
                break;
            }
            let c = child - 1;
            let s = size.get(c).copied().unwrap_or(1);
            total += s;
            child = c + 1 - s;
        }
        if let Some(slot) = size.get_mut(k) {
            *slot = total;
        }
    }
    // Preorder from the root (the last node), children left to right.
    let mut stack: Vec<usize> = alloc::vec![n.checked_sub(1)?];
    let mut counter = 0usize;
    while let Some(k) = stack.pop() {
        if counter == index {
            return shadow.get(k).and_then(|s| s.origin);
        }
        counter += 1;
        let arity = shadow.get(k).map_or(0, |s| s.arity as usize);
        let mut kids = Vec::with_capacity(arity);
        let mut child = k;
        for _ in 0..arity {
            if child == 0 {
                break;
            }
            let c = child - 1;
            kids.push(c);
            child = c + 1 - size.get(c).copied().unwrap_or(1);
        }
        // `kids` is last-to-first; push so the first pops first.
        stack.extend(kids);
    }
    None
}

/// The child patterns of `p`, for walks.
fn pat_children(hir: &hir_lang::Hir, p: PatId, out: &mut Vec<PatId>) {
    match *hir.pat(p) {
        Pat::Bind { sub: Some(s), .. } | Pat::Ref { inner: s, .. } => out.push(s),
        Pat::TypeTest { pat: Some(s), .. } => out.push(s),
        Pat::Range { lo, hi, .. } => {
            out.extend(lo);
            out.extend(hi);
        }
        Pat::Tuple { elems, .. } | Pat::Ctor { elems, .. } | Pat::Or(elems) => {
            out.extend_from_slice(hir.list(elems));
        }
        Pat::Record { fields, .. } => out.extend(hir.list(fields).iter().map(|f| f.pat)),
        Pat::Slice { prefix, rest } => {
            out.extend_from_slice(hir.list(prefix));
            if let Some(r) = rest {
                out.extend(r.bind);
                out.extend_from_slice(hir.list(r.suffix));
            }
        }
        _ => {}
    }
}

impl Ctx<'_> {
    /// Pushes the fields of a positional constructor pattern: written
    /// elements before the rest, wildcards for the elided ones, written
    /// elements after the rest. A count that cannot fit (already reported)
    /// becomes all wildcards.
    fn push_positional(
        &mut self,
        p: PatId,
        elems: &[PatId],
        rest: Option<u32>,
        fields: &[TypeId],
        kind: BuildKind,
        tasks: &mut Vec<Task>,
    ) {
        let n = fields.len();
        let k = elems.len();
        let fits = match rest {
            None => k == n,
            Some(_) => k <= n,
        };
        tasks.push(Task::Build(kind, u32::try_from(n).unwrap_or(0), Some(p)));
        let split = rest.map_or(k, |r| (r as usize).min(k));
        let mut order: Vec<Task> = Vec::with_capacity(n);
        for (i, &ft) in fields.iter().enumerate() {
            let pick = if !fits {
                None
            } else if i < split {
                elems.get(i).copied()
            } else if i >= n - (k - split) {
                elems.get(k - (n - i)).copied()
            } else {
                None
            };
            order.push(match pick {
                Some(e) => Task::Visit(e, ft),
                None => Task::Wild,
            });
        }
        tasks.extend(order.into_iter().rev());
    }

    /// The position of variant `v` in its sum.
    fn variant_index(&self, v: VariantId) -> Option<(hir_lang::ItemId, u32)> {
        let sum = self.hir.variant_owner(v)?;
        let ItemKind::Sum(d) = self.item_kind(sum) else {
            return None;
        };
        let i = self.hir.list(d.variants).iter().position(|&x| x == v)?;
        Some((sum, u32::try_from(i).ok()?))
    }

    /// The sum item a type is an instance of.
    fn sum_of(&self, t: TypeId) -> Option<hir_lang::ItemId> {
        match self.types.get(self.resolve(t)) {
            Type::Adt { item, .. } if matches!(self.item_kind(item), ItemKind::Sum(_)) => {
                Some(item)
            }
            _ => None,
        }
    }

    /// A path pattern: a unit variant, a unit record, or an integer
    /// constant.
    fn constant_pattern(
        &mut self,
        path: hir_lang::PathId,
        t: TypeId,
    ) -> Result<Option<match_lang::Pat>, CheckError> {
        if let Some(v) = self.variant_of_path(path) {
            let Some((sum, i)) = self.variant_index(v) else {
                return Ok(None);
            };
            let unit = self.hir.variant(v).is_some_and(|x| x.shape == Shape::Unit);
            return Ok(
                (self.sum_of(t) == Some(sum) && unit).then(|| match_lang::Pat::variant(i, []))
            );
        }
        let ph = *self.hir.path(path);
        if ph.unresolved != 0 {
            return Ok(None);
        }
        let Some(item) = self.local_item(ph.res) else {
            return Ok(None);
        };
        match self.item_kind(item) {
            ItemKind::Record(d) if d.shape == Shape::Unit => Ok(matches!(
                self.types.get(self.resolve(t)),
                Type::Adt { item: i, .. } if i == item
            )
            .then(|| match_lang::Pat::product([]))),
            ItemKind::Const { value: Some(v), .. } => {
                let Shape2::Int(lo, hi) = shape_of(self, t) else {
                    return Ok(None);
                };
                Ok(match self.const_eval(v)? {
                    Some(x) if (lo..=hi).contains(&x) => Some(match_lang::Pat::int(x)),
                    _ => None,
                })
            }
            _ => Ok(None),
        }
    }

    /// A literal pattern at a type of its own class.
    fn literal_pattern(&mut self, lit: Lit, t: TypeId) -> Option<match_lang::Pat> {
        match (shape_of(self, t), lit) {
            (Shape2::Bool, Lit::Bool(b)) => Some(match_lang::Pat::bool(b)),
            (Shape2::Int(lo, hi), Lit::Int(l)) => {
                let v = i128::from(l.value);
                let v = if l.negative { -v } else { v };
                (lo..=hi).contains(&v).then(|| match_lang::Pat::int(v))
            }
            (Shape2::Char, Lit::Char(c)) => Some(match_lang::Pat::char(c)),
            (Shape2::Opaque, Lit::Str(text)) => {
                let bytes = self.hir.text(text).to_vec();
                let next = self.lit_ids.len() as u64;
                let id = *self.lit_ids.entry(bytes).or_insert(next);
                Some(match_lang::Pat::lit(id))
            }
            _ => None,
        }
    }

    /// For a literal matched against a union: the first member of its
    /// class.
    fn union_member_for_lit(&mut self, lit: Lit, t: TypeId) -> Option<(u32, TypeId)> {
        let Type::Union(ms) = self.types.get(self.resolve(t)) else {
            return None;
        };
        let ms = ms.to_vec();
        for (i, m) in ms.into_iter().enumerate() {
            let fits = matches!(
                (shape_of(self, m), lit),
                (Shape2::Bool, Lit::Bool(_))
                    | (Shape2::Int(..), Lit::Int(_))
                    | (Shape2::Char, Lit::Char(_))
            ) || (matches!(lit, Lit::Str(_)) && self.prim_of(m) == Some(Prim::Str));
            if fits {
                return Some((u32::try_from(i).ok()?, m));
            }
        }
        None
    }

    /// The value of a range bound: an integer or character literal, or an
    /// integer constant.
    fn bound_value(&mut self, p: PatId) -> Result<Option<i128>, CheckError> {
        Ok(match *self.hir.pat(p) {
            Pat::Lit(Lit::Int(l)) => {
                let v = i128::from(l.value);
                Some(if l.negative { -v } else { v })
            }
            Pat::Lit(Lit::Char(c)) => Some(i128::from(u32::from(c))),
            Pat::Path(path) | Pat::Ident { path, .. } => {
                let ph = *self.hir.path(path);
                match (ph.unresolved, self.local_item(ph.res)) {
                    (0, Some(item)) => match self.item_kind(item) {
                        ItemKind::Const { value: Some(v), .. } => self.const_eval(v)?,
                        _ => None,
                    },
                    _ => None,
                }
            }
            _ => None,
        })
    }

    fn range_pattern(
        &mut self,
        lo: Option<PatId>,
        hi: Option<PatId>,
        inclusive: bool,
        t: TypeId,
    ) -> Result<Option<match_lang::Pat>, CheckError> {
        let (min, max, is_char) = match shape_of(self, t) {
            Shape2::Int(a, b) => (a, b, false),
            Shape2::Char => (0, 0x10_FFFF, true),
            _ => return Ok(None),
        };
        let a = match lo {
            Some(p) => match self.bound_value(p)? {
                Some(v) => v,
                None => return Ok(None),
            },
            None => min,
        };
        let b = match hi {
            Some(p) => match self.bound_value(p)? {
                Some(v) if inclusive => v,
                Some(v) => v - 1,
                None => return Ok(None),
            },
            None => max,
        };
        if a > b || a < min || b > max {
            // Empty, or outside the type: it never adds coverage.
            return Ok(None);
        }
        if is_char {
            let (Some(x), Some(y)) = (
                u32::try_from(a).ok().and_then(char::from_u32),
                u32::try_from(b).ok().and_then(char::from_u32),
            ) else {
                return Ok(None);
            };
            return Ok(Some(match_lang::Pat::char_range(x, y)));
        }
        Ok(Some(match_lang::Pat::range(a, b)))
    }

    /// What a constructor pattern builds at `t`: a variant or a tuple
    /// record, with its field types.
    fn ctor_target(
        &mut self,
        path: hir_lang::PathId,
        t: TypeId,
    ) -> Result<Option<(BuildKind, Vec<TypeId>)>, CheckError> {
        if let Some(v) = self.variant_of_path(path) {
            let Some((sum, i)) = self.variant_index(v) else {
                return Ok(None);
            };
            if self.sum_of(t) != Some(sum) {
                return Ok(None);
            }
            let mut fields = Vec::new();
            self.match_fields(t, i, &mut fields)?;
            return Ok(Some((BuildKind::Variant(i), fields)));
        }
        let ph = *self.hir.path(path);
        let item = (ph.unresolved == 0)
            .then(|| self.local_item(ph.res))
            .flatten();
        match (item, self.types.get(self.resolve(t))) {
            (Some(i), Type::Adt { item, .. })
                if i == item && matches!(self.item_kind(i), ItemKind::Record(_)) =>
            {
                let mut fields = Vec::new();
                self.match_fields(t, 0, &mut fields)?;
                Ok(Some((BuildKind::Product, fields)))
            }
            _ => Ok(None),
        }
    }

    /// What a record pattern matches at `t`: its constructor and declared
    /// fields (name and type) in model order.
    fn record_target(
        &mut self,
        path: Option<hir_lang::PathId>,
        t: TypeId,
    ) -> Result<Option<(BuildKind, Vec<Field>)>, CheckError> {
        let r = self.resolve(t);
        let Some(path) = path else {
            return Ok(match self.types.get(r) {
                Type::Record(fields) => Some((BuildKind::Product, fields.to_vec())),
                _ => None,
            });
        };
        let (kind, ids, variant) = if let Some(v) = self.variant_of_path(path) {
            let Some((sum, i)) = self.variant_index(v) else {
                return Ok(None);
            };
            if self.sum_of(t) != Some(sum) {
                return Ok(None);
            }
            let ids = self
                .hir
                .variant(v)
                .map(|x| self.hir.list(x.fields).to_vec())
                .unwrap_or_default();
            (BuildKind::Variant(i), ids, i)
        } else {
            let ph = *self.hir.path(path);
            let item = (ph.unresolved == 0)
                .then(|| self.local_item(ph.res))
                .flatten();
            match (item, self.types.get(r)) {
                (Some(i), Type::Adt { item, .. })
                    if i == item
                        && matches!(self.item_kind(i), ItemKind::Record(d) if !d.is_union) =>
                {
                    (BuildKind::Product, self.record_field_ids(i), 0)
                }
                _ => return Ok(None),
            }
        };
        let mut tys = Vec::new();
        self.match_fields(t, variant, &mut tys)?;
        let mut out = Vec::with_capacity(ids.len());
        for (f, ty) in ids.into_iter().zip(tys) {
            let Some(name) = self.hir.field(f).name else {
                return Ok(None);
            };
            out.push(Field { name: name.sym, ty });
        }
        Ok(Some((kind, out)))
    }

    /// Stores a witness in the result's witness pool, in preorder.
    fn convert_witness(&mut self, w: &match_lang::Witness<TypeId>) -> Result<(), CheckError> {
        let mut stack = alloc::vec![w.root()];
        while let Some(node) = stack.pop() {
            self.meter.tick(1)?;
            let t = self.resolve(*node.ty());
            let arity = u32::try_from(node.arity()).unwrap_or(0);
            let mut names = (0u32, 0u32);
            let kind = match node.ctor() {
                Ctor::Variant(i) => match self.types.get(t) {
                    Type::Nullable(_) => {
                        if i == 0 {
                            WKind::Null
                        } else {
                            WKind::Value
                        }
                    }
                    Type::Union(ms) => {
                        WKind::Member(ms.get(i as usize).copied().unwrap_or(TypeId::ERROR))
                    }
                    Type::Adt { item, .. } => match self.item_kind(item) {
                        ItemKind::Sum(d) => match self.hir.list(d.variants).get(i as usize) {
                            Some(&v) => {
                                if let Some(var) = self.hir.variant(v).copied() {
                                    if var.shape == Shape::Named {
                                        let ids = self.hir.list(var.fields).to_vec();
                                        names = self.witness_field_names(ids);
                                    }
                                }
                                WKind::Variant(v)
                            }
                            None => WKind::Wild,
                        },
                        _ => WKind::Wild,
                    },
                    _ => WKind::Wild,
                },
                Ctor::Product => match self.types.get(t) {
                    Type::Adt { item, .. } => {
                        if let ItemKind::Record(d) = self.item_kind(item) {
                            if d.shape == Shape::Named {
                                let ids = self.hir.list(d.fields).to_vec();
                                names = self.witness_field_names(ids);
                            }
                        }
                        WKind::Item(item)
                    }
                    Type::Ref { .. } => WKind::Ref,
                    Type::Record(fields) => {
                        let start = u32::try_from(self.wsyms.len()).unwrap_or(NONE);
                        let syms: Vec<hir_lang::Symbol> = fields.iter().map(|f| f.name).collect();
                        self.wsyms.extend(syms.iter().copied());
                        names = (start, u32::try_from(syms.len()).unwrap_or(0));
                        WKind::Tuple
                    }
                    _ => WKind::Tuple,
                },
                Ctor::Bool(b) => WKind::Bool(b),
                Ctor::Int { lo, hi } => WKind::Int(lo, hi),
                Ctor::Char { lo, hi } => WKind::Char(lo, hi),
                Ctor::Slice { len } => WKind::Slice(len),
                Ctor::SliceRest { prefix, suffix } => WKind::SliceRest(prefix, suffix),
                _ => WKind::Wild,
            };
            self.wnodes.push(WNode { kind, arity, names });
            let kids: Vec<_> = node.fields().collect();
            stack.extend(kids.into_iter().rev());
        }
        Ok(())
    }

    fn witness_field_names(&mut self, fields: Vec<hir_lang::FieldId>) -> (u32, u32) {
        let start = u32::try_from(self.wsyms.len()).unwrap_or(NONE);
        let mut n = 0u32;
        for f in fields {
            if let Some(name) = self.hir.field(f).name {
                self.wsyms.push(name.sym);
                n += 1;
            }
        }
        (start, n)
    }
}
