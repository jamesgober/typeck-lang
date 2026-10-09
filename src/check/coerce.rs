//! Coercion (a value meeting a context of another type) and joins (the type
//! of `if`/`match` branches that disagree).
//!
//! Unification is tried first; the profile's implicit conversions only when
//! it fails. Every accepted conversion is recorded for lowering.

use alloc::vec::Vec;

use hir_lang::{ExprId, ItemId, ItemKind, NodeRef, Prim};

use super::Ctx;
use crate::{
    diag::DiagnosticKind,
    error::CheckError,
    profile::RecordTyping,
    typed::Coercion,
    types::{Tag, Type, TypeId},
};

/// The outcome of a coercion attempt.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Fit {
    /// Equal types (after unification), or a value that never exists.
    Same,
    /// Accepted with an implicit conversion.
    Converted(Coercion),
    /// Rejected; nothing changed.
    No,
}

impl Ctx<'_> {
    /// Whether a value of `found` may be used where `expected` is required.
    pub(crate) fn coerce(&mut self, found: TypeId, expected: TypeId) -> Result<Fit, CheckError> {
        if found == expected {
            return Ok(Fit::Same);
        }
        self.coerce_with(found, expected, true)
    }

    fn coerce_with(
        &mut self,
        found: TypeId,
        expected: TypeId,
        wrap: bool,
    ) -> Result<Fit, CheckError> {
        let (f, x) = (self.resolve(found), self.resolve(expected));
        let (ft, xt) = (self.tag(f), self.tag(x));
        // A diverging expression fits anywhere without constraining it.
        if ft == Tag::Never {
            return Ok(Fit::Same);
        }
        if self.unify(found, expected)? {
            return Ok(Fit::Same);
        }
        if xt == Tag::Any {
            return Ok(Fit::Converted(Coercion::ToAny));
        }
        if ft == Tag::Null {
            let ok = xt == Tag::Nullable || (!self.profile.null_safety && self.reference_like(x));
            return Ok(if ok {
                Fit::Converted(Coercion::Null)
            } else {
                Fit::No
            });
        }
        if xt == Tag::Nullable && wrap {
            // `T` into `T?`. Nullable layers can stack through variables;
            // peel them all, then convert without wrapping again.
            let mut inner = x;
            while self.tag(inner) == Tag::Nullable {
                self.meter.tick(1)?;
                inner = self.resolve(TypeId::from_raw(self.types.node(inner).x));
            }
            return Ok(match self.coerce_with(f, inner, false)? {
                Fit::No => Fit::No,
                _ => Fit::Converted(Coercion::WrapNullable),
            });
        }
        if self.profile.numeric_widening {
            if let (Some(a), Some(b)) = (self.prim_of(f), self.prim_of(x)) {
                if widens(a, b) {
                    return Ok(Fit::Converted(Coercion::Widen));
                }
            }
        }
        if self.profile.subtyping {
            if let (Type::Adt(a), Type::Adt(b)) = (self.types.get(f), self.types.get(x)) {
                if self.is_subclass(a, b)? {
                    return Ok(Fit::Converted(Coercion::Subclass));
                }
                if self.profile.records == RecordTyping::Structural && self.record_width(f, x)? {
                    return Ok(Fit::Converted(Coercion::RecordWidth));
                }
            } else if self.profile.records == RecordTyping::Structural && self.record_width(f, x)? {
                return Ok(Fit::Converted(Coercion::RecordWidth));
            }
        }
        // Views borrow the store; copy out the ids before unifying.
        enum Shape {
            Unsize(TypeId, TypeId),
            Refs(bool, TypeId, TypeId),
        }
        let shape = match (self.types.get(f), self.types.get(x)) {
            (Type::Array { elem, .. }, Type::Slice(target)) => Some(Shape::Unsize(elem, target)),
            (
                Type::Ref {
                    mutable: fm,
                    inner: fi,
                },
                Type::Ref {
                    mutable: false,
                    inner: xi,
                },
            ) => Some(Shape::Refs(fm, fi, xi)),
            _ => None,
        };
        match shape {
            Some(Shape::Unsize(elem, target)) if self.unify(elem, target)? => {
                return Ok(Fit::Converted(Coercion::Unsize));
            }
            Some(Shape::Refs(fm, fi, xi)) => {
                let (fi_r, xi_r) = (self.resolve(fi), self.resolve(xi));
                let unsize = match (self.types.get(fi_r), self.types.get(xi_r)) {
                    (Type::Array { elem, .. }, Type::Slice(target)) => Some((elem, target)),
                    _ => None,
                };
                if let Some((elem, target)) = unsize {
                    if self.unify(elem, target)? {
                        return Ok(Fit::Converted(Coercion::Unsize));
                    }
                }
                if fm && self.unify(fi, xi)? {
                    return Ok(Fit::Converted(Coercion::Reborrow));
                }
            }
            _ => {}
        }
        Ok(Fit::No)
    }

    /// Types that `null` may stand for when the profile has no null safety.
    fn reference_like(&self, t: TypeId) -> bool {
        match self.types.get(t) {
            Type::Ref { .. }
            | Type::Ptr { .. }
            | Type::Adt(_)
            | Type::Foreign(_)
            | Type::Extern(_)
            | Type::Fn { .. }
            | Type::Slice(_)
            | Type::Map { .. }
            | Type::Nullable(_)
            | Type::Record(_)
            | Type::Param(_)
            | Type::Async(_)
            | Type::Task(_)
            | Type::Generator { .. } => true,
            Type::Prim(p) => p == Prim::Str,
            _ => false,
        }
    }

    /// Whether class `sub` inherits (transitively) from class `sup`.
    pub(crate) fn is_subclass(&mut self, sub: ItemId, sup: ItemId) -> Result<bool, CheckError> {
        if !matches!(self.item_kind(sub), ItemKind::Class(_)) {
            return Ok(false);
        }
        self.new_visit();
        let mut stack: Vec<ItemId> = alloc::vec![sub];
        while let Some(c) = stack.pop() {
            self.meter.tick(1)?;
            if c == sup {
                return Ok(true);
            }
            if !self.visit(c) {
                continue;
            }
            stack.extend(self.idx.bases_of(c).iter().copied());
        }
        Ok(false)
    }

    /// Structural width subtyping: `found` has every field of `expected`
    /// (with equal types), and possibly more.
    fn record_width(&mut self, found: TypeId, expected: TypeId) -> Result<bool, CheckError> {
        let (Some(ff), Some(xf)) = (
            self.record_fields_of(found),
            self.record_fields_of(expected),
        ) else {
            return Ok(false);
        };
        let snap = self.infer.snapshot();
        let mut i = 0;
        for want in &xf {
            while ff.get(i).is_some_and(|f| f.name < want.name) {
                i += 1;
            }
            let ok = match ff.get(i) {
                Some(have) if have.name == want.name => self.unify(have.ty, want.ty)?,
                _ => false,
            };
            if !ok {
                self.infer.rollback(snap);
                return Ok(false);
            }
        }
        self.infer.commit();
        Ok(true)
    }

    /// The sorted fields of an anonymous record or a named-field record item.
    pub(crate) fn record_fields_of(&self, t: TypeId) -> Option<Vec<crate::types::Field>> {
        let n = self.types.node(t);
        match n.tag {
            Tag::Record => Some(self.types.fields_of(&n).to_vec()),
            Tag::Adt => {
                let (start, len) = (*self.record_fields.get(n.x as usize)?)?;
                self.field_pool
                    .get(start as usize..(start as usize).saturating_add(len as usize))
                    .map(<[_]>::to_vec)
            }
            _ => None,
        }
    }

    /// Coerces expression `e` (of type `found`) to `expected`, reporting a
    /// mismatch at `e` and recording any conversion.
    pub(crate) fn coerce_expr(
        &mut self,
        e: ExprId,
        found: TypeId,
        expected: TypeId,
    ) -> Result<bool, CheckError> {
        match self.coerce(found, expected)? {
            Fit::Same => Ok(true),
            Fit::Converted(c) => {
                self.coercions.push((e, c, expected));
                Ok(true)
            }
            Fit::No => {
                self.report(
                    NodeRef::Expr(e),
                    DiagnosticKind::Mismatch { expected, found },
                );
                self.poison(e);
                Ok(false)
            }
        }
    }

    /// The common type of two branches. Tries equality, then converting
    /// either side into the other, then `null` with `T`; on failure reports
    /// at the later branch.
    pub(crate) fn join(
        &mut self,
        prev: TypeId,
        prev_expr: Option<ExprId>,
        next: TypeId,
        next_expr: ExprId,
    ) -> Result<TypeId, CheckError> {
        let (pt, nt) = (self.tag(prev), self.tag(next));
        if pt == Tag::Never || pt == Tag::Error {
            return Ok(next);
        }
        if nt == Tag::Never || nt == Tag::Error {
            return Ok(prev);
        }
        if self.unify(prev, next)? {
            return Ok(prev);
        }
        match self.coerce(next, prev)? {
            Fit::Same => return Ok(prev),
            Fit::Converted(c) => {
                self.coercions.push((next_expr, c, prev));
                return Ok(prev);
            }
            Fit::No => {}
        }
        if let Some(pe) = prev_expr {
            match self.coerce(prev, next)? {
                Fit::Same => return Ok(next),
                Fit::Converted(c) => {
                    self.coercions.push((pe, c, next));
                    return Ok(next);
                }
                Fit::No => {}
            }
        }
        // `null` and `T` join to `T?` under null safety.
        if self.profile.null_safety && (pt == Tag::Null || nt == Tag::Null) {
            let (other, other_expr, null_expr) = if pt == Tag::Null {
                (next, Some(next_expr), prev_expr)
            } else {
                (prev, prev_expr, Some(next_expr))
            };
            let joined = self.types.nullable(other);
            if let Some(e) = other_expr {
                self.coercions.push((e, Coercion::WrapNullable, joined));
            }
            if let Some(e) = null_expr {
                self.coercions.push((e, Coercion::Null, joined));
            }
            return Ok(joined);
        }
        self.report(
            NodeRef::Expr(next_expr),
            DiagnosticKind::Mismatch {
                expected: prev,
                found: next,
            },
        );
        self.poison(next_expr);
        Ok(prev)
    }
}

/// Lossless implicit numeric widening.
pub(crate) fn widens(from: Prim, to: Prim) -> bool {
    let (fb, tb) = (from.bits(), to.bits());
    if from.is_int() && to.is_int() {
        if from.is_signed() && !to.is_signed() {
            return false;
        }
        // Unsigned into signed needs a strictly wider target, and so does
        // any change of width.
        return fb < tb;
    }
    if from.is_int() && to.is_float() {
        // Every value fits the float's mantissa exactly.
        return (to == Prim::F32 && fb <= 16) || (to == Prim::F64 && fb <= 32);
    }
    from == Prim::F32 && to == Prim::F64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_widening_table() {
        assert!(widens(Prim::I8, Prim::I64));
        assert!(widens(Prim::U8, Prim::I16));
        assert!(!widens(Prim::I8, Prim::U64));
        assert!(!widens(Prim::I64, Prim::I32));
        assert!(!widens(Prim::I64, Prim::Isize));
        assert!(widens(Prim::I32, Prim::F64));
        assert!(!widens(Prim::I64, Prim::F64));
        assert!(widens(Prim::U16, Prim::F32));
        assert!(!widens(Prim::U32, Prim::F32));
        assert!(widens(Prim::F32, Prim::F64));
        assert!(!widens(Prim::F64, Prim::F32));
        assert!(!widens(Prim::Bool, Prim::I8));
    }
}
