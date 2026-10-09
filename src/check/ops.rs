//! OPS operations typed by their operand types, and `as` casts.
//!
//! HIR fixes each operation's policy but not its operand types (spec §12):
//! the same `add` is integer, IEEE, or (with the profile's `string_add`)
//! string concatenation. Operands of a binary operation have the same type
//! (OPS §3); shift amounts may be any integer type. An operand of a still
//! unknown type is checked again once inference has finished.

use hir_lang::{ExprId, NodeRef, Op, OpKind, Overflow, Policy, Prim};

use super::Ctx;
use crate::{
    diag::DiagnosticKind,
    error::CheckError,
    infer::{FLOAT, INT, is_float_code, is_int_code},
    types::{Tag, Type, TypeId},
};

/// What an operand must be.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Want {
    /// An integer or float (or a string, for `add` with `string_add`).
    Numeric {
        or_str: bool,
    },
    Int,
    Float,
    IntOrBool,
    /// Equality: numbers, `bool`, `char`, strings.
    Equatable,
    /// Ordering: numbers, `char`, strings.
    Ordered,
    Bool,
}

impl Ctx<'_> {
    /// Whether `t` (resolved, not a general variable) satisfies `want`.
    fn satisfies(&self, t: TypeId, want: Want) -> bool {
        let n = self.types.node(t);
        let (int, float) = match n.tag {
            Tag::Prim => (is_int_code(n.small), is_float_code(n.small)),
            Tag::Var => (
                self.infer.class_of(t) == INT,
                self.infer.class_of(t) == FLOAT,
            ),
            _ => (false, false),
        };
        let prim = self.prim_of(t);
        let is = |p: Prim| prim == Some(p);
        match want {
            Want::Numeric { or_str } => int || float || (or_str && is(Prim::Str)),
            Want::Int => int,
            Want::Float => float,
            Want::IntOrBool => int || is(Prim::Bool),
            Want::Equatable => int || float || is(Prim::Bool) || is(Prim::Char) || is(Prim::Str),
            Want::Ordered => int || float || is(Prim::Char) || is(Prim::Str),
            Want::Bool => is(Prim::Bool),
        }
    }

    /// Checks one operand. `Ok(false)`: reported (or `{error}`); the caller
    /// stops checking this operation.
    fn require(&mut self, op: OpKind, operand: ExprId, want: Want) -> Result<bool, CheckError> {
        let t = self.resolve(self.child(operand));
        match self.tag(t) {
            Tag::Error | Tag::Never => return Ok(false),
            Tag::Var if self.infer.class_of(t) == crate::infer::GENERAL => {
                self.deferred_ops.push((operand, op, want));
                return Ok(true);
            }
            _ => {}
        }
        // An integer literal used where only floats fit becomes a float
        // literal when the profile widens.
        if want == Want::Float
            && self.tag(t) == Tag::Var
            && self.infer.class_of(t) == INT
            && self.profile.numeric_widening
        {
            let f = self.fresh(FLOAT);
            if self.unify(t, f)? {
                return Ok(true);
            }
        }
        if self.satisfies(t, want) {
            return Ok(true);
        }
        self.report(NodeRef::Expr(operand), DiagnosticKind::OpType { op, ty: t });
        self.poison(operand);
        Ok(false)
    }

    /// Unifies a later operand with the first; reports at the later one.
    fn same(&mut self, first: ExprId, later: ExprId) -> Result<bool, CheckError> {
        let (a, b) = (self.child(first), self.child(later));
        if self.is_err(a) || self.is_err(b) {
            return Ok(false);
        }
        if self.unify(a, b)? {
            return Ok(true);
        }
        self.report(
            NodeRef::Expr(later),
            DiagnosticKind::Mismatch {
                expected: a,
                found: b,
            },
        );
        self.poison(later);
        Ok(false)
    }

    /// Re-checks operands whose type was unknown when their operation was
    /// checked.
    pub(crate) fn recheck_deferred_ops(&mut self) -> Result<(), CheckError> {
        let deferred = core::mem::take(&mut self.deferred_ops);
        for &(operand, op, want) in &deferred {
            self.meter.tick(1)?;
            let t = self.resolve(self.ety(operand));
            if matches!(self.tag(t), Tag::Var | Tag::Error | Tag::Never) {
                continue;
            }
            if !self.satisfies(t, want) {
                self.report(NodeRef::Expr(operand), DiagnosticKind::OpType { op, ty: t });
            }
        }
        Ok(())
    }

    /// The type of an `Op` expression under a static profile.
    pub(crate) fn op_type(
        &mut self,
        e: ExprId,
        op: Op,
        args: &[ExprId],
    ) -> Result<TypeId, CheckError> {
        let kind = op.kind;
        // A dynamic operand makes the operation dynamic, which a static
        // profile does not allow.
        if args.iter().any(|&a| self.tag(self.child(a)) == Tag::Any) {
            self.report(NodeRef::Expr(e), DiagnosticKind::DynamicOperation);
            return Ok(TypeId::ERROR);
        }
        let first = args.first().copied();
        let second = args.get(1).copied();
        let a0 = first.map_or(TypeId::ERROR, |a| self.child(a));
        let bool_ty = TypeId::prim(Prim::Bool);
        let result = match kind {
            OpKind::Add
            | OpKind::Sub
            | OpKind::Mul
            | OpKind::Div
            | OpKind::Rem
            | OpKind::Min
            | OpKind::Max => {
                let or_str = kind == OpKind::Add && self.profile.string_add;
                self.binary(kind, args, Want::Numeric { or_str }, a0)?
            }
            OpKind::FloorDiv | OpKind::FloorMod => self.binary(kind, args, Want::Int, a0)?,
            OpKind::And | OpKind::Or | OpKind::Xor => {
                self.binary(kind, args, Want::IntOrBool, a0)?
            }
            OpKind::IeeeRem | OpKind::Fma => self.binary(kind, args, Want::Float, a0)?,
            OpKind::TotalCmp => {
                let _ = self.binary(kind, args, Want::Float, a0)?;
                TypeId::prim(Prim::I8)
            }
            OpKind::Neg | OpKind::Abs => {
                self.unary(kind, first, Want::Numeric { or_str: false }, a0)?
            }
            OpKind::Not => self.unary(kind, first, Want::IntOrBool, a0)?,
            OpKind::Sqrt
            | OpKind::Floor
            | OpKind::Ceil
            | OpKind::Trunc
            | OpKind::Round
            | OpKind::RoundEven => self.unary(kind, first, Want::Float, a0)?,
            OpKind::Shl | OpKind::Shr => {
                let ok = match first {
                    Some(a) => self.require(kind, a, Want::Int)?,
                    None => false,
                };
                if let Some(b) = second {
                    let _ = self.require(kind, b, Want::Int)?;
                }
                if ok { a0 } else { TypeId::ERROR }
            }
            OpKind::Eq | OpKind::Ne => {
                if self.null_check(first, second) {
                    self.null_checks.push(e);
                } else {
                    let _ = self.binary(kind, args, Want::Equatable, a0)?;
                }
                bool_ty
            }
            OpKind::Lt | OpKind::Le | OpKind::Gt | OpKind::Ge => {
                let _ = self.binary(kind, args, Want::Ordered, a0)?;
                bool_ty
            }
            OpKind::IntCast(t)
            | OpKind::IntToFloat(t)
            | OpKind::BoolToInt(t)
            | OpKind::FloatToInt(t) => {
                let want = match kind {
                    OpKind::FloatToInt(_) => Want::Float,
                    OpKind::BoolToInt(_) => Want::Bool,
                    _ => Want::Int,
                };
                self.convert(kind, first, want, None, TypeId::prim(t))?
            }
            OpKind::Zext(t) | OpKind::Sext(t) | OpKind::Narrow(t) | OpKind::Bitcast(t) => {
                let want = if matches!(kind, OpKind::Bitcast(_)) {
                    Want::Numeric { or_str: false }
                } else {
                    Want::Int
                };
                self.convert(kind, first, want, Some(t), TypeId::prim(t))?
            }
            OpKind::F32ToF64 => self.exact_source(kind, first, Prim::F32, Prim::F64)?,
            OpKind::F64ToF32 => self.exact_source(kind, first, Prim::F64, Prim::F32)?,
            OpKind::CharFromU32 => self.exact_source(kind, first, Prim::U32, Prim::Char)?,
        };
        if op.promotes() && !self.is_err(result) {
            self.report(
                NodeRef::Expr(e),
                DiagnosticKind::PromoteOnStatic { op: Some(kind) },
            );
            return Ok(TypeId::ERROR);
        }
        Ok(result)
    }

    /// `x == null`: one side is `null`, the other may be null.
    fn null_check(&self, a: Option<ExprId>, b: Option<ExprId>) -> bool {
        let (Some(a), Some(b)) = (a, b) else {
            return false;
        };
        let (ta, tb) = (self.tag(self.child(a)), self.tag(self.child(b)));
        let nullish = |t: Tag| matches!(t, Tag::Null | Tag::Nullable);
        (ta == Tag::Null && nullish(tb)) || (tb == Tag::Null && nullish(ta))
    }

    fn binary(
        &mut self,
        kind: OpKind,
        args: &[ExprId],
        want: Want,
        a0: TypeId,
    ) -> Result<TypeId, CheckError> {
        // The first operand that does not fit is the one reported: an
        // operation used on the wrong type is one mistake, not one per
        // operand.
        for &a in args {
            if !self.require(kind, a, want)? {
                return Ok(TypeId::ERROR);
            }
        }
        let Some((&first, rest)) = args.split_first() else {
            return Ok(TypeId::ERROR);
        };
        for &later in rest {
            if !self.same(first, later)? {
                return Ok(TypeId::ERROR);
            }
        }
        Ok(a0)
    }

    fn unary(
        &mut self,
        kind: OpKind,
        arg: Option<ExprId>,
        want: Want,
        a0: TypeId,
    ) -> Result<TypeId, CheckError> {
        Ok(match arg {
            Some(a) if self.require(kind, a, want)? => a0,
            _ => TypeId::ERROR,
        })
    }

    /// A conversion to `result`, with a width check for the bit-level ones.
    fn convert(
        &mut self,
        kind: OpKind,
        arg: Option<ExprId>,
        want: Want,
        width_target: Option<Prim>,
        result: TypeId,
    ) -> Result<TypeId, CheckError> {
        let Some(a) = arg else {
            return Ok(result);
        };
        if !self.require(kind, a, want)? {
            return Ok(result);
        }
        if let (Some(target), Some(src)) = (width_target, self.prim_of(self.child(a))) {
            let (sb, tb) = (src.bits(), target.bits());
            let ok = match kind {
                OpKind::Zext(_) | OpKind::Sext(_) => sb <= tb,
                OpKind::Narrow(_) => sb >= tb,
                _ => sb == tb,
            };
            if !ok {
                let from = self.child(a);
                self.report(
                    NodeRef::Expr(a),
                    DiagnosticKind::BadConversion { op: kind, from },
                );
            }
        }
        Ok(result)
    }

    fn exact_source(
        &mut self,
        kind: OpKind,
        arg: Option<ExprId>,
        from: Prim,
        to: Prim,
    ) -> Result<TypeId, CheckError> {
        if let Some(a) = arg {
            let t = self.child(a);
            if !self.is_err(t) && !self.unify(t, TypeId::prim(from))? {
                self.report(NodeRef::Expr(a), DiagnosticKind::OpType { op: kind, ty: t });
                self.poison(a);
            }
        }
        Ok(TypeId::prim(to))
    }

    // ---------------------------------------------------------------- casts

    /// The type of `expr as ty`.
    pub(crate) fn cast_type(
        &mut self,
        e: ExprId,
        inner: ExprId,
        to: TypeId,
        policy: Policy,
    ) -> Result<TypeId, CheckError> {
        let from = self.resolve(self.child(inner));
        let to_r = self.resolve(to);
        if policy.overflow == Some(Overflow::Promote)
            && self.tag(to_r) != Tag::Any
            && !self.is_err(to_r)
        {
            self.report(
                NodeRef::Expr(e),
                DiagnosticKind::PromoteOnStatic { op: None },
            );
        }
        if matches!(self.tag(from), Tag::Error | Tag::Never) || self.is_err(to_r) {
            return Ok(to);
        }
        if !self.cast_ok(from, to_r)? {
            self.report(
                NodeRef::Expr(e),
                DiagnosticKind::InvalidCast { from, to: to_r },
            );
        }
        Ok(to)
    }

    fn cast_ok(&mut self, from: TypeId, to: TypeId) -> Result<bool, CheckError> {
        if self.unify(from, to)? {
            return Ok(true);
        }
        let numeric = |cx: &Self, t: TypeId| cx.satisfies(t, Want::Numeric { or_str: false });
        let (ft, tt) = (self.types.get(from), self.types.get(to));
        Ok(match (ft, tt) {
            (_, Type::Any) | (Type::Any, _) => true,
            (Type::Ptr { .. } | Type::Ref { .. }, Type::Ptr { .. }) => true,
            (Type::Ptr { .. }, Type::Prim(Prim::Usize | Prim::Isize))
            | (Type::Prim(Prim::Usize | Prim::Isize), Type::Ptr { .. }) => true,
            (Type::Prim(Prim::Bool | Prim::Char), Type::Prim(p)) if p.is_int() => true,
            (Type::Prim(Prim::U8), Type::Prim(Prim::Char)) => true,
            (_, Type::Nullable(inner)) => self.unify(from, inner)?,
            (Type::Adt(a), Type::Adt(b)) => self.is_subclass(a, b)? || self.is_subclass(b, a)?,
            _ => numeric(self, from) && numeric(self, to),
        })
    }
}
