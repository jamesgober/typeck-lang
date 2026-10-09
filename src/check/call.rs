//! Calls: what the callee is, and matching arguments to parameters
//! (positional, named, defaults, variadic rests, spreads, by-reference
//! parameters) per HIR v2 §8.1 and §10.
//!
//! Matching runs twice per call over the same rules. Before the arguments
//! are checked it only sets each argument's expected type (so a literal or
//! a mismatched argument is judged, and reported, at the argument itself);
//! after, it reports arity and naming problems and coerces what could not
//! be expected in advance (arguments after a spread).

use hir_lang::{
    Arg, ArgKind, Effects, Expr, ExprId, ItemId, ItemKind, Member, NodeRef, ParamKind, Symbol,
};

use super::{Ctx, lower::ParamInfo, paths::MemberRef};
use crate::{
    diag::DiagnosticKind,
    error::CheckError,
    infer::GENERAL,
    typed::Coercion,
    types::{Tag, Type, TypeId},
};

/// The resolved callee of a call or method call, kept on a stack between
/// the preparation and the finish of the call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CallTarget {
    /// A function item's signature; the first `skip` positional parameters
    /// are taken by a method receiver.
    Sig {
        sig: u32,
        skip: u32,
        /// For method calls: the method item and how many references the
        /// receiver was looked through.
        method: Option<ItemId>,
        deref: u32,
    },
    /// A function-typed value: positional parameters only.
    FnTy { ty: TypeId, skip: u32 },
    /// Nothing to check (already reported, or an `{error}` callee).
    Silent,
}

impl Ctx<'_> {
    // ----------------------------------------------------------- targets

    /// Decides what a call's callee is, once the callee is checked.
    pub(crate) fn call_target(
        &mut self,
        call: ExprId,
        callee: ExprId,
    ) -> Result<CallTarget, CheckError> {
        if let Some(item) = self.callee_fn(callee) {
            if let Some(sig) = self.sig(item)? {
                return Ok(CallTarget::Sig {
                    sig: u32::try_from(sig).unwrap_or(u32::MAX),
                    skip: 0,
                    method: None,
                    deref: 0,
                });
            }
        }
        let t = self.resolve(self.child(callee));
        Ok(match self.tag(t) {
            Tag::Fn => CallTarget::FnTy { ty: t, skip: 0 },
            Tag::Error | Tag::Never => CallTarget::Silent,
            Tag::Any => {
                self.report(NodeRef::Expr(callee), DiagnosticKind::DynamicOperation);
                CallTarget::Silent
            }
            Tag::Var if self.infer.class_of(t) == GENERAL => {
                // A callee of unknown type: it is a function of these
                // arguments.
                let n = match *self.hir.expr(call) {
                    Expr::Call { args, .. } => args.len(),
                    _ => 0,
                };
                let params: alloc::vec::Vec<TypeId> = (0..n).map(|_| self.fresh(GENERAL)).collect();
                let ret = self.fresh(GENERAL);
                let f = self.types.func(&params, ret, Effects::NONE);
                let _ = self.unify(t, f)?;
                CallTarget::FnTy { ty: f, skip: 0 }
            }
            _ => {
                self.report(NodeRef::Expr(callee), DiagnosticKind::NotCallable { ty: t });
                self.poison(callee);
                CallTarget::Silent
            }
        })
    }

    /// The function item a callee path names, recorded when the path was
    /// checked.
    fn callee_fn(&self, callee: ExprId) -> Option<ItemId> {
        self.callee_fns
            .get(callee.index())
            .copied()
            .filter(|&v| v != crate::typed::NONE)
            .and_then(|v| ItemId::from_index(v as usize))
    }

    /// Looks up the method of a method call on the receiver's type, through
    /// references, then a function-typed field of the same name.
    pub(crate) fn method_target(&mut self, call: ExprId) -> Result<CallTarget, CheckError> {
        let Expr::MethodCall {
            receiver,
            method,
            generic_args,
            ..
        } = *self.hir.expr(call)
        else {
            return Ok(CallTarget::Silent);
        };
        let at = NodeRef::Expr(call);
        if !generic_args.is_empty() {
            self.report(
                at,
                DiagnosticKind::Unsupported {
                    feature: crate::diag::Feature::Generics,
                },
            );
            return Ok(CallTarget::Silent);
        }
        let recv = self.settle_literal(self.child(receiver))?;
        match self.tag(recv) {
            // An unknown receiver: `CannotInfer` reports the cause.
            Tag::Error | Tag::Never | Tag::Var => return Ok(CallTarget::Silent),
            Tag::Any => {
                self.report(at, DiagnosticKind::DynamicOperation);
                return Ok(CallTarget::Silent);
            }
            Tag::Nullable => {
                self.report(
                    NodeRef::Expr(receiver),
                    DiagnosticKind::NullableAccess { ty: recv },
                );
                self.poison(receiver);
                return Ok(CallTarget::Silent);
            }
            _ => {}
        }
        let mut t = recv;
        let mut deref = 0u32;
        let mut incomplete = false;
        loop {
            self.meter.tick(1)?;
            match self.member_lookup(t, method.sym)? {
                Lookup::Found(MemberRef::Item(m)) => {
                    self.methods.push((call, m));
                    return self.method_item_target(m, deref, at, t, method.sym);
                }
                Lookup::Found(MemberRef::Host(ty)) => {
                    return Ok(if self.tag(ty) == Tag::Fn {
                        CallTarget::FnTy { ty, skip: 1 }
                    } else {
                        self.report(at, DiagnosticKind::NotCallable { ty });
                        CallTarget::Silent
                    });
                }
                Lookup::Ambiguous => {
                    self.report(
                        at,
                        DiagnosticKind::AmbiguousMethod {
                            ty: t,
                            name: method.sym,
                        },
                    );
                    return Ok(CallTarget::Silent);
                }
                Lookup::NotFound { incomplete: inc } => incomplete |= inc,
            }
            match self.types.get(self.resolve(t)) {
                Type::Ref { inner, .. } => {
                    t = self.resolve(inner);
                    deref += 1;
                }
                _ => break,
            }
        }
        // A field holding a function: `obj.callback(x)`.
        if let Some(field_ty) = self.field_of(recv, Member::Named(method.sym))? {
            let f = self.resolve(field_ty);
            if self.tag(f) == Tag::Fn {
                return Ok(CallTarget::FnTy { ty: f, skip: 0 });
            }
        }
        if !incomplete {
            self.report(
                at,
                DiagnosticKind::NoMethod {
                    ty: recv,
                    name: method.sym,
                },
            );
        }
        Ok(CallTarget::Silent)
    }

    fn method_item_target(
        &mut self,
        m: ItemId,
        deref: u32,
        at: NodeRef,
        owner: TypeId,
        name: Symbol,
    ) -> Result<CallTarget, CheckError> {
        if self.idx.is_generic(m) {
            return Ok(CallTarget::Silent);
        }
        let Some(sig) = self.sig(m)? else {
            // A constant or global member called as a method.
            let t = self.decl_type(m)?;
            return Ok(if self.tag(t) == Tag::Fn {
                CallTarget::FnTy {
                    ty: self.resolve(t),
                    skip: 0,
                }
            } else {
                self.report(at, DiagnosticKind::NotCallable { ty: t });
                CallTarget::Silent
            });
        };
        let has_receiver = self
            .sig_arena
            .get(sig)
            .and_then(|s| s.params.first())
            .is_some_and(|p| p.kind == ParamKind::Receiver);
        if !has_receiver {
            // An associated function is called through its path, not on a
            // value.
            self.report(at, DiagnosticKind::NoMethod { ty: owner, name });
            return Ok(CallTarget::Silent);
        }
        Ok(CallTarget::Sig {
            sig: u32::try_from(sig).unwrap_or(u32::MAX),
            skip: 1,
            method: Some(m),
            deref,
        })
    }

    /// Checks a method call's receiver against the method's receiver
    /// parameter, borrowing or dereferencing it automatically.
    pub(crate) fn check_receiver(
        &mut self,
        receiver: ExprId,
        target: CallTarget,
    ) -> Result<(), CheckError> {
        let CallTarget::Sig { sig, deref, .. } = target else {
            return Ok(());
        };
        let Some(param) = self.param_at(target, 0) else {
            return Ok(());
        };
        let _ = sig;
        let found = self.child(receiver);
        let want = self.resolve(param.ty);
        match self.coerce(found, want)? {
            super::coerce::Fit::Same => return Ok(()),
            super::coerce::Fit::Converted(c) => {
                self.coercions.push((receiver, c, want));
                return Ok(());
            }
            super::coerce::Fit::No => {}
        }
        // Peel the references the lookup looked through.
        let mut base = self.resolve(found);
        for _ in 0..deref {
            if let Type::Ref { inner, .. } = self.types.get(base) {
                base = self.resolve(inner);
            }
        }
        if let Type::Ref { inner, .. } = self.types.get(want) {
            if self.coerce(base, inner)? != super::coerce::Fit::No {
                self.coercions.push((receiver, Coercion::AutoRef, want));
                return Ok(());
            }
        }
        if deref > 0 && self.coerce(base, want)? != super::coerce::Fit::No {
            self.coercions.push((receiver, Coercion::AutoDeref, want));
            return Ok(());
        }
        // Methods found on a base class take the subclass receiver.
        if let (Type::Adt(sub), Type::Adt(sup)) = (self.types.get(base), self.types.get(want)) {
            if self.is_subclass(sub, sup)? {
                self.coercions.push((receiver, Coercion::Subclass, want));
                return Ok(());
            }
        }
        self.report(
            NodeRef::Expr(receiver),
            DiagnosticKind::Mismatch {
                expected: want,
                found,
            },
        );
        self.poison(receiver);
        Ok(())
    }

    // ------------------------------------------------------- parameters

    fn param_count(&self, target: CallTarget) -> usize {
        match target {
            CallTarget::Sig { sig, .. } => self
                .sig_arena
                .get(sig as usize)
                .map_or(0, |s| s.params.len()),
            CallTarget::FnTy { ty, .. } => {
                let n = self.types.node(ty);
                self.types.kids_of(&n).len()
            }
            CallTarget::Silent => 0,
        }
    }

    fn param_at(&self, target: CallTarget, i: usize) -> Option<ParamInfo> {
        match target {
            CallTarget::Sig { sig, .. } => self.sig_arena.get(sig as usize)?.params.get(i).copied(),
            CallTarget::FnTy { ty, .. } => {
                let n = self.types.node(ty);
                let t = *self.types.kids_of(&n).get(i)?;
                Some(ParamInfo {
                    kind: ParamKind::PositionalOnly,
                    name: None,
                    ty: t,
                    has_default: false,
                    by_ref: false,
                })
            }
            CallTarget::Silent => None,
        }
    }

    fn param_named(&self, target: CallTarget, name: Symbol) -> Option<usize> {
        match target {
            CallTarget::Sig { sig, .. } => self.sig_arena.get(sig as usize)?.param_named(name),
            _ => None,
        }
    }

    fn skip_of(target: CallTarget) -> usize {
        match target {
            CallTarget::Sig { skip, .. } | CallTarget::FnTy { skip, .. } => skip as usize,
            CallTarget::Silent => 0,
        }
    }

    /// What the call evaluates to.
    pub(crate) fn call_result_of(&mut self, target: CallTarget) -> TypeId {
        match target {
            CallTarget::Sig { sig, .. } => match self.sig_arena.get(sig as usize) {
                Some(s) => {
                    let (ret, effects) = (s.ret, s.effects);
                    self.call_result(ret, effects)
                }
                None => TypeId::ERROR,
            },
            CallTarget::FnTy { ty, .. } => match self.types.get(ty) {
                Type::Fn { ret, effects, .. } => self.call_result(ret, effects),
                _ => TypeId::ERROR,
            },
            CallTarget::Silent => TypeId::ERROR,
        }
    }

    // ---------------------------------------------------------- matching

    /// Matches `args` to the target's parameters. `finish == false`: only set
    /// the expected type of each argument before the first spread.
    /// `finish == true`: report arity and naming problems at `call`, and
    /// coerce the arguments that had no expectation.
    pub(crate) fn match_args(
        &mut self,
        call: ExprId,
        target: CallTarget,
        args: hir_lang::List<Arg>,
        finish: bool,
    ) -> Result<(), CheckError> {
        if target == CallTarget::Silent {
            return Ok(());
        }
        let n = self.param_count(target);
        let skip = Self::skip_of(target);
        let mut filled = core::mem::take(&mut self.filled);
        filled.clear();
        filled.resize(n, false);
        let mut rest = None;
        let mut rest_named = None;
        let (mut min, mut max) = (0u32, 0u32);
        let mut seen_pos = 0usize;
        for i in 0..n {
            let Some(p) = self.param_at(target, i) else {
                break;
            };
            match p.kind {
                ParamKind::Receiver | ParamKind::PositionalOnly | ParamKind::Normal => {
                    if seen_pos < skip {
                        if let Some(f) = filled.get_mut(i) {
                            *f = true;
                        }
                    } else {
                        max += 1;
                        if !p.has_default {
                            min += 1;
                        }
                    }
                    seen_pos += 1;
                }
                ParamKind::Rest => rest = Some(i),
                ParamKind::RestNamed => rest_named = Some(i),
                ParamKind::NamedOnly => {}
            }
        }
        let mut cursor = 0usize;
        let mut positional = 0u32;
        let mut too_many = false;
        let mut after_spread = false;
        let hir = self.hir;
        for arg in hir.list(args) {
            self.meter.tick(1)?;
            match arg.kind {
                ArgKind::Positional => {
                    positional = positional.saturating_add(1);
                    match self.next_positional(target, &filled, &mut cursor) {
                        Some(i) => {
                            if let Some(f) = filled.get_mut(i) {
                                *f = true;
                            }
                            self.arg_to(arg, target, i, after_spread, finish)?;
                        }
                        None => match rest {
                            Some(r) => self.arg_to(arg, target, r, after_spread, finish)?,
                            None => too_many = true,
                        },
                    }
                }
                ArgKind::Named(id) => match self.param_named(target, id.sym) {
                    Some(i) if filled.get(i).copied().unwrap_or(false) => {
                        if finish {
                            self.report(
                                NodeRef::Expr(arg.value),
                                DiagnosticKind::DuplicateArg { name: Some(id.sym) },
                            );
                        }
                    }
                    Some(i) => {
                        if let Some(f) = filled.get_mut(i) {
                            *f = true;
                        }
                        self.arg_to(arg, target, i, after_spread, finish)?;
                    }
                    None => match rest_named {
                        Some(r) => self.arg_to(arg, target, r, after_spread, finish)?,
                        None => {
                            if finish {
                                self.report(
                                    NodeRef::Expr(arg.value),
                                    DiagnosticKind::UnknownNamedArg { name: id.sym },
                                );
                            }
                        }
                    },
                },
                ArgKind::Spread | ArgKind::SpreadNamed => {
                    after_spread = true;
                    if !finish {
                        break;
                    }
                    if arg.kind == ArgKind::Spread {
                        let more = self.spread_positional(
                            arg.value,
                            target,
                            &mut filled,
                            &mut cursor,
                            rest,
                            &mut too_many,
                        )?;
                        positional = positional.saturating_add(more);
                    } else {
                        self.spread_named(arg.value, target, &mut filled, rest_named)?;
                    }
                }
            }
        }
        if finish {
            if too_many {
                self.report(
                    NodeRef::Expr(call),
                    DiagnosticKind::Arity {
                        min,
                        max: rest.is_none().then_some(max),
                        found: positional,
                    },
                );
            } else {
                let mut missing = 0u32;
                let mut first = None;
                for i in 0..n {
                    let Some(p) = self.param_at(target, i) else {
                        break;
                    };
                    let open = !filled.get(i).copied().unwrap_or(true)
                        && !p.has_default
                        && !matches!(p.kind, ParamKind::Rest | ParamKind::RestNamed);
                    if open {
                        missing += 1;
                        if first.is_none() {
                            first = Some(p.name);
                        }
                    }
                }
                if missing > 0 {
                    self.report(
                        NodeRef::Expr(call),
                        DiagnosticKind::MissingArg {
                            name: first.flatten(),
                            count: missing,
                        },
                    );
                }
            }
        }
        self.filled = filled;
        Ok(())
    }

    fn next_positional(
        &self,
        target: CallTarget,
        filled: &[bool],
        cursor: &mut usize,
    ) -> Option<usize> {
        while let Some(p) = self.param_at(target, *cursor) {
            let i = *cursor;
            *cursor += 1;
            let positional = matches!(
                p.kind,
                ParamKind::Receiver | ParamKind::PositionalOnly | ParamKind::Normal
            );
            if positional && !filled.get(i).copied().unwrap_or(true) {
                return Some(i);
            }
        }
        None
    }

    /// One argument meets parameter `i`.
    fn arg_to(
        &mut self,
        arg: &Arg,
        target: CallTarget,
        i: usize,
        after_spread: bool,
        finish: bool,
    ) -> Result<(), CheckError> {
        let Some(p) = self.param_at(target, i) else {
            return Ok(());
        };
        if !finish {
            self.set_expect(arg.value, p.ty);
            return Ok(());
        }
        if after_spread {
            let found = self.child(arg.value);
            let _ = self.coerce_expr(arg.value, found, p.ty)?;
        }
        if p.by_ref && !arg.place {
            self.report(NodeRef::Expr(arg.value), DiagnosticKind::ByRefNeedsPlace);
        }
        Ok(())
    }

    /// A positional spread (`f(...xs)`). Returns how many positional values
    /// it is known to supply.
    fn spread_positional(
        &mut self,
        value: ExprId,
        target: CallTarget,
        filled: &mut [bool],
        cursor: &mut usize,
        rest: Option<usize>,
        too_many: &mut bool,
    ) -> Result<u32, CheckError> {
        let t = self.resolve(self.child(value));
        let at = NodeRef::Expr(value);
        match self.types.get(t) {
            Type::Tuple(elems) => {
                let elems = elems.to_vec();
                for &e in &elems {
                    self.spread_one(value, e, target, filled, cursor, rest, too_many)?;
                }
                Ok(u32::try_from(elems.len()).unwrap_or(u32::MAX))
            }
            Type::Array { elem, len } => {
                let mut k = 0u64;
                while k < len {
                    self.meter.tick(1)?;
                    let before = *cursor;
                    let Some(i) = self.next_positional(target, filled, cursor) else {
                        *cursor = before;
                        break;
                    };
                    if let Some(f) = filled.get_mut(i) {
                        *f = true;
                    }
                    self.spread_coerce(value, elem, target, i)?;
                    k += 1;
                }
                if k < len {
                    match rest {
                        Some(r) => self.spread_coerce(value, elem, target, r)?,
                        None => *too_many = true,
                    }
                }
                Ok(u32::try_from(len).unwrap_or(u32::MAX))
            }
            Type::Slice(elem) => {
                // A length known only at run time: it may fill every
                // remaining positional parameter and the rest.
                while let Some(i) = self.next_positional(target, filled, cursor) {
                    self.meter.tick(1)?;
                    if let Some(f) = filled.get_mut(i) {
                        *f = true;
                    }
                    self.spread_coerce(value, elem, target, i)?;
                }
                if let Some(r) = rest {
                    self.spread_coerce(value, elem, target, r)?;
                }
                Ok(0)
            }
            Type::Error | Type::Never => {
                filled.iter_mut().for_each(|f| *f = true);
                Ok(0)
            }
            Type::Any => {
                self.report(at, DiagnosticKind::DynamicOperation);
                filled.iter_mut().for_each(|f| *f = true);
                Ok(0)
            }
            _ => {
                let v = self.fresh(GENERAL);
                let expected = self.types.slice(v);
                self.report(at, DiagnosticKind::Mismatch { expected, found: t });
                filled.iter_mut().for_each(|f| *f = true);
                Ok(0)
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn spread_one(
        &mut self,
        value: ExprId,
        elem: TypeId,
        target: CallTarget,
        filled: &mut [bool],
        cursor: &mut usize,
        rest: Option<usize>,
        too_many: &mut bool,
    ) -> Result<(), CheckError> {
        match self.next_positional(target, filled, cursor) {
            Some(i) => {
                if let Some(f) = filled.get_mut(i) {
                    *f = true;
                }
                self.spread_coerce(value, elem, target, i)
            }
            None => match rest {
                Some(r) => self.spread_coerce(value, elem, target, r),
                None => {
                    *too_many = true;
                    Ok(())
                }
            },
        }
    }

    /// One spread element meets parameter `i`; a mismatch is reported at the
    /// spread argument.
    fn spread_coerce(
        &mut self,
        value: ExprId,
        elem: TypeId,
        target: CallTarget,
        i: usize,
    ) -> Result<(), CheckError> {
        let Some(p) = self.param_at(target, i) else {
            return Ok(());
        };
        if self.coerce(elem, p.ty)? == super::coerce::Fit::No {
            self.report(
                NodeRef::Expr(value),
                DiagnosticKind::Mismatch {
                    expected: p.ty,
                    found: elem,
                },
            );
            self.poison(value);
        }
        Ok(())
    }

    /// A named spread (`f(**kw)`): a string-keyed map that may supply any
    /// named parameter.
    fn spread_named(
        &mut self,
        value: ExprId,
        target: CallTarget,
        filled: &mut [bool],
        rest_named: Option<usize>,
    ) -> Result<(), CheckError> {
        let t = self.resolve(self.child(value));
        let named = |p: &ParamInfo| matches!(p.kind, ParamKind::Normal | ParamKind::NamedOnly);
        match self.types.get(t) {
            Type::Map { key, value: v } => {
                let str_ty = TypeId::prim(hir_lang::Prim::Str);
                if !self.unify(key, str_ty)? {
                    let expected = self.types.map(str_ty, v);
                    self.report(
                        NodeRef::Expr(value),
                        DiagnosticKind::Mismatch { expected, found: t },
                    );
                    return Ok(());
                }
                for i in 0..filled.len() {
                    let Some(p) = self.param_at(target, i) else {
                        break;
                    };
                    if named(&p) && !filled.get(i).copied().unwrap_or(true) {
                        if let Some(f) = filled.get_mut(i) {
                            *f = true;
                        }
                        self.spread_coerce(value, v, target, i)?;
                    }
                }
                if let Some(r) = rest_named {
                    self.spread_coerce(value, v, target, r)?;
                }
            }
            Type::Error | Type::Never => filled.iter_mut().for_each(|f| *f = true),
            Type::Any => {
                self.report(NodeRef::Expr(value), DiagnosticKind::DynamicOperation);
                filled.iter_mut().for_each(|f| *f = true);
            }
            _ => {
                let v = self.fresh(GENERAL);
                let expected = self.types.map(TypeId::prim(hir_lang::Prim::Str), v);
                self.report(
                    NodeRef::Expr(value),
                    DiagnosticKind::Mismatch { expected, found: t },
                );
                filled.iter_mut().for_each(|f| *f = true);
            }
        }
        Ok(())
    }

    /// Resolves `t`; an unresolved literal variable takes its default type
    /// now (members are looked up on the default, as `5.abs()` on `i64`).
    pub(crate) fn settle_literal(&mut self, t: TypeId) -> Result<TypeId, CheckError> {
        let r = self.resolve(t);
        if self.tag(r) == Tag::Var {
            let default = match self.infer.class_of(r) {
                crate::infer::INT => self.profile.default_int,
                crate::infer::FLOAT => self.profile.default_float,
                _ => return Ok(r),
            };
            let _ = self.unify(r, TypeId::prim(default))?;
        }
        Ok(self.resolve(r))
    }

    // -------------------------------------------------------------- fields

    /// The type of member `m` of a value of type `base`, looking through
    /// references and base classes. `None` if there is no such field.
    pub(crate) fn field_of(
        &mut self,
        base: TypeId,
        m: Member,
    ) -> Result<Option<TypeId>, CheckError> {
        let mut t = self.resolve(base);
        loop {
            self.meter.tick(1)?;
            match self.types.get(t) {
                Type::Ref { inner, .. } => t = self.resolve(inner),
                Type::Tuple(elems) => {
                    return Ok(match m {
                        Member::Index(i) => elems.get(i as usize).copied(),
                        Member::Named(_) => None,
                    });
                }
                Type::Record(fields) => {
                    return Ok(match m {
                        Member::Named(s) => fields.iter().find(|f| f.name == s).map(|f| f.ty),
                        Member::Index(_) => None,
                    });
                }
                Type::Adt(item) => return self.adt_field(item, m),
                _ => return Ok(None),
            }
        }
    }

    fn adt_field(&mut self, item: ItemId, m: Member) -> Result<Option<TypeId>, CheckError> {
        self.new_visit();
        let mut queue = alloc::vec![item];
        let mut qi = 0;
        while let Some(&c) = queue.get(qi) {
            qi += 1;
            self.meter.tick(1)?;
            if !self.visit(c) {
                continue;
            }
            let raw = u32::try_from(c.index()).unwrap_or(u32::MAX);
            let field = match (self.item_kind(c), m) {
                (ItemKind::Record(_) | ItemKind::Class(_), Member::Named(s)) => self
                    .idx
                    .field_named(super::index::FieldOwner::Item(raw), s)
                    .map(|(_, f)| f),
                (ItemKind::Record(def), Member::Index(i))
                    if def.shape == hir_lang::Shape::Tuple =>
                {
                    self.hir.list(def.fields).get(i as usize).copied()
                }
                _ => None,
            };
            if let Some(f) = field {
                return Ok(Some(self.field_type(f)?));
            }
            queue.extend(self.idx.bases_of(c).iter().copied());
        }
        Ok(None)
    }

    /// Whether member lookups on `t` may be missing members (a class with
    /// mixins, a type extended by generic impls).
    pub(crate) fn members_incomplete(&mut self, t: TypeId) -> bool {
        let Type::Adt(item) = self.types.get(self.resolve(t)) else {
            return false;
        };
        self.new_visit();
        let mut stack = alloc::vec![item];
        while let Some(c) = stack.pop() {
            if !self.visit(c) {
                continue;
            }
            if self.idx.is_incomplete(c) {
                return true;
            }
            stack.extend(self.idx.bases_of(c).iter().copied());
        }
        false
    }
}

/// The outcome of a member lookup.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Lookup {
    Found(MemberRef),
    Ambiguous,
    NotFound { incomplete: bool },
}
