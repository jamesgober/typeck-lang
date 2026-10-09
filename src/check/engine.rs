//! The iterative expression and statement checker (static profiles).
//!
//! Checking is a loop over an explicit task stack: entering an expression
//! schedules its children and an exit task; the exit reads the children's
//! recorded types and computes the expression's. Steps that need a child's
//! type before the next child is checked (a call's callee before its
//! arguments, a `let` initializer before its pattern) are tasks of their
//! own. Nesting depth never touches the call stack.
//!
//! Every expression ends in [`Ctx::finish`], which records its type and, if
//! the parent set an expected type, coerces to it and reports a mismatch at
//! this expression. A reported expression is *poisoned*: its parent reads
//! it as `{error}`, so one mistake produces one diagnostic.

use alloc::vec::Vec;

use hir_lang::{
    Arm, AsmDir, AsmOptions, BinderId, Block, Closure, Expr, ExprId, Intrinsic, ItemKind, MapEntry,
    NodeRef, ParamKind, Prim, Stmt, StmtId,
};

use super::{
    Ctx, Frame, Target,
    call::CallTarget,
    index::FieldOwner,
    paths::{RecordRef, ValueRef},
};
use crate::{
    diag::DiagnosticKind,
    error::CheckError,
    infer::{GENERAL, INT},
    typed::NONE,
    types::{Tag, Type, TypeId},
};

/// One unit of checking work.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Task {
    Expr(ExprId),
    Exit(ExprId),
    Stmt(StmtId),
    /// A `let` or `static` after its initializer: type the pattern.
    LetInit(StmtId),
    CallPrep(ExprId),
    MethodPrep(ExprId),
    AssignPrep(ExprId),
    /// Arm `i` of a `match` (or catch `i` of a `try`) after the scrutinee.
    ArmPat(ExprId, u32),
    /// A `let_place` after its place: bind the alias.
    PlaceBind(ExprId),
}

impl Ctx<'_> {
    /// Checks `root` and everything under it.
    pub(crate) fn run(&mut self, root: ExprId) -> Result<(), CheckError> {
        // One task buffer serves every root of the check.
        let mut tasks = core::mem::take(&mut self.tasks);
        tasks.clear();
        tasks.push(Task::Expr(root));
        let result = self.drain(&mut tasks);
        self.tasks = tasks;
        result
    }

    fn drain(&mut self, tasks: &mut Vec<Task>) -> Result<(), CheckError> {
        while let Some(task) = tasks.pop() {
            self.meter.tick(1)?;
            match task {
                Task::Expr(e) => self.enter(e, tasks)?,
                Task::Exit(e) => self.exit(e)?,
                Task::Stmt(s) => self.stmt(s, tasks)?,
                Task::LetInit(s) => self.let_init(s)?,
                Task::CallPrep(e) => self.call_prep(e)?,
                Task::MethodPrep(e) => self.method_prep(e)?,
                Task::AssignPrep(e) => self.assign_prep(e)?,
                Task::ArmPat(e, i) => self.arm_pat(e, i)?,
                Task::PlaceBind(e) => self.place_bind(e),
            }
            crate::infer::Infer::check_size(&self.types, &self.meter)?;
        }
        Ok(())
    }

    /// Records `e`'s type and coerces it to its expected type, if any.
    pub(crate) fn finish(&mut self, e: ExprId, ty: TypeId) -> Result<(), CheckError> {
        if let Some(slot) = self.expr_ty.get_mut(e.index()) {
            *slot = ty.raw();
        }
        if let Some(expected) = self.take_expect(e) {
            let _ = self.coerce_expr(e, ty, expected)?;
        }
        Ok(())
    }

    fn expected_elem(&self, e: ExprId) -> Option<TypeId> {
        let t = self.resolve(self.peek_expect(e)?);
        match self.types.get(t) {
            Type::Array { elem, .. } | Type::Slice(elem) => Some(elem),
            _ => None,
        }
    }

    // --------------------------------------------------------------- enter

    fn enter(&mut self, e: ExprId, tasks: &mut Vec<Task>) -> Result<(), CheckError> {
        let hir = self.hir;
        let expr = *hir.expr(e);
        let push_exprs = |tasks: &mut Vec<Task>, list: &[ExprId]| {
            tasks.extend(list.iter().rev().map(|&c| Task::Expr(c)));
        };
        match expr {
            Expr::Lit(lit) => {
                let t = self.lit_type(NodeRef::Expr(e), lit);
                self.finish(e, t)?;
            }
            Expr::Path(p) => {
                let r = self.value_path(p, NodeRef::Expr(e))?;
                if let ValueRef::Fn { sig, .. } = r {
                    if let Some(slot) = self.callee_sigs.get_mut(e.index()) {
                        *slot = sig;
                    }
                }
                let t = self.value_type(r)?;
                self.finish(e, t)?;
            }
            Expr::Err => self.finish(e, TypeId::ERROR)?,
            Expr::Continue { .. } => self.finish(e, TypeId::NEVER)?,
            Expr::Tuple(list) => {
                let elems = hir.list(list);
                if let Some(exp) = self.peek_expect(e) {
                    if let Type::Tuple(ts) = self.types.get(self.resolve(exp)) {
                        if ts.len() == elems.len() {
                            let ts = ts.to_vec();
                            for (&c, t) in elems.iter().zip(ts) {
                                self.set_expect(c, t);
                            }
                        }
                    }
                }
                tasks.push(Task::Exit(e));
                push_exprs(tasks, elems);
            }
            Expr::Array(list) => {
                let elems = hir.list(list);
                if let Some(elem) = self.expected_elem(e) {
                    for &c in elems {
                        self.set_expect(c, elem);
                    }
                }
                tasks.push(Task::Exit(e));
                push_exprs(tasks, elems);
            }
            Expr::Repeat { elem, count } => {
                if let Some(t) = self.expected_elem(e) {
                    self.set_expect(elem, t);
                }
                let any_int = self.fresh(INT);
                self.set_expect(count, any_int);
                tasks.push(Task::Exit(e));
                tasks.push(Task::Expr(count));
                tasks.push(Task::Expr(elem));
            }
            Expr::Record { path, fields, base } => {
                if let Some(p) = path {
                    if let Some(target) = self.record_ref(p, NodeRef::Expr(e))? {
                        let adt = self.record_ref_type(target, Some(p));
                        // Checking mode: an expected instance fixes the
                        // arguments before the fields are checked.
                        if let Some(exp) = self.peek_expect(e) {
                            let snap = self.infer.snapshot();
                            if self.unify(adt, exp)? {
                                self.infer.commit();
                            } else {
                                self.infer.rollback(snap);
                            }
                        }
                        self.record_targets.push((e, target, adt));
                        let owner = field_owner(target);
                        for fi in hir.list(fields) {
                            if let Some((_, f)) = self.idx.field_named(owner, fi.name.sym) {
                                let ft = self.field_type_in(f, adt)?;
                                self.set_expect(fi.value, ft);
                            }
                        }
                        if let Some(b) = base {
                            self.set_expect(b, adt);
                        }
                    }
                }
                tasks.push(Task::Exit(e));
                tasks.extend(base.map(Task::Expr));
                tasks.extend(hir.list(fields).iter().rev().map(|f| Task::Expr(f.value)));
            }
            Expr::Map(entries) => {
                tasks.push(Task::Exit(e));
                for entry in hir.list(entries).iter().rev() {
                    tasks.push(Task::Expr(entry.value));
                    tasks.extend(entry.key.map(Task::Expr));
                }
            }
            Expr::Call { callee, args } => {
                tasks.push(Task::Exit(e));
                tasks.extend(hir.list(args).iter().rev().map(|a| Task::Expr(a.value)));
                tasks.push(Task::CallPrep(e));
                tasks.push(Task::Expr(callee));
            }
            Expr::MethodCall { receiver, args, .. } => {
                tasks.push(Task::Exit(e));
                tasks.extend(hir.list(args).iter().rev().map(|a| Task::Expr(a.value)));
                tasks.push(Task::MethodPrep(e));
                tasks.push(Task::Expr(receiver));
            }
            Expr::DynMethodCall {
                receiver,
                name,
                args,
            } => {
                tasks.push(Task::Exit(e));
                tasks.extend(hir.list(args).iter().rev().map(|a| Task::Expr(a.value)));
                tasks.push(Task::Expr(name));
                tasks.push(Task::Expr(receiver));
            }
            Expr::Field { base, .. }
            | Expr::VarVar(base)
            | Expr::Append(base)
            | Expr::Deref(base)
            | Expr::Await(base)
            | Expr::Spawn(base)
            | Expr::Borrow { expr: base, .. }
            | Expr::Cast { expr: base, .. } => {
                tasks.push(Task::Exit(e));
                tasks.push(Task::Expr(base));
            }
            Expr::Throw(value) => {
                if let Some(t) = self.frames.last().and_then(|f| f.throws) {
                    self.set_expect(value, t);
                }
                tasks.push(Task::Exit(e));
                tasks.push(Task::Expr(value));
            }
            Expr::DynField { base, name } | Expr::Index { base, index: name } => {
                tasks.push(Task::Exit(e));
                tasks.push(Task::Expr(name));
                tasks.push(Task::Expr(base));
            }
            Expr::RefAssign { target, source } => {
                tasks.push(Task::Exit(e));
                tasks.push(Task::Expr(source));
                tasks.push(Task::Expr(target));
            }
            Expr::Op { args, .. } | Expr::Intrinsic { args, .. } => {
                tasks.push(Task::Exit(e));
                push_exprs(tasks, hir.list(args));
            }
            Expr::Assign { target, value, .. } => {
                tasks.push(Task::Exit(e));
                tasks.push(Task::Expr(value));
                tasks.push(Task::AssignPrep(e));
                tasks.push(Task::Expr(target));
            }
            Expr::Block(b) => self.enter_block(e, b, tasks),
            Expr::If { cond, then, else_ } => {
                self.set_expect(cond, TypeId::prim(Prim::Bool));
                if let Some(other) = else_ {
                    if let Some(exp) = self.delegate(e) {
                        self.set_expect(then, exp);
                        self.set_expect(other, exp);
                    }
                } else {
                    // Without `else`, the value is unit either way.
                    self.set_expect(then, TypeId::UNIT);
                }
                tasks.push(Task::Exit(e));
                tasks.extend(else_.map(Task::Expr));
                tasks.push(Task::Expr(then));
                tasks.push(Task::Expr(cond));
            }
            Expr::Match { scrutinee, arms } => {
                self.enter_arms(e, hir.list(arms), tasks);
                tasks.push(Task::Expr(scrutinee));
            }
            Expr::Try {
                body,
                catches,
                finally,
            } => {
                if let Some(exp) = self.delegate(e) {
                    self.set_expect(body, exp);
                    for arm in hir.list(catches) {
                        self.set_expect(arm.body, exp);
                    }
                }
                tasks.push(Task::Exit(e));
                tasks.extend(finally.map(Task::Expr));
                self.enter_arms_no_exit(e, hir.list(catches), tasks);
                tasks.push(Task::Expr(body));
            }
            Expr::Loop { label, body, step } => {
                self.push_target(label, true);
                tasks.push(Task::Exit(e));
                tasks.extend(step.map(Task::Expr));
                tasks.push(Task::Expr(body));
            }
            Expr::Break { value, .. } => {
                tasks.push(Task::Exit(e));
                tasks.extend(value.map(Task::Expr));
            }
            Expr::Return(value) => {
                if let (Some(v), Some(frame)) = (value, self.frames.last().copied()) {
                    let want = if frame.yields.is_some() {
                        TypeId::UNIT
                    } else {
                        frame.ret
                    };
                    self.set_expect(v, want);
                }
                tasks.push(Task::Exit(e));
                tasks.extend(value.map(Task::Expr));
            }
            Expr::Yield { key, value } => {
                if let (Some(v), Some(y)) = (value, self.frames.last().and_then(|f| f.yields)) {
                    self.set_expect(v, y);
                }
                tasks.push(Task::Exit(e));
                tasks.extend(value.map(Task::Expr));
                tasks.extend(key.map(Task::Expr));
            }
            Expr::YieldFrom(inner) => {
                tasks.push(Task::Exit(e));
                tasks.push(Task::Expr(inner));
            }
            Expr::LetPlace { place, body, .. } => {
                if let Some(exp) = self.delegate(e) {
                    self.set_expect(body, exp);
                }
                tasks.push(Task::Exit(e));
                tasks.push(Task::Expr(body));
                tasks.push(Task::PlaceBind(e));
                tasks.push(Task::Expr(place));
            }
            Expr::Closure(c) => self.enter_closure(e, c, tasks)?,
            Expr::Asm(asm) => {
                tasks.push(Task::Exit(e));
                tasks.extend(
                    hir.list(asm.operands)
                        .iter()
                        .rev()
                        .map(|o| Task::Expr(o.expr)),
                );
            }
        }
        Ok(())
    }

    fn enter_block(&mut self, e: ExprId, b: Block, tasks: &mut Vec<Task>) {
        if b.label.is_some() {
            self.push_target(b.label, false);
        } else if let Some(tail) = b.tail {
            // The block's value is its tail's: let the tail meet the
            // expectation directly, so a mismatch is reported there.
            if let Some(exp) = self.delegate(e) {
                self.set_expect(tail, exp);
            }
        }
        tasks.push(Task::Exit(e));
        tasks.extend(b.tail.map(Task::Expr));
        tasks.extend(self.hir.list(b.stmts).iter().rev().map(|&s| Task::Stmt(s)));
    }

    fn enter_arms(&mut self, e: ExprId, arms: &[Arm], tasks: &mut Vec<Task>) {
        if let Some(exp) = self.delegate(e) {
            for arm in arms {
                self.set_expect(arm.body, exp);
            }
        }
        tasks.push(Task::Exit(e));
        self.enter_arms_no_exit(e, arms, tasks);
    }

    fn enter_arms_no_exit(&mut self, e: ExprId, arms: &[Arm], tasks: &mut Vec<Task>) {
        for (i, arm) in arms.iter().enumerate().rev() {
            tasks.push(Task::Expr(arm.body));
            if let Some(g) = arm.guard {
                self.set_expect(g, TypeId::prim(Prim::Bool));
                tasks.push(Task::Expr(g));
            }
            tasks.push(Task::ArmPat(e, u32::try_from(i).unwrap_or(u32::MAX)));
        }
    }

    /// Moves `e`'s expectation onto its branches: they meet it themselves,
    /// so a mismatch is reported in the branch, and `e` has the expected
    /// type.
    fn delegate(&mut self, e: ExprId) -> Option<TypeId> {
        let exp = self.take_expect(e)?;
        self.delegated.push((e, exp));
        Some(exp)
    }

    fn was_delegated(&mut self, e: ExprId) -> Option<TypeId> {
        match self.delegated.last() {
            Some(&(d, t)) if d == e => {
                let _ = self.delegated.pop();
                Some(t)
            }
            _ => None,
        }
    }

    /// The type of an expression whose branches met its expectation: the
    /// expectation, unless every branch diverges.
    fn branches_type(&self, exp: TypeId, branches: &[ExprId]) -> TypeId {
        if branches
            .iter()
            .all(|&b| self.tag(self.ety(b)) == Tag::Never)
        {
            TypeId::NEVER
        } else {
            exp
        }
    }

    fn push_target(&mut self, label: Option<BinderId>, is_loop: bool) {
        let pos = u32::try_from(self.targets.len()).unwrap_or(NONE);
        self.targets.push(Target {
            result: None,
            is_loop,
        });
        if is_loop {
            self.loops.push(pos);
        }
        if let Some(l) = label {
            if let Some(slot) = self.label_pos.get_mut(l.index()) {
                *slot = pos;
            }
        }
    }

    fn pop_target(&mut self) -> Option<Target> {
        let t = self.targets.pop()?;
        if t.is_loop {
            let _ = self.loops.pop();
        }
        Some(t)
    }

    fn enter_closure(
        &mut self,
        e: ExprId,
        c: Closure,
        tasks: &mut Vec<Task>,
    ) -> Result<(), CheckError> {
        let hir = self.hir;
        // Explicit captures read the outer variable, outside the closure.
        for cap in hir.list(c.captures) {
            let r = self.value_path(cap.outer, NodeRef::Path(cap.outer))?;
            let t = self.value_type(r)?;
            if let Some(slot) = self.binder_ty.get_mut(cap.binder.index()) {
                *slot = t.raw();
            }
        }
        // Checking mode: an expected function type gives unannotated
        // parameters (and the result) their types.
        let infer = self.profile.infers_closures();
        let expected: Option<(Vec<TypeId>, TypeId)> = if infer {
            self.peek_expect(e)
                .and_then(|x| match self.types.get(self.resolve(x)) {
                    Type::Fn { params, ret, .. } => Some((params.to_vec(), ret)),
                    _ => None,
                })
        } else {
            None
        };
        let positional = hir
            .list(c.params)
            .iter()
            .filter(|&&p| {
                matches!(
                    hir.param(p).kind,
                    ParamKind::Receiver | ParamKind::PositionalOnly | ParamKind::Normal
                )
            })
            .count();
        let expected = expected.filter(|(ps, _)| ps.len() == positional);
        let mut params = Vec::new();
        let mut pos = 0usize;
        for &pid in hir.list(c.params) {
            let param = *hir.param(pid);
            let is_pos = matches!(
                param.kind,
                ParamKind::Receiver | ParamKind::PositionalOnly | ParamKind::Normal
            );
            let t = match param.ty {
                Some(t) => self.lower_ty(t, self.cur_self, false)?,
                None if infer => match (&expected, is_pos) {
                    (Some((ps, _)), true) => ps.get(pos).copied().unwrap_or(TypeId::ERROR),
                    _ => self.fresh(GENERAL),
                },
                None => {
                    self.report(NodeRef::Param(pid), DiagnosticKind::MissingAnnotation);
                    TypeId::ERROR
                }
            };
            if is_pos {
                pos += 1;
            }
            self.bind_param(param.pat, param.kind, t)?;
            if matches!(
                param.kind,
                ParamKind::Receiver | ParamKind::PositionalOnly | ParamKind::Normal
            ) {
                params.push(t);
            }
            if let Some(d) = param.default {
                self.set_expect(d, t);
            }
        }
        let ret = match (c.ret, &expected) {
            (Some(t), _) => self.lower_ty(t, self.cur_self, false)?,
            (None, Some((_, r))) => *r,
            (None, None) => self.fresh(GENERAL),
        };
        let fn_ty = self.types.func(&params, ret, c.effects);
        if let Some(b) = c.self_binder {
            if let Some(slot) = self.binder_ty.get_mut(b.index()) {
                *slot = fn_ty.raw();
            }
        }
        let frame = self.frame_for(ret, None, c.effects);
        self.set_expect(
            c.body,
            if frame.yields.is_some() {
                TypeId::UNIT
            } else {
                ret
            },
        );
        self.frames.push(frame);
        self.closure_types.push(fn_ty);
        tasks.push(Task::Exit(e));
        tasks.push(Task::Expr(c.body));
        tasks.extend(
            hir.list(c.params)
                .iter()
                .rev()
                .filter_map(|&p| hir.param(p).default)
                .map(Task::Expr),
        );
        Ok(())
    }

    /// A function frame. In a generator, the declared result is the type of
    /// the yielded values and the body itself returns unit.
    pub(crate) fn frame_for(
        &self,
        ret: TypeId,
        throws: Option<TypeId>,
        effects: hir_lang::Effects,
    ) -> Frame {
        let generator = effects.contains(hir_lang::Effects::YIELD);
        Frame {
            declared: ret,
            ret: if generator { TypeId::UNIT } else { ret },
            throws,
            yields: generator.then_some(ret),
        }
    }

    /// Types a parameter's pattern: rests bind collections of the declared
    /// element type.
    pub(crate) fn bind_param(
        &mut self,
        pat: hir_lang::PatId,
        kind: ParamKind,
        t: TypeId,
    ) -> Result<(), CheckError> {
        let bound = match kind {
            ParamKind::Rest => self.types.slice(t),
            ParamKind::RestNamed => self.types.map(TypeId::prim(Prim::Str), t),
            _ => t,
        };
        self.check_pat(pat, bound)
    }

    // ----------------------------------------------------------- statements

    fn stmt(&mut self, s: StmtId, tasks: &mut Vec<Task>) -> Result<(), CheckError> {
        match *self.hir.stmt(s) {
            Stmt::Let {
                ty, init, else_, ..
            } => {
                if let Some(t) = ty {
                    let t = self.lower_ty(t, self.cur_self, false)?;
                    self.let_types.push((s, t));
                    if let Some(i) = init {
                        self.set_expect(i, t);
                    }
                }
                if let Some(x) = else_ {
                    // The `else` of let-else must diverge.
                    self.set_expect(x, TypeId::NEVER);
                    tasks.push(Task::Expr(x));
                }
                tasks.push(Task::LetInit(s));
                tasks.extend(init.map(Task::Expr));
            }
            Stmt::Static { ty, init, .. } => {
                if let Some(t) = ty {
                    let t = self.lower_ty(t, self.cur_self, false)?;
                    self.let_types.push((s, t));
                    if let Some(i) = init {
                        self.set_expect(i, t);
                    }
                }
                tasks.push(Task::LetInit(s));
                tasks.extend(init.map(Task::Expr));
            }
            Stmt::Expr(x) | Stmt::Defer(x) => tasks.push(Task::Expr(x)),
            Stmt::Global { binder, path } => {
                let r = self.value_path(path, NodeRef::Path(path))?;
                let t = self.value_type(r)?;
                if let Some(slot) = self.binder_ty.get_mut(binder.index()) {
                    *slot = t.raw();
                }
            }
            // Items are checked on their own; see `check_static`.
            Stmt::Item(_) | Stmt::Err => {}
        }
        Ok(())
    }

    /// The annotation of a `let`/`static`, lowered when the statement was
    /// entered.
    fn let_annotation(&mut self, s: StmtId) -> Option<TypeId> {
        // Lets are entered and finished in stack order: the most recent
        // entry is this statement's when it has an annotation.
        match self.let_types.last() {
            Some(&(q, t)) if q == s => {
                let _ = self.let_types.pop();
                Some(t)
            }
            _ => None,
        }
    }

    fn let_init(&mut self, s: StmtId) -> Result<(), CheckError> {
        let annotation = self.let_annotation(s);
        let init = match *self.hir.stmt(s) {
            Stmt::Let { init, .. } | Stmt::Static { init, .. } => init,
            _ => None,
        };
        let t = match (annotation, init) {
            (Some(t), _) => t,
            (None, Some(i)) => {
                let t = self.child(i);
                // `let x = null`: the profile decides (ISSUES P17).
                if self.tag(t) == Tag::Null
                    && self.profile.null_let == crate::profile::NullLet::Nullable
                {
                    let v = self.fresh(GENERAL);
                    let n = if self.profile.null_safety {
                        self.types.nullable(v)
                    } else {
                        v
                    };
                    if self.profile.null_safety {
                        self.coercions.push((i, crate::typed::Coercion::Null, n));
                    }
                    n
                } else {
                    t
                }
            }
            (None, None) => self.fresh(GENERAL),
        };
        match *self.hir.stmt(s) {
            Stmt::Let { pat, .. } => self.check_pat(pat, t)?,
            Stmt::Static { binder, .. } => {
                if let Some(slot) = self.binder_ty.get_mut(binder.index()) {
                    *slot = t.raw();
                }
            }
            _ => {}
        }
        Ok(())
    }

    // ----------------------------------------------------------- mid-steps

    fn call_prep(&mut self, e: ExprId) -> Result<(), CheckError> {
        let Expr::Call { callee, args } = *self.hir.expr(e) else {
            return Ok(());
        };
        let target = self.call_target(e, callee)?;
        self.match_args(e, target, args, false)?;
        self.call_stack.push(target);
        Ok(())
    }

    fn method_prep(&mut self, e: ExprId) -> Result<(), CheckError> {
        let Expr::MethodCall { args, .. } = *self.hir.expr(e) else {
            return Ok(());
        };
        let target = self.method_target(e)?;
        self.match_args(e, target, args, false)?;
        self.call_stack.push(target);
        Ok(())
    }

    fn assign_prep(&mut self, e: ExprId) -> Result<(), CheckError> {
        let Expr::Assign { target, op, value } = *self.hir.expr(e) else {
            return Ok(());
        };
        // Judge the target first: a value assigned to a function is not
        // also a mismatch against the function's type.
        self.assignable(target);
        if op.is_none() {
            let t = self.child(target);
            self.set_expect(value, t);
        }
        Ok(())
    }

    /// A `let_place` alias has the place's type.
    fn place_bind(&mut self, e: ExprId) {
        if let Expr::LetPlace { binder, place, .. } = *self.hir.expr(e) {
            let t = self.child(place);
            if let Some(slot) = self.binder_ty.get_mut(binder.index()) {
                *slot = t.raw();
            }
        }
    }

    fn arm_pat(&mut self, e: ExprId, i: u32) -> Result<(), CheckError> {
        let (scrut, arms) = match *self.hir.expr(e) {
            Expr::Match { scrutinee, arms } => (self.child(scrutinee), arms),
            // Thrown values are dynamically typed; catch patterns test them.
            Expr::Try { catches, .. } => (TypeId::ANY, catches),
            _ => return Ok(()),
        };
        if let Some(arm) = self.hir.list(arms).get(i as usize) {
            self.check_pat(arm.pat, scrut)?;
        }
        Ok(())
    }

    // ---------------------------------------------------------------- exit

    #[allow(clippy::too_many_lines)]
    fn exit(&mut self, e: ExprId) -> Result<(), CheckError> {
        let hir = self.hir;
        let at = NodeRef::Expr(e);
        let ty = match *hir.expr(e) {
            Expr::Tuple(list) => {
                let elems: Vec<TypeId> = hir.list(list).iter().map(|&c| self.child(c)).collect();
                self.types.tuple(&elems)
            }
            Expr::Array(list) => {
                let elems = hir.list(list);
                let elem = self.join_all(elems, self.expected_elem(e))?;
                self.types.array(elem, elems.len() as u64)
            }
            Expr::Repeat { elem, count } => {
                let elem_ty = self.child(elem);
                match self.const_eval(count)? {
                    Some(n) if n >= 0 => self
                        .types
                        .array(elem_ty, u64::try_from(n).unwrap_or(u64::MAX)),
                    _ => {
                        if !self.is_err(self.child(count)) {
                            self.report(NodeRef::Expr(count), DiagnosticKind::NotConstant);
                        }
                        TypeId::ERROR
                    }
                }
            }
            Expr::Record { path, fields, base } => self.record_exit(e, path, fields, base)?,
            Expr::Map(entries) => self.map_exit(hir.list(entries))?,
            Expr::Call { args, .. } => self.call_exit(e, args)?,
            Expr::MethodCall { receiver, args, .. } => {
                let target = self.call_stack.pop().unwrap_or(CallTarget::Silent);
                self.check_receiver(receiver, target)?;
                self.match_args(e, target, args, true)?;
                self.call_result_of(target)
            }
            Expr::Field { base, member, .. } => self.field_exit(e, base, member)?,
            Expr::DynField { .. }
            | Expr::DynMethodCall { .. }
            | Expr::VarVar(_)
            | Expr::RefAssign { .. } => {
                self.report(at, DiagnosticKind::DynamicForm);
                TypeId::ERROR
            }
            Expr::Append(base) => {
                // `$a[] = v` on an integer-keyed map; anything else is the
                // dynamic array form.
                let b = self.resolve(self.child(base));
                let map = match self.types.get(b) {
                    Type::Map { key, value } => Some((key, value)),
                    _ => None,
                };
                match map {
                    Some((key, value))
                        if self.satisfies_int(key)
                            || self.unify(key, TypeId::prim(self.profile.default_int))? =>
                    {
                        value
                    }
                    _ if self.is_err(b) => TypeId::ERROR,
                    _ => {
                        self.report(at, DiagnosticKind::DynamicForm);
                        TypeId::ERROR
                    }
                }
            }
            Expr::Index { base, index } => self.index_exit(e, base, index)?,
            Expr::Op { op, args } => {
                let args = hir.list(args);
                self.op_type(e, op, args)?
            }
            Expr::Cast { expr, ty, policy } => {
                let to = self.lower_ty(ty, self.cur_self, false)?;
                self.cast_type(e, expr, to, policy)?
            }
            Expr::Assign { target, op, value } => {
                if let Some(op) = op {
                    // `t op= v` is `t = t op v`, with the result stored back.
                    let r = self.op_type(e, op, &[target, value])?;
                    let t = self.child(target);
                    if !self.is_err(r) && !self.is_err(t) && !self.unify(r, t)? {
                        self.report(
                            NodeRef::Expr(value),
                            DiagnosticKind::Mismatch {
                                expected: t,
                                found: r,
                            },
                        );
                    }
                }
                // HIR v3: an assignment evaluates to the value stored (a
                // language whose assignment yields unit lowers a use of its
                // value as `{ a = b; () }`).
                self.child(target)
            }
            Expr::Deref(inner) => {
                let t = self.known(self.child(inner))?;
                match self.types.get(t) {
                    Type::Ref { inner, .. } | Type::Ptr { inner, .. } => inner,
                    Type::Error => TypeId::ERROR,
                    Type::Any => {
                        self.report(at, DiagnosticKind::DynamicOperation);
                        TypeId::ERROR
                    }
                    _ => {
                        self.report(at, DiagnosticKind::CannotDeref { ty: t });
                        TypeId::ERROR
                    }
                }
            }
            Expr::Borrow { kind, expr } => {
                let t = self.child(expr);
                match kind {
                    hir_lang::BorrowKind::Shared => self.types.reference(false, t),
                    hir_lang::BorrowKind::Mut => self.types.reference(true, t),
                    hir_lang::BorrowKind::RawConst => self.types.pointer(false, t),
                    hir_lang::BorrowKind::RawMut => self.types.pointer(true, t),
                }
            }
            Expr::Block(b) => self.block_exit(e, b)?,
            Expr::If { then, else_, .. } => match else_ {
                None => TypeId::UNIT,
                Some(other) => match self.was_delegated(e) {
                    Some(exp) => self.branches_type(exp, &[then, other]),
                    None => {
                        let a = self.child(then);
                        let b = self.child(other);
                        self.join(a, Some(then), b, other)?
                    }
                },
            },
            Expr::Match { scrutinee, arms } => self.match_exit(e, scrutinee, hir.list(arms))?,
            Expr::Try { body, catches, .. } => {
                let catches = hir.list(catches);
                match self.was_delegated(e) {
                    Some(exp) => {
                        let mut branches = alloc::vec![body];
                        branches.extend(catches.iter().map(|a| a.body));
                        self.branches_type(exp, &branches)
                    }
                    None => {
                        let mut t = self.child(body);
                        let mut prev = body;
                        for arm in catches {
                            let b = self.child(arm.body);
                            t = self.join(t, Some(prev), b, arm.body)?;
                            prev = arm.body;
                        }
                        t
                    }
                }
            }
            Expr::Loop { .. } => match self.pop_target() {
                Some(Target {
                    result: Some(t), ..
                }) => t,
                _ => TypeId::NEVER,
            },
            Expr::Break { label, value } => {
                self.break_exit(e, label, value)?;
                TypeId::NEVER
            }
            Expr::Return(_) | Expr::Throw(_) | Expr::Continue { .. } => TypeId::NEVER,
            // Under the generator convention (HIR.md, typeck notes) the
            // values sent back into a generator are not typed: `yield`
            // evaluates to unit, and `yield from` (whose value is the inner
            // generator's return value, which the convention does not
            // track) too.
            Expr::Yield { .. } => TypeId::UNIT,
            Expr::YieldFrom(inner) => {
                let t = self.known(self.child(inner))?;
                let want = self.frames.last().and_then(|f| f.yields);
                match (self.types.get(t), want) {
                    (Type::Generator { item, .. }, Some(y)) => {
                        let _ = self.coerce_expr(inner, item, y)?;
                    }
                    (Type::Error, _) | (_, None) => {}
                    (Type::Any, _) => self.report(at, DiagnosticKind::DynamicOperation),
                    (_, Some(y)) => {
                        let expected = self.types.generator(y, false);
                        self.report(
                            NodeRef::Expr(inner),
                            DiagnosticKind::Mismatch { expected, found: t },
                        );
                    }
                }
                TypeId::UNIT
            }
            Expr::LetPlace { body, .. } => match self.was_delegated(e) {
                Some(exp) => self.branches_type(exp, &[body]),
                None => self.child(body),
            },
            Expr::Closure(_) => {
                let _ = self.frames.pop();
                self.closure_types.pop().unwrap_or(TypeId::ERROR)
            }
            Expr::Await(inner) => {
                let t = self.known(self.child(inner))?;
                match self.types.get(t) {
                    Type::Async(r) | Type::Task(r) => r,
                    Type::Error => TypeId::ERROR,
                    _ => {
                        self.report(at, DiagnosticKind::NotAwaitable { ty: t });
                        TypeId::ERROR
                    }
                }
            }
            Expr::Spawn(callable) => {
                // The task runs the callable; awaiting the handle yields
                // its result.
                let t = self.known(self.child(callable))?;
                match self.types.get(t) {
                    Type::Fn {
                        params: [], ret, ..
                    } => self.types.task(ret),
                    Type::Error => TypeId::ERROR,
                    _ => {
                        self.report(
                            NodeRef::Expr(callable),
                            DiagnosticKind::NotCallable { ty: t },
                        );
                        TypeId::ERROR
                    }
                }
            }
            Expr::Asm(asm) => {
                for op in hir.list(asm.operands) {
                    if op.dir == AsmDir::Const {
                        let t = self.child(op.expr);
                        if !self.is_err(t) && !self.satisfies_int(t) {
                            self.report(NodeRef::Expr(op.expr), DiagnosticKind::NotConstant);
                        }
                    }
                }
                if asm.options.contains(AsmOptions::NORETURN) {
                    TypeId::NEVER
                } else {
                    TypeId::UNIT
                }
            }
            Expr::Intrinsic { kind, args, .. } => self.intrinsic_exit(e, kind, hir.list(args))?,
            // Leaves finish in `enter`.
            Expr::Lit(_) | Expr::Path(_) | Expr::Err => return Ok(()),
        };
        self.finish(e, ty)
    }

    fn satisfies_int(&self, t: TypeId) -> bool {
        let r = self.resolve(t);
        match self.types.get(r) {
            Type::Prim(p) => p.is_int(),
            _ => self.tag(r) == Tag::Var && self.infer.class_of(r) == INT,
        }
    }

    /// Joins the types of `elems` (each already coerced to `expected` when
    /// there is one).
    fn join_all(
        &mut self,
        elems: &[ExprId],
        expected: Option<TypeId>,
    ) -> Result<TypeId, CheckError> {
        if let Some(t) = expected {
            return Ok(t);
        }
        let mut acc: Option<(TypeId, ExprId)> = None;
        for &c in elems {
            let t = self.child(c);
            acc = Some(match acc {
                None => (t, c),
                Some((prev, pe)) => (self.join(prev, Some(pe), t, c)?, c),
            });
        }
        Ok(match acc {
            Some((t, _)) => t,
            None => self.fresh(GENERAL),
        })
    }

    fn call_exit(
        &mut self,
        e: ExprId,
        args: hir_lang::List<hir_lang::Arg>,
    ) -> Result<TypeId, CheckError> {
        let target = self.call_stack.pop().unwrap_or(CallTarget::Silent);
        self.match_args(e, target, args, true)?;
        Ok(self.call_result_of(target))
    }

    fn record_exit(
        &mut self,
        e: ExprId,
        path: Option<hir_lang::PathId>,
        fields: hir_lang::List<hir_lang::FieldInit>,
        base: Option<ExprId>,
    ) -> Result<TypeId, CheckError> {
        let hir = self.hir;
        let at = NodeRef::Expr(e);
        let inits = hir.list(fields);
        if path.is_none() {
            // An anonymous record: its type is its fields.
            let mut fs: Vec<crate::types::Field> = inits
                .iter()
                .map(|fi| crate::types::Field {
                    name: fi.name.sym,
                    ty: self.child(fi.value),
                })
                .collect();
            fs.sort_by_key(|f| f.name);
            return Ok(self.types.record_sorted(&fs));
        }
        let (target, adt) = match self.record_targets.last() {
            Some(&(q, t, adt)) if q == e => {
                let _ = self.record_targets.pop();
                (t, adt)
            }
            // The path was reported (or is `{error}`).
            _ => return Ok(TypeId::ERROR),
        };
        let owner = field_owner(target);
        let mut unknown = false;
        for fi in inits {
            if self.idx.field_named(owner, fi.name.sym).is_none()
                && !self.inherited_field(target, fi.name.sym)
            {
                unknown = true;
                self.report(
                    at,
                    DiagnosticKind::UnknownField {
                        ty: adt,
                        name: fi.name.sym,
                    },
                );
            }
        }
        let union = match target {
            RecordRef::Item(i) => matches!(self.item_kind(i), ItemKind::Record(d) if d.is_union),
            RecordRef::Variant(_) => false,
        };
        if union {
            if inits.len() != 1 {
                self.report(
                    at,
                    DiagnosticKind::UnionLiteral {
                        count: u32::try_from(inits.len()).unwrap_or(u32::MAX),
                    },
                );
            }
        } else if base.is_none() && !unknown {
            self.missing_literal_fields(e, target, inits);
        }
        Ok(adt)
    }

    /// Whether `name` is a field of one of a class's base classes.
    fn inherited_field(&mut self, target: RecordRef, name: hir_lang::Symbol) -> bool {
        let RecordRef::Item(i) = target else {
            return false;
        };
        let bases = self.idx.bases_of(i).to_vec();
        bases.into_iter().any(|b| {
            let raw = u32::try_from(b.index()).unwrap_or(NONE);
            self.idx.field_named(FieldOwner::Item(raw), name).is_some()
        })
    }

    fn missing_literal_fields(
        &mut self,
        e: ExprId,
        target: RecordRef,
        inits: &[hir_lang::FieldInit],
    ) {
        let hir = self.hir;
        let declared: Vec<hir_lang::FieldId> = match target {
            RecordRef::Item(i) => self.record_field_ids(i),
            RecordRef::Variant(v) => hir
                .variant(v)
                .map(|x| hir.list(x.fields).to_vec())
                .unwrap_or_default(),
        };
        let mut given: Vec<hir_lang::Symbol> = inits.iter().map(|f| f.name.sym).collect();
        given.sort_unstable();
        let mut first = None;
        let mut count = 0u32;
        for f in declared {
            let def = hir.field(f);
            let Some(name) = def.name else { continue };
            if def.default.is_none() && given.binary_search(&name.sym).is_err() {
                count += 1;
                let _ = first.get_or_insert(name.sym);
            }
        }
        if let Some(first) = first {
            self.report(
                NodeRef::Expr(e),
                DiagnosticKind::MissingFields { first, count },
            );
        }
    }

    fn map_exit(&mut self, entries: &[MapEntry]) -> Result<TypeId, CheckError> {
        let mut key: Option<(TypeId, ExprId)> = None;
        let mut value: Option<(TypeId, ExprId)> = None;
        let mut next_index = false;
        for entry in entries {
            if let Some(k) = entry.key {
                let t = self.child(k);
                key = Some(match key {
                    None => (t, k),
                    Some((prev, pe)) => (self.join(prev, Some(pe), t, k)?, k),
                });
            } else {
                next_index = true;
            }
            let t = self.child(entry.value);
            value = Some(match value {
                None => (t, entry.value),
                Some((prev, pe)) => (self.join(prev, Some(pe), t, entry.value)?, entry.value),
            });
        }
        let key_ty = match key {
            Some((t, k)) => {
                if next_index && !self.satisfies_int(t) && !self.is_err(t) {
                    // "Next index" keys are integers.
                    let int = self.fresh(INT);
                    if !self.unify(t, int)? {
                        self.report(
                            NodeRef::Expr(k),
                            DiagnosticKind::Mismatch {
                                expected: int,
                                found: t,
                            },
                        );
                    }
                }
                t
            }
            None if next_index => self.fresh(INT),
            None => self.fresh(GENERAL),
        };
        let value_ty = match value {
            Some((t, _)) => t,
            None => self.fresh(GENERAL),
        };
        Ok(self.types.map(key_ty, value_ty))
    }

    fn field_exit(
        &mut self,
        e: ExprId,
        base: ExprId,
        member: hir_lang::Member,
    ) -> Result<TypeId, CheckError> {
        let at = NodeRef::Expr(e);
        let t = self.known(self.child(base))?;
        let t = self.settle_literal(t)?;
        match self.tag(t) {
            // An unknown base: `CannotInfer` reports the cause.
            Tag::Error | Tag::Never | Tag::Var => return Ok(TypeId::ERROR),
            Tag::Any => {
                self.report(at, DiagnosticKind::DynamicOperation);
                return Ok(TypeId::ERROR);
            }
            Tag::Nullable => {
                self.report(
                    NodeRef::Expr(base),
                    DiagnosticKind::NullableAccess { ty: t },
                );
                return Ok(TypeId::ERROR);
            }
            _ => {}
        }
        if let Some(ft) = self.field_of(t, member)? {
            return Ok(ft);
        }
        if !self.members_incomplete(t) {
            self.report(at, DiagnosticKind::NoField { ty: t, member });
        }
        Ok(TypeId::ERROR)
    }

    fn index_exit(&mut self, e: ExprId, base: ExprId, index: ExprId) -> Result<TypeId, CheckError> {
        let at = NodeRef::Expr(e);
        let mut t = self.known(self.child(base))?;
        while let Type::Ref { inner, .. } = self.types.get(t) {
            self.meter.tick(1)?;
            t = self.resolve(inner);
        }
        let idx_ty = self.child(index);
        let int_index = |cx: &mut Self| -> Result<(), CheckError> {
            if cx.is_err(idx_ty) || cx.satisfies_int(idx_ty) {
                return Ok(());
            }
            let int = cx.fresh(INT);
            if !cx.unify(idx_ty, int)? {
                cx.report(
                    NodeRef::Expr(index),
                    DiagnosticKind::Mismatch {
                        expected: TypeId::prim(Prim::Usize),
                        found: idx_ty,
                    },
                );
            }
            Ok(())
        };
        Ok(match self.types.get(t) {
            Type::Array { elem, .. } | Type::Slice(elem) => {
                int_index(self)?;
                elem
            }
            Type::Map { key, value } => {
                let _ = self.coerce_expr(index, idx_ty, key)?;
                value
            }
            Type::Error | Type::Never => TypeId::ERROR,
            Type::Any => {
                self.report(at, DiagnosticKind::DynamicOperation);
                TypeId::ERROR
            }
            Type::Nullable(_) => {
                self.report(
                    NodeRef::Expr(base),
                    DiagnosticKind::NullableAccess { ty: t },
                );
                TypeId::ERROR
            }
            _ => {
                self.report(at, DiagnosticKind::NotIndexable { ty: t });
                TypeId::ERROR
            }
        })
    }

    /// Paths to functions, constants, and constructors are not places.
    fn assignable(&mut self, target: ExprId) {
        let Expr::Path(p) = *self.hir.expr(target) else {
            return;
        };
        let path = self.hir.path(p);
        if path.unresolved != 0 {
            return;
        }
        let bad = match self.local_item(path.res) {
            Some(i) => matches!(
                self.item_kind(i),
                ItemKind::Fn(_) | ItemKind::Const { .. } | ItemKind::Record(_)
            ),
            None => {
                matches!(path.res, hir_lang::Res::Def(d) if matches!(d.def(), hir_lang::Def::Variant(_)) && d.unit() == self.hir.unit())
            }
        };
        if bad {
            self.report(NodeRef::Expr(target), DiagnosticKind::NotAssignable);
            self.poison(target);
        }
    }

    fn block_exit(&mut self, e: ExprId, b: Block) -> Result<TypeId, CheckError> {
        let delegated = if b.label.is_none() && b.tail.is_some() {
            self.was_delegated(e)
        } else {
            None
        };
        let mut t = match b.tail {
            Some(tail) => match delegated {
                Some(exp) => self.branches_type(exp, &[tail]),
                None => self.child(tail),
            },
            None => {
                if self.block_diverges(b) {
                    TypeId::NEVER
                } else {
                    TypeId::UNIT
                }
            }
        };
        if b.label.is_some() {
            if let Some(Target {
                result: Some(r), ..
            }) = self.pop_target()
            {
                // Breaks out of the block join its normal value.
                t = match b.tail {
                    Some(tail) => self.join(r, None, t, tail)?,
                    None => r,
                };
            }
        }
        Ok(t)
    }

    fn block_diverges(&self, b: Block) -> bool {
        self.hir
            .list(b.stmts)
            .iter()
            .any(|&s| match *self.hir.stmt(s) {
                Stmt::Expr(x) => self.tag(self.ety(x)) == Tag::Never,
                Stmt::Let { init: Some(x), .. } => self.tag(self.ety(x)) == Tag::Never,
                _ => false,
            })
    }

    fn match_exit(
        &mut self,
        e: ExprId,
        scrutinee: ExprId,
        arms: &[Arm],
    ) -> Result<TypeId, CheckError> {
        let _ = scrutinee;
        // Exhaustiveness and usefulness are decided by match-lang once every
        // type is known (see `exhaust`).
        self.matches.push(e);
        if let Some(exp) = self.was_delegated(e) {
            let bodies: Vec<ExprId> = arms.iter().map(|a| a.body).collect();
            return Ok(self.branches_type(exp, &bodies));
        }
        let mut acc: Option<(TypeId, ExprId)> = None;
        for arm in arms {
            let t = self.child(arm.body);
            acc = Some(match acc {
                None => (t, arm.body),
                Some((prev, pe)) => (self.join(prev, Some(pe), t, arm.body)?, arm.body),
            });
        }
        Ok(acc.map_or(TypeId::NEVER, |(t, _)| t))
    }

    fn break_exit(
        &mut self,
        e: ExprId,
        label: Option<BinderId>,
        value: Option<ExprId>,
    ) -> Result<(), CheckError> {
        let pos = match label {
            Some(l) => self
                .label_pos
                .get(l.index())
                .copied()
                .filter(|&p| p != NONE),
            None => self.loops.last().copied(),
        };
        let Some(pos) = pos else { return Ok(()) };
        let (vt, ve) = match value {
            Some(v) => (self.child(v), Some(v)),
            None => (TypeId::UNIT, None),
        };
        let prev = self.targets.get(pos as usize).and_then(|t| t.result);
        let joined = match (prev, ve) {
            (None, _) => vt,
            (Some(p), Some(v)) => self.join(p, None, vt, v)?,
            (Some(p), None) => {
                if !self.is_err(p) && !self.unify(p, TypeId::UNIT)? {
                    // A `break` without a value where earlier ones had one.
                    self.report(
                        NodeRef::Expr(e),
                        DiagnosticKind::Mismatch {
                            expected: p,
                            found: TypeId::UNIT,
                        },
                    );
                }
                p
            }
        };
        if let Some(t) = self.targets.get_mut(pos as usize) {
            t.result = Some(joined);
        }
        Ok(())
    }

    fn intrinsic_exit(
        &mut self,
        e: ExprId,
        kind: Intrinsic,
        args: &[ExprId],
    ) -> Result<TypeId, CheckError> {
        let at = NodeRef::Expr(e);
        let arg = |i: usize| args.get(i).copied();
        // The pointee of the first operand, for memory intrinsics.
        let pointee = |cx: &mut Self| -> Result<TypeId, CheckError> {
            let Some(p) = arg(0) else {
                return Ok(TypeId::ERROR);
            };
            let t = cx.resolve(cx.child(p));
            Ok(match cx.types.get(t) {
                Type::Ptr { inner, .. } | Type::Ref { inner, .. } => inner,
                Type::Error => TypeId::ERROR,
                _ => {
                    cx.report(NodeRef::Expr(p), DiagnosticKind::CannotDeref { ty: t });
                    TypeId::ERROR
                }
            })
        };
        let value_fits = |cx: &mut Self, i: usize, want: TypeId| -> Result<(), CheckError> {
            if let Some(v) = arg(i) {
                let t = cx.child(v);
                let _ = cx.coerce_expr(v, t, want)?;
            }
            Ok(())
        };
        Ok(match kind {
            Intrinsic::AtomicLoad(_) | Intrinsic::VolatileLoad => pointee(self)?,
            Intrinsic::AtomicStore(_) | Intrinsic::VolatileStore => {
                let t = pointee(self)?;
                value_fits(self, 1, t)?;
                TypeId::UNIT
            }
            Intrinsic::AtomicRmw(..) => {
                let t = pointee(self)?;
                value_fits(self, 1, t)?;
                t
            }
            Intrinsic::AtomicCmpXchg { .. } => {
                let t = pointee(self)?;
                value_fits(self, 1, t)?;
                value_fits(self, 2, t)?;
                self.types.tuple(&[t, TypeId::prim(Prim::Bool)])
            }
            Intrinsic::Fence(_) => TypeId::UNIT,
            Intrinsic::Named(name) if self.is_try(name) && args.len() == 1 => {
                let Some(&arg) = args.first() else {
                    return Ok(TypeId::ERROR);
                };
                self.try_exit(e, arg)?
            }
            Intrinsic::Named(name) => match self.host_intrinsic(name) {
                Some(f) => match self.types.get(self.resolve(f)) {
                    Type::Fn { params, ret, .. } => {
                        let params = params.to_vec();
                        if params.len() != args.len() {
                            let n = u32::try_from(params.len()).unwrap_or(u32::MAX);
                            self.report(
                                at,
                                DiagnosticKind::Arity {
                                    min: n,
                                    max: Some(n),
                                    found: u32::try_from(args.len()).unwrap_or(u32::MAX),
                                },
                            );
                        } else {
                            for (i, p) in params.into_iter().enumerate() {
                                value_fits(self, i, p)?;
                            }
                        }
                        ret
                    }
                    _ => {
                        self.report(at, DiagnosticKind::NotCallable { ty: f });
                        TypeId::ERROR
                    }
                },
                None => {
                    self.report(at, DiagnosticKind::UnknownExtern { name: Some(name) });
                    TypeId::ERROR
                }
            },
            // `Intrinsic` is non-exhaustive: a newer intrinsic is unknown
            // to this checker.
            _ => {
                self.report(at, DiagnosticKind::UnknownExtern { name: None });
                TypeId::ERROR
            }
        })
    }

    /// Whether `name` is the profile's `?` intrinsic.
    fn is_try(&self, name: hir_lang::Symbol) -> bool {
        matches!(self.profile.try_hook, crate::profile::TryHook::Intrinsic { name: n, .. } if n == name)
    }

    /// `?` through the profile's hook: the operand's success value, with
    /// the failure propagated out of the enclosing function.
    fn try_exit(&mut self, e: ExprId, arg: ExprId) -> Result<TypeId, CheckError> {
        let t = self.known(self.child(arg))?;
        let t = self.settle_literal(t)?;
        let declared = self.frames.last().map_or(TypeId::ERROR, |f| f.declared);
        let declared = self.resolve(declared);
        if matches!(self.tag(t), Tag::Error | Tag::Never) || self.is_err(declared) {
            return Ok(TypeId::ERROR);
        }
        match self.types.get(t) {
            Type::Nullable(inner) => {
                let ok = match self.types.get(declared) {
                    Type::Nullable(_) => true,
                    _ if self.tag(declared) == Tag::Var => {
                        let v = self.fresh(GENERAL);
                        let n = self.types.nullable(v);
                        self.unify(declared, n)?
                    }
                    _ => false,
                };
                if !ok {
                    self.report(
                        NodeRef::Expr(e),
                        DiagnosticKind::TryCarrier { ty: declared },
                    );
                }
                return Ok(inner);
            }
            Type::Adt { item, .. } => {
                if let Some((value_v, fail_v)) = self.carrier_variants(item) {
                    let mut value = Vec::new();
                    self.variant_field_types(t, value_v, &mut value)?;
                    let value = value.first().copied().unwrap_or(TypeId::UNIT);
                    // The function must return the same carrier.
                    let ret_inst = self.adt_fresh(item);
                    if !self.unify(declared, ret_inst)? {
                        self.report(
                            NodeRef::Expr(e),
                            DiagnosticKind::TryCarrier { ty: declared },
                        );
                        return Ok(value);
                    }
                    if let Some(fv) = fail_v {
                        let mut have = Vec::new();
                        self.variant_field_types(t, fv, &mut have)?;
                        let mut want = Vec::new();
                        self.variant_field_types(ret_inst, fv, &mut want)?;
                        if let (Some(&h), Some(&w)) = (have.first(), want.first()) {
                            let snap = self.infer.snapshot();
                            if self.unify(h, w)? {
                                self.infer.commit();
                            } else {
                                self.infer.rollback(snap);
                                match self.try_convert_iface() {
                                    Some(iface) => {
                                        let tr = self.types.trait_ref(iface, &[h]);
                                        self.oblige_impl(w, tr, NodeRef::Expr(e));
                                        self.coercions.push((
                                            e,
                                            crate::typed::Coercion::ErrorConvert,
                                            w,
                                        ));
                                    }
                                    None => self.report(
                                        NodeRef::Expr(arg),
                                        DiagnosticKind::Mismatch {
                                            expected: w,
                                            found: h,
                                        },
                                    ),
                                }
                            }
                        }
                    }
                    return Ok(value);
                }
            }
            _ => {}
        }
        if self.tag(t) != Tag::Var {
            self.report(NodeRef::Expr(arg), DiagnosticKind::TryCarrier { ty: t });
        }
        Ok(TypeId::ERROR)
    }

    /// A carrier sum's success variant, and its failure variant when the
    /// failure carries a value (result-like) rather than none (option-like).
    fn carrier_variants(&self, item: hir_lang::ItemId) -> Option<(u32, Option<u32>)> {
        let ItemKind::Sum(def) = self.item_kind(item) else {
            return None;
        };
        let vs = self.hir.list(def.variants);
        let [a, b] = vs else { return None };
        let shape = |v: hir_lang::VariantId| self.hir.variant(v).map(|x| (x.shape, x.fields.len()));
        match (shape(*a)?, shape(*b)?) {
            ((hir_lang::Shape::Unit, _), (hir_lang::Shape::Tuple, 1)) => Some((1, None)),
            ((hir_lang::Shape::Tuple, 1), (hir_lang::Shape::Unit, _)) => Some((0, None)),
            ((hir_lang::Shape::Tuple, 1), (hir_lang::Shape::Tuple, 1)) => Some((0, Some(1))),
            _ => None,
        }
    }

    /// The field types of variant `v` of an instance of a sum.
    fn variant_field_types(
        &mut self,
        t: TypeId,
        v: u32,
        out: &mut Vec<TypeId>,
    ) -> Result<(), CheckError> {
        let Type::Adt { item, .. } = self.types.get(self.resolve(t)) else {
            return Ok(());
        };
        let ItemKind::Sum(def) = self.item_kind(item) else {
            return Ok(());
        };
        let Some(&var) = self.hir.list(def.variants).get(v as usize) else {
            return Ok(());
        };
        let fields = self
            .hir
            .variant(var)
            .map(|x| self.hir.list(x.fields).to_vec())
            .unwrap_or_default();
        for f in fields {
            out.push(self.field_type_in(f, t)?);
        }
        Ok(())
    }

    /// The conversion interface of the profile's `?` hook, by name.
    fn try_convert_iface(&mut self) -> Option<hir_lang::ItemId> {
        let crate::profile::TryHook::Intrinsic {
            convert: Some(sym), ..
        } = self.profile.try_hook
        else {
            return None;
        };
        if let Some(cached) = self.try_iface {
            return cached;
        }
        let found = self
            .tr
            .ifaces
            .iter()
            .copied()
            .find(|&i| self.item_symbol(i) == Some(sym));
        self.try_iface = Some(found);
        found
    }
}

pub(crate) fn field_owner(target: RecordRef) -> FieldOwner {
    match target {
        RecordRef::Item(i) => FieldOwner::Item(u32::try_from(i.index()).unwrap_or(NONE)),
        RecordRef::Variant(v) => FieldOwner::Variant(u32::try_from(v.index()).unwrap_or(NONE)),
    }
}
