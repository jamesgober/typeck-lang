//! Annotations to types, constant evaluation, and function signatures.
//!
//! Every lowering is memoized per HIR node (a type node sits in exactly one
//! context, so its meaning is fixed) and iterative: a type nested 100,000
//! deep lowers on an explicit stack.

use alloc::vec::Vec;

use hir_lang::{
    Def, Effects, Expr, ExprId, FieldId, ItemId, ItemKind, Lit, NodeRef, OpKind, ParamKind, Pat,
    PathId, Res, Symbol, Ty, TyId,
};

use super::Ctx;
use crate::{
    diag::{DiagnosticKind, Feature},
    error::CheckError,
    typed::NONE,
    types::TypeId,
};

/// One parameter of a function signature.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ParamInfo {
    pub(crate) kind: ParamKind,
    pub(crate) name: Option<Symbol>,
    /// The parameter's type; for `Rest`/`RestNamed`, the element type.
    pub(crate) ty: TypeId,
    pub(crate) has_default: bool,
    pub(crate) by_ref: bool,
}

/// A function's signature, as calls see it.
#[derive(Clone, Debug)]
pub(crate) struct Sig {
    pub(crate) params: Vec<ParamInfo>,
    pub(crate) ret: TypeId,
    pub(crate) effects: Effects,
    pub(crate) throws: Option<TypeId>,
    /// Parameter names to positions, sorted, for named arguments.
    pub(crate) by_name: Vec<(Symbol, u32)>,
}

impl Sig {
    pub(crate) fn param_named(&self, name: Symbol) -> Option<usize> {
        self.by_name
            .binary_search_by(|(n, _)| n.cmp(&name))
            .ok()
            .and_then(|i| self.by_name.get(i))
            .map(|&(_, p)| p as usize)
    }
}

/// Constant-evaluation state of a `const` item.
const CONST_UNKNOWN: u8 = 0;
const CONST_BUSY: u8 = 1;
const CONST_SOME: u8 = 2;
const CONST_NONE: u8 = 3;

impl Ctx<'_> {
    fn memo_ty(&self, ty: TyId) -> Option<TypeId> {
        self.ty_memo
            .get(ty.index())
            .copied()
            .filter(|&v| v != NONE)
            .map(TypeId::from_raw)
    }

    fn set_memo_ty(&mut self, ty: TyId, t: TypeId) {
        if let Some(slot) = self.ty_memo.get_mut(ty.index()) {
            *slot = t.raw();
        }
    }

    /// The `Self` type inside `item` (from its enclosing impl, class, or
    /// interface).
    pub(crate) fn item_self(&self, item: ItemId) -> Option<TypeId> {
        let owner = self.idx.owner_of(item)?;
        self.idx
            .self_ty
            .get(owner.index())
            .copied()
            .filter(|&v| v != NONE)
            .map(TypeId::from_raw)
    }

    /// Lowers a type annotation. `sig`: the annotation is part of a
    /// declaration (signature, field, constant), where `_` is not allowed.
    pub(crate) fn lower_ty(
        &mut self,
        root: TyId,
        self_ty: Option<TypeId>,
        sig: bool,
    ) -> Result<TypeId, CheckError> {
        if let Some(t) = self.memo_ty(root) {
            return Ok(t);
        }
        // (node, children done, Self, declaration context)
        let mut stack: Vec<(TyId, bool, Option<TypeId>, bool)> =
            alloc::vec![(root, false, self_ty, sig)];
        let mut kids: Vec<TyId> = Vec::new();
        while let Some((ty, expanded, self_ty, sig)) = stack.pop() {
            self.meter.tick(1)?;
            if self.memo_ty(ty).is_some() {
                continue;
            }
            let node = *self.hir.ty(ty);
            if !expanded {
                if let Ty::Path(p) = node {
                    if let Some((alias, body)) = self.alias_target(p) {
                        match self.alias_state.get(alias.index()).copied().unwrap_or(0) {
                            0 => {
                                if let Some(s) = self.alias_state.get_mut(alias.index()) {
                                    *s = 1;
                                }
                                stack.push((ty, true, self_ty, sig));
                                let alias_self = self.item_self(alias);
                                stack.push((body, false, alias_self, true));
                                continue;
                            }
                            1 => {
                                self.report(NodeRef::Item(alias), DiagnosticKind::CyclicAlias);
                                if let Some(s) = self.alias_state.get_mut(alias.index()) {
                                    *s = 3;
                                }
                                self.set_memo_ty(ty, TypeId::ERROR);
                                continue;
                            }
                            _ => {}
                        }
                    }
                }
                kids.clear();
                ty_children(&node, self.hir, &mut kids);
                stack.push((ty, true, self_ty, sig));
                for &k in kids.iter().rev() {
                    if self.memo_ty(k).is_none() {
                        stack.push((k, false, self_ty, sig));
                    }
                }
                continue;
            }
            let t = self.build_ty(ty, node, self_ty, sig)?;
            self.set_memo_ty(ty, t);
        }
        Ok(self.memo_ty(root).unwrap_or(TypeId::ERROR))
    }

    fn sub(&self, ty: TyId) -> TypeId {
        self.memo_ty(ty).unwrap_or(TypeId::ERROR)
    }

    /// Builds one type node from its lowered children.
    fn build_ty(
        &mut self,
        id: TyId,
        node: Ty,
        self_ty: Option<TypeId>,
        sig: bool,
    ) -> Result<TypeId, CheckError> {
        let at = NodeRef::Ty(id);
        Ok(match node {
            Ty::Infer => {
                if sig {
                    self.report(at, DiagnosticKind::MissingAnnotation);
                    TypeId::ERROR
                } else {
                    self.fresh(crate::infer::GENERAL)
                }
            }
            Ty::Prim(p) => TypeId::prim(p),
            Ty::Path(p) => self.path_ty(id, p)?,
            Ty::Tuple(list) => {
                let elems: Vec<TypeId> = self.hir.list(list).iter().map(|&t| self.sub(t)).collect();
                self.types.tuple(&elems)
            }
            Ty::Array { elem, len } => {
                let elem = self.sub(elem);
                match self.const_eval(len)? {
                    Some(n) if n >= 0 => {
                        self.types.array(elem, u64::try_from(n).unwrap_or(u64::MAX))
                    }
                    _ => {
                        self.report(NodeRef::Expr(len), DiagnosticKind::NotConstant);
                        TypeId::ERROR
                    }
                }
            }
            Ty::Slice(inner) => {
                let inner = self.sub(inner);
                self.types.slice(inner)
            }
            Ty::Ref { mutable, inner, .. } => {
                let inner = self.sub(inner);
                self.types.reference(mutable, inner)
            }
            Ty::Ptr { mutable, inner } => {
                let inner = self.sub(inner);
                self.types.pointer(mutable, inner)
            }
            Ty::Fn {
                params,
                ret,
                effects,
                ..
            } => {
                let params: Vec<TypeId> =
                    self.hir.list(params).iter().map(|&t| self.sub(t)).collect();
                let ret = self.sub(ret);
                self.types.func(&params, ret, effects)
            }
            Ty::Nullable(inner) => {
                let inner = self.sub(inner);
                self.types.nullable(inner)
            }
            Ty::Any => TypeId::ANY,
            Ty::Never => TypeId::NEVER,
            Ty::Object(_) | Ty::Impl(_) => {
                self.report(
                    at,
                    DiagnosticKind::Unsupported {
                        feature: Feature::Traits,
                    },
                );
                TypeId::ERROR
            }
            Ty::SelfTy => match self_ty {
                Some(t) => t,
                None => {
                    self.report(at, DiagnosticKind::NotAType);
                    TypeId::ERROR
                }
            },
            Ty::Err => TypeId::ERROR,
        })
    }

    /// The alias item a type path names, with its aliased type, when that
    /// alias can be expanded here (not generic).
    fn alias_target(&self, p: PathId) -> Option<(ItemId, TyId)> {
        let path = self.hir.path(p);
        if path.unresolved != 0 || path.qself.is_some() {
            return None;
        }
        let item = self.local_item(path.res)?;
        match self.item_kind(item) {
            ItemKind::Alias { ty, .. } if !self.idx.is_generic(item) => Some((item, ty)),
            _ => None,
        }
    }

    /// The item of this unit a resolution names.
    pub(crate) fn local_item(&self, res: Res) -> Option<ItemId> {
        match res {
            Res::Def(d) if d.unit() == self.hir.unit() => match d.def() {
                Def::Item(i) => Some(i),
                Def::Variant(_) => None,
            },
            _ => None,
        }
    }

    fn has_generic_args(&self, p: PathId) -> bool {
        let path = self.hir.path(p);
        self.hir
            .list(path.segments)
            .iter()
            .any(|s| !s.args.is_empty())
    }

    /// The type a path in a type annotation names.
    fn path_ty(&mut self, ty: TyId, p: PathId) -> Result<TypeId, CheckError> {
        let at = NodeRef::Ty(ty);
        let path = *self.hir.path(p);
        let unsupported = |feature| DiagnosticKind::Unsupported { feature };
        if path.qself.is_some() {
            self.report(at, unsupported(Feature::Traits));
            return Ok(TypeId::ERROR);
        }
        if path.unresolved != 0 {
            if path.res == Res::Err {
                return Ok(TypeId::ERROR);
            }
            // `Self::Item`, `T::Item`, `a::B::C` by type: associated types.
            self.report(at, unsupported(Feature::AssociatedTypes));
            return Ok(TypeId::ERROR);
        }
        if self.has_generic_args(p) {
            self.report(at, unsupported(Feature::Generics));
            return Ok(TypeId::ERROR);
        }
        Ok(match path.res {
            Res::Def(d) if d.unit() == self.hir.unit() => match d.def() {
                Def::Item(i) => match self.item_kind(i) {
                    ItemKind::Record(_) | ItemKind::Sum(_) | ItemKind::Class(_) => {
                        if self.idx.is_generic(i) {
                            // Reported once, at the generic item.
                            TypeId::ERROR
                        } else {
                            self.name_item(i);
                            self.types.adt(i)
                        }
                    }
                    ItemKind::Alias { ty, .. } => {
                        if let Some(s) = self.alias_state.get_mut(i.index()) {
                            if *s == 1 {
                                *s = 2;
                            }
                        }
                        if self.idx.is_generic(i) {
                            TypeId::ERROR
                        } else {
                            self.sub(ty)
                        }
                    }
                    ItemKind::Interface(_) => {
                        self.report(at, unsupported(Feature::Traits));
                        TypeId::ERROR
                    }
                    ItemKind::AssocType { .. } => {
                        self.report(at, unsupported(Feature::AssociatedTypes));
                        TypeId::ERROR
                    }
                    ItemKind::Err => TypeId::ERROR,
                    _ => {
                        self.report(at, DiagnosticKind::NotAType);
                        TypeId::ERROR
                    }
                },
                Def::Variant(v) => match self.hir.variant_owner(v) {
                    Some(sum) if !self.idx.is_generic(sum) => {
                        self.name_item(sum);
                        self.types.adt(sum)
                    }
                    _ => TypeId::ERROR,
                },
            },
            Res::Def(d) => self.types.foreign(d),
            Res::Prim(p) => TypeId::prim(p),
            Res::Extern(sym) => self.types.external(sym),
            Res::Local(b) => match self.hir.binder(b) {
                Some(binder) if binder.kind == hir_lang::BinderKind::TypeParam => {
                    self.types.name_binder(b, binder.name.sym);
                    self.types.param(b)
                }
                _ => {
                    self.report(at, DiagnosticKind::NotAType);
                    TypeId::ERROR
                }
            },
            Res::Unresolved => {
                self.report(NodeRef::Path(p), DiagnosticKind::Unresolved);
                TypeId::ERROR
            }
            Res::Err => TypeId::ERROR,
        })
    }

    // ------------------------------------------------- constant evaluation

    /// Evaluates an integer constant context: literals, paths to `const`
    /// items, and integer arithmetic, with checked `i128` arithmetic.
    /// `None` when the expression is not a compile-time integer (or
    /// overflows, or a constant depends on itself).
    pub(crate) fn const_eval(&mut self, root: ExprId) -> Result<Option<i128>, CheckError> {
        enum Task {
            Eval(ExprId),
            Apply(OpKind, usize),
            EndConst(ItemId),
        }
        let mut tasks = alloc::vec![Task::Eval(root)];
        let mut vals: Vec<Option<i128>> = Vec::new();
        while let Some(task) = tasks.pop() {
            self.meter.tick(1)?;
            match task {
                Task::Eval(e) => match *self.hir.expr(e) {
                    Expr::Lit(Lit::Int(l)) => {
                        let v = i128::from(l.value);
                        vals.push(Some(if l.negative { -v } else { v }));
                    }
                    Expr::Path(p) => {
                        let path = self.hir.path(p);
                        let item = (path.unresolved == 0)
                            .then(|| self.local_item(path.res))
                            .flatten();
                        match item.map(|i| (i, self.item_kind(i))) {
                            Some((i, ItemKind::Const { value: Some(v), .. })) => {
                                match self.const_state(i) {
                                    (CONST_SOME, v) => vals.push(Some(v)),
                                    (CONST_UNKNOWN, _) => {
                                        self.set_const(i, CONST_BUSY, 0);
                                        tasks.push(Task::EndConst(i));
                                        tasks.push(Task::Eval(v));
                                    }
                                    _ => vals.push(None),
                                }
                            }
                            _ => vals.push(None),
                        }
                    }
                    Expr::Op { op, args } => {
                        let args = self.hir.list(args);
                        if const_op(op.kind) && args.len() == op.kind.arity() {
                            tasks.push(Task::Apply(op.kind, args.len()));
                            tasks.extend(args.iter().rev().map(|&a| Task::Eval(a)));
                        } else {
                            vals.push(None);
                        }
                    }
                    Expr::Cast { expr, .. } => tasks.push(Task::Eval(expr)),
                    Expr::Block(b) if b.stmts.is_empty() && b.tail.is_some() => {
                        if let Some(t) = b.tail {
                            tasks.push(Task::Eval(t));
                        }
                    }
                    _ => vals.push(None),
                },
                Task::Apply(kind, n) => {
                    let at = vals.len().saturating_sub(n);
                    let args: Vec<Option<i128>> = vals.drain(at..).collect();
                    let a = args.first().copied().flatten();
                    let b = args.get(1).copied().flatten();
                    vals.push(apply(kind, a, b));
                }
                Task::EndConst(i) => {
                    let v = vals.last().copied().flatten();
                    match v {
                        Some(v) => self.set_const(i, CONST_SOME, v),
                        None => self.set_const(i, CONST_NONE, 0),
                    }
                }
            }
        }
        Ok(vals.pop().flatten())
    }

    fn const_state(&self, item: ItemId) -> (u8, i128) {
        self.const_memo
            .get(item.index())
            .copied()
            .unwrap_or((CONST_NONE, 0))
    }

    fn set_const(&mut self, item: ItemId, state: u8, v: i128) {
        if let Some(slot) = self.const_memo.get_mut(item.index()) {
            *slot = (state, v);
        }
    }

    // ---------------------------------------------------------- signatures

    /// The signature of a function item.
    pub(crate) fn sig(&mut self, item: ItemId) -> Result<Option<usize>, CheckError> {
        if let Some(&s) = self.sigs.get(item.index()) {
            if s != NONE {
                return Ok(Some(s as usize));
            }
        }
        let ItemKind::Fn(def) = self.item_kind(item) else {
            return Ok(None);
        };
        let self_ty = self.item_self(item);
        // Under `Dynamic`, annotations are run-time hints: nothing is
        // lowered, and every parameter is `any`.
        let dynamic = !self.profile.is_static();
        let mut params = Vec::new();
        let mut by_name = Vec::new();
        for (pos, &pid) in self.hir.list(def.params).iter().enumerate() {
            self.meter.tick(1)?;
            let param = *self.hir.param(pid);
            let name = self.pat_name(param.pat);
            let ty = match param.ty {
                _ if dynamic => TypeId::ANY,
                Some(t) => self.lower_ty(t, self_ty, true)?,
                None if param.kind == ParamKind::Receiver => self_ty.unwrap_or(TypeId::ERROR),
                None => {
                    self.report(NodeRef::Param(pid), DiagnosticKind::MissingAnnotation);
                    TypeId::ERROR
                }
            };
            if let Some(n) = name {
                if matches!(param.kind, ParamKind::Normal | ParamKind::NamedOnly) {
                    by_name.push((n, u32::try_from(pos).unwrap_or(NONE)));
                }
            }
            params.push(ParamInfo {
                kind: param.kind,
                name,
                ty,
                has_default: param.default.is_some(),
                by_ref: param.by_ref,
            });
        }
        by_name.sort_unstable();
        by_name.dedup_by_key(|(n, _)| *n);
        let ret = match def.ret {
            _ if dynamic => TypeId::ANY,
            Some(t) => self.lower_ty(t, self_ty, true)?,
            None => TypeId::UNIT,
        };
        let throws = match def.throws {
            Some(t) if !dynamic => Some(self.lower_ty(t, self_ty, true)?),
            _ => None,
        };
        let index = self.sig_arena.len();
        self.sig_arena.push(Sig {
            params,
            ret,
            effects: def.effects,
            throws,
            by_name,
        });
        if let Some(slot) = self.sigs.get_mut(item.index()) {
            *slot = u32::try_from(index).unwrap_or(NONE);
        }
        Ok(Some(index))
    }

    /// The name a parameter pattern binds, if it is a plain binding.
    pub(crate) fn pat_name(&self, pat: hir_lang::PatId) -> Option<Symbol> {
        match *self.hir.pat(pat) {
            Pat::Bind { binder, .. } | Pat::Ident { binder, .. } => {
                self.hir.binder(binder).map(|b| b.name.sym)
            }
            _ => None,
        }
    }

    /// A function value's type: its positional parameters and result.
    pub(crate) fn fn_value_type(&mut self, sig: usize) -> TypeId {
        let Some(s) = self.sig_arena.get(sig) else {
            return TypeId::ERROR;
        };
        let params: Vec<TypeId> = s
            .params
            .iter()
            .filter(|p| {
                matches!(
                    p.kind,
                    ParamKind::Receiver | ParamKind::PositionalOnly | ParamKind::Normal
                )
            })
            .map(|p| p.ty)
            .collect();
        let (ret, effects) = (s.ret, s.effects);
        self.types.func(&params, ret, effects)
    }

    /// What calling a function with these effects produces.
    pub(crate) fn call_result(&mut self, ret: TypeId, effects: Effects) -> TypeId {
        let is_async = effects.contains(Effects::ASYNC);
        if effects.contains(Effects::YIELD) {
            self.types.generator(ret, is_async)
        } else if is_async {
            self.types.awaitable(ret)
        } else {
            ret
        }
    }

    /// A declared field's type.
    pub(crate) fn field_type(&mut self, f: FieldId) -> Result<TypeId, CheckError> {
        if let Some(&v) = self.field_memo.get(f.index()) {
            if v != NONE {
                return Ok(TypeId::from_raw(v));
            }
        }
        let owner = self
            .idx
            .field_owner
            .get(f.index())
            .copied()
            .filter(|&o| o != NONE)
            .and_then(|o| ItemId::from_index(o as usize));
        let self_ty = owner.map(|o| self.types.adt(o));
        let t = match self.hir.field(f).ty {
            Some(ty) => self.lower_ty(ty, self_ty, true)?,
            None => {
                self.report(NodeRef::Field(f), DiagnosticKind::MissingAnnotation);
                TypeId::ERROR
            }
        };
        if let Some(slot) = self.field_memo.get_mut(f.index()) {
            *slot = t.raw();
        }
        Ok(t)
    }

    /// The declared type of a `const` or `global` item.
    pub(crate) fn decl_type(&mut self, item: ItemId) -> Result<TypeId, CheckError> {
        if let Some(&v) = self.decl_memo.get(item.index()) {
            if v != NONE {
                return Ok(TypeId::from_raw(v));
            }
        }
        let ty = match self.item_kind(item) {
            ItemKind::Const { ty, .. } | ItemKind::Global { ty, .. } => ty,
            _ => return Ok(TypeId::ERROR),
        };
        let self_ty = self.item_self(item);
        let t = match ty {
            Some(ty) => self.lower_ty(ty, self_ty, true)?,
            None => {
                self.report(NodeRef::Item(item), DiagnosticKind::MissingAnnotation);
                TypeId::ERROR
            }
        };
        if let Some(slot) = self.decl_memo.get_mut(item.index()) {
            *slot = t.raw();
        }
        Ok(t)
    }

    /// The nominal type of a record, sum, or class item (`{error}` when the
    /// item is generic, which is reported at the item).
    pub(crate) fn adt_type(&mut self, item: ItemId) -> TypeId {
        if self.idx.is_generic(item) {
            return TypeId::ERROR;
        }
        self.name_item(item);
        self.types.adt(item)
    }
}

/// The type children of a type node, in order.
fn ty_children(node: &Ty, hir: &hir_lang::Hir, out: &mut Vec<TyId>) {
    match *node {
        Ty::Tuple(list) => out.extend_from_slice(hir.list(list)),
        Ty::Array { elem, .. } => out.push(elem),
        Ty::Slice(t) | Ty::Ref { inner: t, .. } | Ty::Ptr { inner: t, .. } | Ty::Nullable(t) => {
            out.push(t);
        }
        Ty::Fn { params, ret, .. } => {
            out.extend_from_slice(hir.list(params));
            out.push(ret);
        }
        _ => {}
    }
}

fn const_op(kind: OpKind) -> bool {
    matches!(
        kind,
        OpKind::Add
            | OpKind::Sub
            | OpKind::Mul
            | OpKind::Div
            | OpKind::Rem
            | OpKind::Neg
            | OpKind::Shl
            | OpKind::Shr
            | OpKind::And
            | OpKind::Or
            | OpKind::Xor
            | OpKind::Min
            | OpKind::Max
    )
}

fn apply(kind: OpKind, a: Option<i128>, b: Option<i128>) -> Option<i128> {
    let a = a?;
    match kind {
        OpKind::Neg => a.checked_neg(),
        OpKind::Add => a.checked_add(b?),
        OpKind::Sub => a.checked_sub(b?),
        OpKind::Mul => a.checked_mul(b?),
        OpKind::Div => a.checked_div(b?),
        OpKind::Rem => a.checked_rem(b?),
        OpKind::Shl => u32::try_from(b?)
            .ok()
            .filter(|&s| s < 64)
            .and_then(|s| a.checked_mul(1i128 << s)),
        OpKind::Shr => u32::try_from(b?).ok().and_then(|s| a.checked_shr(s)),
        OpKind::And => Some(a & b?),
        OpKind::Or => Some(a | b?),
        OpKind::Xor => Some(a ^ b?),
        OpKind::Min => Some(a.min(b?)),
        OpKind::Max => Some(a.max(b?)),
        _ => None,
    }
}
