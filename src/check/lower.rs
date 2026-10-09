//! Annotations to types, constant evaluation, and function signatures.
//!
//! Every lowering is memoized per HIR node (a type node sits in exactly one
//! context, so its meaning is fixed) and iterative: a type nested 100,000
//! deep lowers on an explicit stack, including through generic arguments
//! (`Vec<Vec<...>>`), which are children of their path.

use alloc::vec::Vec;

use hir_lang::{
    Bound, Def, Effects, Expr, ExprId, FieldId, GenericArg, ItemId, ItemKind, Lit, NodeRef, OpKind,
    ParamKind, Pat, PathId, PathRoot, Res, Symbol, Ty, TyId,
};

use super::Ctx;
use crate::{
    diag::{DiagnosticKind, Feature},
    error::{CheckError, Limit},
    profile::Polymorphism,
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
        // Lowering re-enters itself only through defaults of generic
        // parameters and associated types defined through other items; a
        // cycle among those reaches this cap instead of the call stack's.
        self.lower_depth = self.lower_depth.saturating_add(1);
        let r = if self.lower_depth > self.nest_limit() {
            Err(CheckError::BudgetExceeded {
                limit: Limit::TraitDepth,
            })
        } else {
            self.lower_ty_inner(root, self_ty, sig)
        };
        self.lower_depth = self.lower_depth.saturating_sub(1);
        r
    }

    fn lower_ty_inner(
        &mut self,
        root: TyId,
        self_ty: Option<TypeId>,
        sig: bool,
    ) -> Result<TypeId, CheckError> {
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
                                // The use's generic arguments, then the body
                                // (in the alias's own placeholders).
                                kids.clear();
                                ty_children(&node, self.hir, &mut kids);
                                for &k in kids.iter().rev() {
                                    if self.memo_ty(k).is_none() {
                                        stack.push((k, false, self_ty, sig));
                                    }
                                }
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
            Ty::Path(p) => self.path_ty(id, p, self_ty, sig)?,
            Ty::Tuple(list) => {
                let elems: Vec<TypeId> = self.hir.list(list).iter().map(|&t| self.sub(t)).collect();
                self.types.tuple(&elems)
            }
            Ty::Union(list) => {
                let members: Vec<TypeId> =
                    self.hir.list(list).iter().map(|&t| self.sub(t)).collect();
                self.types.union(&members)
            }
            Ty::Intersection(list) => {
                let members: Vec<TypeId> =
                    self.hir.list(list).iter().map(|&t| self.sub(t)).collect();
                self.types.intersection(&members)
            }
            Ty::Array { elem, len } => {
                let elem = self.sub(elem);
                if let Some(b) = self.const_param_of(len) {
                    let p = self.types.param(b);
                    return Ok(self.types.array_of(elem, p));
                }
                match self.const_eval(len)? {
                    Some(n) if n >= 0 && i64::try_from(n).is_ok() => {
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
            Ty::Object(bounds) => {
                let bounds: Vec<TyId> = self
                    .hir
                    .list(bounds)
                    .iter()
                    .filter_map(|b| match *b {
                        Bound::Ty(t) => Some(t),
                        Bound::Region(_) => None,
                    })
                    .collect();
                self.dyn_type(&bounds, at)?
            }
            Ty::Impl(_) => match self.impl_ty_owner(id) {
                Some((f, true)) => {
                    let params = self.placeholders(f);
                    self.types.opaque(id, &params)
                }
                Some((_, false)) => self.types.impl_param(id),
                None => {
                    self.report(at, DiagnosticKind::ImplTraitPosition);
                    TypeId::ERROR
                }
            },
            Ty::SelfTy => match self_ty.or_else(|| self.ctx_self()) {
                Some(t) => t,
                None => {
                    self.report(at, DiagnosticKind::NotAType);
                    TypeId::ERROR
                }
            },
            Ty::Err => TypeId::ERROR,
        })
    }

    /// `Self` in the item whose annotations are being lowered.
    fn ctx_self(&self) -> Option<TypeId> {
        let item = self.env_item()?;
        match self.item_kind(item) {
            ItemKind::Impl(_) | ItemKind::Class(_) | ItemKind::Interface(_) => self
                .idx
                .self_ty
                .get(item.index())
                .copied()
                .filter(|&v| v != NONE)
                .map(TypeId::from_raw),
            _ => self.item_self(item),
        }
    }

    /// A `dyn` type over the interfaces `bounds` names: each interface
    /// reference carries the values of its associated types, which must all
    /// be bound.
    fn dyn_type(&mut self, bounds: &[TyId], at: NodeRef) -> Result<TypeId, CheckError> {
        let mut traits = Vec::new();
        for &b in bounds {
            let Some(lb) = self.lower_bound(b, TypeId::ERROR)? else {
                return Ok(TypeId::ERROR);
            };
            let Some(iface) = self.trait_item(lb.tr) else {
                continue;
            };
            let mut args = self.trait_args(lb.tr);
            for assoc in self.assoc_types(iface) {
                match lb.bindings.iter().find(|&&(a, _)| a == assoc) {
                    Some(&(_, v)) => args.push(v),
                    None => {
                        if let Some(name) = self.item_symbol(assoc) {
                            self.report(at, DiagnosticKind::MissingAssocBinding { name });
                        }
                        args.push(TypeId::ERROR);
                    }
                }
            }
            traits.push(self.types.trait_ref(iface, &args));
        }
        Ok(self.types.dyn_of(&traits))
    }

    /// The constant parameter an array length names, if it names one.
    fn const_param_of(&self, len: ExprId) -> Option<hir_lang::BinderId> {
        let Expr::Path(p) = *self.hir.expr(len) else {
            return None;
        };
        let path = self.hir.path(p);
        match (path.unresolved, path.res) {
            (0, Res::Local(b))
                if self
                    .hir
                    .binder(b)
                    .is_some_and(|x| x.kind == hir_lang::BinderKind::ConstParam) =>
            {
                Some(b)
            }
            _ => None,
        }
    }

    /// The alias item a type path names, with its aliased type.
    fn alias_target(&self, p: PathId) -> Option<(ItemId, TyId)> {
        let path = self.hir.path(p);
        if path.unresolved != 0 || path.qself.is_some() {
            return None;
        }
        let item = self.local_item(path.res)?;
        match self.item_kind(item) {
            ItemKind::Alias { ty, .. } => Some((item, ty)),
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

    /// The positional generic arguments written on the last segment of
    /// `p`, lowered (they are children of the path, so already memoized).
    fn segment_args(&mut self, p: PathId, sig: bool) -> Result<Vec<TypeId>, CheckError> {
        let path = *self.hir.path(p);
        let Some(last) = self.hir.list(path.segments).last().copied() else {
            return Ok(Vec::new());
        };
        let written = self.written_args(last.args);
        let mut out = Vec::with_capacity(written.len());
        for a in written {
            out.push(self.lower_arg(a, sig)?);
        }
        Ok(out)
    }

    /// The type a path in a type annotation names.
    fn path_ty(
        &mut self,
        ty: TyId,
        p: PathId,
        self_ty: Option<TypeId>,
        sig: bool,
    ) -> Result<TypeId, CheckError> {
        let at = NodeRef::Ty(ty);
        let path = *self.hir.path(p);
        let segments = self.hir.list(path.segments);
        let last = segments.last().copied();
        // `<T as Iface>::Name` and `<T>::Name`.
        if let Some(q) = path.qself {
            let Some(last) = last else {
                return Ok(TypeId::ERROR);
            };
            let qt = self.sub(q.ty);
            if q.trait_len == 0 {
                return self.assoc_type_of(qt, last.name.sym, at);
            }
            let Some(iface) = self
                .local_item(path.res)
                .filter(|&i| matches!(self.item_kind(i), ItemKind::Interface(_)))
            else {
                if path.res != Res::Err {
                    self.report(at, DiagnosticKind::NotAnInterface);
                }
                return Ok(TypeId::ERROR);
            };
            let trait_seg = segments
                .get(q.trait_len.saturating_sub(1) as usize)
                .copied();
            let written = trait_seg.map_or_else(Vec::new, |s| self.written_args(s.args));
            let args = self.fill_args(iface, &written, at, sig, Some(qt))?;
            return match self.assoc_named(iface, last.name.sym)? {
                Some((decl, assoc)) => {
                    let mut pargs = alloc::vec![qt];
                    pargs.extend(args);
                    self.name_item(assoc);
                    let proj = self.types.projection(decl, assoc, &pargs);
                    self.normalize(proj, at)
                }
                None => {
                    self.report(
                        at,
                        DiagnosticKind::NoAssocType {
                            name: last.name.sym,
                        },
                    );
                    Ok(TypeId::ERROR)
                }
            };
        }
        if path.unresolved > 1 {
            if path.res != Res::Err {
                self.report(
                    at,
                    DiagnosticKind::Unsupported {
                        feature: Feature::LongAssocPaths,
                    },
                );
            }
            return Ok(TypeId::ERROR);
        }
        if path.unresolved == 1 {
            // `T::Item`, `Self::Item`: an associated type by type.
            if path.res == Res::Err {
                return Ok(TypeId::ERROR);
            }
            let Some(last) = last else {
                return Ok(TypeId::ERROR);
            };
            let prefix = if segments.len() == 1 {
                match path.root {
                    PathRoot::SelfType | PathRoot::StaticType => {
                        self_ty.or_else(|| self.ctx_self())
                    }
                    _ => None,
                }
            } else {
                self.prefix_res_type(path.res, at)?
            };
            return match prefix {
                Some(t) => self.assoc_type_of(t, last.name.sym, at),
                None => {
                    self.report(at, DiagnosticKind::NotAType);
                    Ok(TypeId::ERROR)
                }
            };
        }
        let written = match last {
            Some(seg) => self.written_args(seg.args),
            None => Vec::new(),
        };
        Ok(match path.res {
            Res::Def(d) if d.unit() == self.hir.unit() => match d.def() {
                Def::Item(i) => match self.item_kind(i) {
                    ItemKind::Record(_) | ItemKind::Sum(_) | ItemKind::Class(_) => {
                        self.name_item(i);
                        let args = self.fill_args(i, &written, at, sig, None)?;
                        // A written instance must satisfy the item's bounds
                        // (checked in the scope of the annotation).
                        self.push_bounds(i, &args, at)?;
                        self.types.adt_with(i, &args)
                    }
                    ItemKind::Alias { ty: body, .. } => {
                        if let Some(s) = self.alias_state.get_mut(i.index()) {
                            if *s == 1 {
                                *s = 2;
                            }
                        }
                        let body_ty = self.sub(body);
                        let args = self.fill_args(i, &written, at, sig, None)?;
                        let params = self.own_params(i);
                        self.subst(body_ty, &params, &args)?
                    }
                    ItemKind::Interface(_) => {
                        if self.profile.polymorphism == Polymorphism::Interfaces {
                            self.dyn_type(&[ty], at)?
                        } else {
                            self.report(at, DiagnosticKind::InterfaceAsType);
                            TypeId::ERROR
                        }
                    }
                    ItemKind::AssocType { .. } => {
                        // A bare associated-type name inside its interface.
                        match self.idx.owner_of(i) {
                            Some(iface) => {
                                let s = self.types.self_of(iface);
                                let mut pargs = alloc::vec![s];
                                pargs.extend(self.own_params(iface));
                                self.name_item(i);
                                let proj = self.types.projection(iface, i, &pargs);
                                self.normalize(proj, at)?
                            }
                            None => TypeId::ERROR,
                        }
                    }
                    ItemKind::Err => TypeId::ERROR,
                    _ => {
                        self.report(at, DiagnosticKind::NotAType);
                        TypeId::ERROR
                    }
                },
                Def::Variant(v) => match self.hir.variant_owner(v) {
                    Some(sum) => {
                        self.name_item(sum);
                        let args = self.fill_args(sum, &written, at, sig, None)?;
                        self.types.adt_with(sum, &args)
                    }
                    None => TypeId::ERROR,
                },
            },
            Res::Def(d) => {
                let args = self.segment_args(p, sig)?;
                self.types.foreign_with(d, &args)
            }
            Res::Prim(p) => TypeId::prim(p),
            Res::Extern(sym) => {
                let args = self.segment_args(p, sig)?;
                self.types.external_with(sym, &args)
            }
            Res::Local(b) => match self.hir.binder(b) {
                Some(binder) if binder.kind == hir_lang::BinderKind::TypeParam => {
                    self.types.name_binder(b, binder.name.sym);
                    if !written.is_empty() {
                        self.report(
                            at,
                            DiagnosticKind::GenericArity {
                                expected: 0,
                                found: u32::try_from(written.len()).unwrap_or(u32::MAX),
                            },
                        );
                    }
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

    /// The type a resolved path prefix names (`T` of `T::Item`, `Vec` of
    /// `Vec::Item`).
    fn prefix_res_type(&mut self, res: Res, at: NodeRef) -> Result<Option<TypeId>, CheckError> {
        Ok(match res {
            Res::Local(b) => match self.hir.binder(b) {
                Some(x) if x.kind == hir_lang::BinderKind::TypeParam => {
                    self.types.name_binder(b, x.name.sym);
                    Some(self.types.param(b))
                }
                _ => None,
            },
            Res::Def(d) if d.unit() == self.hir.unit() => match d.def() {
                Def::Item(i) => match self.item_kind(i) {
                    ItemKind::Record(_) | ItemKind::Sum(_) | ItemKind::Class(_) => {
                        Some(self.adt_fresh(i))
                    }
                    ItemKind::Alias { ty, .. } => {
                        let saved = self.lower_ctx.replace(i);
                        let t = self.lower_ty(ty, None, true);
                        self.lower_ctx = saved;
                        Some(t?)
                    }
                    _ => {
                        self.report(at, DiagnosticKind::NotAType);
                        None
                    }
                },
                Def::Variant(_) => None,
            },
            Res::Def(d) => Some(self.types.foreign(d)),
            Res::Prim(p) => Some(TypeId::prim(p)),
            Res::Extern(s) => Some(self.types.external(s)),
            _ => None,
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
        let saved = self.lower_ctx.replace(item);
        let r = self.sig_inner(item, def);
        self.lower_ctx = saved;
        r
    }

    fn sig_inner(
        &mut self,
        item: ItemId,
        def: hir_lang::FnDef,
    ) -> Result<Option<usize>, CheckError> {
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
        let self_ty = owner.map(|o| {
            if self.profile.is_static() {
                self.adt_identity(o)
            } else {
                self.types.adt(o)
            }
        });
        let saved = core::mem::replace(&mut self.lower_ctx, owner);
        let t = match self.hir.field(f).ty {
            Some(ty) => self.lower_ty(ty, self_ty, true),
            None => {
                self.report(NodeRef::Field(f), DiagnosticKind::MissingAnnotation);
                Ok(TypeId::ERROR)
            }
        };
        self.lower_ctx = saved;
        let t = t?;
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
        let saved = self.lower_ctx.replace(item);
        let t = match ty {
            Some(ty) => self.lower_ty(ty, self_ty, true),
            None => {
                self.report(NodeRef::Item(item), DiagnosticKind::MissingAnnotation);
                Ok(TypeId::ERROR)
            }
        };
        self.lower_ctx = saved;
        let t = t?;
        if let Some(slot) = self.decl_memo.get_mut(item.index()) {
            *slot = t.raw();
        }
        Ok(t)
    }

    /// The nominal type of a record, sum, or class item at a use: fresh
    /// arguments for a generic item.
    pub(crate) fn adt_type(&mut self, item: ItemId) -> TypeId {
        if !self.profile.is_static() {
            self.name_item(item);
            return self.types.adt(item);
        }
        self.adt_fresh(item)
    }
}

/// The type children of a type node lowered before it, in order: elements,
/// members, parameters, and a path's qualified self and generic type
/// arguments. (Interface paths in `dyn` and `impl` bounds are not types;
/// they are lowered as bounds.)
fn ty_children(node: &Ty, hir: &hir_lang::Hir, out: &mut Vec<TyId>) {
    match *node {
        Ty::Tuple(list) | Ty::Union(list) | Ty::Intersection(list) => {
            out.extend_from_slice(hir.list(list));
        }
        Ty::Array { elem, .. } => out.push(elem),
        Ty::Slice(t) | Ty::Ref { inner: t, .. } | Ty::Ptr { inner: t, .. } | Ty::Nullable(t) => {
            out.push(t);
        }
        Ty::Fn { params, ret, .. } => {
            out.extend_from_slice(hir.list(params));
            out.push(ret);
        }
        Ty::Path(p) => {
            let path = hir.path(p);
            if let Some(q) = path.qself {
                out.push(q.ty);
            }
            for seg in hir.list(path.segments) {
                for a in hir.list(seg.args) {
                    if let GenericArg::Ty(t) | GenericArg::Binding { ty: t, .. } = *a {
                        out.push(t);
                    }
                }
            }
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
