//! The checker: context, driver, and the public `Checker`.
//!
//! Layout:
//! - [`index`]: one pre-pass over the tree (live nodes, item owners, method,
//!   field, and variant tables, class bases).
//! - [`lower`]: annotations to types, constant evaluation, signatures.
//! - [`engine`]: the iterative expression and statement checker.
//! - [`pat`], [`call`], [`ops`], [`coerce`]: pattern, argument, operation, and
//!   coercion rules.
//! - [`dynamic`]: the `Dynamic` discipline.
//! - [`finalize`]: literal defaults, inference failures, and resolving every
//!   recorded type.

mod call;
mod coerce;
mod dynamic;
mod engine;
mod finalize;
mod index;
mod items;
mod lower;
mod ops;
mod pat;
mod paths;

use alloc::vec::Vec;

use hir_lang::{
    BinderId, Def, DefId, ExprId, Hir, IdKind, IntLit, ItemId, NodeRef, PatId, PathId, Prim, Symbol,
};

use crate::{
    diag::{Diagnostic, DiagnosticKind},
    error::{Budget, CheckError, Meter},
    infer::{Infer, UnifyCfg},
    profile::{Profile, RecordTyping},
    typed::{Coercion, NONE, Typed},
    types::{Field, Tag, TypeId, Types},
};

pub(crate) use index::Index;

/// The configured path: declare host types, set a budget, then check.
///
/// [`check`](crate::check) is this with no declarations and the default
/// budget scaled to the HIR.
///
/// # Examples
///
/// ```
/// use hir_lang::{Builder, Effects, Name, Prim, Res};
/// use intern_lang::Interner;
/// use typeck_lang::{Checker, Profile, TypeId};
///
/// let mut names = Interner::new();
/// let print = names.intern("print");
/// let mut b = Builder::new();
/// // fn main() { print("hi") }   with `print` bound by the host.
/// let path = b.resolved_path(Name::new(print), hir_lang::Ns::Value, Res::Extern(print));
/// let callee = b.expr(hir_lang::Expr::Path(path));
/// let hi = b.str_lit("hi");
/// let call = b.call(callee, &[hi]);
/// let s = b.expr_stmt(call);
/// let body = b.block(&[s], None);
/// let main = b.func(Name::new(names.intern("main")), &[], body);
/// let root = b.module(None, &[main]);
/// let hir = b.finish(root)?;
///
/// let mut checker = Checker::new(&hir, Profile::static_explicit());
/// let print_ty = checker.types_mut().func(&[TypeId::prim(Prim::Str)], TypeId::UNIT, Effects::NONE);
/// checker.declare_extern(print, print_ty);
/// let typed = checker.check().unwrap();
/// assert!(typed.is_ok());
/// assert_eq!(typed.expr(call), Some(TypeId::UNIT));
/// # Ok::<(), hir_lang::HirError>(())
/// ```
#[derive(Debug)]
pub struct Checker<'h> {
    hir: &'h Hir,
    profile: Profile,
    budget: Budget,
    types: Types,
    host: Host,
}

/// Declarations the host makes about names the unit does not define.
#[derive(Debug, Default)]
pub(crate) struct Host {
    /// Value types of `Res::Extern` symbols.
    pub(crate) externs: Vec<(Symbol, TypeId)>,
    /// Value types of other units' definitions.
    pub(crate) foreign: Vec<(DefId, TypeId)>,
    /// Types of `Intrinsic::Named` intrinsics (function types).
    pub(crate) intrinsics: Vec<(Symbol, TypeId)>,
    /// Methods and associated items of host types: (owner, name, type).
    pub(crate) members: Vec<(TypeId, Symbol, TypeId)>,
}

fn upsert<K: Ord + Copy, V>(table: &mut Vec<(K, V)>, key: K, value: V) {
    match table.binary_search_by(|(k, _)| k.cmp(&key)) {
        Ok(i) => {
            if let Some(slot) = table.get_mut(i) {
                slot.1 = value;
            }
        }
        Err(i) => table.insert(i, (key, value)),
    }
}

fn find<K: Ord + Copy, V: Copy>(table: &[(K, V)], key: K) -> Option<V> {
    table
        .binary_search_by(|(k, _)| k.cmp(&key))
        .ok()
        .and_then(|i| table.get(i))
        .map(|&(_, v)| v)
}

impl<'h> Checker<'h> {
    /// A checker for `hir` under `profile`, with [`Budget::for_hir`].
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Builder, Effects, Expr, Name, Ns, Prim, Res};
    /// use intern_lang::Interner;
    /// use typeck_lang::{Checker, Profile, TypeId};
    ///
    /// let mut names = Interner::new();
    /// let pi = names.intern("pi");
    /// let mut b = Builder::new();
    /// // fn main() { pi; }   with `pi` bound by the host
    /// let path = b.resolved_path(Name::new(pi), Ns::Value, Res::Extern(pi));
    /// let use_pi = b.expr(Expr::Path(path));
    /// let s = b.expr_stmt(use_pi);
    /// let body = b.block(&[s], None);
    /// let main = b.func(Name::new(names.intern("main")), &[], body);
    /// let root = b.module(None, &[main]);
    /// let hir = b.finish(root)?;
    ///
    /// let mut checker = Checker::new(&hir, Profile::static_explicit());
    /// checker.declare_extern(pi, TypeId::prim(Prim::F64));
    /// let typed = checker.check().unwrap();
    /// assert!(typed.is_ok());
    /// assert_eq!(typed.expr(use_pi), Some(TypeId::prim(Prim::F64)));
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    #[must_use]
    pub fn new(hir: &'h Hir, profile: Profile) -> Self {
        Self {
            hir,
            profile,
            budget: Budget::for_hir(hir),
            types: Types::new(),
            host: Host::default(),
        }
    }

    /// Replaces the budget.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::Builder;
    /// use typeck_lang::{Budget, CheckError, Checker, Limit, Profile};
    ///
    /// let mut b = Builder::new();
    /// let one = b.int(1);
    /// let body = b.block(&[], Some(one));
    /// let f = b.func(hir_lang::Name::new(intern_lang::Interner::new().intern("f")), &[], body);
    /// let root = b.module(None, &[f]);
    /// let hir = b.finish(root)?;
    /// let mut checker = Checker::new(&hir, Profile::static_explicit());
    /// checker.set_budget(Budget { steps: 2, ..Budget::default() });
    /// assert_eq!(checker.check(), Err(CheckError::BudgetExceeded { limit: Limit::Steps }));
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    pub fn set_budget(&mut self, budget: Budget) -> &mut Self {
        self.budget = budget;
        self
    }

    /// The type store, to build the types of host declarations.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Builder, Effects, Expr, Name, Ns, Prim, Res};
    /// use intern_lang::Interner;
    /// use typeck_lang::{Checker, Profile, TypeId};
    ///
    /// let mut names = Interner::new();
    /// let pi = names.intern("pi");
    /// let mut b = Builder::new();
    /// // fn main() { pi; }   with `pi` bound by the host
    /// let path = b.resolved_path(Name::new(pi), Ns::Value, Res::Extern(pi));
    /// let use_pi = b.expr(Expr::Path(path));
    /// let s = b.expr_stmt(use_pi);
    /// let body = b.block(&[s], None);
    /// let main = b.func(Name::new(names.intern("main")), &[], body);
    /// let root = b.module(None, &[main]);
    /// let hir = b.finish(root)?;
    ///
    /// let mut checker = Checker::new(&hir, Profile::static_explicit());
    /// // A host type built in the checker's own store.
    /// let f64_ty = TypeId::prim(Prim::F64);
    /// let wrapped = checker.types_mut().tuple(&[f64_ty]);
    /// assert_ne!(wrapped, f64_ty);
    /// checker.declare_extern(pi, f64_ty);
    /// let typed = checker.check().unwrap();
    /// assert!(typed.is_ok());
    /// assert_eq!(typed.expr(use_pi), Some(TypeId::prim(Prim::F64)));
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    pub fn types_mut(&mut self) -> &mut Types {
        &mut self.types
    }

    /// Declares the value type of a host symbol (`Res::Extern(name)` in a
    /// value path). A later declaration of the same name replaces it.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Builder, Effects, Expr, Name, Ns, Prim, Res};
    /// use intern_lang::Interner;
    /// use typeck_lang::{Checker, Profile, TypeId};
    ///
    /// let mut names = Interner::new();
    /// let pi = names.intern("pi");
    /// let mut b = Builder::new();
    /// // fn main() { pi; }   with `pi` bound by the host
    /// let path = b.resolved_path(Name::new(pi), Ns::Value, Res::Extern(pi));
    /// let use_pi = b.expr(Expr::Path(path));
    /// let s = b.expr_stmt(use_pi);
    /// let body = b.block(&[s], None);
    /// let main = b.func(Name::new(names.intern("main")), &[], body);
    /// let root = b.module(None, &[main]);
    /// let hir = b.finish(root)?;
    ///
    /// let mut checker = Checker::new(&hir, Profile::static_explicit());
    /// checker.declare_extern(pi, TypeId::prim(Prim::F64));
    /// let typed = checker.check().unwrap();
    /// assert!(typed.is_ok());
    /// assert_eq!(typed.expr(use_pi), Some(TypeId::prim(Prim::F64)));
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    pub fn declare_extern(&mut self, name: Symbol, ty: TypeId) -> &mut Self {
        upsert(&mut self.host.externs, name, ty);
        self
    }

    /// Declares the value type of another unit's definition (a value path
    /// resolved to a `DefId` of another unit).
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Builder, Def, DefId, ItemId, UnitId};
    /// use typeck_lang::{Checker, Profile, TypeId};
    ///
    /// let mut b = Builder::new();
    /// let root = b.module(None, &[]);
    /// let hir = b.finish(root)?;
    /// let other = DefId::foreign(UnitId::new(7), Def::Item(ItemId::from_index(0).unwrap()));
    /// let mut checker = Checker::new(&hir, Profile::static_explicit());
    /// checker.declare_foreign(other, TypeId::UNIT);
    /// assert!(checker.check().unwrap().is_ok());
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    pub fn declare_foreign(&mut self, def: DefId, ty: TypeId) -> &mut Self {
        upsert(&mut self.host.foreign, def, ty);
        self
    }

    /// Declares the function type of a named intrinsic
    /// (`Intrinsic::Named(name)`).
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Builder, Effects, Prim};
    /// use intern_lang::Interner;
    /// use typeck_lang::{Checker, Profile, TypeId};
    ///
    /// let mut names = Interner::new();
    /// let mut b = Builder::new();
    /// let root = b.module(None, &[]);
    /// let hir = b.finish(root)?;
    /// let mut checker = Checker::new(&hir, Profile::static_explicit());
    /// let ty = checker.types_mut().func(&[], TypeId::prim(Prim::U64), Effects::NONE);
    /// checker.declare_intrinsic(names.intern("rdtsc"), ty);
    /// assert!(checker.check().is_ok());
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    pub fn declare_intrinsic(&mut self, name: Symbol, ty: TypeId) -> &mut Self {
        upsert(&mut self.host.intrinsics, name, ty);
        self
    }

    /// Declares a method or associated item of a type (typically a host
    /// type such as `types_mut().external(vec)`): `owner::name` in a path,
    /// and `value.name(..)` in a method call when `ty` is a function whose
    /// first parameter is the receiver.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Builder, Effects, Prim};
    /// use intern_lang::Interner;
    /// use typeck_lang::{Checker, Profile, TypeId};
    ///
    /// let mut names = Interner::new();
    /// let vec = names.intern("Vec");
    /// let mut b = Builder::new();
    /// let root = b.module(None, &[]);
    /// let hir = b.finish(root)?;
    /// let mut checker = Checker::new(&hir, Profile::static_explicit());
    /// let vec_ty = checker.types_mut().external(vec);
    /// let len = checker.types_mut().func(&[vec_ty], TypeId::prim(Prim::Usize), Effects::NONE);
    /// checker.declare_member(vec_ty, names.intern("len"), len);
    /// assert!(checker.check().is_ok());
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    pub fn declare_member(&mut self, owner: TypeId, name: Symbol, ty: TypeId) -> &mut Self {
        let key = (owner, name);
        match self
            .host
            .members
            .binary_search_by(|&(o, n, _)| (o, n).cmp(&key))
        {
            Ok(i) => {
                if let Some(slot) = self.host.members.get_mut(i) {
                    slot.2 = ty;
                }
            }
            Err(i) => self.host.members.insert(i, (owner, name, ty)),
        }
        self
    }

    /// Runs the check.
    ///
    /// # Errors
    ///
    /// [`CheckError::NotImplemented`] for a discipline this version does not
    /// implement, [`CheckError::InvalidProfile`] for inconsistent literal
    /// defaults, and [`CheckError::BudgetExceeded`] when the budget runs out.
    /// Type errors in the program are diagnostics in the `Ok` result.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Builder, Effects, Expr, Name, Ns, Prim, Res};
    /// use intern_lang::Interner;
    /// use typeck_lang::{Checker, Profile, TypeId};
    ///
    /// let mut names = Interner::new();
    /// let pi = names.intern("pi");
    /// let mut b = Builder::new();
    /// // fn main() { pi; }   with `pi` bound by the host
    /// let path = b.resolved_path(Name::new(pi), Ns::Value, Res::Extern(pi));
    /// let use_pi = b.expr(Expr::Path(path));
    /// let s = b.expr_stmt(use_pi);
    /// let body = b.block(&[s], None);
    /// let main = b.func(Name::new(names.intern("main")), &[], body);
    /// let root = b.module(None, &[main]);
    /// let hir = b.finish(root)?;
    ///
    /// let mut checker = Checker::new(&hir, Profile::static_explicit());
    /// checker.declare_extern(pi, TypeId::prim(Prim::F64));
    /// let typed = checker.check().unwrap();
    /// assert!(typed.is_ok());
    /// assert_eq!(typed.expr(use_pi), Some(TypeId::prim(Prim::F64)));
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    pub fn check(self) -> Result<Typed, CheckError> {
        let profile = self.profile;
        if !profile.discipline.is_implemented() {
            return Err(CheckError::NotImplemented {
                discipline: profile.discipline,
            });
        }
        if !profile.default_int.is_int() || !profile.default_float.is_float() {
            return Err(CheckError::InvalidProfile);
        }
        let mut cx = Ctx::new(self.hir, profile, self.budget, self.types, self.host);
        cx.meter.tick(1)?;
        cx.build_index()?;
        if profile.is_static() {
            cx.check_static()?;
        } else {
            cx.check_dynamic()?;
        }
        cx.into_typed()
    }
}

/// A function or closure being checked.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Frame {
    /// What `return` values must be.
    pub(crate) ret: TypeId,
    /// The declared thrown type, if any.
    pub(crate) throws: Option<TypeId>,
    /// What `yield` values must be, in a generator.
    pub(crate) yields: Option<TypeId>,
}

/// A loop or labelled block that `break` can target.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Target {
    /// The join of the break values so far.
    pub(crate) result: Option<TypeId>,
    /// Whether this is a loop (unlabelled `break` targets the innermost one).
    pub(crate) is_loop: bool,
}

/// The shared state of one check.
pub(crate) struct Ctx<'h> {
    pub(crate) hir: &'h Hir,
    pub(crate) profile: Profile,
    pub(crate) types: Types,
    pub(crate) infer: Infer,
    pub(crate) meter: Meter,
    pub(crate) host: Host,
    pub(crate) idx: Index,

    // Output side tables (dense, by HIR index).
    pub(crate) expr_ty: Vec<u32>,
    pub(crate) pat_ty: Vec<u32>,
    pub(crate) binder_ty: Vec<u32>,
    /// The pattern that binds each binder, for diagnostics.
    pub(crate) binder_site: Vec<u32>,
    pub(crate) diags: Vec<Diagnostic>,
    pub(crate) methods: Vec<(ExprId, ItemId)>,
    pub(crate) coercions: Vec<(ExprId, Coercion, TypeId)>,
    pub(crate) deferred: Vec<ExprId>,

    // Checking state.
    /// The type each expression must coerce to, set by its parent.
    pub(crate) expect: Vec<u32>,
    /// Expressions reported against their context; parents read them as
    /// `{error}` so the report is not repeated.
    pub(crate) poisoned: Vec<bool>,
    /// Unsuffixed integer literals and their variables, range-checked once
    /// the variables are resolved.
    pub(crate) int_lits: Vec<(NodeRef, TypeId, IntLit)>,
    pub(crate) frames: Vec<Frame>,
    pub(crate) targets: Vec<Target>,
    /// Binder index -> index into `targets`, for labelled targets.
    pub(crate) label_pos: Vec<u32>,
    /// The `Self` type of the item being checked.
    pub(crate) cur_self: Option<TypeId>,

    // Lowering memos.
    pub(crate) ty_memo: Vec<u32>,
    /// Per item: 0 untouched, 1 lowering in progress, 2 done (aliases).
    pub(crate) alias_state: Vec<u8>,
    pub(crate) sigs: Vec<u32>,
    pub(crate) sig_arena: Vec<lower::Sig>,
    /// Per const/global item: its declared type.
    pub(crate) decl_memo: Vec<u32>,
    /// Sorted field lists of named-field record items (structural records
    /// and record literals).
    pub(crate) record_fields: Vec<Option<(u32, u32)>>,
    pub(crate) field_pool: Vec<Field>,
    /// Per field: its declared type.
    pub(crate) field_memo: Vec<u32>,
    /// Per const item: constant-evaluation state and value.
    pub(crate) const_memo: Vec<(u8, i128)>,
    /// Innermost-last indices into `targets` of the enclosing loops.
    pub(crate) loops: Vec<u32>,
    /// Scratch: which parameters an argument list filled.
    pub(crate) filled: Vec<bool>,
    /// Operands whose type was unknown at their operation: re-checked once
    /// inference is done.
    pub(crate) deferred_ops: Vec<(ExprId, hir_lang::OpKind, ops::Want)>,
    /// `x == null` comparisons (their op class).
    pub(crate) null_checks: Vec<ExprId>,
    /// Expressions whose expectation moved to their branches (stack).
    pub(crate) delegated: Vec<(ExprId, TypeId)>,
    /// Record literals' targets between entry and exit (stack).
    pub(crate) record_targets: Vec<(ExprId, paths::RecordRef)>,
    /// `let` annotations between entry and the pattern (stack).
    pub(crate) let_types: Vec<(hir_lang::StmtId, TypeId)>,
    /// Closure types between entry and exit (stack).
    pub(crate) closure_types: Vec<TypeId>,
    /// Per path: the definition the checker resolved its tail to.
    pub(crate) path_def: Vec<Option<Def>>,
    /// Per expression: the function item a callee path names (`NONE`).
    pub(crate) callee_fns: Vec<u32>,
    /// Call targets between a call's preparation and its finish.
    pub(crate) call_stack: Vec<call::CallTarget>,
    /// The engine's task stack, reused across roots.
    pub(crate) tasks: Vec<engine::Task>,
    /// Visited marks for walks over class hierarchies (epoch-stamped, so a
    /// new walk costs nothing to start).
    pub(crate) item_stamp: Vec<u32>,
    pub(crate) item_epoch: u32,
}

impl<'h> Ctx<'h> {
    fn new(hir: &'h Hir, profile: Profile, budget: Budget, types: Types, host: Host) -> Self {
        let n = |k| hir.count(k);
        Self {
            hir,
            profile,
            types,
            infer: Infer::default(),
            meter: Meter::new(budget),
            host,
            idx: Index::default(),
            expr_ty: alloc::vec![NONE; n(IdKind::Expr)],
            pat_ty: alloc::vec![NONE; n(IdKind::Pat)],
            binder_ty: alloc::vec![NONE; n(IdKind::Binder)],
            binder_site: alloc::vec![NONE; n(IdKind::Binder)],
            diags: Vec::new(),
            methods: Vec::new(),
            coercions: Vec::new(),
            deferred: Vec::new(),
            expect: alloc::vec![NONE; n(IdKind::Expr)],
            poisoned: alloc::vec![false; n(IdKind::Expr)],
            int_lits: Vec::new(),
            frames: Vec::new(),
            targets: Vec::new(),
            label_pos: alloc::vec![NONE; n(IdKind::Binder)],
            cur_self: None,
            ty_memo: alloc::vec![NONE; n(IdKind::Ty)],
            alias_state: alloc::vec![0; n(IdKind::Item)],
            sigs: alloc::vec![NONE; n(IdKind::Item)],
            sig_arena: Vec::new(),
            decl_memo: alloc::vec![NONE; n(IdKind::Item)],
            record_fields: alloc::vec![None; n(IdKind::Item)],
            field_pool: Vec::new(),
            field_memo: alloc::vec![NONE; n(IdKind::Field)],
            const_memo: alloc::vec![(0, 0); n(IdKind::Item)],
            loops: Vec::new(),
            filled: Vec::new(),
            deferred_ops: Vec::new(),
            delegated: Vec::new(),
            record_targets: Vec::new(),
            let_types: Vec::new(),
            closure_types: Vec::new(),
            path_def: alloc::vec![None; n(IdKind::Path)],
            null_checks: Vec::new(),
            callee_fns: alloc::vec![NONE; n(IdKind::Expr)],
            call_stack: Vec::new(),
            tasks: Vec::new(),
            item_stamp: alloc::vec![0; n(IdKind::Item)],
            item_epoch: 0,
        }
    }

    // ------------------------------------------------------------ helpers

    pub(crate) fn report(&mut self, node: NodeRef, kind: DiagnosticKind) {
        let origin = self.hir.origin(node);
        self.diags.push(Diagnostic { kind, node, origin });
    }

    pub(crate) fn fresh(&mut self, class: u8) -> TypeId {
        self.infer.fresh(&mut self.types, class)
    }

    /// The node representing `t`'s class (one level: a bound variable reads
    /// as its binding).
    pub(crate) fn resolve(&self, t: TypeId) -> TypeId {
        self.infer.resolve(t)
    }

    pub(crate) fn tag(&self, t: TypeId) -> Tag {
        self.types.node(self.resolve(t)).tag
    }

    pub(crate) fn is_err(&self, t: TypeId) -> bool {
        self.tag(t) == Tag::Error
    }

    /// The primitive `t` resolves to, if any.
    pub(crate) fn prim_of(&self, t: TypeId) -> Option<Prim> {
        match self.types.get(self.resolve(t)) {
            crate::types::Type::Prim(p) => Some(p),
            _ => None,
        }
    }

    pub(crate) fn unify(&mut self, a: TypeId, b: TypeId) -> Result<bool, CheckError> {
        let cfg = UnifyCfg {
            int_to_float: self.profile.numeric_widening,
            structural: self.profile.records == RecordTyping::Structural,
            record_fields: &self.record_fields,
            field_pool: &self.field_pool,
        };
        self.infer.unify(&self.types, &cfg, &mut self.meter, a, b)
    }

    pub(crate) fn ety(&self, e: ExprId) -> TypeId {
        self.expr_ty
            .get(e.index())
            .copied()
            .filter(|&r| r != NONE)
            .map_or(TypeId::ERROR, TypeId::from_raw)
    }

    /// An expression's type as its parent sees it: `{error}` if it was
    /// already reported against its context.
    pub(crate) fn child(&self, e: ExprId) -> TypeId {
        if self.poisoned.get(e.index()).copied().unwrap_or(false) {
            TypeId::ERROR
        } else {
            self.ety(e)
        }
    }

    pub(crate) fn typed(&self, e: ExprId) -> bool {
        self.expr_ty.get(e.index()).is_some_and(|&r| r != NONE)
    }

    pub(crate) fn poison(&mut self, e: ExprId) {
        if let Some(p) = self.poisoned.get_mut(e.index()) {
            *p = true;
        }
    }

    pub(crate) fn set_expect(&mut self, e: ExprId, t: TypeId) {
        if let Some(slot) = self.expect.get_mut(e.index()) {
            *slot = t.raw();
        }
    }

    pub(crate) fn take_expect(&mut self, e: ExprId) -> Option<TypeId> {
        let slot = self.expect.get_mut(e.index())?;
        let v = core::mem::replace(slot, NONE);
        (v != NONE).then(|| TypeId::from_raw(v))
    }

    pub(crate) fn peek_expect(&self, e: ExprId) -> Option<TypeId> {
        self.expect
            .get(e.index())
            .copied()
            .filter(|&v| v != NONE)
            .map(TypeId::from_raw)
    }

    pub(crate) fn set_binder(&mut self, b: BinderId, t: TypeId, site: PatId) {
        if let Some(slot) = self.binder_ty.get_mut(b.index()) {
            *slot = t.raw();
        }
        if let Some(slot) = self.binder_site.get_mut(b.index()) {
            if *slot == NONE {
                *slot = u32::try_from(site.index()).unwrap_or(NONE);
            }
        }
    }

    pub(crate) fn binder_type(&self, b: BinderId) -> Option<TypeId> {
        self.binder_ty
            .get(b.index())
            .copied()
            .filter(|&v| v != NONE)
            .map(TypeId::from_raw)
    }

    pub(crate) fn host_extern(&self, name: Symbol) -> Option<TypeId> {
        find(&self.host.externs, name)
    }

    pub(crate) fn host_foreign(&self, def: DefId) -> Option<TypeId> {
        find(&self.host.foreign, def)
    }

    pub(crate) fn host_intrinsic(&self, name: Symbol) -> Option<TypeId> {
        find(&self.host.intrinsics, name)
    }

    pub(crate) fn host_member(&self, owner: TypeId, name: Symbol) -> Option<TypeId> {
        let key = (owner, name);
        self.host
            .members
            .binary_search_by(|&(o, n, _)| (o, n).cmp(&key))
            .ok()
            .and_then(|i| self.host.members.get(i))
            .map(|&(_, _, t)| t)
    }

    pub(crate) fn record_path_def(&mut self, path: PathId, def: Def) {
        if let Some(slot) = self.path_def.get_mut(path.index()) {
            *slot = Some(def);
        }
    }

    /// Starts a new walk over items (see [`visit`](Self::visit)).
    pub(crate) fn new_visit(&mut self) {
        self.item_epoch = self.item_epoch.wrapping_add(1);
        if self.item_epoch == 0 {
            self.item_stamp.iter_mut().for_each(|s| *s = 0);
            self.item_epoch = 1;
        }
    }

    /// Marks `item` visited in the current walk; `false` if it already was.
    pub(crate) fn visit(&mut self, item: ItemId) -> bool {
        match self.item_stamp.get_mut(item.index()) {
            Some(s) if *s == self.item_epoch => false,
            Some(s) => {
                *s = self.item_epoch;
                true
            }
            None => false,
        }
    }

    /// The display name of an item, remembered for type rendering.
    pub(crate) fn name_item(&mut self, item: ItemId) {
        if let Some(name) = self.hir.get_item(item).and_then(|it| it.name) {
            self.types.name_item(item, name.sym);
        }
    }

    /// An item's kind; `Err` for an id this unit did not issue (a host can
    /// build nominal types naming any item id).
    pub(crate) fn item_kind(&self, item: ItemId) -> hir_lang::ItemKind {
        self.hir
            .get_item(item)
            .map_or(hir_lang::ItemKind::Err, |it| it.kind)
    }
}
