//! The result of a check: side tables keyed by HIR ids, and diagnostics.

use alloc::{string::String, vec::Vec};

use hir_lang::{BinderId, Def, ExprId, ItemId, PatId, PathId, Prim};
use intern_lang::Lookup;

use crate::{
    diag::Diagnostic,
    profile::Profile,
    types::{TypeDisplay, TypeId, Types},
};

/// An implicit conversion the checker accepted where a value meets a
/// context of another type. Lowering must materialise it.
///
/// # Examples
///
/// ```
/// use typeck_lang::Coercion;
///
/// assert_ne!(Coercion::Widen, Coercion::ToAny);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Coercion {
    /// A lossless numeric widening (`i32` to `i64`, `i32` to `f64`).
    Widen,
    /// A value boxed into the dynamic type `any`.
    ToAny,
    /// `T` used as `T?`.
    WrapNullable,
    /// `null` used as a nullable or (without null safety) reference type.
    Null,
    /// A subclass used as one of its base classes.
    Subclass,
    /// A structural record used as a record with fewer fields.
    RecordWidth,
    /// An array used as a slice (`[T; n]` to `[T]`, also behind `&`).
    Unsize,
    /// `&mut T` used as `&T`.
    Reborrow,
    /// A method receiver borrowed automatically (`x.m()` with `fn m(&self)`).
    AutoRef,
    /// A method receiver dereferenced automatically.
    AutoDeref,
}

/// How an OPS operation was resolved by its operand types (HIR leaves this
/// open: the same `add` is integer, IEEE, or string concatenation).
///
/// # Examples
///
/// ```
/// use hir_lang::Prim;
/// use typeck_lang::OpClass;
///
/// assert_ne!(OpClass::Int(Prim::I32), OpClass::Float(Prim::F64));
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum OpClass {
    /// Integer semantics (OPS §3) on this type.
    Int(Prim),
    /// IEEE semantics (OPS §4) on this type.
    Float(Prim),
    /// Logical operations on `bool`.
    Bool,
    /// Comparisons of `char`.
    Char,
    /// String comparison or concatenation (a runtime-library operation).
    Str,
    /// `x == null` / `x != null`.
    NullCheck,
    /// Dispatched at run time on dynamic values.
    Dynamic,
}

/// Work counters of a finished check.
///
/// # Examples
///
/// ```
/// use hir_lang::Builder;
/// use typeck_lang::{check, Profile};
///
/// let mut b = Builder::new();
/// let root = b.module(None, &[]);
/// let hir = b.finish(root)?;
/// let typed = check(&hir, &Profile::static_explicit()).unwrap();
/// assert!(typed.stats().steps < 100);
/// # Ok::<(), hir_lang::HirError>(())
/// ```
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Stats {
    /// Steps charged against [`Budget::steps`](crate::Budget::steps).
    pub steps: u64,
    /// Final type-store size (nodes plus pooled children).
    pub type_nodes: usize,
}

pub(crate) const NONE: u32 = u32::MAX;

/// The result of checking one HIR unit.
///
/// Every live expression, pattern, and bound binder has a type (dense side
/// tables, indexed by HIR id); a type is [`TypeId::ERROR`] where something
/// was reported. Dead nodes (unreachable error forms left by lenient
/// validation) have none.
///
/// # Examples
///
/// ```
/// use hir_lang::{Builder, Name, OpKind, Prim};
/// use intern_lang::Interner;
/// use typeck_lang::{check, Profile, TypeId};
///
/// let mut names = Interner::new();
/// let mut b = Builder::new();
/// let (one, two) = (b.int(1), b.int(2));
/// let sum = b.op(OpKind::Add, &[one, two]);
/// let body = b.block(&[], Some(sum));
/// let main = b.func(Name::new(names.intern("main")), &[], body);
/// let root = b.module(None, &[main]);
/// let hir = b.finish(root)?;
///
/// // `main` has no declared return type: its body must be unit.
/// let typed = check(&hir, &Profile::static_explicit()).unwrap();
/// assert_eq!(typed.expr(sum), Some(TypeId::prim(Prim::I64)));
/// assert_eq!(typed.diagnostics().len(), 1);
/// assert_eq!(
///     typed.message(&typed.diagnostics()[0], &names),
///     "mismatched types: expected `()`, found `i64`",
/// );
/// # Ok::<(), hir_lang::HirError>(())
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Typed {
    pub(crate) types: Types,
    pub(crate) exprs: Vec<u32>,
    pub(crate) pats: Vec<u32>,
    pub(crate) binders: Vec<u32>,
    pub(crate) path_defs: Vec<(PathId, Def)>,
    pub(crate) methods: Vec<(ExprId, ItemId)>,
    pub(crate) coercions: Vec<(ExprId, Coercion, TypeId)>,
    pub(crate) op_classes: Vec<(ExprId, OpClass)>,
    pub(crate) deferred: Vec<ExprId>,
    pub(crate) diagnostics: Vec<Diagnostic>,
    pub(crate) profile: Profile,
    pub(crate) stats: Stats,
}

fn lookup<K: Ord + Copy, V: Copy>(table: &[(K, V)], key: K) -> Option<V> {
    table
        .binary_search_by(|(k, _)| k.cmp(&key))
        .ok()
        .and_then(|i| table.get(i))
        .map(|&(_, v)| v)
}

fn dense(table: &[u32], index: usize) -> Option<TypeId> {
    table
        .get(index)
        .copied()
        .filter(|&raw| raw != NONE)
        .map(TypeId::from_raw)
}

impl Typed {
    /// The type of a live expression.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Builder, Lit, Name, Prim};
    /// use intern_lang::Interner;
    /// use typeck_lang::{check, Profile, TypeId};
    ///
    /// let mut names = Interner::new();
    /// let mut b = Builder::new();
    /// let c = b.lit(Lit::Char('x'));
    /// let s = b.expr_stmt(c);
    /// let body = b.block(&[s], None);
    /// let main = b.func(Name::new(names.intern("main")), &[], body);
    /// let root = b.module(None, &[main]);
    /// let hir = b.finish(root)?;
    /// let typed = check(&hir, &Profile::static_explicit()).unwrap();
    /// assert_eq!(typed.expr(c), Some(TypeId::prim(Prim::Char)));
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    #[must_use]
    pub fn expr(&self, id: ExprId) -> Option<TypeId> {
        dense(&self.exprs, id.index())
    }

    /// The type a live pattern matches.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Builder, Name};
    /// use intern_lang::Interner;
    /// use typeck_lang::{check, Profile, TypeId};
    ///
    /// let mut names = Interner::new();
    /// let mut b = Builder::new();
    /// let x = b.new_binder(Name::new(names.intern("x")), hir_lang::BinderKind::Local);
    /// let pat = b.bind(x);
    /// let init = b.lit(hir_lang::Lit::Bool(true));
    /// let stmt = b.let_stmt(pat, Some(init));
    /// let body = b.block(&[stmt], None);
    /// let main = b.func(Name::new(names.intern("main")), &[], body);
    /// let root = b.module(None, &[main]);
    /// let hir = b.finish(root)?;
    /// let typed = check(&hir, &Profile::static_explicit()).unwrap();
    /// assert_eq!(typed.pat(pat), Some(TypeId::prim(hir_lang::Prim::Bool)));
    /// assert_eq!(typed.binder(x), Some(TypeId::prim(hir_lang::Prim::Bool)));
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    #[must_use]
    pub fn pat(&self, id: PatId) -> Option<TypeId> {
        dense(&self.pats, id.index())
    }

    /// The type of a bound binder (a variable, parameter, or capture).
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Builder, Lit, Name, Prim};
    /// use intern_lang::Interner;
    /// use typeck_lang::{check, Profile, TypeId};
    ///
    /// let mut names = Interner::new();
    /// let mut b = Builder::new();
    /// let x = b.new_binder(Name::new(names.intern("x")), hir_lang::BinderKind::Local);
    /// let pat = b.bind(x);
    /// let init = b.lit(Lit::Bool(false));
    /// let s = b.let_stmt(pat, Some(init));
    /// let body = b.block(&[s], None);
    /// let main = b.func(Name::new(names.intern("main")), &[], body);
    /// let root = b.module(None, &[main]);
    /// let hir = b.finish(root)?;
    /// let typed = check(&hir, &Profile::static_explicit()).unwrap();
    /// assert_eq!(typed.binder(x), Some(TypeId::prim(Prim::Bool)));
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    #[must_use]
    pub fn binder(&self, id: BinderId) -> Option<TypeId> {
        dense(&self.binders, id.index())
    }

    /// The type store the side tables point into.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::Builder;
    /// use typeck_lang::{check, Profile, Type, TypeId};
    ///
    /// let mut b = Builder::new();
    /// let root = b.module(None, &[]);
    /// let hir = b.finish(root)?;
    /// let typed = check(&hir, &Profile::dynamic()).unwrap();
    /// assert_eq!(typed.types().get(TypeId::ANY), Type::Any);
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    #[must_use]
    pub fn types(&self) -> &Types {
        &self.types
    }

    /// The diagnostics, in source order (span start, then discovery).
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Builder, Lit, Name, Prim};
    /// use intern_lang::Interner;
    /// use typeck_lang::{check, Profile, TypeId};
    ///
    /// let mut names = Interner::new();
    /// let mut b = Builder::new();
    /// // let x: bool = 1;
    /// let one = b.int(1);
    /// let ann = b.ty(hir_lang::Ty::Prim(Prim::Bool));
    /// let x = b.new_binder(Name::new(names.intern("x")), hir_lang::BinderKind::Local);
    /// let pat = b.bind(x);
    /// let s = b.stmt(hir_lang::Stmt::Let { pat, ty: Some(ann), init: Some(one), else_: None });
    /// let body = b.block(&[s], None);
    /// let main = b.func(Name::new(names.intern("main")), &[], body);
    /// let root = b.module(None, &[main]);
    /// let hir = b.finish(root)?;
    /// let typed = check(&hir, &Profile::static_explicit()).unwrap();
    /// let d = typed.diagnostics()[0];
    /// assert_eq!(d.node, hir_lang::NodeRef::Expr(one));
    /// assert_eq!(d.kind.code(), "T0001");
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    #[must_use]
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    /// `true` if no diagnostics were reported.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::Builder;
    /// use typeck_lang::{check, Profile};
    ///
    /// let mut b = Builder::new();
    /// let root = b.module(None, &[]);
    /// let hir = b.finish(root)?;
    /// assert!(check(&hir, &Profile::static_explicit()).unwrap().is_ok());
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    #[must_use]
    pub fn is_ok(&self) -> bool {
        self.diagnostics.is_empty()
    }

    /// The definition the checker resolved a path's unresolved tail to
    /// (`Shape::Circle` to a variant, `Point::new` to an impl function).
    /// `None` for paths resolution resolved completely.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Builder, Def, Expr, Ident, Item, ItemKind, List, Name, Ns, Path, Res, Segment, Shape, Span, SumDef, Variant};
    /// use intern_lang::Interner;
    /// use typeck_lang::{check, Profile};
    ///
    /// let mut names = Interner::new();
    /// let mut b = Builder::new();
    /// // enum Shape { Empty }   fn main() { Shape::Empty; }
    /// let empty = b.variant(Variant {
    ///     name: Ident::new(names.intern("Empty"), Span::empty(0)),
    ///     shape: Shape::Unit,
    ///     fields: List::EMPTY,
    ///     discriminant: None,
    /// });
    /// let variants = b.list(&[empty]);
    /// let shape = b.item(Item::new(
    ///     Some(Name::new(names.intern("Shape"))),
    ///     ItemKind::Sum(SumDef { variants, ..SumDef::default() }),
    /// ));
    /// // `Shape` resolved by name; `Empty` left to the checker.
    /// let origin = b.origin();
    /// let segments = b.list(&[
    ///     Segment::new(Name::new(names.intern("Shape")), origin),
    ///     Segment::new(Name::new(names.intern("Empty")), origin),
    /// ]);
    /// let def = b.def(Def::Item(shape));
    /// let path = b.path(Path { res: Res::Def(def), unresolved: 1, ..Path::new(segments, Ns::Value) });
    /// let e = b.expr(Expr::Path(path));
    /// let s = b.expr_stmt(e);
    /// let body = b.block(&[s], None);
    /// let main = b.func(Name::new(names.intern("main")), &[], body);
    /// let root = b.module(None, &[shape, main]);
    /// let hir = b.finish(root)?;
    /// let typed = check(&hir, &Profile::static_explicit()).unwrap();
    /// assert_eq!(typed.path_def(path), Some(Def::Variant(empty)));
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    #[must_use]
    pub fn path_def(&self, path: PathId) -> Option<Def> {
        lookup(&self.path_defs, path)
    }

    /// The function item a method call dispatches to statically.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Arg, BinderKind, Builder, Def, Expr, FieldDef, FnDef, Ident, ImplDef, Item, ItemKind, List, Name, Ns, Param, ParamKind, Prim, RecordDef, Res, Span, Ty};
    /// use intern_lang::Interner;
    /// use typeck_lang::{check, Profile, TypeId};
    ///
    /// let mut names = Interner::new();
    /// let mut b = Builder::new();
    /// // struct P { x: i64 }  impl P { fn get(self) -> i64 { self.x } }
    /// let i64_ty = b.ty(Ty::Prim(Prim::I64));
    /// let x = names.intern("x");
    /// let field = b.field(FieldDef { ty: Some(i64_ty), ..FieldDef::named(Ident::new(x, Span::empty(0))) });
    /// let fields = b.list(&[field]);
    /// let p = b.item(Item::new(Some(Name::new(names.intern("P"))), ItemKind::Record(RecordDef { fields, ..RecordDef::default() })));
    /// let me = b.new_binder(Name::new(names.intern("self")), BinderKind::Param);
    /// let me_pat = b.bind(me);
    /// let recv = b.param(Param { kind: ParamKind::Receiver, ..Param::new(me_pat) });
    /// let base = b.use_binder(me);
    /// let read = b.expr(Expr::Field { base, member: hir_lang::Member::Named(x), span: Span::empty(0) });
    /// let get_body = b.block(&[], Some(read));
    /// let ret = b.ty(Ty::Prim(Prim::I64));
    /// let params = b.list(&[recv]);
    /// let get = b.item(Item::new(Some(Name::new(names.intern("get"))), ItemKind::Fn(FnDef { params, ret: Some(ret), body: Some(get_body), ..FnDef::default() })));
    /// let p_def = b.def(Def::Item(p));
    /// let p_path = b.resolved_path(Name::new(names.intern("P")), Ns::Type, Res::Def(p_def));
    /// let self_ty = b.ty(Ty::Path(p_path));
    /// let items = b.list(&[get]);
    /// let imp = b.item(Item::new(None, ItemKind::Impl(ImplDef { items, ..ImplDef::new(self_ty) })));
    /// // fn main(v: P) { v.get(); }
    /// let p_path2 = b.resolved_path(Name::new(names.intern("P")), Ns::Type, Res::Def(p_def));
    /// let v_ty = b.ty(Ty::Path(p_path2));
    /// let v = b.new_binder(Name::new(names.intern("v")), BinderKind::Param);
    /// let v_pat = b.bind(v);
    /// let v_param = b.param(Param { ty: Some(v_ty), ..Param::new(v_pat) });
    /// let receiver = b.use_binder(v);
    /// let args = b.list::<Arg>(&[]);
    /// let call = b.expr(Expr::MethodCall { receiver, method: Ident::new(names.intern("get"), Span::empty(0)), generic_args: List::EMPTY, args });
    /// let s = b.expr_stmt(call);
    /// let body = b.block(&[s], None);
    /// let main = b.func(Name::new(names.intern("main")), &[v_param], body);
    /// let root = b.module(None, &[p, imp, main]);
    /// let hir = b.finish(root)?;
    /// let typed = check(&hir, &Profile::static_explicit()).unwrap();
    /// assert!(typed.is_ok());
    /// assert_eq!(typed.method(call), Some(get));
    /// assert_eq!(typed.expr(call), Some(TypeId::prim(Prim::I64)));
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    #[must_use]
    pub fn method(&self, call: ExprId) -> Option<ItemId> {
        lookup(&self.methods, call)
    }

    /// The implicit conversion applied to an expression's value, and the
    /// type it was converted to.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Builder, Lit, Name, Prim};
    /// use intern_lang::Interner;
    /// use typeck_lang::{check, Coercion, Profile, TypeId};
    ///
    /// let mut names = Interner::new();
    /// let mut b = Builder::new();
    /// // let x: f64 = 2i32;   accepted with numeric widening
    /// let two = b.lit(Lit::Int(hir_lang::IntLit::new(2).with_suffix(Prim::I32)));
    /// let ann = b.ty(hir_lang::Ty::Prim(Prim::F64));
    /// let x = b.new_binder(Name::new(names.intern("x")), hir_lang::BinderKind::Local);
    /// let pat = b.bind(x);
    /// let s = b.stmt(hir_lang::Stmt::Let { pat, ty: Some(ann), init: Some(two), else_: None });
    /// let body = b.block(&[s], None);
    /// let main = b.func(Name::new(names.intern("main")), &[], body);
    /// let root = b.module(None, &[main]);
    /// let hir = b.finish(root)?;
    /// let profile = Profile::static_explicit().with_numeric_widening(true);
    /// let typed = check(&hir, &profile).unwrap();
    /// assert!(typed.is_ok());
    /// assert_eq!(typed.coercion(two), Some((Coercion::Widen, TypeId::prim(Prim::F64))));
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    #[must_use]
    pub fn coercion(&self, expr: ExprId) -> Option<(Coercion, TypeId)> {
        self.coercions
            .binary_search_by(|(e, _, _)| e.cmp(&expr))
            .ok()
            .and_then(|i| self.coercions.get(i))
            .map(|&(_, c, t)| (c, t))
    }

    /// How an `Op` expression's operation was resolved.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Builder, Name, OpKind, Prim};
    /// use intern_lang::Interner;
    /// use typeck_lang::{check, OpClass, Profile};
    ///
    /// let mut names = Interner::new();
    /// let mut b = Builder::new();
    /// let (x, y) = (b.int(1), b.int(2));
    /// let lt = b.op(OpKind::Lt, &[x, y]);
    /// let s = b.expr_stmt(lt);
    /// let body = b.block(&[s], None);
    /// let main = b.func(Name::new(names.intern("main")), &[], body);
    /// let root = b.module(None, &[main]);
    /// let hir = b.finish(root)?;
    /// let typed = check(&hir, &Profile::static_explicit()).unwrap();
    /// assert_eq!(typed.op_class(lt), Some(OpClass::Int(Prim::I64)));
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    #[must_use]
    pub fn op_class(&self, op: ExprId) -> Option<OpClass> {
        lookup(&self.op_classes, op)
    }

    /// `match` expressions whose exhaustiveness depends on nested patterns:
    /// the checker verified the top-level constructors and leaves the precise
    /// answer to a pattern compiler (match-lang). Empty unless the profile
    /// requires exhaustive matches.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::Builder;
    /// use typeck_lang::{check, Profile};
    ///
    /// let mut b = Builder::new();
    /// let root = b.module(None, &[]);
    /// let hir = b.finish(root)?;
    /// assert!(check(&hir, &Profile::static_explicit()).unwrap().deferred_matches().is_empty());
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    #[must_use]
    pub fn deferred_matches(&self) -> &[ExprId] {
        &self.deferred
    }

    /// The profile the program was checked under.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::Builder;
    /// use typeck_lang::{check, Profile};
    ///
    /// let mut b = Builder::new();
    /// let root = b.module(None, &[]);
    /// let hir = b.finish(root)?;
    /// let typed = check(&hir, &Profile::dynamic()).unwrap();
    /// assert_eq!(*typed.profile(), Profile::dynamic());
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    #[must_use]
    pub fn profile(&self) -> &Profile {
        &self.profile
    }

    /// Work counters.
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Builder, Name};
    /// use intern_lang::Interner;
    /// use typeck_lang::{check, Profile};
    ///
    /// let mut b = Builder::new();
    /// let one = b.int(1);
    /// let s = b.expr_stmt(one);
    /// let body = b.block(&[s], None);
    /// let main = b.func(Name::new(Interner::new().intern("main")), &[], body);
    /// let root = b.module(None, &[main]);
    /// let hir = b.finish(root)?;
    /// let stats = check(&hir, &Profile::static_explicit()).unwrap().stats();
    /// assert!(stats.steps > 0 && stats.type_nodes >= 20);
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    #[must_use]
    pub fn stats(&self) -> Stats {
        self.stats
    }

    /// Renders a type; see [`Types::display`].
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::Builder;
    /// use intern_lang::Interner;
    /// use typeck_lang::{check, Profile, TypeId};
    ///
    /// let mut b = Builder::new();
    /// let root = b.module(None, &[]);
    /// let hir = b.finish(root)?;
    /// let typed = check(&hir, &Profile::dynamic()).unwrap();
    /// assert_eq!(typed.display(TypeId::ANY, &Interner::new()).to_string(), "any");
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    #[must_use]
    pub fn display<'a, L: Lookup>(&'a self, ty: TypeId, names: &'a L) -> TypeDisplay<'a, L> {
        self.types.display(ty, names)
    }

    /// Renders a diagnostic's message (without code or location).
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::{Builder, Lit, Name, Prim};
    /// use intern_lang::Interner;
    /// use typeck_lang::{check, Profile, TypeId};
    ///
    /// let mut names = Interner::new();
    /// let mut b = Builder::new();
    /// // let x: bool = 1;
    /// let one = b.int(1);
    /// let ann = b.ty(hir_lang::Ty::Prim(Prim::Bool));
    /// let x = b.new_binder(Name::new(names.intern("x")), hir_lang::BinderKind::Local);
    /// let pat = b.bind(x);
    /// let s = b.stmt(hir_lang::Stmt::Let { pat, ty: Some(ann), init: Some(one), else_: None });
    /// let body = b.block(&[s], None);
    /// let main = b.func(Name::new(names.intern("main")), &[], body);
    /// let root = b.module(None, &[main]);
    /// let hir = b.finish(root)?;
    /// let typed = check(&hir, &Profile::static_explicit()).unwrap();
    /// let d = typed.diagnostics()[0];
    /// assert_eq!(typed.message(&d, &names), "mismatched types: expected `bool`, found `i64`");
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    #[must_use]
    pub fn message<L: Lookup>(&self, diagnostic: &Diagnostic, names: &L) -> String {
        let mut out = String::new();
        diagnostic.kind.render(&self.types, names, &mut out);
        out
    }
}
