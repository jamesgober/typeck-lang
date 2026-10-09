//! Typed diagnostics.
//!
//! A diagnostic is data: a [`DiagnosticKind`] (with the types and names
//! involved), the HIR node it is about, and that node's [`Origin`] (source
//! span and expansion). [`Typed::message`](crate::Typed::message) renders the
//! text. Each kind has a stable code (`T0001`...).

use alloc::string::String;
use core::fmt::Write as _;

use hir_lang::{Member, NodeRef, OpKind, Origin, Symbol, VariantId};
use intern_lang::Lookup;

use crate::types::{TypeId, Types};

/// A language feature the checker recognises but this version does not
/// check under the profile's discipline. Each is scheduled in
/// `dev/ROADMAP.md`.
///
/// # Examples
///
/// ```
/// use typeck_lang::Feature;
///
/// assert_eq!(Feature::Generics.name(), "generics");
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Feature {
    /// Generic items, generic arguments, and uses of generic items (0.5).
    Generics,
    /// Interfaces and traits used as types (`dyn`, `impl`, interface paths,
    /// qualified paths, `T::method` on a type parameter) (0.5).
    Traits,
    /// Associated types and multi-segment associated paths (`T::Item`,
    /// `A::B::c`) (0.5).
    AssociatedTypes,
    /// `impl` blocks on structural types (tuples, arrays, references) (0.5,
    /// with generics).
    StructuralImpls,
}

impl Feature {
    /// A short name for messages.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(typeck_lang::Feature::Traits.name(), "traits and interfaces as types");
    /// ```
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Generics => "generics",
            Self::Traits => "traits and interfaces as types",
            Self::AssociatedTypes => "associated types",
            Self::StructuralImpls => "impl blocks on structural types",
        }
    }
}

/// What a diagnostic says. Types are ids into the
/// [`Typed`](crate::Typed)'s store, resolved (no inference variables).
///
/// # Examples
///
/// ```
/// use typeck_lang::{DiagnosticKind, TypeId};
///
/// let k = DiagnosticKind::Mismatch { expected: TypeId::UNIT, found: TypeId::NULL };
/// assert_eq!(k.code(), "T0001");
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum DiagnosticKind {
    /// The expression's type does not fit its context.
    Mismatch {
        /// What the context requires.
        expected: TypeId,
        /// What the expression has.
        found: TypeId,
    },
    /// A static profile needs a declared type here (parameter, return of a
    /// signature slot written `_`, field, constant, global).
    MissingAnnotation,
    /// A name that resolution never resolved.
    Unresolved,
    /// A host or other-unit definition whose type was not declared to the
    /// checker.
    UnknownExtern {
        /// The name as written (last segment).
        name: Option<Symbol>,
    },
    /// The path names something that is not a value (a type, a module, a
    /// record with named fields).
    NotAValue,
    /// The path names something that is not a type.
    NotAType,
    /// Wrong number of arguments or pattern elements.
    Arity {
        /// The fewest accepted.
        min: u32,
        /// The most accepted (`None`: unbounded).
        max: Option<u32>,
        /// How many were given.
        found: u32,
    },
    /// A named argument that matches no parameter.
    UnknownNamedArg {
        /// The argument name.
        name: Symbol,
    },
    /// A parameter given twice (positionally and by name).
    DuplicateArg {
        /// The parameter name.
        name: Option<Symbol>,
    },
    /// A required parameter not given.
    MissingArg {
        /// The first missing parameter's name.
        name: Option<Symbol>,
        /// How many are missing.
        count: u32,
    },
    /// Calling a value whose type is not a function.
    NotCallable {
        /// The callee's type.
        ty: TypeId,
    },
    /// No such field.
    NoField {
        /// The accessed type.
        ty: TypeId,
        /// The member.
        member: Member,
    },
    /// No such method or associated item.
    NoMethod {
        /// The receiver or owner type.
        ty: TypeId,
        /// The name.
        name: Symbol,
    },
    /// Several impl blocks define the method.
    AmbiguousMethod {
        /// The receiver type.
        ty: TypeId,
        /// The name.
        name: Symbol,
    },
    /// A record literal or pattern names a field the record does not have.
    UnknownField {
        /// The record type.
        ty: TypeId,
        /// The field name.
        name: Symbol,
    },
    /// A record literal leaves out fields that have no default.
    MissingFields {
        /// The first missing field.
        first: Symbol,
        /// How many are missing.
        count: u32,
    },
    /// A union literal must initialise exactly one field.
    UnionLiteral {
        /// How many it initialises.
        count: u32,
    },
    /// Indexing a type that cannot be indexed.
    NotIndexable {
        /// The indexed type.
        ty: TypeId,
    },
    /// Dereferencing a type that is not a reference or pointer.
    CannotDeref {
        /// The type.
        ty: TypeId,
    },
    /// Awaiting a value that is not awaitable.
    NotAwaitable {
        /// The type.
        ty: TypeId,
    },
    /// An operation (OPS) is not defined for the operand type.
    OpType {
        /// The operation.
        op: OpKind,
        /// The offending operand's type.
        ty: TypeId,
    },
    /// The `promote` overflow policy on an operation whose result is
    /// statically typed (`promote` is only for dynamic results).
    PromoteOnStatic {
        /// The operation (`None`: a cast).
        op: Option<OpKind>,
    },
    /// A conversion op whose source or target width is wrong
    /// (`sext` to a narrower type, `bitcast` between different widths).
    BadConversion {
        /// The operation.
        op: OpKind,
        /// The source type.
        from: TypeId,
    },
    /// An `as` cast the profile does not allow.
    InvalidCast {
        /// The source type.
        from: TypeId,
        /// The target type.
        to: TypeId,
    },
    /// An integer literal outside the range of the type it got.
    LiteralOutOfRange {
        /// The literal's type.
        ty: TypeId,
    },
    /// No type could be inferred; add an annotation.
    CannotInfer,
    /// An operation on a dynamic (`any`) value under a static profile;
    /// cast or type-test it first.
    DynamicOperation,
    /// A dynamic-only form (`$$x`, `$o->$m()`, `$a = &$b`, `$a[]`) under a
    /// static profile.
    DynamicForm,
    /// Using a nullable value as if it were not null.
    NullableAccess {
        /// The nullable type.
        ty: TypeId,
    },
    /// A `match` that leaves values uncovered.
    NonExhaustive {
        /// A variant no arm covers, when the scrutinee is a sum.
        missing: Option<VariantId>,
    },
    /// A feature this version does not check (see [`Feature`]).
    Unsupported {
        /// Which feature.
        feature: Feature,
    },
    /// A type alias that expands to itself.
    CyclicAlias,
    /// A class whose base classes form a cycle.
    InheritanceCycle,
    /// A constant context (array length, repeat count) that is not a
    /// compile-time integer.
    NotConstant,
    /// A type test that can never succeed.
    ImpossibleTypeTest {
        /// The tested value's type.
        from: TypeId,
        /// The tested-for type.
        to: TypeId,
    },
    /// A by-reference parameter given a value instead of a place argument.
    ByRefNeedsPlace,
    /// Assigning to something that is not assignable (a function, constant,
    /// or constructor).
    NotAssignable,
}

impl DiagnosticKind {
    /// The stable code.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(typeck_lang::DiagnosticKind::CannotInfer.code(), "T0023");
    /// ```
    #[must_use]
    pub const fn code(&self) -> &'static str {
        match self {
            Self::Mismatch { .. } => "T0001",
            Self::MissingAnnotation => "T0002",
            Self::Unresolved => "T0003",
            Self::UnknownExtern { .. } => "T0004",
            Self::NotAValue => "T0005",
            Self::NotAType => "T0006",
            Self::Arity { .. } => "T0007",
            Self::UnknownNamedArg { .. } => "T0008",
            Self::DuplicateArg { .. } => "T0009",
            Self::MissingArg { .. } => "T0010",
            Self::NotCallable { .. } => "T0011",
            Self::NoField { .. } => "T0012",
            Self::NoMethod { .. } => "T0013",
            Self::UnknownField { .. } => "T0014",
            Self::MissingFields { .. } => "T0015",
            Self::NotIndexable { .. } => "T0016",
            Self::CannotDeref { .. } => "T0017",
            Self::OpType { .. } => "T0018",
            Self::PromoteOnStatic { .. } => "T0019",
            Self::InvalidCast { .. } => "T0020",
            Self::BadConversion { .. } => "T0021",
            Self::LiteralOutOfRange { .. } => "T0022",
            Self::CannotInfer => "T0023",
            Self::DynamicOperation => "T0024",
            Self::DynamicForm => "T0025",
            Self::NullableAccess { .. } => "T0026",
            Self::NonExhaustive { .. } => "T0027",
            Self::Unsupported { .. } => "T0028",
            Self::CyclicAlias => "T0029",
            Self::NotConstant => "T0030",
            Self::ImpossibleTypeTest { .. } => "T0032",
            Self::AmbiguousMethod { .. } => "T0033",
            Self::ByRefNeedsPlace => "T0034",
            Self::InheritanceCycle => "T0036",
            Self::NotAwaitable { .. } => "T0037",
            Self::NotAssignable => "T0038",
            Self::UnionLiteral { .. } => "T0039",
        }
    }

    /// Calls `f` on every type the kind mentions (so finalisation can resolve
    /// them).
    pub(crate) fn types_mut(&mut self, mut f: impl FnMut(&mut TypeId)) {
        match self {
            Self::Mismatch { expected, found } => {
                f(expected);
                f(found);
            }
            Self::InvalidCast { from, to } | Self::ImpossibleTypeTest { from, to } => {
                f(from);
                f(to);
            }
            Self::NotCallable { ty }
            | Self::NoField { ty, .. }
            | Self::NoMethod { ty, .. }
            | Self::AmbiguousMethod { ty, .. }
            | Self::UnknownField { ty, .. }
            | Self::NotIndexable { ty }
            | Self::CannotDeref { ty }
            | Self::NotAwaitable { ty }
            | Self::OpType { ty, .. }
            | Self::LiteralOutOfRange { ty }
            | Self::NullableAccess { ty } => f(ty),
            Self::BadConversion { from, .. } => f(from),
            _ => {}
        }
    }

    pub(crate) fn render<L: Lookup>(&self, types: &Types, names: &L, out: &mut String) {
        let ty = |t: TypeId, out: &mut String| {
            out.push('`');
            types.render(t, names, out);
            out.push('`');
        };
        let name = |s: Option<Symbol>, out: &mut String| {
            out.push('`');
            match s.and_then(|s| names.resolve_with(s, |t| out.push_str(t))) {
                Some(()) => {}
                None => out.push('?'),
            }
            out.push('`');
        };
        match *self {
            Self::Mismatch { expected, found } => {
                out.push_str("mismatched types: expected ");
                ty(expected, out);
                out.push_str(", found ");
                ty(found, out);
            }
            Self::MissingAnnotation => out.push_str("a type annotation is required here"),
            Self::Unresolved => out.push_str("unresolved name"),
            Self::UnknownExtern { name: n } => {
                out.push_str("the type of ");
                name(n, out);
                out.push_str(" is not declared to the checker");
            }
            Self::NotAValue => out.push_str("this names a type or module, not a value"),
            Self::NotAType => out.push_str("this does not name a type"),
            Self::Arity { min, max, found } => {
                let _ = match max {
                    Some(max) if max == min => {
                        write!(out, "expected {min} arguments, found {found}")
                    }
                    Some(max) => write!(out, "expected {min} to {max} arguments, found {found}"),
                    None => write!(out, "expected at least {min} arguments, found {found}"),
                };
            }
            Self::UnknownNamedArg { name: n } => {
                out.push_str("no parameter named ");
                name(Some(n), out);
            }
            Self::DuplicateArg { name: n } => {
                out.push_str("parameter ");
                name(n, out);
                out.push_str(" is given more than once");
            }
            Self::MissingArg { name: n, count } => {
                out.push_str("missing argument for parameter ");
                name(n, out);
                if count > 1 {
                    let _ = write!(out, " and {} more", count - 1);
                }
            }
            Self::NotCallable { ty: t } => {
                ty(t, out);
                out.push_str(" is not callable");
            }
            Self::NoField { ty: t, member } => {
                ty(t, out);
                out.push_str(" has no field ");
                match member {
                    Member::Named(s) => name(Some(s), out),
                    Member::Index(i) => {
                        let _ = write!(out, "`{i}`");
                    }
                }
            }
            Self::NoMethod { ty: t, name: n } => {
                ty(t, out);
                out.push_str(" has no method or associated item ");
                name(Some(n), out);
            }
            Self::AmbiguousMethod { ty: t, name: n } => {
                out.push_str("several impl blocks of ");
                ty(t, out);
                out.push_str(" define ");
                name(Some(n), out);
            }
            Self::UnknownField { ty: t, name: n } => {
                ty(t, out);
                out.push_str(" has no field ");
                name(Some(n), out);
            }
            Self::MissingFields { first, count } => {
                out.push_str("missing field ");
                name(Some(first), out);
                if count > 1 {
                    let _ = write!(out, " and {} more", count - 1);
                }
            }
            Self::UnionLiteral { count } => {
                let _ = write!(
                    out,
                    "a union literal initialises exactly one field, found {count}"
                );
            }
            Self::NotIndexable { ty: t } => {
                ty(t, out);
                out.push_str(" cannot be indexed");
            }
            Self::CannotDeref { ty: t } => {
                ty(t, out);
                out.push_str(" cannot be dereferenced");
            }
            Self::NotAwaitable { ty: t } => {
                ty(t, out);
                out.push_str(" is not awaitable");
            }
            Self::OpType { op, ty: t } => {
                let _ = write!(out, "`{}` is not defined for ", op.name());
                ty(t, out);
            }
            Self::PromoteOnStatic { op } => {
                out.push_str("the `promote` overflow policy needs a dynamically typed result");
                if let Some(op) = op {
                    let _ = write!(out, " (`{}`)", op.name());
                }
            }
            Self::BadConversion { op, from } => {
                let _ = write!(out, "`{}` cannot convert from ", op.name());
                ty(from, out);
            }
            Self::InvalidCast { from, to } => {
                out.push_str("cannot cast ");
                ty(from, out);
                out.push_str(" to ");
                ty(to, out);
            }
            Self::LiteralOutOfRange { ty: t } => {
                out.push_str("literal out of range for ");
                ty(t, out);
            }
            Self::CannotInfer => out.push_str("cannot infer a type here; add an annotation"),
            Self::DynamicOperation => {
                out.push_str("operation on a dynamic `any` value; cast or type-test it first")
            }
            Self::DynamicForm => {
                out.push_str("this dynamic form is not allowed under a static profile");
            }
            Self::NullableAccess { ty: t } => {
                ty(t, out);
                out.push_str(" may be null");
            }
            Self::NonExhaustive { .. } => out.push_str("non-exhaustive match"),
            Self::Unsupported { feature } => {
                let _ = write!(
                    out,
                    "{} are not supported by this profile in this version",
                    feature.name()
                );
            }
            Self::CyclicAlias => out.push_str("type alias expands to itself"),
            Self::InheritanceCycle => out.push_str("class inherits from itself"),
            Self::NotConstant => out.push_str("expected a compile-time integer constant"),
            Self::ImpossibleTypeTest { from, to } => {
                out.push_str("a value of type ");
                ty(from, out);
                out.push_str(" can never be a ");
                ty(to, out);
            }
            Self::ByRefNeedsPlace => {
                out.push_str("a by-reference parameter needs a place argument");
            }
            Self::NotAssignable => out.push_str("cannot assign to this"),
        }
    }
}

/// One finding about the checked program.
///
/// [`Typed::message`](crate::Typed::message) renders it as text.
///
/// # Examples
///
/// ```
/// use hir_lang::{BinderKind, Builder, Name, NodeRef};
/// use intern_lang::Interner;
/// use typeck_lang::{check, DiagnosticKind, Profile};
///
/// let mut names = Interner::new();
/// let mut b = Builder::new();
/// // fn main() { let x; }   -- nothing determines x's type
/// let x = b.new_binder(Name::new(names.intern("x")), BinderKind::Local);
/// let pat = b.bind(x);
/// let stmt = b.let_stmt(pat, None);
/// let body = b.block(&[stmt], None);
/// let main = b.func(Name::new(names.intern("main")), &[], body);
/// let root = b.module(None, &[main]);
/// let hir = b.finish(root)?;
///
/// let typed = check(&hir, &Profile::static_explicit()).unwrap();
/// let d = typed.diagnostics()[0];
/// assert_eq!(d.kind, DiagnosticKind::CannotInfer);
/// assert_eq!(d.kind.code(), "T0023");
/// assert_eq!(d.node, NodeRef::Pat(pat));
/// assert_eq!(d.origin, hir.origin(NodeRef::Pat(pat)));
/// # Ok::<(), hir_lang::HirError>(())
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct Diagnostic {
    /// What is wrong.
    pub kind: DiagnosticKind,
    /// The node it is about.
    pub node: NodeRef,
    /// The node's origin: source span and expansion.
    pub origin: Origin,
}

#[cfg(test)]
mod tests {
    use alloc::{string::String, vec::Vec};

    use hir_lang::{Member, OpKind, Prim};
    use intern_lang::Interner;

    use super::*;

    fn all_kinds() -> Vec<DiagnosticKind> {
        let mut names = Interner::new();
        let s = names.intern("n");
        let t = TypeId::prim(Prim::I32);
        alloc::vec![
            DiagnosticKind::Mismatch {
                expected: t,
                found: t
            },
            DiagnosticKind::MissingAnnotation,
            DiagnosticKind::Unresolved,
            DiagnosticKind::UnknownExtern { name: Some(s) },
            DiagnosticKind::NotAValue,
            DiagnosticKind::NotAType,
            DiagnosticKind::Arity {
                min: 1,
                max: Some(2),
                found: 3
            },
            DiagnosticKind::UnknownNamedArg { name: s },
            DiagnosticKind::DuplicateArg { name: Some(s) },
            DiagnosticKind::MissingArg {
                name: Some(s),
                count: 2
            },
            DiagnosticKind::NotCallable { ty: t },
            DiagnosticKind::NoField {
                ty: t,
                member: Member::Index(0)
            },
            DiagnosticKind::NoMethod { ty: t, name: s },
            DiagnosticKind::AmbiguousMethod { ty: t, name: s },
            DiagnosticKind::UnknownField { ty: t, name: s },
            DiagnosticKind::MissingFields { first: s, count: 3 },
            DiagnosticKind::UnionLiteral { count: 2 },
            DiagnosticKind::NotIndexable { ty: t },
            DiagnosticKind::CannotDeref { ty: t },
            DiagnosticKind::NotAwaitable { ty: t },
            DiagnosticKind::OpType {
                op: OpKind::Add,
                ty: t
            },
            DiagnosticKind::PromoteOnStatic { op: None },
            DiagnosticKind::BadConversion {
                op: OpKind::Sext(Prim::I8),
                from: t
            },
            DiagnosticKind::InvalidCast { from: t, to: t },
            DiagnosticKind::LiteralOutOfRange { ty: t },
            DiagnosticKind::CannotInfer,
            DiagnosticKind::DynamicOperation,
            DiagnosticKind::DynamicForm,
            DiagnosticKind::NullableAccess { ty: t },
            DiagnosticKind::NonExhaustive { missing: None },
            DiagnosticKind::Unsupported {
                feature: Feature::AssociatedTypes
            },
            DiagnosticKind::CyclicAlias,
            DiagnosticKind::InheritanceCycle,
            DiagnosticKind::NotConstant,
            DiagnosticKind::ImpossibleTypeTest { from: t, to: t },
            DiagnosticKind::ByRefNeedsPlace,
            DiagnosticKind::NotAssignable,
        ]
    }

    #[test]
    fn test_codes_are_unique_and_messages_render() {
        let names = Interner::new();
        let types = Types::new();
        let kinds = all_kinds();
        let mut codes: Vec<&str> = kinds.iter().map(DiagnosticKind::code).collect();
        codes.sort_unstable();
        let n = codes.len();
        codes.dedup();
        assert_eq!(codes.len(), n, "duplicate diagnostic codes");
        for k in &kinds {
            let mut out = String::new();
            k.render(&types, &names, &mut out);
            assert!(!out.is_empty(), "{k:?}");
        }
    }

    #[test]
    fn test_arity_wording() {
        let names = Interner::new();
        let types = Types::new();
        let render = |k: DiagnosticKind| {
            let mut out = String::new();
            k.render(&types, &names, &mut out);
            out
        };
        assert_eq!(
            render(DiagnosticKind::Arity {
                min: 2,
                max: Some(2),
                found: 1
            }),
            "expected 2 arguments, found 1"
        );
        assert_eq!(
            render(DiagnosticKind::Arity {
                min: 1,
                max: Some(3),
                found: 5
            }),
            "expected 1 to 3 arguments, found 5"
        );
        assert_eq!(
            render(DiagnosticKind::Arity {
                min: 1,
                max: None,
                found: 0
            }),
            "expected at least 1 arguments, found 0"
        );
        assert_eq!(
            render(DiagnosticKind::UnknownExtern { name: None }),
            "the type of `?` is not declared to the checker"
        );
    }

    #[test]
    fn test_feature_names() {
        for f in [
            Feature::Generics,
            Feature::Traits,
            Feature::AssociatedTypes,
            Feature::StructuralImpls,
        ] {
            assert!(!f.name().is_empty());
        }
    }
}
