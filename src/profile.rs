//! Type-system profiles: what a language's checker is, as data.
//!
//! A [`Profile`] is a [`Discipline`] (how much is checked statically and how
//! much is inferred) plus toggles that differ between languages of the same
//! discipline. One checker reads the profile; no language gets its own
//! checker.

use hir_lang::{Prim, Symbol};

use crate::mono::MonoPolicy;

/// How much a language checks statically, and how much it infers.
///
/// | Discipline | Like | Static checking | Inference |
/// |---|---|---|---|
/// | `Dynamic` | Python, Lua, Mox | Only statically certain arity and shape errors | none: every value is `any` |
/// | `Gradual` | TypeScript, Mercury | Where annotated; `any` at the boundaries | local |
/// | `StaticExplicit` | C, Go, Zero | Everything | `let` initializers, literals, generic arguments |
/// | `StaticInferred` | Kraken, Iron | Everything | bidirectional: also closure signatures from context |
/// | `Hm` | ML family | Everything | full, with let-polymorphism |
///
/// Both static disciplines check generic items, interfaces (traits), `impl`
/// blocks, associated types, and `dyn`/`impl Trait` types: any HIR that uses
/// them needs them. `StaticInferred` additionally infers unannotated closure
/// parameters and results from the expected function type, or from use.
///
/// Implemented in 0.3.0: `Dynamic`, `StaticExplicit`, and `StaticInferred`.
/// `Gradual` and `Hm` are designed (see the crate's `dev/ROADMAP.md`) and
/// land in 0.5.0; checking under them returns
/// [`CheckError::NotImplemented`](crate::CheckError::NotImplemented).
///
/// # Examples
///
/// ```
/// use typeck_lang::Discipline;
///
/// assert!(Discipline::Dynamic.is_implemented());
/// assert!(Discipline::StaticInferred.is_implemented());
/// assert!(!Discipline::Hm.is_implemented());
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Discipline {
    /// No static type errors; every value has type `any`.
    Dynamic,
    /// Checked where annotated; unannotated values are `any`.
    Gradual,
    /// Declared types on signatures and globals; local inference for `let`.
    StaticExplicit,
    /// Bidirectional local inference, generics, traits or interfaces.
    StaticInferred,
    /// Hindley-Milner: full inference with let-polymorphism.
    Hm,
}

impl Discipline {
    /// Whether this version of the checker implements the discipline.
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::Discipline;
    ///
    /// assert!(Discipline::StaticExplicit.is_implemented());
    /// assert!(!Discipline::Gradual.is_implemented());
    /// ```
    #[must_use]
    pub const fn is_implemented(self) -> bool {
        matches!(
            self,
            Self::Dynamic | Self::StaticExplicit | Self::StaticInferred
        )
    }

    /// The discipline's name as profiles spell it (`static-explicit`).
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::Discipline;
    ///
    /// assert_eq!(Discipline::StaticExplicit.name(), "static-explicit");
    /// ```
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Dynamic => "dynamic",
            Self::Gradual => "gradual",
            Self::StaticExplicit => "static-explicit",
            Self::StaticInferred => "static-inferred",
            Self::Hm => "hm",
        }
    }
}

/// Whether record types are identified by declaration or by shape.
///
/// # Examples
///
/// ```
/// use typeck_lang::RecordTyping;
///
/// assert_ne!(RecordTyping::Nominal, RecordTyping::Structural);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RecordTyping {
    /// Two record declarations are different types even with equal fields
    /// (Rust, C, Kraken).
    Nominal,
    /// Records with the same field names and types are the same type, and an
    /// anonymous record literal of that shape has it (TypeScript, Go's
    /// unnamed structs). Applies to records with named fields; tuple-shaped
    /// records and classes stay nominal.
    Structural,
}

/// How a language attaches behaviour to types.
///
/// All three resolve members through the same engine (`impl` blocks and
/// classes' declared interfaces are both implementations). The difference is
/// what an interface name means where a type is expected: with
/// `Interfaces`, the interface type (a `dyn` value, as in Java or Kraken);
/// with `Traits` and `Typeclasses`, an error (write `dyn Trait` or
/// `impl Trait`).
///
/// # Examples
///
/// ```
/// use typeck_lang::Polymorphism;
///
/// assert_ne!(Polymorphism::Traits, Polymorphism::Typeclasses);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Polymorphism {
    /// Nominal implementations, coherent, separate from the type (Rust).
    Traits,
    /// Declared at the class, checked structurally against the interface
    /// (Java, Go, Kraken).
    Interfaces,
    /// Dictionary-passing typeclasses (Haskell).
    Typeclasses,
}

/// What `let x = null` (no annotation) gives `x` (ISSUES P17).
///
/// # Examples
///
/// ```
/// use typeck_lang::NullLet;
///
/// assert_ne!(NullLet::NullType, NullLet::Nullable);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum NullLet {
    /// The type of the literal, `null`: the variable can only ever hold
    /// `null` (the 0.2 convention).
    NullType,
    /// `T?` for a `T` inferred from the variable's later uses (an
    /// assignment `x = 5` makes it `i64?`). Under a profile without null
    /// safety, `T` itself.
    Nullable,
}

/// How `?`-style error propagation reaches the checker.
///
/// HIR lowers `e?` as a template (`match e { Ok(v) => v, Err(x) => return
/// Err(x) }`, spec section 8.7), which needs no hook: it is ordinary code. A
/// language whose lowering keeps `?` as a named intrinsic instead gets it
/// typed here: the operand is a *carrier* (a nullable `T?`, or a sum of two
/// variants that is either option-like, one unit variant and one with a
/// single field, or result-like, two single-field variants with the success
/// variant first); the expression has the success value's type, and the
/// enclosing function must return a carrier of the same kind whose failure
/// type the operand's failure converts to.
///
/// # Examples
///
/// ```
/// use typeck_lang::TryHook;
///
/// assert_eq!(TryHook::default(), TryHook::Template);
/// ```
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum TryHook {
    /// `?` arrives lowered as a `match`; nothing special.
    #[default]
    Template,
    /// `Intrinsic::Named(name)` with one operand is `?`.
    Intrinsic {
        /// The intrinsic's name.
        name: Symbol,
        /// An interface (by name, among this unit's interfaces) whose
        /// implementation `impl Conv<E1> for E2` lets a failure of type `E1`
        /// propagate out of a function failing with `E2` (Rust's `From`).
        /// `None`: the failure types must be equal.
        convert: Option<Symbol>,
    },
}

/// A type-system profile.
///
/// Built from a preset and adjusted with the `with_*` methods; fields are
/// public to read. `#[non_exhaustive]`: profiles grow toggles as disciplines
/// land, without breaking callers that start from a preset.
///
/// # Examples
///
/// ```
/// use typeck_lang::{Profile, RecordTyping};
///
/// let iron_like = Profile::static_explicit()
///     .with_records(RecordTyping::Nominal)
///     .with_numeric_widening(false);
/// assert!(iron_like.null_safety);
/// assert!(!iron_like.numeric_widening);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct Profile {
    /// How much is checked and inferred.
    pub discipline: Discipline,
    /// A subclass value may be used where a base class is expected, and (with
    /// structural records) a record with extra fields where fewer are
    /// expected.
    pub subtyping: bool,
    /// Nominal or structural records.
    pub records: RecordTyping,
    /// Lossless numeric conversions are implicit (`i32` to `i64`, `f32` to
    /// `f64`, integers to floats that hold them exactly), and integer
    /// literals may type as floats.
    pub numeric_widening: bool,
    /// `null` inhabits only `T?` types (Kotlin, Kraken). When `false`, `null`
    /// coerces to any non-value type: references, pointers, nominal types,
    /// functions, strings, slices, maps (Java, Go).
    pub null_safety: bool,
    /// `match` must cover every value of the scrutinee's type.
    pub exhaustive_match: bool,
    /// Traits, interfaces, or typeclasses: what an interface name means as
    /// a type.
    pub polymorphism: Polymorphism,
    /// The type of an unsuffixed integer literal that nothing constrains.
    pub default_int: Prim,
    /// The type of an unsuffixed float literal that nothing constrains.
    pub default_float: Prim,
    /// `add` on two strings is concatenation.
    pub string_add: bool,
    /// Under `Dynamic`: report the arity and shape errors that are certain
    /// whatever the run-time values (wrong argument count to a known
    /// function, an unknown named argument or record field, a constructor
    /// pattern of the wrong length).
    pub certain_errors: bool,
    /// Method receivers are borrowed (`&x`, `&mut x`) and dereferenced
    /// implicitly to fit the method's receiver parameter, and lookup looks
    /// through references (Rust, Iron). When `false`, the receiver must
    /// already have the receiver parameter's type.
    pub method_autoref: bool,
    /// Which generic items the monomorphization plan copies per
    /// instantiation and which it shares through dictionary passing.
    pub mono: MonoPolicy,
    /// What `let x = null` gives `x`.
    pub null_let: NullLet,
    /// How `?` reaches the checker.
    pub try_hook: TryHook,
}

impl Default for Profile {
    /// [`Profile::static_explicit`].
    fn default() -> Self {
        Self::static_explicit()
    }
}

impl Profile {
    /// Python, Lua, Mox: no static type errors, only certain shape errors.
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{Discipline, Profile};
    ///
    /// let p = Profile::dynamic();
    /// assert_eq!(p.discipline, Discipline::Dynamic);
    /// assert!(p.certain_errors);
    /// ```
    #[must_use]
    pub const fn dynamic() -> Self {
        Self {
            discipline: Discipline::Dynamic,
            subtyping: true,
            records: RecordTyping::Structural,
            numeric_widening: true,
            null_safety: false,
            exhaustive_match: false,
            polymorphism: Polymorphism::Interfaces,
            default_int: Prim::I64,
            default_float: Prim::F64,
            string_add: true,
            certain_errors: true,
            method_autoref: true,
            mono: MonoPolicy::Shared,
            null_let: NullLet::NullType,
            try_hook: TryHook::Template,
        }
    }

    /// TypeScript-like: checked where annotated (0.5).
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{Discipline, Profile};
    ///
    /// assert_eq!(Profile::gradual().discipline, Discipline::Gradual);
    /// ```
    #[must_use]
    pub const fn gradual() -> Self {
        Self {
            discipline: Discipline::Gradual,
            null_safety: true,
            ..Self::dynamic()
        }
    }

    /// C, Go, Zero: declared types, local inference for `let`.
    ///
    /// Nominal records, no subtyping beyond `Never`, `null` only in `T?`,
    /// no implicit widening, exhaustive `match`, `i64`/`f64` literal
    /// defaults.
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{Profile, RecordTyping};
    ///
    /// let p = Profile::static_explicit();
    /// assert_eq!(p.records, RecordTyping::Nominal);
    /// assert!(p.exhaustive_match);
    /// ```
    #[must_use]
    pub const fn static_explicit() -> Self {
        Self {
            discipline: Discipline::StaticExplicit,
            subtyping: false,
            records: RecordTyping::Nominal,
            numeric_widening: false,
            null_safety: true,
            exhaustive_match: true,
            polymorphism: Polymorphism::Interfaces,
            default_int: Prim::I64,
            default_float: Prim::F64,
            string_add: false,
            certain_errors: true,
            method_autoref: true,
            mono: MonoPolicy::Copy,
            null_let: NullLet::NullType,
            try_hook: TryHook::Template,
        }
    }

    /// Kraken, Iron: bidirectional inference, generics, traits.
    ///
    /// As [`static_explicit`](Self::static_explicit), with traits, closure
    /// signatures inferred from context, and `let x = null` giving a nullable
    /// type inferred from later uses.
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{Discipline, NullLet, Polymorphism, Profile};
    ///
    /// let p = Profile::static_inferred();
    /// assert_eq!(p.discipline, Discipline::StaticInferred);
    /// assert_eq!(p.polymorphism, Polymorphism::Traits);
    /// assert_eq!(p.null_let, NullLet::Nullable);
    /// ```
    #[must_use]
    pub const fn static_inferred() -> Self {
        Self {
            discipline: Discipline::StaticInferred,
            polymorphism: Polymorphism::Traits,
            null_let: NullLet::Nullable,
            ..Self::static_explicit()
        }
    }

    /// ML: Hindley-Milner with let-polymorphism (0.5).
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{Discipline, Polymorphism, Profile};
    ///
    /// let p = Profile::hm();
    /// assert_eq!(p.discipline, Discipline::Hm);
    /// assert_eq!(p.polymorphism, Polymorphism::Typeclasses);
    /// ```
    #[must_use]
    pub const fn hm() -> Self {
        Self {
            discipline: Discipline::Hm,
            polymorphism: Polymorphism::Typeclasses,
            ..Self::static_explicit()
        }
    }

    /// Sets [`subtyping`](Self::subtyping).
    ///
    /// # Examples
    ///
    /// ```
    /// assert!(typeck_lang::Profile::static_explicit().with_subtyping(true).subtyping);
    /// ```
    #[must_use]
    pub const fn with_subtyping(mut self, on: bool) -> Self {
        self.subtyping = on;
        self
    }

    /// Sets [`records`](Self::records).
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{Profile, RecordTyping};
    ///
    /// let p = Profile::static_explicit().with_records(RecordTyping::Structural);
    /// assert_eq!(p.records, RecordTyping::Structural);
    /// ```
    #[must_use]
    pub const fn with_records(mut self, records: RecordTyping) -> Self {
        self.records = records;
        self
    }

    /// Sets [`numeric_widening`](Self::numeric_widening).
    ///
    /// # Examples
    ///
    /// ```
    /// assert!(typeck_lang::Profile::static_explicit().with_numeric_widening(true).numeric_widening);
    /// ```
    #[must_use]
    pub const fn with_numeric_widening(mut self, on: bool) -> Self {
        self.numeric_widening = on;
        self
    }

    /// Sets [`null_safety`](Self::null_safety).
    ///
    /// # Examples
    ///
    /// ```
    /// assert!(!typeck_lang::Profile::static_explicit().with_null_safety(false).null_safety);
    /// ```
    #[must_use]
    pub const fn with_null_safety(mut self, on: bool) -> Self {
        self.null_safety = on;
        self
    }

    /// Sets [`exhaustive_match`](Self::exhaustive_match).
    ///
    /// # Examples
    ///
    /// ```
    /// assert!(!typeck_lang::Profile::static_explicit().with_exhaustive_match(false).exhaustive_match);
    /// ```
    #[must_use]
    pub const fn with_exhaustive_match(mut self, on: bool) -> Self {
        self.exhaustive_match = on;
        self
    }

    /// Sets [`polymorphism`](Self::polymorphism).
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{Polymorphism, Profile};
    ///
    /// let p = Profile::static_inferred().with_polymorphism(Polymorphism::Interfaces);
    /// assert_eq!(p.polymorphism, Polymorphism::Interfaces);
    /// ```
    #[must_use]
    pub const fn with_polymorphism(mut self, polymorphism: Polymorphism) -> Self {
        self.polymorphism = polymorphism;
        self
    }

    /// Sets the literal defaults. A non-integer `int` or non-float `float` is
    /// refused by [`check`](crate::check) with
    /// [`CheckError::InvalidProfile`](crate::CheckError::InvalidProfile).
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::Prim;
    /// use typeck_lang::Profile;
    ///
    /// let p = Profile::static_explicit().with_literal_defaults(Prim::I32, Prim::F32);
    /// assert_eq!(p.default_int, Prim::I32);
    /// ```
    #[must_use]
    pub const fn with_literal_defaults(mut self, int: Prim, float: Prim) -> Self {
        self.default_int = int;
        self.default_float = float;
        self
    }

    /// Sets [`string_add`](Self::string_add).
    ///
    /// # Examples
    ///
    /// ```
    /// assert!(typeck_lang::Profile::static_explicit().with_string_add(true).string_add);
    /// ```
    #[must_use]
    pub const fn with_string_add(mut self, on: bool) -> Self {
        self.string_add = on;
        self
    }

    /// Sets [`certain_errors`](Self::certain_errors).
    ///
    /// # Examples
    ///
    /// ```
    /// assert!(!typeck_lang::Profile::dynamic().with_certain_errors(false).certain_errors);
    /// ```
    #[must_use]
    pub const fn with_certain_errors(mut self, on: bool) -> Self {
        self.certain_errors = on;
        self
    }

    /// Sets [`method_autoref`](Self::method_autoref).
    ///
    /// # Examples
    ///
    /// ```
    /// assert!(!typeck_lang::Profile::static_inferred().with_method_autoref(false).method_autoref);
    /// ```
    #[must_use]
    pub const fn with_method_autoref(mut self, on: bool) -> Self {
        self.method_autoref = on;
        self
    }

    /// Sets [`mono`](Self::mono).
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{MonoPolicy, Profile};
    ///
    /// let iron = Profile::static_inferred().with_mono(MonoPolicy::Selective { max_nodes: 64 });
    /// assert_eq!(iron.mono, MonoPolicy::Selective { max_nodes: 64 });
    /// ```
    #[must_use]
    pub const fn with_mono(mut self, mono: MonoPolicy) -> Self {
        self.mono = mono;
        self
    }

    /// Sets [`null_let`](Self::null_let).
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{NullLet, Profile};
    ///
    /// let p = Profile::static_explicit().with_null_let(NullLet::Nullable);
    /// assert_eq!(p.null_let, NullLet::Nullable);
    /// ```
    #[must_use]
    pub const fn with_null_let(mut self, null_let: NullLet) -> Self {
        self.null_let = null_let;
        self
    }

    /// Sets [`try_hook`](Self::try_hook).
    ///
    /// # Examples
    ///
    /// ```
    /// use intern_lang::Interner;
    /// use typeck_lang::{Profile, TryHook};
    ///
    /// let mut names = Interner::new();
    /// let hook = TryHook::Intrinsic { name: names.intern("try"), convert: None };
    /// assert_eq!(Profile::static_inferred().with_try_hook(hook).try_hook, hook);
    /// ```
    #[must_use]
    pub const fn with_try_hook(mut self, hook: TryHook) -> Self {
        self.try_hook = hook;
        self
    }

    /// Whether the static rules apply (every discipline but `Dynamic`).
    pub(crate) const fn is_static(&self) -> bool {
        !matches!(self.discipline, Discipline::Dynamic)
    }

    /// Whether unannotated closure signatures are inferred.
    pub(crate) const fn infers_closures(&self) -> bool {
        matches!(self.discipline, Discipline::StaticInferred | Discipline::Hm)
    }
}
