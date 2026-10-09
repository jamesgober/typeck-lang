//! Type-system profiles: what a language's checker is, as data.
//!
//! A [`Profile`] is a [`Discipline`] (how much is checked statically and how
//! much is inferred) plus toggles that differ between languages of the same
//! discipline. One checker reads the profile; no language gets its own
//! checker.

use hir_lang::Prim;

/// How much a language checks statically, and how much it infers.
///
/// | Discipline | Like | Static checking | Inference |
/// |---|---|---|---|
/// | `Dynamic` | Python, Lua, Mox | Only statically certain arity and shape errors | none: every value is `any` |
/// | `Gradual` | TypeScript, Mercury | Where annotated; `any` at the boundaries | local |
/// | `StaticExplicit` | C, Go, Zero | Everything | `let` initializers and literals only |
/// | `StaticInferred` | Kraken, Iron | Everything | bidirectional, generics, traits |
/// | `Hm` | ML family | Everything | full, with let-polymorphism |
///
/// Implemented in 0.2.0: `Dynamic` and `StaticExplicit`. The others are
/// designed (see the crate's `dev/ROADMAP.md`) and land in 0.5.0; checking
/// under them returns
/// [`CheckError::NotImplemented`](crate::CheckError::NotImplemented).
///
/// # Examples
///
/// ```
/// use typeck_lang::Discipline;
///
/// assert!(Discipline::Dynamic.is_implemented());
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
        matches!(self, Self::Dynamic | Self::StaticExplicit)
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

/// How a language attaches behaviour to types (consulted by the 0.5
/// `StaticInferred` and `Hm` disciplines).
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
    /// Traits, interfaces, or typeclasses (0.5 disciplines).
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
        }
    }

    /// Kraken, Iron: bidirectional inference, generics, traits (0.5).
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{Discipline, Polymorphism, Profile};
    ///
    /// let p = Profile::static_inferred();
    /// assert_eq!(p.discipline, Discipline::StaticInferred);
    /// assert_eq!(p.polymorphism, Polymorphism::Traits);
    /// ```
    #[must_use]
    pub const fn static_inferred() -> Self {
        Self {
            discipline: Discipline::StaticInferred,
            polymorphism: Polymorphism::Traits,
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

    /// Whether the static rules apply (every discipline but `Dynamic`).
    pub(crate) const fn is_static(&self) -> bool {
        !matches!(self.discipline, Discipline::Dynamic)
    }
}
