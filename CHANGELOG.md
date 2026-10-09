<h1 align="center">
    <img width="90px" height="auto" src="https://raw.githubusercontent.com/jamesgober/jamesgober/main/media/icons/hexagon-3.svg" alt="Triple Hexagon">
    <br><b>CHANGELOG</b>
</h1>
<p>
  All notable changes to <code>typeck-lang</code> will be documented in this file. The format is based on <a href="https://keepachangelog.com/en/1.1.0/">Keep a Changelog</a>,
  and this project adheres to <a href="https://semver.org/spec/v2.0.0.html/">Semantic Versioning</a>.
</p>

---

## [Unreleased]

### Added

### Changed

### Fixed

### Security

---

## [0.3.0] - 2026-10-09

The `static-inferred` discipline (Kraken, Iron): bidirectional checking,
generics, interfaces (traits) with associated types and default methods,
`impl` blocks (generic ones indexed), `dyn` and `impl Trait`, closures with
inferred signatures, a monomorphization plan with a selective policy, and `?`
through a profile hook. Exhaustiveness is decided by match-lang. HIR v3
(hir-lang 0.4): unions and intersections, `let_place`, keyed `yield`,
`yield from`, `bit_not`, `pow`. ISSUES P17 is addressed.

### Breaking

- **hir-lang 0.4** (HIR spec v3) replaces 0.3: `Typed` and every type id
  refer to v3 HIR. `Expr::Yield { key, value }`, `Expr::YieldFrom`,
  `Expr::LetPlace`, `Ty::Union`, `Ty::Intersection`, `OpKind::BitNot`, and
  `OpKind::Pow` are checked; `not` now requires `bool` and `bit_not` an
  integer (HIR splits them).
- **Assignments evaluate to the value stored** (HIR v3 §8.2): `Assign` has
  its target's type, not unit.
- **`Type` views of nominal types carry generic arguments**:
  `Type::Adt { item, args }`, `Type::Foreign { def, args }`,
  `Type::Extern { name, args }` replace the tuple variants. New views:
  `ParamArray`, `ImplParam`, `Union`, `Intersection`, `Trait`, `Dyn`,
  `Projection`, `Opaque`, `Const`. Array lengths are stored as types (a
  constant, or a constant parameter).
- **`Typed::deferred_matches` is removed**: match-lang decides every
  `match`. `NonExhaustive` diagnostics now come with witnesses
  (`Typed::witnesses`, and in the message).
- **`Diagnostic` has a `severity`** (`Severity`); `Typed::is_ok` is true
  when there is no *error* (unreachable arms are warnings).
- **`Feature`** lists only what is still unsupported:
  `GenericAssocTypes` and `LongAssocPaths` replace `Generics`, `Traits`,
  `AssociatedTypes`, and `StructuralImpls`, which are now checked.
- **`Profile`** has new fields (`method_autoref`, `mono`, `null_let`,
  `try_hook`); it is `#[non_exhaustive]`, so code starting from a preset is
  unaffected. `Discipline::StaticInferred` is implemented.
- **`Budget`** has a new field, `trait_depth` (default 256); struct literals
  without `..Budget::default()` need it. `Limit::TraitDepth` is new.
- `Polymorphism` is consulted by both static disciplines (what an interface
  name means where a type is expected).

### Added

- **`static-inferred`**: closure parameters and results inferred from the
  expected function type or from use; `let x = null` typed as a nullable
  inferred from later uses (`NullLet::Nullable`, P17).
- **Bidirectional checking through generic calls**: an expected result type
  is probed into the arguments (rolled back), so a wrong argument is
  reported at itself; record literals of generic types take an expected
  instance before their fields; pending goals are solved before a variable's
  structure is needed (a field, a method, an index, a callee).
- **Generics**: generic functions, records, sums, classes, interfaces,
  impls, and aliases; explicit (`f::<i32>`) and inferred arguments;
  defaults; constant parameters and arguments (`Buf<4>`, `[T; N]`); bounds
  and where clauses checked at instantiation, construction, and in written
  annotations; `impl Trait` parameters (anonymous generics) and results
  (opaque types with hidden types, `Typed::opaque_type`).
- **Interfaces**: methods, default methods, constants, associated types
  (`T::Item`, `Self::Item`, `<T as I>::Item`, `I<Item = T>`, `I<Item: B>`),
  supertraits; implementations by `impl` blocks (generic ones included,
  indexed by self-type head with a blanket bucket: P17) and by classes'
  declared interfaces (inherited by subclasses); member lookup through
  bounds, `dyn`, and implementations; `T::new()`, `Iface::method(x)`,
  `<T as Iface>::method`; overlap reported (`OverlappingImpls`); conformance
  (`MissingMember`, `NotAMember`, signature `Mismatch`); `dyn Iface` with
  required associated-type bindings and `Coercion::ToDyn`.
- **Receiver auto-ref and auto-deref as a profile toggle**
  (`Profile::method_autoref`).
- **Unions and intersections** with canonical forms (`Types::union`,
  `Types::intersection`), `Coercion::ToUnion`, `Coercion::FromIntersection`,
  field access across members, type tests against members.
- **Exhaustiveness through match-lang** (P17): a `Model` over the checker's
  types (sums, products, nullable, unions, integer and character domains,
  arrays and slices); missing values as witnesses; `UnreachableArm` and
  `RedundantAlternative` warnings.
- **Monomorphization plan** (`Typed::mono_plan`, `MonoPlan`, `Instance`,
  `Strategy`): every reachable instance of a generic function; interface
  calls on placeholders resolved per instance; `dyn` coercions add their
  vtable's methods; `MonoPolicy::{Copy, Shared, Selective { max_nodes }}` and
  `Checker::declare_mono_attribute` (Iron's selective monomorphization);
  polymorphic recursion reported (`RecursiveInstantiation`) and cut.
- `Typed::instantiation` (`Instantiation`, `Dispatch`): the generic item,
  arguments, and dispatch (static, through a bound, dynamic) of each use.
- **`?` through a profile hook** (`TryHook::Intrinsic { name, convert }`):
  nullable and two-variant carrier sums, with an optional conversion
  interface (`Coercion::ErrorConvert`); `TryCarrier` otherwise.
- Diagnostics T0040–T0055: `UnreachableArm`, `RedundantAlternative`,
  `NotAnInterface`, `GenericArity`, `NoAssocType`, `AmbiguousAssocType`,
  `Unsatisfied`, `AmbiguousImpl`, `OverlappingImpls`, `MissingMember`,
  `NotAMember`, `InterfaceAsType`, `ImplTraitPosition`,
  `MissingAssocBinding`, `RecursiveInstantiation`, `TryCarrier`.
- `Types::adt_with`, `foreign_with`, `external_with`; host members may be
  declared on a generic host type's bare head.
- Typing conventions recorded in `specs/HIR.md` §8.11 (P17): generator
  result = yield type, `yield`/`yield from` evaluate to unit, `let x = null`
  per profile, assignment values, `?`.
- Tests: `tests/inferred.rs`, `tests/traits.rs`, `tests/generics.rs`,
  `tests/exhaustive.rs`, `tests/mono.rs` (plan and `?`),
  `tests/kraken_corpus.rs` (Kraken-like programs),
  `tests/adversarial_generics.rs` (deep generics, recursive bounds, cycles,
  scale, small stacks), `tests/properties_generic.rs` (a typed generator over
  generics and interfaces: exact types, dispatch, and plan instances;
  single-mutation blame; error containment; determinism); the arbitrary-HIR
  generator covers the v3 forms, generics, interfaces, impls, `dyn`, `impl
  Trait`, unions, and the `?` hook under five profiles. Benchmarks: the 100k
  and 1M programs under `static-inferred`, and generic-heavy programs at 100k
  and 1M nodes. Example: `generics`.

### Changed

- Version 0.3.0. Wires `hir-lang` 0.4 and `match-lang` 0.2.
- Unifying `{error}` with a structured type binds that type's variables to
  `{error}` (error containment through generic structure); of two equal
  terms, a variable-free one represents their class.

### Fixed

- Member lookups on types extended by generic impls are no longer silently
  skipped (P17).

---

## [0.2.0] - 2026-10-08

The foundation: one type checker over HIR, configured by a type-system profile.
The `dynamic` and `static-explicit` disciplines are implemented; `gradual`,
`static-inferred`, and `hm` are designed (`dev/ROADMAP.md`) and return
`CheckError::NotImplemented` until 0.5.0.

### Added

- `check(&hir, &profile)` (Tier 1) and `Checker` (Tier 2): host declarations
  (`declare_extern`, `declare_foreign`, `declare_intrinsic`, `declare_member`)
  with types built in `types_mut`, and `set_budget`.
- The profile model as data: `Profile` (discipline plus `subtyping`,
  `records`, `numeric_widening`, `null_safety`, `exhaustive_match`,
  `polymorphism`, literal defaults, `string_add`, `certain_errors`), presets
  for every discipline, `Discipline`, `RecordTyping`, `Polymorphism`.
- The `dynamic` discipline: every value `any`; with `certain_errors`, the
  arity and shape errors that fail whatever the run-time values.
- The `static-explicit` discipline: declared signatures, fields, constants,
  and globals; `let` inference and deferred initialisation; literal classes
  with defaults and range checks; tuples, arrays, slices, references,
  pointers, functions, nullables, maps, structural records, records, sums,
  classes, host and foreign nominal types, aliases; OPS operations typed by
  operand type with policy legality (`promote` rejected on static results);
  casts; calls with named, default, variadic, spread, and by-reference
  parameters; fields and methods through `impl` blocks, classes, base classes,
  references, and host members; control flow, closures, effects (`async`,
  `await`, `spawn`, generators, `throw`/`try`/`catch`), intrinsics; the
  certain part of `match` exhaustiveness, with nested coverage deferred.
- Partial-path tails resolved by type (`Shape::Circle`, `Point::new`,
  `Self::`, `parent::`), reported by `Typed::path_def`.
- `Typed`: dense types per expression, pattern, and binder; diagnostics in
  source order; coercions; op classes; method dispatch; deferred matches;
  stats. `Diagnostic`, `DiagnosticKind` (stable codes `T0001`...), `Feature`.
- `Types`, `TypeId`, `Type`, `Field`, `TypeDisplay`: a hash-consed type store
  with a capped, iterative renderer.
- Termination and budgets: union-find over interned terms (linear on shared
  structure, ISSUES M39), journaled rollback, memoized zonking, iterative
  traversals, `Budget`, `Limit`, `CheckError`.
- Tests: unit tests; integration tests per rule; property tests (typed
  generator with exact types, single-mutation diagnostics at the mutation
  site, error containment, determinism, totality on arbitrary repaired HIR,
  any budget terminates); adversarial and scale tests; criterion benchmarks
  at 100k and 1M HIR nodes; `quickstart` and `host` examples.

### Changed

- Version 0.2.0. Wires `hir-lang` 0.3 and `intern-lang` 1. `type-lang` 1 is
  deliberately not wired (its unifier expands shared structure, M39-M41); the
  reasoning, and the recommendation that type-lang 2.0 adopt this crate's
  store, are in `dev/ROADMAP.md`.
- `dev/DIRECTIVES.md` §1 states that solving runs on typeck-lang's own store.

---

## [0.1.0] - 2026-10-08

Initial scaffold and repository bootstrap. No domain logic yet &mdash; this release establishes the structure, tooling, and quality gates the implementation will be built on.

### Added

- `Cargo.toml` with crate metadata, Rust 2024 edition, MSRV 1.85.
- Dual `Apache-2.0 OR MIT` license files.
- `README.md`, `CHANGELOG.md`, and a documentation skeleton.
- `REPS.md` compliance baseline.
- `.github/workflows/ci.yml` CI matrix; `deny.toml`, `clippy.toml`, `rustfmt.toml`.
- `dev/DIRECTIVES.md` and `dev/ROADMAP.md` (committed engineering standards + plan).

[Unreleased]: https://github.com/jamesgober/typeck-lang/compare/v0.3.0...HEAD
[0.3.0]: https://github.com/jamesgober/typeck-lang/compare/v0.2.0...v0.3.0
[0.2.0]: https://github.com/jamesgober/typeck-lang/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/jamesgober/typeck-lang/releases/tag/v0.1.0
