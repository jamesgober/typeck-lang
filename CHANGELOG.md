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

[Unreleased]: https://github.com/jamesgober/typeck-lang/compare/v0.2.0...HEAD
[0.2.0]: https://github.com/jamesgober/typeck-lang/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/jamesgober/typeck-lang/releases/tag/v0.1.0
