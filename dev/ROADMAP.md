# typeck-lang - Roadmap

> Path from scaffold to a stable 1.0. Hard parts are front-loaded; each phase has hard exit criteria.
> Master plan: ../_lexersketch/ROADMAP.md and ../_lexersketch/NEW-LIBS.md
>
> **Anti-deferral rule:** no listed hard task moves to a later phase unless this file records the move and the reason.

## v0.1.0 - Scaffold (DONE)
Compiles, CI green, structure correct, no domain logic.
- [x] Manifest, README, CHANGELOG, REPS, dual license, CI, deny, clippy, rustfmt, DIRECTIVES, ROADMAP.

## v0.2.0 - Foundation (DONE)
- [x] Profile model; checker over HIR; dynamic and static-explicit profiles; diagnostics.
- [x] Wires hir-lang (type-lang deliberately not wired: see "Dependency wiring"). Property tests: termination, no panics, error-type containment.

Exit criteria:
- [x] Every public item has rustdoc and a runnable example; README and `docs/API.md` code blocks run as doctests.
- [x] Every `dev/DIRECTIVES.md` §4 invariant property-tested (see "How the invariants are tested").

Delivered:
- **Profile model as data**: `Profile` (discipline + toggles: `subtyping`, `records`
  nominal/structural, `numeric_widening`, `null_safety`, `exhaustive_match`,
  `polymorphism` traits/interfaces/typeclasses, literal defaults, `string_add`,
  `certain_errors`), presets for all five disciplines, `Discipline::is_implemented`.
- **`dynamic`**: every live expression, pattern, and bound binder is `any`; annotations are
  not lowered; with `certain_errors`, the statically certain arity and shape errors (calls of
  known functions without spreads, tuple-constructor calls and patterns of the wrong length,
  unknown record fields of records and variants).
- **`static-explicit`**: declared types on parameters, returns, fields, constants, and globals;
  `let` inference from initializers and deferred assignment; literal classes with defaults and
  range checks; primitive, tuple, array, slice, reference, pointer, function, nullable, map,
  structural-record, record/sum/class, host, and foreign types; aliases (cycle detection);
  OPS ops typed per operand type with policy legality (`promote` rejected on static results)
  and resolved op classes; casts; calls with positional/named/default/rest/named-rest
  parameters, spreads, and by-reference parameters; field and method access through `impl`
  blocks, classes, base classes, references, and host members (auto-ref/deref receivers);
  `if`/`match`/`loop`/labelled blocks/`break` values/`return`; closures (captures, recursive
  self binders); `async`/`await`/`spawn`, generators and `yield`, `throw`/`try`/`catch` with
  type tests; atomic, volatile, fence, and host-declared named intrinsics; inline assembly
  operands; the certain part of exhaustiveness (top-level constructor coverage, nested
  coverage deferred to match-lang).
- **Partial paths**: one-segment tails resolved by type (variants, `impl`/class/host members,
  `Self::`/`static::`/`parent::` roots) and reported in `Typed::path_def`.
- **Output**: `Typed` with dense side tables (expressions, patterns, binders), diagnostics
  (37 kinds, stable codes `T0001`...) with origins in source order, coercions, op classes,
  method dispatch, partial-path definitions, deferred matches, stats.
- **Host declarations**: `Checker::declare_extern`, `declare_foreign`, `declare_intrinsic`,
  `declare_member`, with types built in `Checker::types_mut`.
- **Termination and budgets**: hash-consed type store with union-find (Huet merging before
  decomposition, journaled rollback, memoized zonking, has-var-pruned occurs check), every
  traversal iterative, `Budget` (steps, type-store size) with `CheckError::BudgetExceeded`.
- **One root cause, one diagnostic**: expected types pushed down to where a mistake is made;
  reported expressions are poisoned to `{error}`, which every check accepts silently.

How the invariants are tested:
- *Never panics, always terminates*: `tests/arbitrary.rs` (random HIR of every form repaired by
  lenient validation, three profiles, every live expression and pattern typed, determinism;
  any step budget finishes or errors); `tests/adversarial.rs` (100k-deep expressions, 50k
  blocks/ifs, 30k-deep types and patterns, 20k-alias chains, 5k-class inheritance chains,
  2^40-element array spreads, budgets).
- *Every expression typed; one root cause, one diagnostic*: `tests/properties.rs` (typed
  generator over primitives, tuples, arrays, a record with a method, and a sum matched with
  `match`: exact types and method dispatch; one-literal mutation gives exactly one diagnostic
  at the literal; error nodes give none; determinism; dynamic accepts all; a coverage test
  keeps the generator from going vacuous).
- *Profiles sound for what they claim*: rule-by-rule tests in `tests/static_explicit.rs`,
  `tests/features.rs`, `tests/dynamic.rs`, `tests/host.rs`. (No mechanised soundness proof.)
- *Shared structure never expanded*: unit test (20k-level unification, linear steps) and
  `tests/adversarial.rs` (step counts at 2k vs 4k levels, 50k levels end to end).

Dependency wiring (decided here, recorded per the anti-deferral rule):
- **hir-lang 0.3: wired.** The input; side tables are keyed by its ids.
- **intern-lang 1: wired.** `Lookup` renders names in types and messages (same interner
  version hir-lang uses).
- **type-lang 1: not wired.** The task was to use it only if its defects (ISSUES M39-M41)
  could not be triggered through this crate's usage. They can:
  - M39 (exponential occurs check, `resolve`, mismatch construction on shared structure) is
    triggered by ordinary local inference: `let x1 = (x0, x0); let x2 = (x1, x1); ...` gives
    `x_n` a type whose tree has 2^n leaves. type-lang's `Type` is an owned tree
    (`App(TyCon, Vec<Type>)`), so building that type alone is exponential before any
    unification, and unifying it with another chain (`y_n = x_n`) runs its occurs check and
    `resolve` over the tree. No usage pattern avoids this: every `let` whose initializer
    mentions a variable twice copies its type.
  - M40 (recursive `resolve`, `Clone`, `Drop`, `PartialEq`, `Display`; deep clones in
    `unify`): deep annotations and deep literals (100k levels are in this crate's tests) would
    overflow the stack through any of those.
  - M41 (unvalidated deserialized unifiers) does not arise here (nothing is deserialized), but
    M39 and M40 alone rule type-lang 1 out.
  - Instead, typeck-lang has its own store (`src/types.rs`, `src/infer.rs`): hash-consed
    nodes (structural sharing is free, equality is an id compare), one union-find over all
    nodes with Huet merging (each class pair is decomposed once), a journal for rollback (a
    failed unification leaves no merge behind, so shared interned terms are never poisoned), an
    occurs check over class representatives with a visited set and variable-free subtrees
    skipped in O(1), memoized zonking, iterative everything, budgeted.
  - **Recommendation for type-lang 2.0:** adopt this store as its core (interned terms +
    union-find + journal + memoized zonk), keeping its `TyCon`-indexed application form as a
    view. typeck-lang would then depend on type-lang 2.0 for the store and keep the checking
    rules. Until then the store lives here; it is internal (`pub(crate)`), so moving it is not a
    breaking change for typeck-lang's users.
- **resolve-lang, match-lang: not wired.** typeck consumes resolutions already in the HIR and
  defers precise exhaustiveness to match-lang through `Typed::deferred_matches`; the
  LexerSketch app connects them (single responsibility).

Moved to v0.5.0 (anti-deferral record). Each is reported as `Unsupported` (or the 0.5
disciplines return `CheckError::NotImplemented`) rather than guessed:
- **Generic items and generic arguments** (`Feature::Generics`). Instantiation needs the
  bound language (traits/interfaces) to type anything useful inside generic bodies; designing
  instantiation without bounds would be redone in 0.5. Inside a generic item its parameters are
  rigid types today, so bodies are still checked.
- **Traits and interfaces as types, qualified paths, `T::method`** (`Feature::Traits`), and
  **associated types** (`Feature::AssociatedTypes`): the trait-resolution engine of
  `static-inferred`.
- **`impl` blocks on structural types** (`Feature::StructuralImpls`): need generic impl
  matching.
- **Interface conformance** (a class or `impl` providing every interface member with
  compatible signatures): part of the trait engine; members are already checked as items.
- **`gradual`, `static-inferred`, `hm` disciplines**: designed below; they depend on the
  items above.

Not this crate's job (recorded so they are not mistaken for deferrals): name resolution and
visibility (resolve-lang), precise exhaustiveness and usefulness (match-lang), mutability,
ownership, and borrowing (capabilities over typed HIR, borrow-cc), mixin expansion (resolve-lang
expands `MixinUse`; until then member lookups on classes using mixins stay silent).

## v0.5.0 - Implementation
- [ ] Static-inferred (bidirectional, generics, interfaces/traits, monomorphization plan) and HM (let-polymorphism with levels); gradual profile.
- [ ] Generic items and arguments, traits/interfaces as types, associated types, qualified paths, `impl` on structural types, interface conformance (moved from 0.2.0, above).

Designs (the profile model already carries every toggle these need):

**`gradual`** (TypeScript, Mercury). Annotated positions are checked exactly as in
`static-explicit`; an unannotated parameter, field, or return is `any`. `any` is the dynamic
type of gradual typing: it is *consistent* with every type in both directions (a coercion
`ToAny` one way, a run-time-checked `FromAny` cast the other), so a typed value flows into
untyped code and back with checks at the boundary, recorded as coercions for lowering to emit.
Operations on `any` are dynamic (`OpClass::Dynamic`, `promote` legal). `let` inference as in
`static-explicit`. Soundness claim: a run-time type error can only occur at a recorded
`FromAny` boundary.

**`static-inferred`** (Kraken, Iron). Bidirectional checking: expected types already flow
down (0.2.0's expectation machinery becomes the checking mode); closures take parameter types
from the expected function type; method calls and generic calls instantiate fresh variables
from the callee's generics and unify argument types with them. Generics: `Adt(item, args)`
terms (the store already interns argument lists), substitution by memoized rebuild (linear in
the DAG, like zonking). Bounds and `impl` selection: a goal queue of `T: Trait` obligations
solved after each item against an index of `impl` heads (traits: coherent, nominal;
interfaces: structural against the class's declared interfaces; selected by the profile's
`polymorphism`). Associated types normalise through the selected `impl`. Monomorphization
plan: `Typed` gains the set of instantiations reached from each root (the selective
monomorphization of LANGUAGES.md, Iron) for codegen to choose dictionary passing or copies.

**`hm`** (ML family). Algorithm W with **levels** for let-generalization: every variable
carries the level of the `let` that created it (the union-find root keeps the minimum), so
generalization is a scan of variables above the current level, never of the environment.
Schemes are stored as `(quantified vars, body TypeId)`; instantiation is a memoized rebuild.
Value restriction for effectful bindings. No annotations required anywhere; annotations, if
present, are checked as in `static-explicit`.

## v0.9.0 - Hardening
- [ ] Adversarial inference inputs (deep and shared types), fuzzing, scale benchmarks (0.2.0
  already covers deep and shared types and 1M-node benchmarks for its disciplines; 0.9 repeats
  the work for the 0.5 disciplines, adds a fuzz target over the HIR binary decoder once
  hir-lang 0.5 ships it).

## v1.0.0 - Stable
- [ ] Frozen after Mox, Mercury, and a Kraken subset check through it (D18).
