# typeck-lang - Roadmap

> Path from scaffold to a stable 1.0. Hard parts are front-loaded; each phase has hard exit criteria.
> Master plan: ../_lexersketch/ROADMAP.md and ../_lexersketch/NEW-LIBS.md
>
> **Anti-deferral rule:** no listed hard task moves to a later phase unless this file records the move and the reason.

## v0.1.0 - Scaffold (DONE)
Compiles, CI green, structure correct, no domain logic.
- [x] Manifest, README, CHANGELOG, REPS, dual license, CI, deny, clippy, rustfmt, DIRECTIVES, ROADMAP.

## v0.2.0 - Foundation
- [ ] Profile model; checker skeleton over HIR; dynamic and static-explicit profiles; diagnostics.
- [ ] Wires hir-lang and type-lang. Property tests: termination, no panics, error-type containment.

## v0.5.0 - Implementation
- [ ] Static-inferred (bidirectional, generics, interfaces/traits, monomorphization plan) and HM (let-polymorphism with levels); gradual profile.

## v0.9.0 - Hardening
- [ ] Adversarial inference inputs (deep and shared types), fuzzing, scale benchmarks.

## v1.0.0 - Stable
- [ ] Frozen after Mox, Mercury, and a Kraken subset check through it (D18).
