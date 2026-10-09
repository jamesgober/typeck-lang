<h1 align="center">
    <img width="99" alt="Rust logo" src="https://raw.githubusercontent.com/jamesgober/rust-collection/72baabd71f00e14aa9184efcb16fa3deddda3a0a/assets/rust-logo.svg">
    <br>
    <b>typeck-lang</b>
    <br>
    <sub><sup>PROFILE-DRIVEN TYPE CHECKING</sup></sub>
</h1>

<div align="center">
    <a href="https://crates.io/crates/typeck-lang"><img alt="Crates.io" src="https://img.shields.io/crates/v/typeck-lang"></a>
    <a href="https://crates.io/crates/typeck-lang"><img alt="Downloads" src="https://img.shields.io/crates/d/typeck-lang?color=%230099ff"></a>
    <a href="https://docs.rs/typeck-lang"><img alt="docs.rs" src="https://img.shields.io/docsrs/typeck-lang"></a>
    <a href="https://github.com/jamesgober/typeck-lang/actions"><img alt="CI" src="https://github.com/jamesgober/typeck-lang/actions/workflows/ci.yml/badge.svg"></a>
    <a href="https://github.com/rust-lang/rfcs/blob/master/text/2495-min-rust-version.md"><img alt="MSRV" src="https://img.shields.io/badge/MSRV-1.85%2B-blue"></a>
</div>

<br>

<div align="left">
    <p>
        <strong>typeck-lang</strong> type-checks HIR (the <a href="https://crates.io/crates/hir-lang"><code>hir-lang</code></a> representation every LexerSketch language lowers into) under a <strong>type-system profile</strong> instead of per-language code. A profile is data: a discipline &mdash; <code>dynamic</code>, <code>gradual</code>, <code>static-explicit</code>, <code>static-inferred</code>, or <code>hm</code> &mdash; plus toggles for subtyping, nominal or structural records, implicit numeric widening, null safety, exhaustive matches, and traits versus interfaces.
    </p>
    <p>
        The result is a side table of types keyed by HIR ids (every live expression, pattern, and binder), typed diagnostics with origins, the implicit conversions lowering must materialise, how each OPS operation resolved (integer, IEEE, string), and the definitions of partial paths' unresolved tails (<code>Shape::Circle</code>, <code>Point::new</code>). One mistake produces one diagnostic: anything reported has the error type, which every later check accepts silently.
    </p>
    <br>
    <hr>
    <p>
        <strong>MSRV is 1.85+</strong> (Rust 2024 edition). <code>no_std</code>-compatible (needs only <code>alloc</code>), <code>#![forbid(unsafe_code)]</code>, two dependencies from the family: <a href="https://crates.io/crates/hir-lang"><code>hir-lang</code></a> 0.3 and <a href="https://crates.io/crates/intern-lang"><code>intern-lang</code></a> 1.
    </p>
    <blockquote>
        <strong>Status: pre-1.0 (0.2.0).</strong> This release implements the <code>dynamic</code> and <code>static-explicit</code> disciplines. <code>gradual</code>, <code>static-inferred</code> (generics, traits, bidirectional inference), and <code>hm</code> are designed in <a href="./dev/ROADMAP.md"><code>dev/ROADMAP.md</code></a> and land in 0.5.0; checking under them returns <code>CheckError::NotImplemented</code>. See <a href="./CHANGELOG.md"><code>CHANGELOG.md</code></a>.
    </blockquote>
</div>

<hr>
<br>

## What it does

- **`static-explicit`** (C, Go, Zero): declared types on parameters, returns, fields, constants, and globals; local inference for `let` from initializers and for unsuffixed literals; primitive, tuple, array, slice, reference, pointer, function, nullable, map, record, sum, and class types; every OPS operation typed by its operand types, with policy legality (`promote` is rejected on statically typed results); calls with named, default, variadic, and spread arguments; fields and methods through `impl` blocks, classes, and base classes; `if`, `match`, loops, labelled blocks, closures, `async`/`await`/`spawn`, generators, `try`/`catch` with type tests, casts, and intrinsics.
- **`dynamic`** (Python, Lua, Mox): every value is `any`; only the errors that are certain whatever the run-time values are reported (wrong argument count to a known function, unknown named arguments, constructor patterns of the wrong length, unknown record fields).
- **Host declarations**: a language's library lives outside the unit; `Checker` takes the types of extern names, other units' definitions, named intrinsics, and members of host types.

Not in this release, and reported as `Unsupported` rather than guessed: generic items and arguments, traits and interfaces used as types, associated types (all 0.5.0). Not this crate's job: name resolution (resolve-lang), precise pattern exhaustiveness (match-lang: the checker verifies top-level constructor coverage and lists the rest in `Typed::deferred_matches`), and mutability and ownership (capabilities over typed HIR).

What each guarantee rests on:

| Guarantee | How it is checked |
|---|---|
| Well-typed programs check clean, with exactly the types they should have. | A typed generator builds random well-typed programs (arithmetic, comparisons, `if`, blocks, calls, tuples, arrays, records, sums with `match`, constructor calls, method calls, field access, indexing); property tests require no diagnostic, the generated type for every expression, and the right method for every method call. |
| One mistake, one diagnostic, at the mistake. | Property: replacing one numeric literal of a well-typed program with `true` yields exactly one diagnostic, on that literal. Property: replacing any leaf with an error node yields none. |
| Checking never panics and always terminates. | Property: random HIR of every form, repaired by `hir-lang`'s lenient validation, checks without panicking under three profiles, types every live expression and pattern, and is deterministic; under any step budget it finishes or returns `BudgetExceeded`. |
| Shared type structure is never expanded (type-lang's ISSUES M39). | Types are hash-consed terms in a union-find store. Unifying two `Pair(v, v)` doubling chains is linear: step counts are compared at 2,000 and 4,000 levels, and 50,000 levels check in a test. |
| Work is linear in the program. | Step counts at 2,000 and 20,000 functions differ by the size factor. Deep input is checked on an explicit stack: tests cover 100,000-deep expressions, 50,000 nested blocks and `if`s, 30,000-deep types and patterns, 20,000-long alias chains, and 5,000-deep inheritance. |

<hr>
<br>

## Installation

```toml
[dependencies]
typeck-lang = "0.2"
```

Without the standard library:

```toml
[dependencies]
typeck-lang = { version = "0.2", default-features = false }
```

<hr>
<br>

## Quick start

```rust
use hir_lang::{Builder, Lit, Name, NodeRef, OpKind};
use intern_lang::Interner;
use typeck_lang::{check, Profile, TypeId};

let mut names = Interner::new();
let mut b = Builder::new();
// fn main() { let x = 1 + true; }
let one = b.int(1);
let yes = b.lit(Lit::Bool(true));
let sum = b.op(OpKind::Add, &[one, yes]);
let x = b.new_binder(Name::new(names.intern("x")), hir_lang::BinderKind::Local);
let pat = b.bind(x);
let stmt = b.let_stmt(pat, Some(sum));
let body = b.block(&[stmt], None);
let main = b.func(Name::new(names.intern("main")), &[], body);
let root = b.module(None, &[main]);
let hir = b.finish(root)?;

// Static: one diagnostic, at `true`; `x` is the error type, so nothing
// that uses it is reported again.
let typed = check(&hir, &Profile::static_explicit()).unwrap();
let d = typed.diagnostics()[0];
assert_eq!(d.node, NodeRef::Expr(yes));
assert_eq!(d.kind.code(), "T0018");
assert_eq!(typed.message(&d, &names), "`add` is not defined for `bool`");
assert_eq!(typed.binder(x), Some(TypeId::ERROR));

// Dynamic: no static errors; every value is `any`.
let typed = check(&hir, &Profile::dynamic()).unwrap();
assert!(typed.is_ok());
assert_eq!(typed.binder(x), Some(TypeId::ANY));
# Ok::<(), hir_lang::HirError>(())
```

Profiles start from a preset and adjust toggles:

```rust
use typeck_lang::{Profile, RecordTyping};

let kraken_like = Profile::static_explicit()
    .with_records(RecordTyping::Nominal)
    .with_subtyping(true)
    .with_numeric_widening(true)
    .with_string_add(true);
assert!(kraken_like.null_safety);
```

Host declarations go through [`Checker`](./docs/API.md#checker):

```rust
use hir_lang::{Builder, Effects, Expr, Name, Ns, Prim, Res};
use intern_lang::Interner;
use typeck_lang::{Checker, Profile, TypeId};

let mut names = Interner::new();
let print = names.intern("print");
let mut b = Builder::new();
// fn main() { print("hi") }  -- `print` is bound by the host
let path = b.resolved_path(Name::new(print), Ns::Value, Res::Extern(print));
let callee = b.expr(Expr::Path(path));
let hi = b.str_lit("hi");
let call = b.call(callee, &[hi]);
let stmt = b.expr_stmt(call);
let body = b.block(&[stmt], None);
let main = b.func(Name::new(names.intern("main")), &[], body);
let root = b.module(None, &[main]);
let hir = b.finish(root)?;

let mut checker = Checker::new(&hir, Profile::static_explicit());
let print_ty = checker.types_mut().func(&[TypeId::prim(Prim::Str)], TypeId::UNIT, Effects::NONE);
checker.declare_extern(print, print_ty);
let typed = checker.check().unwrap();
assert!(typed.is_ok());
# Ok::<(), hir_lang::HirError>(())
```

Runnable programs: `cargo run --example quickstart`, `cargo run --example host`.

<hr>
<br>

## Performance

`cargo bench --bench bench`, release profile, Windows x86_64. Library only: the HIR is built before timing starts. Measured on a machine shared with concurrent builds (CPU at 100%), so these are ranges across runs and upper bounds; re-measure on an idle machine before quoting them.

| Benchmark | Time | Throughput |
|---|---:|---:|
| `static-explicit`, 100k HIR nodes | 14.7&ndash;17.1 ms | 5.7&ndash;6.6 M nodes/s |
| `static-explicit`, 1M HIR nodes | 130&ndash;200 ms | 4.8&ndash;7.5 M nodes/s |
| `dynamic`, 100k HIR nodes | 3.6&ndash;5.7 ms | 17&ndash;27 M nodes/s |
| `dynamic`, 1M HIR nodes | 49&ndash;80 ms | 12&ndash;20 M nodes/s |
| Doubling chain, 100k levels (1.4M nodes) | 227&ndash;347 ms | 4.0&ndash;6.2 M nodes/s |

<hr>
<br>

## Platforms

Linux, macOS, and Windows. The crate uses no operating-system facilities: a program checks the same way, with the same type ids and diagnostics, on every platform.

<hr>
<br>

## Contributing

See [`REPS.md`](./REPS.md) for the engineering standards every change is held to, [`dev/DIRECTIVES.md`](./dev/DIRECTIVES.md) for the definition of done, and [`dev/ROADMAP.md`](./dev/ROADMAP.md) for the plan. Before a PR: `cargo fmt --all`, `cargo clippy --all-targets --all-features -- -D warnings`, and `cargo test --all-features` must be clean.

<br>

<div id="license">
    <h2>License</h2>
    <p>Licensed under either of</p>
    <ul>
        <li><b>Apache License, Version 2.0</b> &mdash; <a href="./LICENSE-APACHE">LICENSE-APACHE</a></li>
        <li><b>MIT License</b> &mdash; <a href="./LICENSE-MIT">LICENSE-MIT</a></li>
    </ul>
    <p>at your option.</p>
</div>

<div align="center">
  <h2></h2>
  <sup>COPYRIGHT <small>&copy;</small> 2026 <strong>James Gober.</strong></sup>
</div>
