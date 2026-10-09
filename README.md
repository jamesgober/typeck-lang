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
        The result is a side table of types keyed by HIR ids (every live expression, pattern, and binder), typed diagnostics with origins, the implicit conversions lowering must materialise, how each OPS operation resolved (integer, IEEE, string), the definitions of partial paths' unresolved tails (<code>Shape::Circle</code>, <code>T::new</code>), what each use of a generic item instantiates, and a <strong>monomorphization plan</strong>: every instance of a generic function the program reaches, copied or shared through dictionary passing. One mistake produces one diagnostic: anything reported has the error type, which every later check accepts silently.
    </p>
    <br>
    <hr>
    <p>
        <strong>MSRV is 1.85+</strong> (Rust 2024 edition). <code>no_std</code>-compatible (needs only <code>alloc</code>), <code>#![forbid(unsafe_code)]</code>, three dependencies, all from the family: <a href="https://crates.io/crates/hir-lang"><code>hir-lang</code></a> 0.4, <a href="https://crates.io/crates/intern-lang"><code>intern-lang</code></a> 1, and <a href="https://crates.io/crates/match-lang"><code>match-lang</code></a> 0.2.
    </p>
    <blockquote>
        <strong>Status: pre-1.0 (0.3.0).</strong> This release implements the <code>dynamic</code>, <code>static-explicit</code>, and <code>static-inferred</code> disciplines. <code>gradual</code> and <code>hm</code> are designed in <a href="./dev/ROADMAP.md"><code>dev/ROADMAP.md</code></a> and land in 0.5.0; checking under them returns <code>CheckError::NotImplemented</code>. See <a href="./CHANGELOG.md"><code>CHANGELOG.md</code></a>.
    </blockquote>
</div>

<hr>
<br>

## What it does

- **`static-inferred`** (Kraken, Iron): everything below, plus closures whose parameter and result types come from the expected function type (or from use), and `let x = null` typed as a nullable inferred from later uses.
- **Generics and interfaces** (both static disciplines): generic functions and types with bounds, where clauses, defaults, and constant parameters; interfaces (traits) with methods, default methods, constants, associated types (`T::Item`, `<T as I>::Item`, `I<Item = u8>`), and supertraits; `impl` blocks, generic ones included; interface methods resolved through bounds, `dyn` types, and implementations, with automatic receiver borrowing as a profile toggle; `impl Trait` parameters and results (the hidden type is reported); overlapping implementations and missing, extra, or mistyped members are reported. Checking mode flows through generic calls: an expected result type reaches the arguments, so a wrong argument is reported at itself.
- **Unions and intersections** (`int|string`, `A & B`) from HIR v3, with injections and type tests.
- **Exhaustiveness** through match-lang: the values a `match` misses are reported as patterns (`non-exhaustive match: Some(false) not covered`); unreachable arms and redundant or-alternatives are warnings.
- **Monomorphization plan**: every reachable instance of a generic function, with a copy-or-share policy per profile (copy all, share all, or Iron's selective policy: copy small or attributed items) and interface calls on placeholders resolved per instance.
- **`?` through a profile hook**: a `?` lowered as a template is ordinary code; one kept as a named intrinsic is typed against nullable and two-variant carrier types, with an optional conversion interface for failure values.
- **`static-explicit`** (C, Go, Zero): declared types on parameters, returns, fields, constants, and globals; local inference for `let` from initializers and for unsuffixed literals; primitive, tuple, array, slice, reference, pointer, function, nullable, map, record, sum, and class types; every OPS operation typed by its operand types, with policy legality (`promote` is rejected on statically typed results); calls with named, default, variadic, and spread arguments; fields and methods through `impl` blocks, classes, and base classes; `if`, `match`, loops, labelled blocks, closures, `async`/`await`/`spawn`, generators, `try`/`catch` with type tests, casts, and intrinsics.
- **`dynamic`** (Python, Lua, Mox): every value is `any`; only the errors that are certain whatever the run-time values are reported (wrong argument count to a known function, unknown named arguments, constructor patterns of the wrong length, unknown record fields).
- **Host declarations**: a language's library lives outside the unit; `Checker` takes the types of extern names, other units' definitions, named intrinsics, members of host types, and attributes that force a monomorphization strategy.

Not in this release: the `gradual` and `hm` disciplines (0.5.0), associated types with parameters of their own, and multi-segment associated paths (`T::Assoc::f`), both reported as `Unsupported`. Not this crate's job: name resolution (resolve-lang), compiling patterns into decision trees, orphan rules (they depend on crate boundaries a unit does not see), and mutability and ownership (capabilities over typed HIR).

What each guarantee rests on:

| Guarantee | How it is checked |
|---|---|
| Well-typed programs check clean, with exactly the types they should have. | A typed generator builds random well-typed programs (arithmetic, comparisons, `if`, blocks, calls, tuples, arrays, records, sums with `match`, constructor calls, method calls, field access, indexing); property tests require no diagnostic, the generated type for every expression, and the right method for every method call. |
| One mistake, one diagnostic, at the mistake. | Property: replacing one numeric literal of a well-typed program with `true` yields exactly one diagnostic, on that literal. Property: replacing any leaf with an error node yields none. |
| Checking never panics and always terminates. | Property: random HIR of every form, repaired by `hir-lang`'s lenient validation, checks without panicking under three profiles, types every live expression and pattern, and is deterministic; under any step budget it finishes or returns `BudgetExceeded`. |
| Generic programs check clean, with exactly the types, dispatch, and instances they should have. | A second typed generator builds programs over a generic record with a generic impl, a generic sum, an interface with a default method, an interface with an associated type and a bounded generic impl, bounded generic functions, and closures passed to generics; property tests require no diagnostic, the exact type (generic arguments included) of every expression, the exact method of every method call, and a plan instance with the exact arguments for every generic call. A corpus of Kraken-like programs (generic containers, interface dispatch by bound and by `dyn`, closures, `?`, an iterator interface, `match` exhaustiveness) checks expected types, dispatch, plans, and diagnostics. |
| One mistake in a generic program, one diagnostic, at the mistake. | Property: replacing a numeric literal that an expectation reaches (through generic calls by checking mode, record literals, constructors, closure operands) with `true` yields exactly one diagnostic, on that literal; replacing any leaf with an error node yields none. |
| Interface resolution terminates. | `impl<T: Tr> Tr for T` and an impl whose where clause needs ever-larger types are budget errors (`Limit::TraitDepth`), not hangs; supertrait cycles, cyclic generic aliases and defaults, and cyclic associated types terminate (the last two on a 1 MiB stack). Random HIR with generics, interfaces, impls, `dyn`, `impl Trait`, unions, and the v3 forms checks without panicking under five profiles. |
| Shared type structure is never expanded (type-lang's ISSUES M39). | Types are hash-consed terms in a union-find store. Unifying two `Pair(v, v)` doubling chains is linear: step counts are compared at 2,000 and 4,000 levels, and 50,000 levels check in a test. |
| Work is linear in the program. | Step counts at 2,000 and 20,000 functions differ by the size factor; so do 10,000 and 20,000 nested generic calls, and 2,000 and 4,000 interface implementations each called once. Deep input is checked on an explicit stack: tests cover 100,000-deep expressions, 50,000 nested blocks and `if`s, 30,000-deep types, generic arguments, and patterns, 20,000-long alias chains, and 5,000-deep inheritance. |

<hr>
<br>

## Installation

```toml
[dependencies]
typeck-lang = "0.3"
```

Without the standard library:

```toml
[dependencies]
typeck-lang = { version = "0.3", default-features = false }
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
use typeck_lang::{MonoPolicy, Profile, RecordTyping};

let kraken_like = Profile::static_inferred()
    .with_records(RecordTyping::Nominal)
    .with_subtyping(true)
    .with_string_add(true);
assert!(kraken_like.null_safety);
let iron_like = Profile::static_inferred().with_mono(MonoPolicy::Selective { max_nodes: 64 });
assert!(iron_like.method_autoref);
```

A generic function, its instantiation, and the plan:

```rust
use hir_lang::{Builder, Expr, FnDef, GenericParam, Generics, Item, ItemKind, Lit, Name, Ns, Param, ParamKind, Prim, Res, Ty};
use intern_lang::Interner;
use typeck_lang::{check, Profile, TypeId};

let mut names = Interner::new();
let mut b = Builder::new();
// fn id<T>(x: T) -> T { x }    fn main() { let y = id(true); }
let t = b.new_binder(Name::new(names.intern("T")), hir_lang::BinderKind::TypeParam);
let mut tp = |b: &mut Builder| {
    let p = b.resolved_path(Name::new(names.intern("T")), Ns::Type, Res::Local(t));
    b.ty(Ty::Path(p))
};
let (pt, rt) = (tp(&mut b), tp(&mut b));
let x = b.new_binder(Name::new(names.intern("x")), hir_lang::BinderKind::Param);
let pat = b.bind(x);
let param = b.param(Param { pat, ty: Some(pt), default: None, kind: ParamKind::Normal, by_ref: false });
let body = { let ux = b.use_binder(x); b.block(&[], Some(ux)) };
let generics = Generics { params: b.list(&[GenericParam::new(t)]), preds: hir_lang::List::EMPTY };
let params = b.list(&[param]);
let id = b.item(Item::new(
    Some(Name::new(names.intern("id"))),
    ItemKind::Fn(FnDef { generics, params, ret: Some(rt), body: Some(body), ..FnDef::default() }),
));
let def = b.def(hir_lang::Def::Item(id));
let path = b.resolved_path(Name::new(names.intern("id")), Ns::Value, Res::Def(def));
let callee = b.expr(Expr::Path(path));
let yes = b.lit(Lit::Bool(true));
let call = b.call(callee, &[yes]);
let y = b.new_binder(Name::new(names.intern("y")), hir_lang::BinderKind::Local);
let ypat = b.bind(y);
let stmt = b.let_stmt(ypat, Some(call));
let main_body = b.block(&[stmt], None);
let main = b.func(Name::new(names.intern("main")), &[], main_body);
let root = b.module(None, &[id, main]);
let hir = b.finish(root)?;

let typed = check(&hir, &Profile::static_inferred()).unwrap();
assert!(typed.is_ok());
assert_eq!(typed.binder(y), Some(TypeId::prim(Prim::Bool)));
let instance = typed.mono_plan().instances_of(id).next().unwrap();
assert_eq!(instance.args, &[TypeId::prim(Prim::Bool)]);
# Ok::<(), hir_lang::HirError>(())
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

Runnable programs: `cargo run --example quickstart`, `cargo run --example host`, `cargo run --example generics`.

<hr>
<br>

## Performance

`cargo bench --bench bench`, release profile, Windows x86_64, 0.3.0. Library only: the HIR is built before timing starts. Measured on a machine shared with concurrent builds, so treat these as upper bounds and re-measure on an idle machine before quoting them. The generic programs call a generic function, a method of a generic impl, a bounded generic function on a nested generic record (resolving an interface method through a bounded generic impl), and a generic function with a closure whose signature is inferred, in every function of about 50 nodes.

| Benchmark | Time | Throughput |
|---|---:|---:|
| `static-explicit`, 100k HIR nodes | 9.7&ndash;10.5 ms | 9.2&ndash;10.0 M nodes/s |
| `static-explicit`, 1M HIR nodes | 131&ndash;137 ms | 7.1&ndash;7.4 M nodes/s |
| `static-inferred`, same 100k program | 10.5&ndash;11.7 ms | 8.3&ndash;9.2 M nodes/s |
| `static-inferred`, same 1M program | 132&ndash;145 ms | 6.7&ndash;7.3 M nodes/s |
| `static-inferred`, generic program, 100k nodes | 35&ndash;37 ms | 2.7&ndash;2.9 M nodes/s |
| `static-inferred`, generic program, 1M nodes | 332&ndash;348 ms | 2.9&ndash;3.1 M nodes/s |
| `dynamic`, 100k HIR nodes | 3.0&ndash;3.2 ms | 31&ndash;32 M nodes/s |
| `dynamic`, 1M HIR nodes | 41&ndash;46 ms | 21&ndash;24 M nodes/s |
| Doubling chain, 100k levels (1.4M nodes) | 143&ndash;149 ms | 9.4&ndash;9.8 M nodes/s |

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
