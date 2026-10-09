# typeck-lang &mdash; API Reference

> Complete reference for every public item in `typeck-lang`, with examples.
> **Status: pre-1.0 (0.3.0).** The surface is designed across the 0.x series
> and frozen at 1.0.0, after Mox, Mercury, and a Kraken subset have checked
> through it (LexerSketch decision D18). See
> [`../dev/ROADMAP.md`](../dev/ROADMAP.md).

<sub>Copyright &copy; 2026 <strong>James Gober</strong>.</sub>

## Table of contents

- [Overview](#overview)
- [Installation](#installation)
- [Quick start](#quick-start)
- [Concepts](#concepts)
  - [Profiles](#profiles)
  - [The checking model](#the-checking-model)
  - [The static-explicit rules](#the-static-explicit-rules)
  - [Generics](#generics)
  - [Interfaces and traits](#interfaces-and-traits)
  - [The static-inferred rules](#the-static-inferred-rules)
  - [Unions and intersections](#unions-and-intersections)
  - [Exhaustiveness](#exhaustiveness)
  - [The monomorphization plan](#the-monomorphization-plan)
  - [Typing conventions](#typing-conventions)
  - [The dynamic rules](#the-dynamic-rules)
  - [Partial paths](#partial-paths)
  - [Host declarations](#host-declarations)
  - [Types, union-find, and budgets](#types-union-find-and-budgets)
- [`check`](#check)
- [`Checker`](#checker)
- [`Profile`](#profile)
- [`Discipline`](#discipline)
- [`RecordTyping`](#recordtyping)
- [`Polymorphism`](#polymorphism)
- [`NullLet`](#nulllet)
- [`TryHook`](#tryhook)
- [`MonoPolicy`](#monopolicy)
- [`Typed`](#typed)
- [`Coercion`](#coercion)
- [`OpClass`](#opclass)
- [`Stats`](#stats)
- [`MonoPlan`](#monoplan)
- [`Instance`](#instance)
- [`Strategy`](#strategy)
- [`Instantiation`](#instantiation)
- [`Dispatch`](#dispatch)
- [`Types`](#types)
- [`TypeId`](#typeid)
- [`Type`](#type)
- [`Field`](#field)
- [`TypeDisplay`](#typedisplay)
- [`Diagnostic`](#diagnostic)
- [`DiagnosticKind`](#diagnostickind)
- [`Severity`](#severity)
- [`Feature`](#feature)
- [`CheckError`](#checkerror)
- [`Limit`](#limit)
- [`Budget`](#budget)
- [Feature flags](#feature-flags)
- [Limits](#limits)
- [Stability](#stability)

## Overview

`typeck-lang` type-checks one HIR unit ([`hir_lang::Hir`](https://docs.rs/hir-lang))
under a [`Profile`](#profile). The Tier-1 entry point is [`check`](#check); the
configured path is [`Checker`](#checker), which takes host declarations and a
budget. The result, [`Typed`](#typed), holds:

- the type of every live expression, pattern, and bound binder (dense tables
  indexed by HIR ids);
- [`Diagnostic`](#diagnostic)s with stable codes and origins;
- the implicit [`Coercion`](#coercion)s lowering must materialise;
- how each OPS operation resolved ([`OpClass`](#opclass));
- the definitions the checker resolved partial paths' tails to;
- the method each method call dispatches to, and the generic item and
  arguments each use of a generic item instantiates;
- the **monomorphization plan**: every instance of a generic function the
  program reaches, copied or shared ([`MonoPlan`](#monoplan));
- for each non-exhaustive `match`, the values it misses (witnesses).

Types live in a [`Types`](#types) store owned by the result; a
[`TypeId`](#typeid) is an index into it, and [`Types::get`](#types) returns a
[`Type`](#type) view.

## Installation

```toml
[dependencies]
typeck-lang = "0.3"
```

`no_std` (alloc only):

```toml
[dependencies]
typeck-lang = { version = "0.3", default-features = false }
```

## Quick start

```rust
use hir_lang::{Builder, Name, OpKind, Prim};
use intern_lang::Interner;
use typeck_lang::{check, Profile, TypeId};

let mut names = Interner::new();
let mut b = Builder::new();
// fn main() { let s = 1 + 2; }
let (one, two) = (b.int(1), b.int(2));
let sum = b.op(OpKind::Add, &[one, two]);
let s = b.new_binder(Name::new(names.intern("s")), hir_lang::BinderKind::Local);
let pat = b.bind(s);
let stmt = b.let_stmt(pat, Some(sum));
let body = b.block(&[stmt], None);
let main = b.func(Name::new(names.intern("main")), &[], body);
let root = b.module(None, &[main]);
let hir = b.finish(root)?;

let typed = check(&hir, &Profile::static_explicit()).unwrap();
assert!(typed.is_ok());
// Unsuffixed literals nothing constrains take the profile's default.
assert_eq!(typed.binder(s), Some(TypeId::prim(Prim::I64)));
# Ok::<(), hir_lang::HirError>(())
```

## Concepts

### Profiles

A profile is a discipline plus toggles. The disciplines:

| Discipline | Like | Static checking | Inference | In 0.3.0 |
|---|---|---|---|---|
| `Dynamic` | Python, Lua, Mox | Only statically certain arity and shape errors | none: every value is `any` | implemented |
| `Gradual` | TypeScript, Mercury | Where annotated; `any` at the boundaries | local | designed (0.5) |
| `StaticExplicit` | C, Go, Zero | Everything | `let` initializers, literals, generic arguments | implemented |
| `StaticInferred` | Kraken, Iron | Everything | bidirectional: also closure signatures | implemented |
| `Hm` | ML family | Everything | full, let-polymorphism | designed (0.5) |

Both static disciplines check generics, interfaces, `impl` blocks, associated
types, `dyn` and `impl Trait` types, unions and intersections: HIR that uses
them needs them. `StaticInferred` also infers unannotated closure parameters
and results from the expected function type (or from use), and its preset
types `let x = null` as a nullable inferred from later uses.

The toggles ([`Profile`](#profile) fields): `subtyping`, `records`
(nominal or structural), `numeric_widening`, `null_safety`,
`exhaustive_match`, `polymorphism` (what an interface name means as a type),
`default_int` / `default_float` (literal defaults), `string_add` (`add` on
strings concatenates), `certain_errors` (the dynamic discipline's statically
certain errors), `method_autoref` (receivers borrowed and dereferenced
implicitly), `mono` (the plan's copy-or-share policy), `null_let` (what
`let x = null` gives `x`), and `try_hook` (how `?` reaches the checker).

### The checking model

Checking is iterative: an explicit task stack, never recursion over the
input, so nesting depth is irrelevant. Every item is checked on its own (items
cannot see each other's locals); then any live expression no item reached
(array lengths and constant arguments inside annotations) is checked as a root
of its own.

Types flow bottom-up, and a parent may give a child an **expected type**
before checking it: a `let` annotation to its initializer, a parameter type to
its argument, a declared return type to the body and to `return` values, a
field type to a record literal's field, an `if`'s expectation to its branches,
an array's element type to its elements. When an expression finishes, it is
coerced to its expected type; on failure the mismatch is reported **at that
expression** and the expression is *poisoned*: its parent reads it as
[`TypeId::ERROR`](#typeid). The error type unifies with everything without
binding shared structure, so one mistake is reported once.

When two branches disagree and nothing was expected (an `if` used as an
operand), the later branch is blamed. When an operation's operands disagree,
the later operand is blamed; an operand of the wrong class (`true` in `add`)
is blamed directly.

**Checking mode through generic calls.** When a call of a generic function
(or a generic constructor) has an expected type, a probe unifies the callee's
instantiated result with it, reads what that says about each parameter, and
rolls back: the arguments are then checked against those types. So in
`let v: Opt<i64> = Some(true)` the mistake is reported at `true`, not at the
call. A record literal of a generic type with an expected instance fixes its
arguments before its fields are checked. Where a type's structure is needed
(a field, a method, an index, a callee) and it is still a variable, pending
interface goals are solved first.

### The static-explicit rules

**Declarations.** Parameters, fields, constants, and globals need a declared
type (`MissingAnnotation` otherwise; the receiver of a method defaults to
`Self`). A function without a return type returns unit. A `let` takes its
annotation, else its initializer's type, else a fresh variable that later
assignments determine (`CannotInfer` if nothing does). `_` is allowed in
local annotations, not in signatures.

**Literals.** An unsuffixed integer literal is a variable of the integer
class: it becomes whatever integer type it meets, else `default_int`; with
`numeric_widening` it may also become a float. Float literals likewise. Every
integer literal is range-checked against its final type
(`LiteralOutOfRange`). `null` has type `null`; `b"..."` is `[u8]`; a big
integer literal is out of range for every static type.

**Coercions** (at every expected type): equal types; `!` (diverging) fits
anything; any value into `any`; `null` into `T?` (or, without null safety,
into references, pointers, nominal and host types, functions, strings,
slices, maps); `T` into `T?`; with `numeric_widening`, lossless numeric
widening (`i32` to `i64`, `u8` to `i16`, integers of at most 32 bits to
`f64`, at most 16 to `f32`, `f32` to `f64`); with `subtyping`, a subclass into
a base class and (with structural records) a record into one with fewer
fields; an array into a slice (also behind `&`); `&mut T` into `&T`.

**Operations** (OPS, typed by operands): `add sub mul div rem min max neg
abs` on integers and floats (`add` on strings with `string_add`);
`floor_div floor_mod` on integers; `and or xor not` on integers and `bool`;
`shl shr` with an integer of any type as the amount; `sqrt floor ceil trunc
round round_even ieee_rem fma total_cmp` on floats; `eq ne` on numbers,
`bool`, `char`, strings, and `x == null`; `lt le gt ge` on numbers, `char`,
strings; conversions check their source class and, for `zext sext narrow
bitcast`, the widths. The `promote` overflow policy is rejected on every
statically typed result (`PromoteOnStatic`). An operand of type `any` is
rejected (`DynamicOperation`): cast or type-test it first.

**Calls.** A call of a function item matches arguments to parameters:
positional arguments fill positional-only and normal parameters in order,
then the rest parameter; named arguments match normal and named-only
parameters by name, else the named rest; parameters with defaults may be left
out; a spread of a tuple or fixed-length array supplies that many positional
arguments, a spread of a slice may supply any number, a spread of a
string-keyed map may supply named ones; a by-reference parameter needs a
place argument. A rest parameter's binder is a slice of its declared element
type; a named rest's is a map from strings. Calls of function values are
positional. Calling an `ASYNC` function yields `async<T>`, a `YIELD`
function `generator<T>` (its declared result is the type of the yielded
values).

**Records, sums, classes.** A record literal names its record, class, or
variant; unknown fields, missing fields without defaults, and union literals
that do not set exactly one field are reported. Fields are found on records,
classes, their base classes, tuples (by position), through references, on
every member of an intersection, and on a union when every member has the
field with one type. Methods are found on `impl` blocks of the receiver's type
(generic ones too), on classes and their base classes, on host members, on the
interfaces the receiver implements, and (with `method_autoref`) through
references, borrowing and dereferencing the receiver; a field of function
type can be called as a method.

**Assignments** evaluate to the value stored (HIR v3): `x = 5` has `x`'s type.
A language whose assignment yields unit lowers a use of its value as
`{ a = b; () }`.

**Control.** `if` conditions and guards are `bool`; an `if` without `else` is
unit. `match` arms join; exhaustiveness is decided by match-lang
([Exhaustiveness](#exhaustiveness)). A `loop` has the type of its `break`
values (`!` without one); a labelled block joins its tail with breaks to it. A
`let ... else` branch must diverge. `let_place p = place in body` binds `p` to
the place's type and has the body's type.

**Effects.** `await` takes `async<T>` or `task<T>`; `spawn` takes a
zero-parameter function and yields `task<T>`; `yield` values meet the
generator's item type ([Typing conventions](#typing-conventions)); `yield
from` takes a generator of that item type; `throw` values meet a declared
`throws` type; `catch` patterns test thrown values, which are `any`
(type-test patterns narrow them).

**Operations.** HIR v3 splits `not` (logical, on `bool`) from `bit_not`
(bitwise, on integers); `pow` is defined on integers and floats.

**Not checked here.** Mutability and ownership (capabilities over typed HIR)
and visibility (resolve-lang).

### Generics

Functions, records, sums, classes, interfaces, impls, and aliases may have
generic parameters (type parameters, constant parameters; region parameters
and arguments are erased). Inside an item its parameters are rigid
placeholders ([`Type::Param`](#type)); a member of an impl, class, or
interface sees its owner's parameters first, then its own, and an interface's
members also see its `Self` ([`Type::SelfOf`](#type)).

**Using a generic item instantiates it**: each placeholder gets a written
argument (`f::<i32>`, `Vec<i64>`, `Point::<T>::new`) or a fresh inference
variable, by a memoized rebuild of the types that mention placeholders
(linear in the type DAG; placeholder-free parts are skipped in constant
time). Missing trailing arguments take their defaults (`struct P<A, B = A>`),
which may mention earlier parameters; in a local annotation a missing
argument is inferred; in a signature, a parameter without a default must be
written (`GenericArity`). Constant arguments are compile-time integers
([`Type::Const`](#type)) or constant parameters; `[T; N]` with a constant
parameter `N` is [`Type::ParamArray`](#type), and an array argument
determines `N`. A generic alias expands with its arguments.

**Bounds** (`T: Show`, `where T::Item: Show`, `impl Trait` parameters) are
lowered once per item. Instantiating an item queues its bounds, with the
arguments substituted, as goals; so does constructing a value of a bounded
generic type, writing an instance of one in an annotation (checked in the
annotation's scope), coercing to `dyn`, and returning an `impl Trait`. A goal
on a placeholder is met by the bounds in scope (with supertraits); any other
by the one implementation that applies ([Interfaces and traits](#interfaces-and-traits)).
Unmet goals are `Unsatisfied`; goals still undecided when an item ends wait
for literal defaults, then become `CannotInfer` at the expression that
created them.

`impl Trait` in a parameter type is an anonymous generic parameter
([`Type::ImplParam`](#type)); in a result type, an opaque type
([`Type::Opaque`](#type)) whose callers see only its bounds, and whose hidden
type the body infers ([`Typed::opaque_type`](#typed)). Elsewhere it is
`ImplTraitPosition`.

### Interfaces and traits

An interface (trait) declares methods (a body is a default), constants, and
associated types; supertraits are its `supers`. An implementation is an
`impl Iface<A> for T { .. }` block, possibly generic (`impl<T: Show> Show for
Vec<T>`), or a class declaring an interface (its own members implement it,
and its subclasses inherit the declaration).

**The index.** Every implementation is indexed by the head of its self type
(an item, a primitive, a tuple of n, a reference, ...), with a separate
bucket for blanket impls (`impl<T> Show for T`); a lookup tests only the
records that could apply, by unifying their self type (instantiated with
fresh variables) with the type at hand inside a rolled-back snapshot. Generic
impls are indexed like any other (ISSUES P17: member lookups on generic types
are never silently skipped).

**Member lookup** on a value (methods) or a type (associated functions and
constants, `T::default()`, `Show::show(x)`, `<T as Show>::show`): for a
placeholder, opaque type, or `dyn` type, the members of its bounds' interfaces
(with supertraits); otherwise inherent members (walking base classes), host
members, then the members of the interfaces the type implements, where a
record's own member overrides the interface's default. Several candidates are
`AmbiguousMethod`. With `method_autoref` the lookup also looks through
references and the receiver is borrowed or dereferenced to fit; without it
the receiver must already fit.

**Associated types** are written `T::Item`, `Self::Item`, `<T as Iter>::Item`,
or bound (`I: Iter<Item = u8>`, `Iter<Item: Show>`). A projection on a
concrete type normalizes through the selected implementation's `type Item =
..` (or the interface's default); on a placeholder, through a binding in
scope, else it stays a rigid [`Type::Projection`](#type); on a variable, it
becomes a variable with a pending goal. `dyn Iface` must bind every
associated type of `Iface` (`MissingAssocBinding`).

**Coherence and conformance.** Two implementations of one interface whose
self types and arguments unify overlap; the later one is reported
(`OverlappingImpls`) since selection between them would be ambiguous (orphan
rules depend on crate boundaries a unit does not see, and are not checked).
An implementation must provide every member without a default
(`MissingMember`), only members the interface declares (`NotAMember`), and
methods whose signatures match the interface's with `Self`, the interface's
arguments, and the method's own parameters substituted (`Mismatch` at the
parameter or result). Associated types with parameters of their own are
`Unsupported`.

**Polymorphism.** With `Interfaces`, an interface name where a type is
expected is the interface type (`dyn`); with `Traits` and `Typeclasses` it is
`InterfaceAsType` (write `dyn` or `impl`).

**Termination.** Nested goals (an implementation's bounds, associated types
defined through others, the plan's instance chains) are capped by
[`Budget::trait_depth`](#budget): `impl<T: Tr> Tr for T`, or an impl whose
where clause needs ever-larger types, is
[`CheckError::BudgetExceeded`](#checkerror) with `Limit::TraitDepth`, never
a hang. Re-entrant lowering and normalization additionally nest at most 32
deep, so they stay within any thread's stack.

### The static-inferred rules

Everything above, and: an unannotated closure parameter takes its type from
the expected function type when the closure has one with as many positional
parameters (a closure passed to `apply<T>(f: fn(T) -> T, x: T)`), else a
fresh variable inferred from use; an unannotated result likewise. Under
`StaticExplicit` an unannotated closure parameter is `MissingAnnotation`.

### Unions and intersections

`A | B` ([`Type::Union`](#type)) and `A & B` ([`Type::Intersection`](#type))
are kept in canonical form (flattened, sorted, deduplicated; a nullable member
makes the union nullable). A value coerces into a union containing (a
supertype of) its type, and a union into one containing all its members
(`Coercion::ToUnion`); into an intersection by fitting every member; out of an
intersection as any member (`Coercion::FromIntersection`). Fields follow the
rules above; methods on a union need narrowing (a type test). A type test on
a union value must name a type related to a member.

### Exhaustiveness

Every `match` is decided by match-lang over a model of the checker's types:
sums are sums, records, tuples, and references are products, `T?` is a sum of
`null` and a value, a union is a sum of its members (matched by type tests),
integers and characters have their exact domains (ranges cover them), and
other types (floats, strings, host and generic types) are opaque, so only a
wildcard covers them. With `exhaustive_match`, a match that misses values is
`NonExhaustive`, with the missing values as patterns ([`Typed::witnesses`](#typed),
also in the message: ``non-exhaustive match: `Some(false)` not covered``).
Unreachable arms (`UnreachableArm`) and redundant or-pattern alternatives
(`RedundantAlternative`) are [warnings](#severity), whatever the profile. A
pattern the model cannot express exactly (a type test against a class, a
float range) makes its arm count as guarded: it never adds coverage. The
analysis is charged to the step budget.

### The monomorphization plan

[`Typed::mono_plan`](#typed) lists every instance of a generic function the
program reaches from its non-generic code (breadth first, each (item,
arguments) once): calls in instances are walked with the instance's arguments
substituted, interface methods called through a bound are resolved to the
implementing method of each concrete instance, and values coerced to `dyn`
add their implementation's methods (the vtable). The profile's
[`MonoPolicy`](#monopolicy) decides each item's [`Strategy`](#strategy):
`Copy` (one instance per argument list), `Shared` (dictionary passing: one
body, entered once with its own placeholders, plus one entry per concrete call
site and the methods of the implementations its bounds need), or `Selective {
max_nodes }` (copy items whose body is small, LANGUAGES.md's Iron). An
attribute declared with [`Checker::declare_mono_attribute`](#checker) forces a
strategy. A chain of instances deeper than the trait depth (polymorphic
recursion such as `f::<Wrap<T>>` inside `f<T>`) is reported
(`RecursiveInstantiation`) and cut.

### Typing conventions

Choices HIR leaves to the type checker (ISSUES P17; also recorded in
`specs/HIR.md` §8.11):

- **Generators.** A `YIELD` function's declared result type is the type of
  the values it yields; calling it gives `generator<T>`. Its body returns
  unit (`return` without a value). `yield` evaluates to unit (values sent back
  into a generator are not typed), and `yield from` takes a generator of the
  same item type and evaluates to unit. Keys of keyed yields are typed but
  unconstrained.
- **`let x = null`.** [`Profile::null_let`](#profile): `NullType` (the
  variable has type `null`, the `static-explicit` preset) or `Nullable` (`T?`
  for a `T` inferred from later uses, the `static-inferred` preset).
- **Assignments** evaluate to the value stored.
- **`?`.** Lowered as a template, it is ordinary code. Kept as a named
  intrinsic, it is typed by the profile's [`TryHook`](#tryhook).

### The dynamic rules

Every live expression, pattern, and bound binder has type `any`; nothing is
lowered from annotations (they are run-time hints), so no type error is ever
reported. With `certain_errors`, these are reported because they fail whatever
the values: a call of a function item of this unit, without spreads, whose
arguments cannot match its parameters (count, names, duplicates, missing);
a tuple constructor called with the wrong number of arguments or a named
argument; a constructor pattern of the wrong length; a record literal naming
a field its record (not a class: classes take dynamic properties) or variant
does not declare.

### Partial paths

HIR lowers before resolution, so a path's resolution may cover only a prefix
(`Vec::new`: `Vec` by name, `new` by type). The checker resolves a one-segment
tail by type: a variant of a sum, else a member of the prefix's type (see
member lookup under [Interfaces and traits](#interfaces-and-traits)): on a
type parameter through its bounds (`T::new()`), on an interface with a fresh
`Self` (`Show::show(x)`), and with a qualified self (`<T as Show>::show`).
Roots `Self::`, `static::`, and `parent::` use the current `Self` type and its
first base. The definition found is in [`Typed::path_def`](#typed). Longer
tails (`T::Assoc::f`) are `Unsupported`.

### Host declarations

Names the unit does not define (`Res::Extern` symbols, other units'
definitions, `Intrinsic::Named` intrinsics) have no type until the host
declares one through [`Checker`](#checker); a static profile reports
`UnknownExtern` for an undeclared one. A *type* path to an extern or another
unit's definition is a nominal opaque type (`Type::Extern`, `Type::Foreign`)
whose members the host may declare with `declare_member`, on the type itself
or on its bare head (`Vec` for `Vec<i32>`).

### Types, union-find, and budgets

Types are hash-consed: structurally equal types are one node and one
`TypeId`, so a type that mentions the same sub-type twice stores it once.
Inference variables and every other node share one union-find; unifying two
compound nodes merges their classes before comparing children, so each pair
of classes is compared once (Huet's algorithm) and shared structure is never
expanded. The occurs check walks class representatives with a visited set and
skips variable-free subterms in constant time. A failed unification rolls back
every merge it made; unifying `{error}` with a type binds that type's
variables to `{error}` (they stand for parts of something already reported),
never merging shared terms. Of two equal terms, a variable-free one represents
their class. After checking, every recorded type is resolved to its
variable-free form with one shared memo.

Every step (task, unification pair, occurs-check visit, constant-evaluation
step, pattern node) is charged to a [`Budget`](#budget). The default scales
with the HIR and is not expected to bind on real programs; an exhausted budget
is [`CheckError::BudgetExceeded`](#checkerror), never a hang.

## `check`

```rust,ignore
pub fn check(hir: &Hir, profile: &Profile) -> Result<Typed, CheckError>
```

Checks `hir` under `profile`, with no host declarations and
[`Budget::for_hir`](#budget). Type errors in the program are diagnostics in
the `Ok` result.

**Errors:** [`CheckError::NotImplemented`](#checkerror) for `Gradual` and
`Hm`; [`CheckError::InvalidProfile`](#checkerror) when `default_int` is not an
integer type or `default_float` not a float type;
[`CheckError::BudgetExceeded`](#checkerror) when a budget runs out (steps,
type-store size, or trait-resolution depth).

```rust
use hir_lang::Builder;
use typeck_lang::{check, CheckError, Discipline, Profile};

let mut b = Builder::new();
let root = b.module(None, &[]);
let hir = b.finish(root)?;
assert!(check(&hir, &Profile::static_explicit()).unwrap().is_ok());
assert_eq!(
    check(&hir, &Profile::gradual()),
    Err(CheckError::NotImplemented { discipline: Discipline::Gradual }),
);
# Ok::<(), hir_lang::HirError>(())
```

## `Checker`

The configured path: build host types, declare host names, set a budget,
then check.

| Method | Description |
|---|---|
| `Checker::new(hir, profile)` | A checker with [`Budget::for_hir`](#budget). |
| `set_budget(budget) -> &mut Self` | Replaces the budget. |
| `types_mut() -> &mut Types` | The store the result will own; build host types here. |
| `declare_extern(name, ty) -> &mut Self` | The value type of `Res::Extern(name)`. |
| `declare_foreign(def, ty) -> &mut Self` | The value type of another unit's definition `def`. |
| `declare_intrinsic(name, ty) -> &mut Self` | The function type of `Intrinsic::Named(name)`. |
| `declare_member(owner, name, ty) -> &mut Self` | A member of type `owner`: `owner::name` in paths, and `value.name(..)` in method calls when `ty` is a function whose first parameter is the receiver. |
| `declare_mono_attribute(name, strategy) -> &mut Self` | An attribute named `name` on a generic item forces `strategy` in the [plan](#the-monomorphization-plan). |
| `check(self) -> Result<Typed, CheckError>` | Runs the check; errors as for [`check`](#check). |

A later declaration of the same key replaces the earlier one. Types passed in
must come from `types_mut()`; an id from another store reads as the error
type.

```rust
use hir_lang::{Arg, Builder, Effects, Expr, Ident, List, Name, Ns, Prim, Res, Span};
use intern_lang::Interner;
use typeck_lang::{Checker, Profile, TypeId};

let mut names = Interner::new();
let (vec, new, len) = (names.intern("Vec"), names.intern("vec_new"), names.intern("len"));
let mut b = Builder::new();
// fn main() { vec_new().len() }  -- with `main` returning usize
let path = b.resolved_path(Name::new(new), Ns::Value, Res::Extern(new));
let callee = b.expr(Expr::Path(path));
let made = b.call(callee, &[]);
let args = b.list::<Arg>(&[]);
let call = b.expr(Expr::MethodCall {
    receiver: made,
    method: Ident::new(len, Span::empty(0)),
    generic_args: List::EMPTY,
    args,
});
let body = b.block(&[], Some(call));
let usize_ty = b.ty(hir_lang::Ty::Prim(Prim::Usize));
let main = b.item(hir_lang::Item::new(
    Some(Name::new(names.intern("main"))),
    hir_lang::ItemKind::Fn(hir_lang::FnDef { ret: Some(usize_ty), body: Some(body), ..Default::default() }),
));
let root = b.module(None, &[main]);
let hir = b.finish(root)?;

let mut checker = Checker::new(&hir, Profile::static_explicit());
let vec_ty = checker.types_mut().external(vec);
let new_ty = checker.types_mut().func(&[], vec_ty, Effects::NONE);
let len_ty = checker.types_mut().func(&[vec_ty], TypeId::prim(Prim::Usize), Effects::NONE);
checker.declare_extern(new, new_ty).declare_member(vec_ty, len, len_ty);
let typed = checker.check().unwrap();
assert!(typed.is_ok());
assert_eq!(typed.expr(call), Some(TypeId::prim(Prim::Usize)));
# Ok::<(), hir_lang::HirError>(())
```

## `Profile`

A discipline plus toggles; `#[non_exhaustive]`, so it is built from a preset
and adjusted with `with_*` methods. Fields are public to read.

| Preset | Discipline | Notes |
|---|---|---|
| `Profile::dynamic()` | `Dynamic` | `certain_errors` on |
| `Profile::gradual()` | `Gradual` | 0.5 |
| `Profile::static_explicit()` (also `Default`) | `StaticExplicit` | nominal records, no subtyping or widening, null safety, exhaustive matches, `i64`/`f64` literal defaults, auto-ref, `MonoPolicy::Copy`, `NullLet::NullType` |
| `Profile::static_inferred()` | `StaticInferred` | as `static_explicit`, with `Traits` and `NullLet::Nullable` |
| `Profile::hm()` | `Hm` | typeclasses; 0.5 |

| Field | Type | Meaning |
|---|---|---|
| `discipline` | [`Discipline`](#discipline) | how much is checked and inferred |
| `subtyping` | `bool` | subclass-to-base and record-width coercions |
| `records` | [`RecordTyping`](#recordtyping) | nominal or structural records |
| `numeric_widening` | `bool` | lossless implicit numeric conversions; integer literals may type as floats |
| `null_safety` | `bool` | `null` only inhabits `T?` |
| `exhaustive_match` | `bool` | `match` must cover every value |
| `polymorphism` | [`Polymorphism`](#polymorphism) | what an interface name means as a type |
| `default_int`, `default_float` | `Prim` | types of unconstrained literals |
| `string_add` | `bool` | `add` on strings is concatenation |
| `certain_errors` | `bool` | the dynamic discipline's certain errors |
| `method_autoref` | `bool` | receivers borrowed and dereferenced implicitly; lookup through references |
| `mono` | [`MonoPolicy`](#monopolicy) | copy or share generic items in the plan |
| `null_let` | [`NullLet`](#nulllet) | what `let x = null` gives `x` |
| `try_hook` | [`TryHook`](#tryhook) | how `?` reaches the checker |

Builders: `with_subtyping`, `with_records`, `with_numeric_widening`,
`with_null_safety`, `with_exhaustive_match`, `with_polymorphism`,
`with_literal_defaults(int, float)`, `with_string_add`,
`with_certain_errors`, `with_method_autoref`, `with_mono`, `with_null_let`,
`with_try_hook`.

```rust
use hir_lang::Prim;
use typeck_lang::{Discipline, Profile, RecordTyping};

let p = Profile::static_explicit()
    .with_records(RecordTyping::Structural)
    .with_subtyping(true)
    .with_literal_defaults(Prim::I32, Prim::F32);
assert_eq!(p.discipline, Discipline::StaticExplicit);
assert_eq!(p.default_int, Prim::I32);
assert_eq!(Profile::default(), Profile::static_explicit());
```

## `Discipline`

`Dynamic`, `Gradual`, `StaticExplicit`, `StaticInferred`, `Hm`
(`#[non_exhaustive]`). `is_implemented()` is true for `Dynamic`,
`StaticExplicit`, and `StaticInferred`; `name()` gives the profile spelling
(`static-inferred`).

```rust
use typeck_lang::Discipline;

assert!(Discipline::StaticInferred.is_implemented());
assert!(!Discipline::Hm.is_implemented());
assert_eq!(Discipline::Hm.name(), "hm");
```

## `RecordTyping`

`Nominal` (two declarations are two types) or `Structural` (records with the
same field names and types are one type; applies to records with named
fields; tuple records and classes stay nominal).

```rust
use typeck_lang::{Profile, RecordTyping};

assert_eq!(Profile::static_explicit().records, RecordTyping::Nominal);
```

## `Polymorphism`

`Traits`, `Interfaces`, `Typeclasses`. All resolve members through one
engine; with `Interfaces` an interface name where a type is expected is the
interface type (`dyn`), with the others it is `InterfaceAsType`.

```rust
use typeck_lang::{Polymorphism, Profile};

assert_eq!(Profile::static_inferred().polymorphism, Polymorphism::Traits);
```

## `NullLet`

What `let x = null` (no annotation) gives `x`: `NullType` (the type `null`)
or `Nullable` (`T?` for a `T` inferred from later uses; plain `T` without
null safety). ISSUES P17.

```rust
use typeck_lang::{NullLet, Profile};

assert_eq!(Profile::static_explicit().null_let, NullLet::NullType);
assert_eq!(Profile::static_inferred().null_let, NullLet::Nullable);
```

## `TryHook`

How `?`-style propagation reaches the checker (`#[non_exhaustive]`,
`Default` = `Template`):

- `Template`: `?` arrives lowered as a `match` (HIR §8.7) and is ordinary
  code.
- `Intrinsic { name, convert }`: `Intrinsic::Named(name)` with one operand is
  `?`. The operand must be a *carrier*: `T?`, or a sum of two variants that is
  option-like (one unit variant and one with a single field) or result-like
  (two single-field variants, success first). The expression has the success
  value's type; the enclosing function must return a carrier of the same kind
  (`TryCarrier` otherwise). For result-like carriers the failure types must
  agree, or, with `convert: Some(iface)`, the function's failure type must
  implement the interface named `iface` over the operand's failure type
  (`impl Conv<E1> for E2`, Rust's `From`); the conversion is recorded as
  `Coercion::ErrorConvert` on the `?` expression.

```rust
use intern_lang::Interner;
use typeck_lang::{Profile, TryHook};

let mut names = Interner::new();
let hook = TryHook::Intrinsic { name: names.intern("try"), convert: Some(names.intern("From")) };
let p = Profile::static_inferred().with_try_hook(hook);
assert_eq!(p.try_hook, hook);
assert_eq!(TryHook::default(), TryHook::Template);
```

## `MonoPolicy`

The plan's policy (`#[non_exhaustive]`): `Copy` (every generic item copied
per instantiation; the static presets), `Shared` (every generic item shared
through dictionary passing; the dynamic preset), `Selective { max_nodes }`
(copy items whose body has at most `max_nodes` live HIR nodes, share the
rest).

```rust
use typeck_lang::{MonoPolicy, Profile};

let iron = Profile::static_inferred().with_mono(MonoPolicy::Selective { max_nodes: 64 });
assert_eq!(iron.mono, MonoPolicy::Selective { max_nodes: 64 });
```

## `Typed`

The result of a check (`Clone`, `PartialEq`, `Debug`).

| Method | Returns |
|---|---|
| `expr(ExprId)` | `Option<TypeId>`: the type of a live expression (`None` for dead nodes and foreign ids) |
| `pat(PatId)` | `Option<TypeId>`: the type a live pattern matches |
| `binder(BinderId)` | `Option<TypeId>`: the type of a bound variable, parameter, or capture |
| `types()` | `&Types`: the store the ids point into |
| `diagnostics()` | `&[Diagnostic]`, in source order (span start, then discovery) |
| `is_ok()` | no error ([warnings](#severity) allowed) |
| `path_def(PathId)` | `Option<hir_lang::Def>`: the definition the checker resolved a partial path's tail to |
| `method(ExprId)` | `Option<ItemId>`: the function a method call dispatches to |
| `coercion(ExprId)` | `Option<(Coercion, TypeId)>`: the implicit conversion applied, and its target |
| `op_class(ExprId)` | `Option<OpClass>`: how an `Op` expression resolved |
| `witnesses(ExprId, &impl Lookup)` | `Vec<String>`: the values a non-exhaustive `match` misses, as patterns (at most eight) |
| `instantiation(ExprId)` | `Option<`[`Instantiation`](#instantiation)`>`: the generic item an expression uses (a path, a method call), its arguments, and its dispatch |
| `mono_plan()` | `&`[`MonoPlan`](#monoplan) |
| `opaque_type(TyId)` | `Option<TypeId>`: the hidden type of a function's `impl Trait` result, by the `impl` type node |
| `profile()` | `&Profile` |
| `stats()` | [`Stats`](#stats) |
| `display(TypeId, &impl Lookup)` | a [`TypeDisplay`](#typedisplay) |
| `message(&Diagnostic, &impl Lookup)` | the diagnostic's text |

```rust
use hir_lang::{Builder, Lit, Name, Prim};
use intern_lang::Interner;
use typeck_lang::{check, Coercion, Profile, TypeId};

let mut names = Interner::new();
let mut b = Builder::new();
// fn main() { let x: i64? = 5i64; }
let five = b.lit(Lit::Int(hir_lang::IntLit::new(5).with_suffix(Prim::I64)));
let i64_ty = b.ty(hir_lang::Ty::Prim(Prim::I64));
let ann = b.ty(hir_lang::Ty::Nullable(i64_ty));
let x = b.new_binder(Name::new(names.intern("x")), hir_lang::BinderKind::Local);
let pat = b.bind(x);
let stmt = b.stmt(hir_lang::Stmt::Let { pat, ty: Some(ann), init: Some(five), else_: None });
let body = b.block(&[stmt], None);
let main = b.func(Name::new(names.intern("main")), &[], body);
let root = b.module(None, &[main]);
let hir = b.finish(root)?;

let typed = check(&hir, &Profile::static_explicit()).unwrap();
let opt = typed.binder(x).unwrap();
assert_eq!(typed.display(opt, &names).to_string(), "i64?");
assert_eq!(typed.coercion(five), Some((Coercion::WrapNullable, opt)));
assert_eq!(typed.expr(five), Some(TypeId::prim(Prim::I64)));
# Ok::<(), hir_lang::HirError>(())
```

## `Coercion`

The implicit conversions (`#[non_exhaustive]`): `Widen`, `ToAny`,
`WrapNullable`, `Null`, `Subclass`, `RecordWidth`, `Unsize`, `Reborrow`,
`AutoRef`, `AutoDeref`, `ToUnion`, `FromIntersection`, `ToDyn` (lowering
builds the vtable), `ErrorConvert` (a `?` failure converted through the
[`TryHook`](#tryhook)'s interface). See [The static-explicit
rules](#the-static-explicit-rules) and [Unions and
intersections](#unions-and-intersections).

```rust
use typeck_lang::Coercion;

assert_ne!(Coercion::Widen, Coercion::Unsize);
```

## `OpClass`

How an operation resolved (`#[non_exhaustive]`): `Int(Prim)`, `Float(Prim)`,
`Bool`, `Char`, `Str`, `NullCheck`, `Dynamic` (every operation under the
dynamic discipline).

```rust
use hir_lang::Prim;
use typeck_lang::OpClass;

assert_eq!(OpClass::Int(Prim::U8), OpClass::Int(Prim::U8));
```

## `Stats`

`steps` (charged against [`Budget::steps`](#budget)) and `type_nodes` (the
final store size, nodes plus pooled children).

```rust
use typeck_lang::Stats;

assert_eq!(Stats::default().steps, 0);
```

## `MonoPlan`

The instances a program needs ([The monomorphization
plan](#the-monomorphization-plan)). `len()`, `is_empty()`, `instances()` (in
discovery order) and `instances_of(item)` yield [`Instance`](#instance)s.

```rust
use hir_lang::{Builder, GenericParam, Generics, Item, ItemKind, FnDef, Name, Ns, Param, ParamKind, Res, Ty};
use intern_lang::Interner;
use typeck_lang::{check, Profile, Strategy, TypeId};

let mut names = Interner::new();
let mut b = Builder::new();
// fn id<T>(x: T) -> T { x }   fn main() { id(true); }
let t = b.new_binder(Name::new(names.intern("T")), hir_lang::BinderKind::TypeParam);
let tp = |b: &mut Builder, names: &mut Interner| {
    let p = b.resolved_path(Name::new(names.intern("T")), Ns::Type, Res::Local(t));
    b.ty(Ty::Path(p))
};
let (pt, rt) = (tp(&mut b, &mut names), tp(&mut b, &mut names));
let x = b.new_binder(Name::new(names.intern("x")), hir_lang::BinderKind::Param);
let pat = b.bind(x);
let param = b.param(Param { pat, ty: Some(pt), default: None, kind: ParamKind::Normal, by_ref: false });
let ux = b.use_binder(x);
let body = b.block(&[], Some(ux));
let generics = Generics { params: b.list(&[GenericParam::new(t)]), preds: hir_lang::List::EMPTY };
let params = b.list(&[param]);
let id = b.item(Item::new(
    Some(Name::new(names.intern("id"))),
    ItemKind::Fn(FnDef { generics, params, ret: Some(rt), body: Some(body), ..FnDef::default() }),
));
let yes = b.lit(hir_lang::Lit::Bool(true));
let def = b.def(hir_lang::Def::Item(id));
let path = b.resolved_path(Name::new(names.intern("id")), Ns::Value, Res::Def(def));
let callee = b.expr(hir_lang::Expr::Path(path));
let call = b.call(callee, &[yes]);
let s = b.expr_stmt(call);
let main_body = b.block(&[s], None);
let main = b.func(Name::new(names.intern("main")), &[], main_body);
let root = b.module(None, &[id, main]);
let hir = b.finish(root)?;

let typed = check(&hir, &Profile::static_inferred()).unwrap();
assert!(typed.is_ok());
let inst = typed.mono_plan().instances_of(id).next().unwrap();
assert_eq!(inst.args, &[TypeId::prim(hir_lang::Prim::Bool)]);
assert_eq!(inst.strategy, Strategy::Copy);
assert_eq!(typed.instantiation(callee).unwrap().item, id);
# Ok::<(), hir_lang::HirError>(())
```

## `Instance`

`{ item: ItemId, args: &[TypeId], strategy: Strategy }`: a generic item, its
placeholders' arguments in order (owner placeholders first: an interface's
`Self` and the owner's parameters, then the item's own), and how it is
compiled. A shared item's body appears once with its own placeholders as
arguments.

```rust
use typeck_lang::{Instance, Strategy};

fn copies(i: &Instance<'_>) -> bool {
    i.strategy == Strategy::Copy
}
# let _ = copies;
```

## `Strategy`

`Copy` (one copy per instantiation) or `Shared` (one body; dictionaries
passed).

```rust
use typeck_lang::Strategy;

assert!(Strategy::Copy < Strategy::Shared);
```

## `Instantiation`

`{ item: ItemId, args: &[TypeId], dispatch: Dispatch }`, from
[`Typed::instantiation`](#typed): the item a path or method call uses and its
placeholders' arguments (which may mention the placeholders of the item the
expression is in).

```rust
use typeck_lang::{Dispatch, Instantiation};

fn is_virtual(i: Instantiation<'_>) -> bool {
    i.dispatch == Dispatch::Dynamic
}
# let _ = is_virtual;
```

## `Dispatch`

`Static` (the callee is known), `Bound` (an interface method on a placeholder:
resolved per instance in the plan, or through a dictionary), `Dynamic` (an
interface method on a `dyn` value). `#[non_exhaustive]`.

```rust
use typeck_lang::Dispatch;

assert_ne!(Dispatch::Bound, Dispatch::Static);
```

## `Types`

The store of interned type terms. Structurally equal types are one id.

| Method | Description |
|---|---|
| `Types::new()` / `Default` | the fixed types only |
| `len()`, `is_empty()` | node count |
| `get(TypeId) -> Type<'_>` | a view (`Type::Error` for foreign ids) |
| `tuple(&[TypeId])` | `tuple(&[])` is `TypeId::UNIT` |
| `array(elem, len)`, `slice(elem)` | |
| `reference(mutable, inner)`, `pointer(mutable, inner)` | |
| `func(&[params], ret, Effects)` | positional parameters |
| `nullable(inner)` | `nullable(T?)` is `T?` |
| `map(key, value)` | |
| `record(&[Field])` | sorted by name; a repeated name keeps its first type |
| `adt(ItemId)`, `adt_with(ItemId, &[args])` | a record, sum, or class of the checked unit (with generic arguments) |
| `foreign(DefId)`, `foreign_with(DefId, &[args])` | another unit's nominal type |
| `external(Symbol)`, `external_with(Symbol, &[args])` | a host type (`Vec<i32>`) |
| `union(&[TypeId])`, `intersection(&[TypeId])` | in canonical form: flattened, sorted, deduplicated; a single member is itself; `null` members make a union nullable |
| `awaitable(T)`, `task(T)`, `generator(T, is_async)` | effect results |
| `display(TypeId, &impl Lookup)` | a capped rendering |

```rust
use hir_lang::{Effects, Prim};
use typeck_lang::{Type, TypeId, Types};

let mut types = Types::new();
let i32_ = TypeId::prim(Prim::I32);
let pair = types.tuple(&[i32_, i32_]);
assert_eq!(pair, types.tuple(&[i32_, i32_]));
let f = types.func(&[pair], i32_, Effects::NONE);
assert!(matches!(types.get(f), Type::Fn { params, .. } if params == [pair]));
```

## `TypeId`

A type in a store. Fixed ids: `TypeId::ERROR` (`{error}`), `ANY`, `NEVER`
(`!`), `NULL`, `UNIT`, and `TypeId::prim(p)` for each primitive. `index()`
is the dense position.

```rust
use hir_lang::Prim;
use typeck_lang::{Type, TypeId, Types};

assert_eq!(Types::new().get(TypeId::prim(Prim::Char)), Type::Prim(Prim::Char));
assert_eq!(TypeId::ERROR.index(), 0);
```

## `Type`

A view of one node (`#[non_exhaustive]`): `Error`, `Any`, `Never`, `Null`,
`Prim(Prim)`, `Tuple(&[TypeId])`, `Array { elem, len }`,
`ParamArray { elem, len }` (length a constant parameter), `Slice(T)`,
`Ref { mutable, inner }`, `Ptr { mutable, inner }`,
`Fn { params, ret, effects }`, `Nullable(T)`, `Map { key, value }`,
`Record(&[Field])`, `Adt { item, args }`, `Foreign { def, args }`,
`Extern { name, args }`, `Param(BinderId)` (a rigid generic parameter inside
its item), `ImplParam(TyId)` (an `impl Trait` parameter), `SelfOf(ItemId)`
(`Self` inside an interface), `Union(&[T])`, `Intersection(&[T])`,
`Trait { item, args }` (an interface reference, in bounds and inside `dyn`,
where the associated types' values follow the arguments), `Dyn(&[T])`,
`Projection { interface, assoc, args }` (a rigid `<T as I>::Item`; `args`
starts with the self type), `Opaque { origin, args }` (an `impl Trait`
result), `Const(i64)` (a constant generic argument), `Async(T)`, `Task(T)`,
`Generator { item, is_async }`.

```rust
use typeck_lang::{Type, TypeId, Types};

let mut types = Types::new();
let s = types.slice(TypeId::UNIT);
assert_eq!(types.get(s), Type::Slice(TypeId::UNIT));
```

## `Field`

`{ name: Symbol, ty: TypeId }`, a field of a structural record type.

```rust
use intern_lang::Interner;
use typeck_lang::{Field, Type, TypeId, Types};

let mut names = Interner::new();
let mut types = Types::new();
let f = Field { name: names.intern("x"), ty: TypeId::UNIT };
let r = types.record(&[f]);
assert_eq!(types.get(r), Type::Record(&[f]));
```

## `TypeDisplay`

`Display` for a type, from [`Types::display`](#types) or
[`Typed::display`](#typed). Rendering is iterative and capped at about 200
characters (then `…`), so a type of any size renders in bounded time.

```rust
use hir_lang::Prim;
use intern_lang::Interner;
use typeck_lang::{TypeId, Types};

let mut types = Types::new();
let t = types.nullable(TypeId::prim(Prim::Str));
assert_eq!(types.display(t, &Interner::new()).to_string(), "str?");
```

## `Diagnostic`

`{ kind: DiagnosticKind, node: NodeRef, origin: Origin, severity: Severity }`
(`#[non_exhaustive]`): what is wrong, the HIR node it is about, that node's
origin (span and expansion), and whether it is an error or a warning.

```rust
use hir_lang::{BinderKind, Builder, Name, NodeRef};
use intern_lang::Interner;
use typeck_lang::{check, DiagnosticKind, Profile};

let mut names = Interner::new();
let mut b = Builder::new();
let x = b.new_binder(Name::new(names.intern("x")), BinderKind::Local);
let pat = b.bind(x);
let stmt = b.let_stmt(pat, None);
let body = b.block(&[stmt], None);
let main = b.func(Name::new(names.intern("main")), &[], body);
let root = b.module(None, &[main]);
let hir = b.finish(root)?;
let typed = check(&hir, &Profile::static_explicit()).unwrap();
let d = typed.diagnostics()[0];
assert_eq!((d.kind, d.node), (DiagnosticKind::CannotInfer, NodeRef::Pat(pat)));
# Ok::<(), hir_lang::HirError>(())
```

## `DiagnosticKind`

`#[non_exhaustive]`. Types in a kind are resolved ids of the result's store.

| Code | Variant | Meaning |
|---|---|---|
| T0001 | `Mismatch { expected, found }` | the expression's type does not fit its context |
| T0002 | `MissingAnnotation` | a declaration needs a type |
| T0003 | `Unresolved` | a name resolution never resolved |
| T0004 | `UnknownExtern { name }` | a host or other-unit name with no declared type |
| T0005 | `NotAValue` | the path names a type, module, or named-field record |
| T0006 | `NotAType` | the path names something that is not a type |
| T0007 | `Arity { min, max, found }` | wrong number of arguments or pattern elements |
| T0008 | `UnknownNamedArg { name }` | no parameter has that name |
| T0009 | `DuplicateArg { name }` | a parameter given twice |
| T0010 | `MissingArg { name, count }` | required parameters not given |
| T0011 | `NotCallable { ty }` | calling a non-function |
| T0012 | `NoField { ty, member }` | no such field |
| T0013 | `NoMethod { ty, name }` | no such method or associated item |
| T0014 | `UnknownField { ty, name }` | a record literal or pattern names an undeclared field |
| T0015 | `MissingFields { first, count }` | a record literal or pattern leaves out fields |
| T0016 | `NotIndexable { ty }` | indexing a non-indexable value |
| T0017 | `CannotDeref { ty }` | dereferencing a non-reference |
| T0018 | `OpType { op, ty }` | the operation is not defined for the operand type |
| T0019 | `PromoteOnStatic { op }` | `promote` on a statically typed result |
| T0020 | `InvalidCast { from, to }` | a cast the profile does not allow |
| T0021 | `BadConversion { op, from }` | a bit-level conversion of the wrong width |
| T0022 | `LiteralOutOfRange { ty }` | an integer literal outside its type |
| T0023 | `CannotInfer` | nothing determined a type |
| T0024 | `DynamicOperation` | an operation on `any` under a static profile |
| T0025 | `DynamicForm` | `$$x`, `$o->$m()`, `$a = &$b`, `$a[]` under a static profile |
| T0026 | `NullableAccess { ty }` | using a `T?` as a `T` |
| T0027 | `NonExhaustive { missing }` | a `match` leaves values uncovered (the first missing value's variant, for a sum) |
| T0028 | `Unsupported { feature }` | a [`Feature`](#feature) this version does not check |
| T0029 | `CyclicAlias` | an alias expands to itself |
| T0030 | `NotConstant` | an array length or repeat count is not a constant integer |
| T0032 | `ImpossibleTypeTest { from, to }` | a type test that can never succeed |
| T0033 | `AmbiguousMethod { ty, name }` | several impl blocks define the member |
| T0034 | `ByRefNeedsPlace` | a by-reference parameter given a value |
| T0036 | `InheritanceCycle` | a class inherits from itself |
| T0037 | `NotAwaitable { ty }` | `await` on a non-awaitable |
| T0038 | `NotAssignable` | assigning to a function, constant, or constructor |
| T0039 | `UnionLiteral { count }` | a union literal must set exactly one field |
| T0040 | `UnreachableArm` | a `match` arm no value reaches (warning) |
| T0041 | `RedundantAlternative` | an or-alternative that only matches matched values (warning) |
| T0042 | `NotAnInterface` | a bound, supertrait, or `impl` header names a non-interface |
| T0043 | `GenericArity { expected, found }` | the wrong number of generic arguments |
| T0044 | `NoAssocType { name }` | no interface in reach declares that associated type |
| T0045 | `AmbiguousAssocType { name }` | several interfaces declare it; qualify the path |
| T0046 | `Unsatisfied { ty, interface }` | a type does not implement an interface it must |
| T0047 | `AmbiguousImpl { ty, interface }` | several implementations apply |
| T0048 | `OverlappingImpls { other }` | two implementations of one interface overlap |
| T0049 | `MissingMember { name, count }` | an implementation lacks required members |
| T0050 | `NotAMember { interface, name }` | an implementation defines an undeclared member |
| T0051 | `InterfaceAsType` | an interface name as a type under `Traits` polymorphism |
| T0052 | `ImplTraitPosition` | `impl Trait` outside parameter and result types |
| T0053 | `MissingAssocBinding { name }` | `dyn` leaves an associated type unbound |
| T0054 | `RecursiveInstantiation` | the plan's instances grow without bound |
| T0055 | `TryCarrier { ty }` | `?` on (or in a function returning) a non-carrier |

`code()` returns the code.

```rust
use typeck_lang::DiagnosticKind;

assert_eq!(DiagnosticKind::DynamicForm.code(), "T0025");
```

## `Severity`

`Warning` or `Error` (`Warning < Error`). Only errors make
[`Typed::is_ok`](#typed) false.

```rust
use typeck_lang::Severity;

assert!(Severity::Warning < Severity::Error);
```

## `Feature`

What `Unsupported` names (`#[non_exhaustive]`): `GenericAssocTypes`
(associated types with parameters of their own), `LongAssocPaths`
(`T::Assoc::f`). `name()` gives the message text.

```rust
use typeck_lang::Feature;

assert_eq!(Feature::GenericAssocTypes.name(), "generic associated types");
```

## `CheckError`

Why a check produced no result (`#[non_exhaustive]`, `Display`,
`std::error::Error` with `std`):

- `NotImplemented { discipline }`: the discipline is designed but not in
  this version (`Gradual`, `Hm`).
- `InvalidProfile`: inconsistent literal defaults.
- `BudgetExceeded { limit }`: a [`Budget`](#budget) ran out.

```rust
use typeck_lang::{CheckError, Limit};

let e = CheckError::BudgetExceeded { limit: Limit::Steps };
assert_eq!(e.to_string(), "type checking exceeded its step budget");
```

## `Limit`

Which budget ran out (`#[non_exhaustive]`): `Steps`, `TypeNodes`,
`TraitDepth`.

```rust
use typeck_lang::Limit;

assert_ne!(Limit::Steps, Limit::TypeNodes);
```

## `Budget`

`{ steps: u64, type_nodes: usize, trait_depth: u32 }`. `Default`: 50 million
steps, 64 million type-store entries, trait depth 256 (how deep interface
resolution and the plan's instance chains may nest).
`Budget::for_hir(&hir)`: at least the default, and 256 steps and 64 type
entries per HIR node.

```rust
use hir_lang::{Builder, Name};
use intern_lang::Interner;
use typeck_lang::{Budget, CheckError, Checker, Limit, Profile};

let mut b = Builder::new();
let one = b.int(1);
let body = b.block(&[], Some(one));
let f = b.func(Name::new(Interner::new().intern("f")), &[], body);
let root = b.module(None, &[f]);
let hir = b.finish(root)?;
let mut checker = Checker::new(&hir, Profile::static_explicit());
checker.set_budget(Budget { steps: 3, ..Budget::default() });
assert_eq!(checker.check(), Err(CheckError::BudgetExceeded { limit: Limit::Steps }));
# Ok::<(), hir_lang::HirError>(())
```

## Feature flags

| Flag | Default | Effect |
|---|---|---|
| `std` | on | `std::error::Error` for `CheckError`; `hir-lang/std`, `intern-lang/std`, and `match-lang/std`. Without it the crate is `no_std` and needs only `alloc`. |

## Limits

- A check's work is bounded by its [`Budget`](#budget).
- Rendered types are capped at about 200 characters.
- Array lengths are constant-evaluated with checked 128-bit arithmetic over
  literals, `const` items, and `add sub mul div rem neg shl shr and or xor
  min max`; anything else is `NotConstant`. Constant generic arguments must
  fit an `i64`.
- Interface resolution nests at most [`Budget::trait_depth`](#budget) deep;
  re-entrant lowering and normalization at most 32.
- At most eight witnesses are kept per non-exhaustive `match`.

## Stability

Pre-1.0. The surface above may change in 0.x minor releases (recorded in
[`../CHANGELOG.md`](../CHANGELOG.md)); it is frozen at 1.0.0 after real
languages have checked through it end to end.
