//! # typeck_lang
//!
//! Profile-driven type checking over HIR: one checker, configured by a
//! type-system [`Profile`] instead of written per language.
//!
//! ```
//! use hir_lang::{Builder, Name, OpKind};
//! use intern_lang::Interner;
//! use typeck_lang::{check, Profile};
//!
//! let mut names = Interner::new();
//! let mut b = Builder::new();
//! // fn main() { 1 + true; }
//! let one = b.int(1);
//! let yes = b.lit(hir_lang::Lit::Bool(true));
//! let sum = b.op(OpKind::Add, &[one, yes]);
//! let stmt = b.expr_stmt(sum);
//! let body = b.block(&[stmt], None);
//! let main = b.func(Name::new(names.intern("main")), &[], body);
//! let root = b.module(None, &[main]);
//! let hir = b.finish(root)?;
//!
//! // Statically: one diagnostic, at `true`.
//! let typed = check(&hir, &Profile::static_explicit()).unwrap();
//! let d = typed.diagnostics()[0];
//! assert_eq!(d.node, hir_lang::NodeRef::Expr(yes));
//! assert_eq!(typed.message(&d, &names), "`add` is not defined for `bool`");
//!
//! // Dynamically: nothing to report; every value is `any`.
//! assert!(check(&hir, &Profile::dynamic()).unwrap().is_ok());
//! # Ok::<(), hir_lang::HirError>(())
//! ```
//!
//! ## What it does
//!
//! - **Profiles as data** ([`Profile`], [`Discipline`]): `dynamic`,
//!   `gradual`, `static-explicit`, `static-inferred`, and `hm`, with toggles
//!   for subtyping, nominal or structural records, numeric widening, null
//!   safety, exhaustive matches, and traits versus interfaces. This version
//!   implements `dynamic` and `static-explicit`; the others return
//!   [`CheckError::NotImplemented`] (see `dev/ROADMAP.md`).
//! - **Output** ([`Typed`]): dense side tables of types keyed by HIR
//!   expression, pattern, and binder ids; typed diagnostics with origins;
//!   the implicit conversions lowering must materialise; how each operation
//!   resolved (integer, IEEE, string); and the definitions of partial paths'
//!   unresolved tails (`Shape::Circle`, `Point::new`).
//! - **One root cause, one diagnostic**: anything reported has type
//!   [`TypeId::ERROR`], which every later check accepts silently.
//! - **Termination**: union-find over hash-consed type terms (no exponential
//!   blow-up on shared structure), iterative traversals everywhere, and a
//!   [`Budget`] that turns pathological input into
//!   [`CheckError::BudgetExceeded`] instead of a hang.
//!
//! The checker does not resolve names (resolve-lang does) and does not
//! compile patterns (match-lang does): it checks the top-level coverage of a
//! `match` and lists the rest in [`Typed::deferred_matches`].

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![deny(unused_must_use)]
#![deny(unused_results)]
#![deny(clippy::unwrap_used)]
#![deny(clippy::expect_used)]
#![deny(clippy::panic)]
#![deny(clippy::todo)]
#![deny(clippy::unimplemented)]
#![deny(clippy::unreachable)]
#![deny(clippy::print_stdout)]
#![deny(clippy::print_stderr)]
#![deny(clippy::dbg_macro)]

extern crate alloc;

mod check;
mod diag;
mod error;
mod infer;
mod profile;
mod typed;
mod types;

pub use check::Checker;
pub use diag::{Diagnostic, DiagnosticKind, Feature};
pub use error::{Budget, CheckError, Limit};
pub use profile::{Discipline, Polymorphism, Profile, RecordTyping};
pub use typed::{Coercion, OpClass, Stats, Typed};
pub use types::{Field, Type, TypeDisplay, TypeId, Types};

use hir_lang::Hir;

/// Checks `hir` under `profile`, with no host declarations and a budget
/// scaled to the HIR ([`Budget::for_hir`]).
///
/// Type errors in the program are [`Diagnostic`]s in the result; see
/// [`Checker`] to declare host functions and types, or to set a budget.
///
/// # Errors
///
/// See [`Checker::check`].
///
/// # Examples
///
/// ```
/// use hir_lang::{Builder, Lit, Name, Prim};
/// use intern_lang::Interner;
/// use typeck_lang::{check, Profile, TypeId};
///
/// let mut b = Builder::new();
/// let t = b.lit(Lit::Bool(true));
/// let body = b.block(&[], Some(t));
/// // A function without a declared return type returns unit.
/// let f = b.func(Name::new(Interner::new().intern("f")), &[], body);
/// let root = b.module(None, &[f]);
/// let hir = b.finish(root)?;
/// let typed = check(&hir, &Profile::static_explicit()).unwrap();
/// assert_eq!(typed.diagnostics().len(), 1);
/// assert_eq!(typed.expr(t), Some(TypeId::prim(Prim::Bool)));
/// # Ok::<(), hir_lang::HirError>(())
/// ```
pub fn check(hir: &Hir, profile: &Profile) -> Result<Typed, CheckError> {
    Checker::new(hir, *profile).check()
}

/// Compiles and runs the `rust` code blocks in `README.md` and `docs/API.md`
/// as part of `cargo test`, so the published examples cannot drift from the
/// API.
#[cfg(doctest)]
#[doc = include_str!("../README.md")]
#[doc = include_str!("../docs/API.md")]
pub struct MarkdownDocTests;
