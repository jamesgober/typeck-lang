//! Why a check could not run to completion, and the budgets that bound it.
//!
//! Type errors in the program are not errors of the check: they are
//! [`Diagnostic`](crate::Diagnostic)s in a successful [`Typed`](crate::Typed).
//! A [`CheckError`] means the checker refused to start or stopped early.

use core::fmt;

use hir_lang::{Hir, IdKind};

use crate::profile::Discipline;

/// Limits on the work one check may do.
///
/// Every algorithm in the checker is linear or near-linear in the HIR and its
/// types, so these are not expected to bind on real programs; they turn a
/// hostile or pathological input into an error instead of a hang or an
/// out-of-memory abort.
///
/// # Examples
///
/// ```
/// use typeck_lang::Budget;
///
/// let tight = Budget { steps: 10_000, ..Budget::default() };
/// assert_eq!(tight.steps, 10_000);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Budget {
    /// Checker steps: one per task, unification pair, occurs-check visit,
    /// constant-evaluation step, and pattern node.
    pub steps: u64,
    /// Type-store size: nodes plus pooled children.
    pub type_nodes: usize,
}

impl Default for Budget {
    /// 50 million steps and 64 million type-store entries.
    fn default() -> Self {
        Self {
            steps: 50_000_000,
            type_nodes: 1 << 26,
        }
    }
}

impl Budget {
    /// A budget scaled to `hir`: a fixed floor plus 256 steps and 64 type
    /// entries per HIR node, never less than [`Budget::default`].
    ///
    /// # Examples
    ///
    /// ```
    /// use hir_lang::Builder;
    /// use typeck_lang::Budget;
    ///
    /// let mut b = Builder::new();
    /// let root = b.module(None, &[]);
    /// let hir = b.finish(root)?;
    /// assert_eq!(Budget::for_hir(&hir), Budget::default());
    /// # Ok::<(), hir_lang::HirError>(())
    /// ```
    #[must_use]
    pub fn for_hir(hir: &Hir) -> Self {
        let nodes: usize = [
            IdKind::Item,
            IdKind::Expr,
            IdKind::Stmt,
            IdKind::Pat,
            IdKind::Ty,
            IdKind::Path,
            IdKind::Field,
            IdKind::Variant,
            IdKind::Param,
            IdKind::Binder,
        ]
        .into_iter()
        .map(|k| hir.count(k))
        .sum();
        let base = Self::default();
        Self {
            steps: base.steps.max((nodes as u64).saturating_mul(256)),
            type_nodes: base.type_nodes.max(nodes.saturating_mul(64)),
        }
    }
}

/// Which budget ran out.
///
/// # Examples
///
/// ```
/// use typeck_lang::Limit;
///
/// assert_ne!(Limit::Steps, Limit::TypeNodes);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Limit {
    /// [`Budget::steps`].
    Steps,
    /// [`Budget::type_nodes`].
    TypeNodes,
}

/// Why a check did not produce a [`Typed`](crate::Typed).
///
/// # Examples
///
/// ```
/// use hir_lang::Builder;
/// use typeck_lang::{check, CheckError, Discipline, Profile};
///
/// let mut b = Builder::new();
/// let root = b.module(None, &[]);
/// let hir = b.finish(root)?;
/// let err = check(&hir, &Profile::hm()).unwrap_err();
/// assert_eq!(err, CheckError::NotImplemented { discipline: Discipline::Hm });
/// # Ok::<(), hir_lang::HirError>(())
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum CheckError {
    /// The profile's discipline is designed but not implemented in this
    /// version (see [`Discipline::is_implemented`]). Use `Dynamic` or
    /// `StaticExplicit`, or a later version of the crate.
    NotImplemented {
        /// The requested discipline.
        discipline: Discipline,
    },
    /// The profile is inconsistent: `default_int` is not an integer type or
    /// `default_float` not a float type. Fix the profile.
    InvalidProfile,
    /// A budget ran out before the check finished. The input is pathological
    /// or hostile; raise the budget only if the program is trusted and
    /// genuinely that large.
    BudgetExceeded {
        /// Which limit.
        limit: Limit,
    },
}

impl fmt::Display for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotImplemented { discipline } => write!(
                f,
                "the `{}` discipline is not implemented in this version",
                discipline.name()
            ),
            Self::InvalidProfile => f.write_str(
                "invalid profile: the literal defaults must be an integer and a float type",
            ),
            Self::BudgetExceeded { limit } => write!(
                f,
                "type checking exceeded its {} budget",
                match limit {
                    Limit::Steps => "step",
                    Limit::TypeNodes => "type-store",
                }
            ),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for CheckError {}

/// The running step count against a budget.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Meter {
    pub(crate) used: u64,
    pub(crate) budget: Budget,
}

impl Meter {
    pub(crate) const fn new(budget: Budget) -> Self {
        Self { used: 0, budget }
    }

    /// Charges `n` steps.
    #[inline]
    pub(crate) fn tick(&mut self, n: u64) -> Result<(), CheckError> {
        self.used = self.used.saturating_add(n);
        if self.used > self.budget.steps {
            Err(CheckError::BudgetExceeded {
                limit: Limit::Steps,
            })
        } else {
            Ok(())
        }
    }
}
