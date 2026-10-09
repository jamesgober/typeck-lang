//! The monomorphization plan: which instances of generic items a program
//! needs, and how each is compiled.
//!
//! A generic item is compiled either as a **copy** per instantiation (every
//! placeholder replaced by a concrete type: fastest code, more code), or
//! **shared** through dictionary passing (one body; the implementations its
//! bounds need are passed at run time). LANGUAGES.md's Iron asks for a
//! *selective* policy: copy small (or explicitly marked) generics, share the
//! rest. The plan lists every instance reachable from the program's
//! non-generic code, with its strategy; trait-method calls on placeholders
//! are resolved to the implementing method of each instance.

use alloc::vec::Vec;

use hir_lang::{ExprId, ItemId};

use crate::types::TypeId;

/// How a generic item is compiled.
///
/// # Examples
///
/// ```
/// use typeck_lang::Strategy;
///
/// assert_ne!(Strategy::Copy, Strategy::Shared);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Strategy {
    /// One copy per instantiation, with concrete types.
    Copy,
    /// One shared body; the implementations its bounds need are passed as
    /// dictionaries.
    Shared,
}

/// Which generic items a profile copies and which it shares.
///
/// [`Checker::declare_mono_attribute`](crate::Checker::declare_mono_attribute)
/// lets an attribute on an item override the policy (a language's
/// `@inline` or `@hot`).
///
/// # Examples
///
/// ```
/// use typeck_lang::MonoPolicy;
///
/// let iron = MonoPolicy::Selective { max_nodes: 64 };
/// assert_ne!(iron, MonoPolicy::Copy);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum MonoPolicy {
    /// Copy every generic item (Rust, Kraken).
    Copy,
    /// Share every generic item (dictionary passing everywhere).
    Shared,
    /// Copy generic items whose body has at most `max_nodes` HIR nodes;
    /// share the rest (Iron).
    Selective {
        /// The largest body, in live HIR nodes, that is copied.
        max_nodes: u32,
    },
}

/// One instance in a [`MonoPlan`].
///
/// # Examples
///
/// ```
/// use typeck_lang::{Instance, Strategy};
///
/// fn describe(i: Instance<'_>) -> usize {
///     if i.strategy == Strategy::Copy { i.args.len() } else { 0 }
/// }
/// # let _ = describe;
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Instance<'a> {
    /// The generic item (a function, possibly a method of a generic impl or
    /// interface).
    pub item: ItemId,
    /// The item's placeholders, in order, replaced by concrete types (owner
    /// placeholders first: an interface's `Self` and the owner's parameters,
    /// then the item's own). For a [`Strategy::Shared`] item reached only
    /// from other shared code, the item's own placeholders.
    pub args: &'a [TypeId],
    /// How the instance is compiled.
    pub strategy: Strategy,
}

/// The instances a program needs.
///
/// # Examples
///
/// ```
/// use hir_lang::Builder;
/// use typeck_lang::{check, Profile};
///
/// let mut b = Builder::new();
/// let root = b.module(None, &[]);
/// let hir = b.finish(root)?;
/// let typed = check(&hir, &Profile::static_inferred()).unwrap();
/// assert!(typed.mono_plan().is_empty());
/// # Ok::<(), hir_lang::HirError>(())
/// ```
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MonoPlan {
    pub(crate) instances: Vec<(ItemId, u32, u32, Strategy)>,
    pub(crate) args: Vec<TypeId>,
}

impl MonoPlan {
    /// The number of instances.
    ///
    /// # Examples
    ///
    /// ```
    /// assert_eq!(typeck_lang::MonoPlan::default().len(), 0);
    /// ```
    #[must_use]
    pub fn len(&self) -> usize {
        self.instances.len()
    }

    /// Whether the plan has no instances (the program uses no generic
    /// function).
    ///
    /// # Examples
    ///
    /// ```
    /// assert!(typeck_lang::MonoPlan::default().is_empty());
    /// ```
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.instances.is_empty()
    }

    /// The instances, in discovery order (breadth first from the program's
    /// non-generic items).
    ///
    /// # Examples
    ///
    /// ```
    /// let plan = typeck_lang::MonoPlan::default();
    /// assert_eq!(plan.instances().count(), 0);
    /// ```
    pub fn instances(&self) -> impl Iterator<Item = Instance<'_>> + '_ {
        self.instances
            .iter()
            .map(|&(item, start, len, strategy)| Instance {
                item,
                args: self
                    .args
                    .get(start as usize..(start as usize).saturating_add(len as usize))
                    .unwrap_or(&[]),
                strategy,
            })
    }

    /// The instances of one item.
    ///
    /// # Examples
    ///
    /// ```
    /// let plan = typeck_lang::MonoPlan::default();
    /// let item = hir_lang::ItemId::from_index(0).unwrap();
    /// assert_eq!(plan.instances_of(item).count(), 0);
    /// ```
    pub fn instances_of(&self, item: ItemId) -> impl Iterator<Item = Instance<'_>> + '_ {
        self.instances().filter(move |i| i.item == item)
    }
}

/// How a call reaches its callee.
///
/// # Examples
///
/// ```
/// use typeck_lang::Dispatch;
///
/// assert_ne!(Dispatch::Static, Dispatch::Dynamic);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Dispatch {
    /// The callee is known here.
    Static,
    /// An interface method called on a placeholder (inside a generic item):
    /// the implementing method depends on the instance (resolved per
    /// instance in the [`MonoPlan`], or through the dictionary of a shared
    /// item).
    Bound,
    /// An interface method called on a `dyn` value: dispatched at run time.
    Dynamic,
}

/// The generic item an expression uses and its arguments: a path to a
/// generic function, a method call, a constructor of a generic type.
///
/// # Examples
///
/// ```
/// use typeck_lang::{Dispatch, Instantiation};
///
/// fn is_virtual(i: Instantiation<'_>) -> bool {
///     i.dispatch == Dispatch::Dynamic
/// }
/// # let _ = is_virtual;
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Instantiation<'a> {
    /// The item used.
    pub item: ItemId,
    /// Its placeholders' arguments (they may mention the placeholders of the
    /// item the expression is in).
    pub args: &'a [TypeId],
    /// How the call is dispatched.
    pub dispatch: Dispatch,
}

/// One recorded use of an item, for the plan.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Use {
    pub(crate) at: ExprId,
    /// The item whose body contains the use (`None`: a constant context).
    pub(crate) owner: Option<ItemId>,
    pub(crate) callee: ItemId,
    pub(crate) args: (u32, u32),
    pub(crate) dispatch: Dispatch,
}
