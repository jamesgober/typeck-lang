//! Interned type terms.
//!
//! Every type is a node in one [`Types`] store, and structurally equal nodes
//! are the same node (hash-consing): `(i32, i32)` built twice is one
//! [`TypeId`]. Equality of finished types is therefore an integer compare, and
//! a type that mentions the same sub-type twice stores it once, so shared
//! structure never multiplies (ISSUES M39: the `Pair(v, v)` doubling chain is a
//! DAG of `n` nodes here, never a tree of `2^n`).
//!
//! The store also holds inference variables while a check runs. They never
//! reach the output: [`Typed`](crate::Typed) side tables only name
//! variable-free types.

use alloc::{string::String, vec::Vec};
use core::fmt;

use hir_lang::{BinderId, Def, DefId, Effects, ItemId, Prim, Symbol, UnitId, VariantId};
use intern_lang::Lookup;

/// A type in a [`Types`] store.
///
/// Ids are dense and only meaningful for the store that issued them. The
/// fixed ids below exist in every store.
///
/// # Examples
///
/// ```
/// use typeck_lang::{TypeId, Types};
/// use hir_lang::Prim;
///
/// let mut types = Types::new();
/// let pair = types.tuple(&[TypeId::prim(Prim::I32), TypeId::prim(Prim::I32)]);
/// // Hash-consed: building the same type again yields the same id.
/// assert_eq!(pair, types.tuple(&[TypeId::prim(Prim::I32), TypeId::prim(Prim::I32)]));
/// assert_ne!(pair, TypeId::UNIT);
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeId(u32);

/// The number of [`Prim`] variants; their types have the fixed ids after the
/// five builtins.
const PRIMS: [Prim; 15] = [
    Prim::Bool,
    Prim::I8,
    Prim::I16,
    Prim::I32,
    Prim::I64,
    Prim::Isize,
    Prim::U8,
    Prim::U16,
    Prim::U32,
    Prim::U64,
    Prim::Usize,
    Prim::F32,
    Prim::F64,
    Prim::Char,
    Prim::Str,
];

/// Builtin nodes that precede the primitives.
const FIRST_PRIM: u32 = 5;

const fn prim_code(p: Prim) -> u8 {
    match p {
        Prim::Bool => 0,
        Prim::I8 => 1,
        Prim::I16 => 2,
        Prim::I32 => 3,
        Prim::I64 => 4,
        Prim::Isize => 5,
        Prim::U8 => 6,
        Prim::U16 => 7,
        Prim::U32 => 8,
        Prim::U64 => 9,
        Prim::Usize => 10,
        Prim::F32 => 11,
        Prim::F64 => 12,
        Prim::Char => 13,
        Prim::Str => 14,
    }
}

impl TypeId {
    /// The error type `{error}`: the type of anything already reported. Every
    /// check that meets it succeeds silently, so one root cause produces one
    /// diagnostic.
    pub const ERROR: Self = Self(0);
    /// The dynamic type: any value, checked at run time.
    pub const ANY: Self = Self(1);
    /// The type of expressions that never produce a value (`return`, `break`,
    /// `throw`, an endless loop). It coerces to every type.
    pub const NEVER: Self = Self(2);
    /// The type of the `null` literal.
    pub const NULL: Self = Self(3);
    /// The empty tuple `()`.
    pub const UNIT: Self = Self(4);

    /// The type of a primitive.
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{Type, TypeId, Types};
    /// use hir_lang::Prim;
    ///
    /// let types = Types::new();
    /// assert_eq!(types.get(TypeId::prim(Prim::Bool)), Type::Prim(Prim::Bool));
    /// ```
    #[must_use]
    pub const fn prim(p: Prim) -> Self {
        Self(FIRST_PRIM + prim_code(p) as u32)
    }

    /// The dense index of this id in its store.
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::TypeId;
    ///
    /// assert_eq!(TypeId::ERROR.index(), 0);
    /// ```
    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }

    pub(crate) const fn raw(self) -> u32 {
        self.0
    }

    pub(crate) const fn from_raw(raw: u32) -> Self {
        Self(raw)
    }
}

impl fmt::Debug for TypeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TypeId({})", self.0)
    }
}

/// A named field of a structural record type.
///
/// # Examples
///
/// ```
/// use typeck_lang::{Field, TypeId, Types, Type};
/// use intern_lang::Interner;
///
/// let mut names = Interner::new();
/// let mut types = Types::new();
/// let x = Field { name: names.intern("x"), ty: TypeId::UNIT };
/// let rec = types.record(&[x]);
/// assert_eq!(types.get(rec), Type::Record(&[x]));
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Field {
    /// The field name.
    pub name: Symbol,
    /// The field type.
    pub ty: TypeId,
}

/// A read-only view of one type node.
///
/// `#[non_exhaustive]`: generics, traits, and the other profiles add forms.
///
/// # Examples
///
/// ```
/// use typeck_lang::{Type, TypeId, Types};
/// use hir_lang::Prim;
///
/// let mut types = Types::new();
/// let arr = types.array(TypeId::prim(Prim::U8), 4);
/// assert_eq!(types.get(arr), Type::Array { elem: TypeId::prim(Prim::U8), len: 4 });
/// assert_eq!(types.get(TypeId::UNIT), Type::Tuple(&[]));
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Type<'a> {
    /// `{error}`: already reported.
    Error,
    /// The dynamic type.
    Any,
    /// The type of diverging expressions.
    Never,
    /// The type of `null`.
    Null,
    /// A primitive.
    Prim(Prim),
    /// A tuple; the empty tuple is unit.
    Tuple(&'a [TypeId]),
    /// A fixed-length array.
    Array {
        /// The element type.
        elem: TypeId,
        /// The length.
        len: u64,
    },
    /// A slice (an array of statically unknown length).
    Slice(TypeId),
    /// A reference.
    Ref {
        /// `&mut`.
        mutable: bool,
        /// The referenced type.
        inner: TypeId,
    },
    /// A raw pointer.
    Ptr {
        /// `*mut`.
        mutable: bool,
        /// The pointed-to type.
        inner: TypeId,
    },
    /// A function type: positional parameters, a result, declared effects.
    Fn {
        /// Parameter types, in order.
        params: &'a [TypeId],
        /// The return type.
        ret: TypeId,
        /// Declared effects (`ASYNC` makes a call produce an awaitable).
        effects: Effects,
    },
    /// `T?`: a value of `T` or `null`.
    Nullable(TypeId),
    /// An ordered key-to-value map (map literals, named-argument rests).
    Map {
        /// The key type.
        key: TypeId,
        /// The value type.
        value: TypeId,
    },
    /// An anonymous structural record, fields sorted by symbol.
    Record(&'a [Field]),
    /// A nominal type declared in this unit: a record, sum, or class item.
    Adt(ItemId),
    /// A nominal type declared in another unit.
    Foreign(DefId),
    /// A host type named by an `Extern` resolution.
    Extern(Symbol),
    /// A rigid generic parameter, inside the item that declares it.
    Param(BinderId),
    /// `Self` inside an interface: the implementing type, unknown here.
    SelfOf(ItemId),
    /// The awaitable a call of an `ASYNC` function returns.
    Async(TypeId),
    /// The handle `spawn` returns; awaiting it yields the task's result.
    Task(TypeId),
    /// The generator a call of a `YIELD` function returns.
    Generator {
        /// The type of the yielded values.
        item: TypeId,
        /// An async generator (`ASYNC + YIELD`).
        is_async: bool,
    },
}

/// The node kinds, as stored.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub(crate) enum Tag {
    Error,
    Any,
    Never,
    Null,
    Tuple,
    Prim,
    Array,
    Slice,
    Ref,
    Ptr,
    Fn,
    Nullable,
    Map,
    Record,
    Adt,
    Foreign,
    Extern,
    Param,
    SelfOf,
    Async,
    Task,
    Gen,
    AsyncGen,
    Var,
}

/// One stored node. Scalars `x y z` are per-tag; `start`/`len` name a range of
/// the children pool (`Tuple`, `Fn` params) or the field pool (`Record`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Node {
    pub(crate) tag: Tag,
    /// Prim code, mutability, effect bits, or variable class.
    pub(crate) small: u8,
    /// The node mentions an inference variable somewhere below it.
    pub(crate) has_var: bool,
    pub(crate) x: u32,
    pub(crate) y: u32,
    pub(crate) z: u32,
    pub(crate) start: u32,
    pub(crate) len: u32,
}

impl Node {
    const fn leaf(tag: Tag) -> Self {
        Self {
            tag,
            small: 0,
            has_var: false,
            x: 0,
            y: 0,
            z: 0,
            start: 0,
            len: 0,
        }
    }
}

/// A node being interned: its pooled children are passed as slices so a
/// duplicate is found before anything is pushed.
struct Key<'k> {
    tag: Tag,
    small: u8,
    x: u32,
    y: u32,
    z: u32,
    kids: &'k [TypeId],
    fields: &'k [Field],
}

const EMPTY: u32 = u32::MAX;

pub(crate) fn effects_bits(e: Effects) -> u8 {
    let mut bits = 0u8;
    for (i, flag) in [
        Effects::THROWS,
        Effects::ASYNC,
        Effects::YIELD,
        Effects::UNSAFE,
    ]
    .into_iter()
    .enumerate()
    {
        if e.contains(flag) {
            bits |= 1 << i;
        }
    }
    bits
}

pub(crate) fn effects_from_bits(bits: u8) -> Effects {
    let mut e = Effects::NONE;
    for (i, flag) in [
        Effects::THROWS,
        Effects::ASYNC,
        Effects::YIELD,
        Effects::UNSAFE,
    ]
    .into_iter()
    .enumerate()
    {
        if bits & (1 << i) != 0 {
            e = e.union(flag);
        }
    }
    e
}

/// The store of interned type terms.
///
/// A [`Typed`](crate::Typed) result owns the store its side tables point into;
/// [`Checker::types_mut`](crate::Checker::types_mut) exposes the store before a
/// check, to build the types of host declarations.
///
/// # Examples
///
/// ```
/// use typeck_lang::{Type, TypeId, Types};
/// use hir_lang::{Effects, Prim};
///
/// let mut types = Types::new();
/// let i32_ = TypeId::prim(Prim::I32);
/// let f = types.func(&[i32_, i32_], i32_, Effects::NONE);
/// match types.get(f) {
///     Type::Fn { params, ret, .. } => {
///         assert_eq!(params, &[i32_, i32_]);
///         assert_eq!(ret, i32_);
///     }
///     other => panic!("{other:?}"),
/// }
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Types {
    nodes: Vec<Node>,
    kids: Vec<TypeId>,
    fields: Vec<Field>,
    /// Open-addressing hash table of node indices; `EMPTY` marks a free slot.
    table: Vec<u32>,
    /// Interned nodes in `table` (variables are never interned).
    interned: usize,
    /// Display names of nominal items and generic parameters, by index
    /// (`0` = unnamed). Not part of type identity.
    item_names: Vec<u32>,
    binder_names: Vec<u32>,
}

fn set_name(names: &mut Vec<u32>, index: usize, name: Symbol) {
    if index >= names.len() {
        names.resize(index + 1, 0);
    }
    if let Some(slot) = names.get_mut(index) {
        *slot = name.as_u32();
    }
}

impl Default for Types {
    fn default() -> Self {
        Self::new()
    }
}

impl Types {
    /// A store holding only the fixed types.
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{Type, TypeId, Types};
    ///
    /// let types = Types::new();
    /// assert_eq!(types.get(TypeId::NEVER), Type::Never);
    /// ```
    #[must_use]
    pub fn new() -> Self {
        let mut types = Self {
            nodes: Vec::with_capacity(64),
            kids: Vec::new(),
            fields: Vec::new(),
            table: alloc::vec![EMPTY; 64],
            interned: 0,
            item_names: Vec::new(),
            binder_names: Vec::new(),
        };
        // The fixed ids, in order: ERROR ANY NEVER NULL UNIT, then the prims.
        for tag in [Tag::Error, Tag::Any, Tag::Never, Tag::Null] {
            let _ = types.intern(Key {
                tag,
                small: 0,
                x: 0,
                y: 0,
                z: 0,
                kids: &[],
                fields: &[],
            });
        }
        let _ = types.tuple(&[]);
        for p in PRIMS {
            let _ = types.intern(Key {
                tag: Tag::Prim,
                small: prim_code(p),
                x: 0,
                y: 0,
                z: 0,
                kids: &[],
                fields: &[],
            });
        }
        types
    }

    /// Returns the number of nodes in the store (variables included).
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::Types;
    ///
    /// let mut types = Types::new();
    /// let before = types.len();
    /// let _ = types.slice(typeck_lang::TypeId::UNIT);
    /// assert_eq!(types.len(), before + 1);
    /// ```
    #[must_use]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Returns `true` if the store holds no nodes (never: the fixed types are
    /// always present).
    ///
    /// # Examples
    ///
    /// ```
    /// assert!(!typeck_lang::Types::new().is_empty());
    /// ```
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Size of the store in elements, including pooled children: what the
    /// type budget counts.
    pub(crate) fn footprint(&self) -> usize {
        self.nodes.len() + self.kids.len() + self.fields.len()
    }

    // ------------------------------------------------------------ reading

    pub(crate) fn node(&self, id: TypeId) -> Node {
        self.nodes
            .get(id.index())
            .copied()
            .unwrap_or(Node::leaf(Tag::Error))
    }

    pub(crate) fn kids_of(&self, n: &Node) -> &[TypeId] {
        let start = n.start as usize;
        self.kids
            .get(start..start.saturating_add(n.len as usize))
            .unwrap_or(&[])
    }

    pub(crate) fn fields_of(&self, n: &Node) -> &[Field] {
        let start = n.start as usize;
        self.fields
            .get(start..start.saturating_add(n.len as usize))
            .unwrap_or(&[])
    }

    /// Calls `f` on every direct child of `id` (element, parameter, field,
    /// inner type), in a fixed order.
    pub(crate) fn for_each_child(&self, id: TypeId, mut f: impl FnMut(TypeId)) {
        let n = self.node(id);
        match n.tag {
            Tag::Tuple => self.kids_of(&n).iter().for_each(|&k| f(k)),
            Tag::Fn => {
                self.kids_of(&n).iter().for_each(|&k| f(k));
                f(TypeId(n.z));
            }
            Tag::Record => self.fields_of(&n).iter().for_each(|fl| f(fl.ty)),
            Tag::Array
            | Tag::Slice
            | Tag::Ref
            | Tag::Ptr
            | Tag::Nullable
            | Tag::Async
            | Tag::Task
            | Tag::Gen
            | Tag::AsyncGen => f(TypeId(n.x)),
            Tag::Map => {
                f(TypeId(n.x));
                f(TypeId(n.y));
            }
            _ => {}
        }
    }

    /// Returns a view of a type. Ids from another store, and inference
    /// variables (which never appear in results), read as [`Type::Error`].
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{Type, TypeId, Types};
    ///
    /// let mut types = Types::new();
    /// let n = types.nullable(TypeId::UNIT);
    /// assert_eq!(types.get(n), Type::Nullable(TypeId::UNIT));
    /// ```
    #[must_use]
    pub fn get(&self, id: TypeId) -> Type<'_> {
        let n = self.node(id);
        match n.tag {
            Tag::Error | Tag::Var => Type::Error,
            Tag::Any => Type::Any,
            Tag::Never => Type::Never,
            Tag::Null => Type::Null,
            Tag::Prim => Type::Prim(
                PRIMS
                    .get(usize::from(n.small))
                    .copied()
                    .unwrap_or(Prim::Bool),
            ),
            Tag::Tuple => Type::Tuple(self.kids_of_ref(id)),
            Tag::Array => Type::Array {
                elem: TypeId(n.x),
                len: u64::from(n.y) | (u64::from(n.z) << 32),
            },
            Tag::Slice => Type::Slice(TypeId(n.x)),
            Tag::Ref => Type::Ref {
                mutable: n.small != 0,
                inner: TypeId(n.x),
            },
            Tag::Ptr => Type::Ptr {
                mutable: n.small != 0,
                inner: TypeId(n.x),
            },
            Tag::Fn => Type::Fn {
                params: self.kids_of_ref(id),
                ret: TypeId(n.z),
                effects: effects_from_bits(n.small),
            },
            Tag::Nullable => Type::Nullable(TypeId(n.x)),
            Tag::Map => Type::Map {
                key: TypeId(n.x),
                value: TypeId(n.y),
            },
            Tag::Record => Type::Record(self.fields_of_ref(id)),
            Tag::Adt => ItemId::from_index(n.x as usize).map_or(Type::Error, Type::Adt),
            Tag::Foreign => foreign_def(&n).map_or(Type::Error, Type::Foreign),
            Tag::Extern => Symbol::from_u32(n.x).map_or(Type::Error, Type::Extern),
            Tag::Param => BinderId::from_index(n.x as usize).map_or(Type::Error, Type::Param),
            Tag::SelfOf => ItemId::from_index(n.x as usize).map_or(Type::Error, Type::SelfOf),
            Tag::Async => Type::Async(TypeId(n.x)),
            Tag::Task => Type::Task(TypeId(n.x)),
            Tag::Gen => Type::Generator {
                item: TypeId(n.x),
                is_async: false,
            },
            Tag::AsyncGen => Type::Generator {
                item: TypeId(n.x),
                is_async: true,
            },
        }
    }

    fn kids_of_ref(&self, id: TypeId) -> &[TypeId] {
        let n = self.node(id);
        let start = n.start as usize;
        self.kids
            .get(start..start.saturating_add(n.len as usize))
            .unwrap_or(&[])
    }

    fn fields_of_ref(&self, id: TypeId) -> &[Field] {
        let n = self.node(id);
        let start = n.start as usize;
        self.fields
            .get(start..start.saturating_add(n.len as usize))
            .unwrap_or(&[])
    }

    // ----------------------------------------------------------- interning

    fn hash(key: &Key<'_>) -> u64 {
        // FxHash-style mixing: fixed, platform-independent, so ids are
        // deterministic everywhere.
        const K: u64 = 0x51_7c_c1_b7_27_22_0a_95;
        let mut h = 0u64;
        let mut add = |v: u64| h = (h.rotate_left(5) ^ v).wrapping_mul(K);
        add(key.tag as u64);
        add(u64::from(key.small));
        add(u64::from(key.x));
        add(u64::from(key.y));
        add(u64::from(key.z));
        add(key.kids.len() as u64);
        for k in key.kids {
            add(u64::from(k.0));
        }
        add(key.fields.len() as u64);
        for f in key.fields {
            add(u64::from(f.name.as_u32()));
            add(u64::from(f.ty.0));
        }
        h
    }

    fn matches(&self, n: &Node, key: &Key<'_>) -> bool {
        n.tag == key.tag
            && n.small == key.small
            && n.x == key.x
            && n.y == key.y
            && n.z == key.z
            && if n.tag == Tag::Record {
                key.kids.is_empty() && self.fields_of(n) == key.fields
            } else {
                key.fields.is_empty() && self.kids_of(n) == key.kids
            }
    }

    fn intern(&mut self, key: Key<'_>) -> TypeId {
        let hash = Self::hash(&key);
        let mask = self.table.len() - 1;
        let mut slot = (hash as usize) & mask;
        loop {
            match self.table.get(slot).copied() {
                Some(EMPTY) | None => break,
                Some(existing) => {
                    if let Some(n) = self.nodes.get(existing as usize) {
                        if self.matches(n, &key) {
                            return TypeId(existing);
                        }
                    }
                }
            }
            slot = (slot + 1) & mask;
        }
        let id = self.push(&key);
        if let Some(s) = self.table.get_mut(slot) {
            *s = id.0;
        }
        self.interned += 1;
        if self.interned * 2 > self.table.len() {
            self.grow();
        }
        id
    }

    fn push(&mut self, key: &Key<'_>) -> TypeId {
        let has_var = key.kids.iter().any(|&k| self.node(k).has_var)
            || key.fields.iter().any(|f| self.node(f.ty).has_var)
            || self.scalar_children_have_var(key);
        let (start, len) = if key.fields.is_empty() {
            let start = self.kids.len();
            self.kids.extend_from_slice(key.kids);
            (start, key.kids.len())
        } else {
            let start = self.fields.len();
            self.fields.extend_from_slice(key.fields);
            (start, key.fields.len())
        };
        let id = TypeId(u32::try_from(self.nodes.len()).unwrap_or(u32::MAX));
        self.nodes.push(Node {
            tag: key.tag,
            small: key.small,
            has_var: has_var || key.tag == Tag::Var,
            x: key.x,
            y: key.y,
            z: key.z,
            start: u32::try_from(start).unwrap_or(u32::MAX),
            len: u32::try_from(len).unwrap_or(0),
        });
        id
    }

    /// Whether the scalar-encoded children (`x`, `y`, `z` of the tags that
    /// store type ids there) mention a variable.
    fn scalar_children_have_var(&self, key: &Key<'_>) -> bool {
        let var = |raw: u32| self.node(TypeId(raw)).has_var;
        match key.tag {
            Tag::Array
            | Tag::Slice
            | Tag::Ref
            | Tag::Ptr
            | Tag::Nullable
            | Tag::Async
            | Tag::Task
            | Tag::Gen
            | Tag::AsyncGen => var(key.x),
            Tag::Map => var(key.x) || var(key.y),
            Tag::Fn => var(key.z),
            _ => false,
        }
    }

    fn grow(&mut self) {
        let cap = self.table.len() * 2;
        let mut table = alloc::vec![EMPTY; cap];
        let mask = cap - 1;
        for (i, n) in self.nodes.iter().enumerate() {
            if n.tag == Tag::Var {
                continue;
            }
            let key = Key {
                tag: n.tag,
                small: n.small,
                x: n.x,
                y: n.y,
                z: n.z,
                kids: if n.tag == Tag::Record {
                    &[]
                } else {
                    self.kids_of(n)
                },
                fields: if n.tag == Tag::Record {
                    self.fields_of(n)
                } else {
                    &[]
                },
            };
            let mut slot = (Self::hash(&key) as usize) & mask;
            while table.get(slot).is_some_and(|&s| s != EMPTY) {
                slot = (slot + 1) & mask;
            }
            if let Some(s) = table.get_mut(slot) {
                *s = u32::try_from(i).unwrap_or(u32::MAX);
            }
        }
        self.table = table;
    }

    fn simple(&mut self, tag: Tag, small: u8, x: u32, y: u32, z: u32) -> TypeId {
        self.intern(Key {
            tag,
            small,
            x,
            y,
            z,
            kids: &[],
            fields: &[],
        })
    }

    /// A fresh inference variable of the given class (never interned: each
    /// call is a distinct variable).
    pub(crate) fn fresh_var(&mut self, class: u8) -> TypeId {
        let n = u32::try_from(self.nodes.len()).unwrap_or(u32::MAX);
        self.push(&Key {
            tag: Tag::Var,
            small: class,
            x: n,
            y: 0,
            z: 0,
            kids: &[],
            fields: &[],
        })
    }

    // -------------------------------------------------------- constructors

    /// A tuple type; `tuple(&[])` is [`TypeId::UNIT`].
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{TypeId, Types};
    ///
    /// assert_eq!(Types::new().tuple(&[]), TypeId::UNIT);
    /// ```
    pub fn tuple(&mut self, elems: &[TypeId]) -> TypeId {
        self.intern(Key {
            tag: Tag::Tuple,
            small: 0,
            x: 0,
            y: 0,
            z: 0,
            kids: elems,
            fields: &[],
        })
    }

    /// A fixed-length array type.
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{Type, TypeId, Types};
    /// use hir_lang::Prim;
    ///
    /// let mut types = Types::new();
    /// let a = types.array(TypeId::prim(Prim::I32), 3);
    /// assert_eq!(types.get(a), Type::Array { elem: TypeId::prim(Prim::I32), len: 3 });
    /// ```
    pub fn array(&mut self, elem: TypeId, len: u64) -> TypeId {
        self.simple(Tag::Array, 0, elem.0, len as u32, (len >> 32) as u32)
    }

    /// A slice type.
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{Type, TypeId, Types};
    ///
    /// let mut types = Types::new();
    /// let s = types.slice(TypeId::UNIT);
    /// assert_eq!(types.get(s), Type::Slice(TypeId::UNIT));
    /// ```
    pub fn slice(&mut self, elem: TypeId) -> TypeId {
        self.simple(Tag::Slice, 0, elem.0, 0, 0)
    }

    /// A reference type.
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{Type, TypeId, Types};
    ///
    /// let mut types = Types::new();
    /// let r = types.reference(true, TypeId::UNIT);
    /// assert_eq!(types.get(r), Type::Ref { mutable: true, inner: TypeId::UNIT });
    /// ```
    pub fn reference(&mut self, mutable: bool, inner: TypeId) -> TypeId {
        self.simple(Tag::Ref, u8::from(mutable), inner.0, 0, 0)
    }

    /// A raw pointer type.
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{Type, TypeId, Types};
    ///
    /// let mut types = Types::new();
    /// let p = types.pointer(false, TypeId::UNIT);
    /// assert_eq!(types.get(p), Type::Ptr { mutable: false, inner: TypeId::UNIT });
    /// ```
    pub fn pointer(&mut self, mutable: bool, inner: TypeId) -> TypeId {
        self.simple(Tag::Ptr, u8::from(mutable), inner.0, 0, 0)
    }

    /// A function type with positional parameters.
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{TypeId, Types};
    /// use hir_lang::Effects;
    ///
    /// let mut types = Types::new();
    /// let thunk = types.func(&[], TypeId::UNIT, Effects::NONE);
    /// assert_eq!(thunk, types.func(&[], TypeId::UNIT, Effects::NONE));
    /// ```
    pub fn func(&mut self, params: &[TypeId], ret: TypeId, effects: Effects) -> TypeId {
        self.intern(Key {
            tag: Tag::Fn,
            small: effects_bits(effects),
            x: 0,
            y: 0,
            z: ret.0,
            kids: params,
            fields: &[],
        })
    }

    /// `T?`. Nullable types do not nest: `nullable(T?)` is `T?`.
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{TypeId, Types};
    ///
    /// let mut types = Types::new();
    /// let once = types.nullable(TypeId::UNIT);
    /// assert_eq!(types.nullable(once), once);
    /// ```
    pub fn nullable(&mut self, inner: TypeId) -> TypeId {
        if self.node(inner).tag == Tag::Nullable {
            return inner;
        }
        self.simple(Tag::Nullable, 0, inner.0, 0, 0)
    }

    /// A map type.
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{Type, TypeId, Types};
    /// use hir_lang::Prim;
    ///
    /// let mut types = Types::new();
    /// let m = types.map(TypeId::prim(Prim::Str), TypeId::prim(Prim::I64));
    /// assert!(matches!(types.get(m), Type::Map { .. }));
    /// ```
    pub fn map(&mut self, key: TypeId, value: TypeId) -> TypeId {
        self.simple(Tag::Map, 0, key.0, value.0, 0)
    }

    /// A structural record type. Fields are sorted by symbol; a repeated name
    /// keeps its first type.
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{Field, TypeId, Types};
    /// use intern_lang::Interner;
    ///
    /// let mut names = Interner::new();
    /// let (a, b) = (names.intern("a"), names.intern("b"));
    /// let mut types = Types::new();
    /// let ab = types.record(&[Field { name: a, ty: TypeId::UNIT }, Field { name: b, ty: TypeId::NULL }]);
    /// let ba = types.record(&[Field { name: b, ty: TypeId::NULL }, Field { name: a, ty: TypeId::UNIT }]);
    /// assert_eq!(ab, ba);
    /// ```
    pub fn record(&mut self, fields: &[Field]) -> TypeId {
        let mut sorted: Vec<Field> = fields.to_vec();
        sorted.sort_by_key(|f| f.name);
        sorted.dedup_by_key(|f| f.name);
        self.record_sorted(&sorted)
    }

    pub(crate) fn record_sorted(&mut self, sorted: &[Field]) -> TypeId {
        if sorted.is_empty() {
            // An empty field pool range is indistinguishable from "no
            // fields", which the interner keys as the kids pool; tag keeps
            // it distinct from unit.
            return self.simple(Tag::Record, 0, 0, 0, 0);
        }
        self.intern(Key {
            tag: Tag::Record,
            small: 0,
            x: 0,
            y: 0,
            z: 0,
            kids: &[],
            fields: sorted,
        })
    }

    /// The nominal type of a record, sum, or class item of the checked unit.
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{Type, Types};
    /// use hir_lang::ItemId;
    ///
    /// let mut types = Types::new();
    /// let item = ItemId::from_index(3).unwrap();
    /// let t = types.adt(item);
    /// assert_eq!(types.get(t), Type::Adt(item));
    /// ```
    pub fn adt(&mut self, item: ItemId) -> TypeId {
        self.simple(
            Tag::Adt,
            0,
            u32::try_from(item.index()).unwrap_or(u32::MAX),
            0,
            0,
        )
    }

    /// Remembers an item's name, for display of its nominal type.
    pub(crate) fn name_item(&mut self, item: ItemId, name: Symbol) {
        set_name(&mut self.item_names, item.index(), name);
    }

    /// Remembers a generic parameter's name, for display.
    pub(crate) fn name_binder(&mut self, binder: BinderId, name: Symbol) {
        set_name(&mut self.binder_names, binder.index(), name);
    }

    /// The nominal type of another unit's definition.
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{Type, Types};
    /// use hir_lang::{Def, DefId, ItemId, UnitId};
    ///
    /// let mut types = Types::new();
    /// let def = DefId::foreign(UnitId::new(2), Def::Item(ItemId::from_index(0).unwrap()));
    /// let t = types.foreign(def);
    /// assert_eq!(types.get(t), Type::Foreign(def));
    /// ```
    pub fn foreign(&mut self, def: DefId) -> TypeId {
        let (kind, index) = match def.def() {
            Def::Item(i) => (0, i.index()),
            Def::Variant(v) => (1, v.index()),
        };
        self.simple(
            Tag::Foreign,
            kind,
            def.unit().as_u32(),
            u32::try_from(index).unwrap_or(u32::MAX),
            0,
        )
    }

    /// The nominal type of a host symbol (`Res::Extern`).
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{Type, Types};
    /// use intern_lang::Interner;
    ///
    /// let mut names = Interner::new();
    /// let vec = names.intern("Vec");
    /// let mut types = Types::new();
    /// let t = types.external(vec);
    /// assert_eq!(types.get(t), Type::Extern(vec));
    /// ```
    pub fn external(&mut self, name: Symbol) -> TypeId {
        self.simple(Tag::Extern, 0, name.as_u32(), 0, 0)
    }

    pub(crate) fn param(&mut self, binder: BinderId) -> TypeId {
        self.simple(
            Tag::Param,
            0,
            u32::try_from(binder.index()).unwrap_or(u32::MAX),
            0,
            0,
        )
    }

    pub(crate) fn self_of(&mut self, item: ItemId) -> TypeId {
        self.simple(
            Tag::SelfOf,
            0,
            u32::try_from(item.index()).unwrap_or(u32::MAX),
            0,
            0,
        )
    }

    /// The awaitable a call of an `ASYNC` function returns.
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{Type, TypeId, Types};
    ///
    /// let mut types = Types::new();
    /// let a = types.awaitable(TypeId::UNIT);
    /// assert_eq!(types.get(a), Type::Async(TypeId::UNIT));
    /// ```
    pub fn awaitable(&mut self, result: TypeId) -> TypeId {
        self.simple(Tag::Async, 0, result.0, 0, 0)
    }

    /// The handle `spawn` returns.
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{Type, TypeId, Types};
    ///
    /// let mut types = Types::new();
    /// let t = types.task(TypeId::UNIT);
    /// assert_eq!(types.get(t), Type::Task(TypeId::UNIT));
    /// ```
    pub fn task(&mut self, result: TypeId) -> TypeId {
        self.simple(Tag::Task, 0, result.0, 0, 0)
    }

    /// A generator yielding `item`.
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{Type, TypeId, Types};
    ///
    /// let mut types = Types::new();
    /// let g = types.generator(TypeId::UNIT, false);
    /// assert_eq!(types.get(g), Type::Generator { item: TypeId::UNIT, is_async: false });
    /// ```
    pub fn generator(&mut self, item: TypeId, is_async: bool) -> TypeId {
        let tag = if is_async { Tag::AsyncGen } else { Tag::Gen };
        self.simple(tag, 0, item.0, 0, 0)
    }

    /// Rebuilds node `id` with new children (same tag and scalars). Used by
    /// zonking; `kids` replaces the pooled or scalar children in
    /// `for_each_child` order.
    pub(crate) fn rebuild(&mut self, id: TypeId, kids: &[TypeId]) -> TypeId {
        let n = self.node(id);
        let first = |i: usize| kids.get(i).copied().unwrap_or(TypeId::ERROR);
        match n.tag {
            Tag::Tuple => self.tuple(kids),
            Tag::Fn => {
                let (params, ret) = kids.split_at(kids.len().saturating_sub(1));
                let ret = ret.first().copied().unwrap_or(TypeId::ERROR);
                self.intern(Key {
                    tag: Tag::Fn,
                    small: n.small,
                    x: 0,
                    y: 0,
                    z: ret.0,
                    kids: params,
                    fields: &[],
                })
            }
            Tag::Record => {
                let fields: Vec<Field> = self
                    .fields_of(&n)
                    .iter()
                    .zip(kids)
                    .map(|(f, &ty)| Field { name: f.name, ty })
                    .collect();
                self.record_sorted(&fields)
            }
            Tag::Array => self.simple(Tag::Array, 0, first(0).0, n.y, n.z),
            Tag::Nullable => self.nullable(first(0)),
            Tag::Map => self.map(first(0), first(1)),
            Tag::Slice
            | Tag::Ref
            | Tag::Ptr
            | Tag::Async
            | Tag::Task
            | Tag::Gen
            | Tag::AsyncGen => self.simple(n.tag, n.small, first(0).0, 0, 0),
            _ => id,
        }
    }

    // ------------------------------------------------------------ display

    /// Renders a type for messages, resolving names with `names`.
    ///
    /// Rendering is iterative and capped (about 200 characters, then `…`), so
    /// a type of any depth or sharing renders in bounded time.
    ///
    /// # Examples
    ///
    /// ```
    /// use typeck_lang::{TypeId, Types};
    /// use hir_lang::Prim;
    /// use intern_lang::Interner;
    ///
    /// let names = Interner::new();
    /// let mut types = Types::new();
    /// let t = types.tuple(&[TypeId::prim(Prim::I32), TypeId::prim(Prim::Bool)]);
    /// let s = types.slice(t);
    /// assert_eq!(types.display(s, &names).to_string(), "[(i32, bool)]");
    /// ```
    #[must_use]
    pub fn display<'a, L: Lookup>(&'a self, id: TypeId, names: &'a L) -> TypeDisplay<'a, L> {
        TypeDisplay {
            types: self,
            id,
            names,
        }
    }

    pub(crate) fn render<L: Lookup>(&self, id: TypeId, names: &L, out: &mut String) {
        render(self, id, names, out);
    }
}

fn foreign_def(n: &Node) -> Option<DefId> {
    let unit = UnitId::new(n.x);
    let def = if n.small == 0 {
        Def::Item(ItemId::from_index(n.y as usize)?)
    } else {
        Def::Variant(VariantId::from_index(n.y as usize)?)
    };
    Some(DefId::foreign(unit, def))
}

/// A type rendered for display; see [`Types::display`].
///
/// # Examples
///
/// ```
/// use typeck_lang::{TypeId, Types};
/// use intern_lang::Interner;
///
/// let names = Interner::new();
/// let types = Types::new();
/// assert_eq!(types.display(TypeId::ERROR, &names).to_string(), "{error}");
/// ```
pub struct TypeDisplay<'a, L> {
    types: &'a Types,
    id: TypeId,
    names: &'a L,
}

impl<L: Lookup> fmt::Display for TypeDisplay<'_, L> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut out = String::new();
        render(self.types, self.id, self.names, &mut out);
        f.write_str(&out)
    }
}

/// Output cap for one rendered type.
const RENDER_CAP: usize = 200;

enum Piece {
    Ty(TypeId),
    Text(&'static str),
    Name(u32),
    Len(u64),
}

fn push_name<L: Lookup>(names: &L, raw: u32, out: &mut String) {
    let resolved = Symbol::from_u32(raw).and_then(|s| {
        names.resolve_with(s, |text| {
            out.push_str(text);
        })
    });
    if resolved.is_none() {
        out.push('#');
        push_u64(u64::from(raw), out);
    }
}

fn push_u64(mut v: u64, out: &mut String) {
    let mut digits = [0u8; 20];
    let mut i = digits.len();
    loop {
        i -= 1;
        if let Some(d) = digits.get_mut(i) {
            *d = b'0' + (v % 10) as u8;
        }
        v /= 10;
        if v == 0 || i == 0 {
            break;
        }
    }
    for &d in digits.get(i..).unwrap_or(&[]) {
        out.push(char::from(d));
    }
}

fn render<L: Lookup>(types: &Types, id: TypeId, names: &L, out: &mut String) {
    let mut stack = alloc::vec![Piece::Ty(id)];
    while let Some(piece) = stack.pop() {
        if out.len() > RENDER_CAP {
            out.push('…');
            return;
        }
        let id = match piece {
            Piece::Text(t) => {
                out.push_str(t);
                continue;
            }
            Piece::Name(raw) => {
                push_name(names, raw, out);
                continue;
            }
            Piece::Len(len) => {
                push_u64(len, out);
                continue;
            }
            Piece::Ty(id) => id,
        };
        let n = types.node(id);
        // Children are pushed in reverse so they pop in order.
        let seq =
            |open: &'static str, items: &[TypeId], close: &'static str, stack: &mut Vec<Piece>| {
                stack.push(Piece::Text(close));
                if items.len() == 1 && open == "(" {
                    stack.push(Piece::Text(","));
                }
                for (i, &k) in items.iter().enumerate().rev() {
                    stack.push(Piece::Ty(k));
                    if i > 0 {
                        stack.push(Piece::Text(", "));
                    }
                }
                stack.push(Piece::Text(open));
            };
        match n.tag {
            Tag::Error => out.push_str("{error}"),
            Tag::Var => out.push_str(match n.small {
                1 => "{integer}",
                2 => "{float}",
                _ => "_",
            }),
            Tag::Any => out.push_str("any"),
            Tag::Never => out.push('!'),
            Tag::Null => out.push_str("null"),
            Tag::Prim => out.push_str(
                PRIMS
                    .get(usize::from(n.small))
                    .copied()
                    .unwrap_or(Prim::Bool)
                    .name(),
            ),
            Tag::Tuple => seq("(", types.kids_of(&n), ")", &mut stack),
            Tag::Array => {
                stack.push(Piece::Text("]"));
                stack.push(Piece::Len(u64::from(n.y) | (u64::from(n.z) << 32)));
                stack.push(Piece::Text("; "));
                stack.push(Piece::Ty(TypeId(n.x)));
                stack.push(Piece::Text("["));
            }
            Tag::Slice => {
                stack.push(Piece::Text("]"));
                stack.push(Piece::Ty(TypeId(n.x)));
                stack.push(Piece::Text("["));
            }
            Tag::Ref | Tag::Ptr => {
                stack.push(Piece::Ty(TypeId(n.x)));
                stack.push(Piece::Text(match (n.tag, n.small != 0) {
                    (Tag::Ref, false) => "&",
                    (Tag::Ref, true) => "&mut ",
                    (_, false) => "*const ",
                    (_, true) => "*mut ",
                }));
            }
            Tag::Fn => {
                stack.push(Piece::Ty(TypeId(n.z)));
                stack.push(Piece::Text(" -> "));
                seq("fn(", types.kids_of(&n), ")", &mut stack);
                if n.small & 0b10 != 0 {
                    stack.push(Piece::Text("async "));
                }
            }
            Tag::Nullable => {
                stack.push(Piece::Text("?"));
                stack.push(Piece::Ty(TypeId(n.x)));
            }
            Tag::Map => {
                stack.push(Piece::Text("}"));
                stack.push(Piece::Ty(TypeId(n.y)));
                stack.push(Piece::Text(": "));
                stack.push(Piece::Ty(TypeId(n.x)));
                stack.push(Piece::Text("{"));
            }
            Tag::Record => {
                stack.push(Piece::Text(" }"));
                let fields = types.fields_of(&n);
                for (i, fl) in fields.iter().enumerate().rev() {
                    stack.push(Piece::Ty(fl.ty));
                    stack.push(Piece::Text(": "));
                    stack.push(Piece::Name(fl.name.as_u32()));
                    if i > 0 {
                        stack.push(Piece::Text(", "));
                    }
                }
                stack.push(Piece::Text("{ "));
            }
            Tag::Adt | Tag::Param => {
                let table = if n.tag == Tag::Adt {
                    &types.item_names
                } else {
                    &types.binder_names
                };
                match table.get(n.x as usize).copied().filter(|&raw| raw != 0) {
                    Some(raw) => push_name(names, raw, out),
                    None => {
                        out.push_str(if n.tag == Tag::Adt { "item#" } else { "param#" });
                        push_u64(u64::from(n.x), out);
                    }
                }
            }
            Tag::Foreign => {
                out.push('u');
                push_u64(u64::from(n.x), out);
                out.push_str(if n.small == 0 { ":item#" } else { ":variant#" });
                push_u64(u64::from(n.y), out);
            }
            Tag::Extern => push_name(names, n.x, out),
            Tag::SelfOf => out.push_str("Self"),
            Tag::Async | Tag::Task | Tag::Gen | Tag::AsyncGen => {
                stack.push(Piece::Text(">"));
                stack.push(Piece::Ty(TypeId(n.x)));
                stack.push(Piece::Text(match n.tag {
                    Tag::Async => "async<",
                    Tag::Task => "task<",
                    Tag::Gen => "generator<",
                    _ => "async-generator<",
                }));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::string::ToString;

    use hir_lang::{BinderId, Def, DefId, Effects, ItemId, Prim, UnitId, VariantId};
    use intern_lang::Interner;

    use super::*;

    fn item(i: usize) -> ItemId {
        ItemId::from_index(i).unwrap_or_else(|| item(0))
    }

    #[test]
    fn test_fixed_ids_are_the_builtins() {
        let t = Types::new();
        assert_eq!(t.get(TypeId::ERROR), Type::Error);
        assert_eq!(t.get(TypeId::ANY), Type::Any);
        assert_eq!(t.get(TypeId::NEVER), Type::Never);
        assert_eq!(t.get(TypeId::NULL), Type::Null);
        assert_eq!(t.get(TypeId::UNIT), Type::Tuple(&[]));
        for p in PRIMS {
            assert_eq!(t.get(TypeId::prim(p)), Type::Prim(p));
        }
        assert_eq!(t.len(), 20);
    }

    #[test]
    fn test_hash_consing_survives_table_growth() {
        let mut t = Types::new();
        let mut ids = alloc::vec::Vec::new();
        let mut cur = TypeId::UNIT;
        for _ in 0..5_000 {
            cur = t.slice(cur);
            ids.push(cur);
        }
        // Rebuilding every type yields the same ids, after many regrowths.
        let mut again = TypeId::UNIT;
        for &id in &ids {
            again = t.slice(again);
            assert_eq!(again, id);
        }
        assert_eq!(t.len(), 20 + 5_000);
    }

    #[test]
    fn test_distinct_shapes_are_distinct() {
        let mut t = Types::new();
        let i32_ = TypeId::prim(Prim::I32);
        let a = t.array(i32_, 3);
        let b = t.array(i32_, 4);
        let c = t.array(i32_, 3 + (1 << 32));
        assert_ne!(a, b);
        assert_ne!(a, c);
        assert_eq!(
            t.get(c),
            Type::Array {
                elem: i32_,
                len: 3 + (1 << 32)
            }
        );
        let r = t.reference(false, i32_);
        let m = t.reference(true, i32_);
        let p = t.pointer(false, i32_);
        assert_ne!(r, m);
        assert_ne!(r, p);
        let f = t.func(&[i32_], i32_, Effects::NONE);
        let g = t.func(&[i32_], i32_, Effects::ASYNC);
        assert_ne!(f, g);
        assert_eq!(
            t.get(g),
            Type::Fn {
                params: &[i32_],
                ret: i32_,
                effects: Effects::ASYNC
            }
        );
        let empty_record = t.record(&[]);
        assert_ne!(empty_record, TypeId::UNIT);
        assert_eq!(t.get(empty_record), Type::Record(&[]));
    }

    #[test]
    fn test_effect_bits_round_trip() {
        for e in [
            Effects::NONE,
            Effects::THROWS,
            Effects::ASYNC.union(Effects::YIELD),
            Effects::UNSAFE,
        ] {
            assert_eq!(effects_from_bits(effects_bits(e)), e);
        }
    }

    #[test]
    fn test_nominal_and_host_types() {
        let mut t = Types::new();
        let it = item(7);
        let a = t.adt(it);
        assert_eq!(a, t.adt(it));
        let def = DefId::foreign(UnitId::new(3), Def::Item(it));
        let f = t.foreign(def);
        assert_eq!(t.get(f), Type::Foreign(def));
        let v = VariantId::from_index(2)
            .map(Def::Variant)
            .unwrap_or(Def::Item(it));
        let fv = t.foreign(DefId::foreign(UnitId::new(3), v));
        assert_ne!(f, fv);
        if let Some(b) = BinderId::from_index(1) {
            let p = t.param(b);
            assert_eq!(t.get(p), Type::Param(b));
        }
        let s = t.self_of(it);
        assert_eq!(t.get(s), Type::SelfOf(it));
        let g = t.generator(TypeId::UNIT, true);
        assert_eq!(
            t.get(g),
            Type::Generator {
                item: TypeId::UNIT,
                is_async: true
            }
        );
    }

    #[test]
    fn test_rendering_covers_every_form() {
        let mut names = Interner::new();
        let x = names.intern("x");
        let vec = names.intern("Vec");
        let mut t = Types::new();
        let i32_ = TypeId::prim(Prim::I32);
        let cases: alloc::vec::Vec<(TypeId, &str)> = alloc::vec![
            (TypeId::ERROR, "{error}"),
            (TypeId::ANY, "any"),
            (TypeId::NEVER, "!"),
            (TypeId::NULL, "null"),
            (TypeId::UNIT, "()"),
            (t.tuple(&[i32_]), "(i32,)"),
            (t.tuple(&[i32_, i32_]), "(i32, i32)"),
            (t.array(i32_, 4), "[i32; 4]"),
            (t.slice(i32_), "[i32]"),
            (t.reference(false, i32_), "&i32"),
            (t.reference(true, i32_), "&mut i32"),
            (t.pointer(false, i32_), "*const i32"),
            (t.pointer(true, i32_), "*mut i32"),
            (
                t.func(&[i32_], TypeId::UNIT, Effects::ASYNC),
                "async fn(i32) -> ()"
            ),
            (t.nullable(i32_), "i32?"),
            (t.map(i32_, i32_), "{i32: i32}"),
            (t.record(&[Field { name: x, ty: i32_ }]), "{ x: i32 }"),
            (t.external(vec), "Vec"),
            (t.awaitable(i32_), "async<i32>"),
            (t.task(i32_), "task<i32>"),
            (t.generator(i32_, false), "generator<i32>"),
        ];
        for (id, want) in cases {
            assert_eq!(t.display(id, &names).to_string(), want);
        }
        let it = item(4);
        let adt = t.adt(it);
        assert_eq!(t.display(adt, &names).to_string(), "item#4");
        t.name_item(it, x);
        assert_eq!(t.display(adt, &names).to_string(), "x");
    }

    #[test]
    fn test_rendering_is_capped() {
        let names = Interner::new();
        let mut t = Types::new();
        let mut cur = TypeId::prim(Prim::I32);
        for _ in 0..64 {
            cur = t.tuple(&[cur, cur]);
        }
        let s = t.display(cur, &names).to_string();
        assert!(s.ends_with('\u{2026}'));
        assert!(s.len() < 300);
    }
}
