//! Union-find over interned type terms: unification, the occurs check, and
//! zonking (replacing variables by what they were bound to).
//!
//! This replaces type-lang 1's substitution-map unifier, whose occurs check,
//! `resolve`, and mismatch construction expand shared structure into trees
//! (ISSUES M39–M41). Here:
//!
//! - every type node (variable or not) has a union-find class; unifying two
//!   compound nodes **merges their classes before descending**, so a pair of
//!   nodes is decomposed at most once per class merge (Huet's algorithm): the
//!   `Pair(v, v)` doubling chain unifies in linear time;
//! - the occurs check is a DFS over class representatives with a visited set,
//!   skipping variable-free subterms in O(1) through the `has_var` bit, so it
//!   is linear in the DAG, never in its tree expansion;
//! - every traversal is iterative and every step is charged to the budget;
//! - a failed unification rolls back every class merge it made (a journal),
//!   so a mismatch never leaves interned, shared terms merged.
//!
//! Merging two non-variable classes is permanent and global, which is sound
//! because it only happens when the two terms are equal under the
//! substitution, and the substitution only grows.

use alloc::{collections::BTreeSet, vec::Vec};

use crate::{
    error::{CheckError, Limit, Meter},
    types::{Field, Tag, TypeId, Types},
};

/// Variable classes: what a variable may be bound to.
pub(crate) const GENERAL: u8 = 0;
/// An unsuffixed integer literal: an integer type (or a float type, when the
/// profile widens).
pub(crate) const INT: u8 = 1;
/// An unsuffixed float literal: a float type.
pub(crate) const FLOAT: u8 = 2;

#[derive(Clone, Copy, Debug)]
enum Undo {
    Parent(u32, u32),
    Rank(u32, u8),
    Repr(u32, u32),
    Class(u32, u8),
}

/// What unification needs from the checker: profile flags and the field
/// lists of record items (for structural records).
pub(crate) struct UnifyCfg<'a> {
    /// Integer-literal variables may bind float types.
    pub(crate) int_to_float: bool,
    /// Record items with equal field lists are equal.
    pub(crate) structural: bool,
    /// Sorted field lists of record items, by item index (`None`: not a
    /// record with named fields).
    pub(crate) record_fields: &'a [Option<(u32, u32)>],
    /// The pool those ranges point into.
    pub(crate) field_pool: &'a [Field],
}

impl UnifyCfg<'_> {
    fn fields_of_item(&self, item: u32) -> Option<&[Field]> {
        let (start, len) = (*self.record_fields.get(item as usize)?)?;
        self.field_pool
            .get(start as usize..(start as usize).saturating_add(len as usize))
    }
}

/// The union-find state of one check.
#[derive(Debug, Default)]
pub(crate) struct Infer {
    parent: Vec<u32>,
    rank: Vec<u8>,
    /// Per root: the node that represents the class (a non-variable node if
    /// the class has one).
    repr: Vec<u32>,
    /// Per root: the variable class, when the representative is a variable.
    class: Vec<u8>,
    journal: Vec<Undo>,
    /// Open snapshots; the journal is kept while any is open.
    open: u32,
    stamp: Vec<u32>,
    epoch: u32,
    work: Vec<(TypeId, TypeId)>,
    stack: Vec<TypeId>,
    /// Nominal-record pairs under structural comparison in the current
    /// unification.
    assumed: BTreeSet<(u32, u32)>,
    /// Scratch stacks of `zonk` and `first_free`, reused across calls.
    walk: Vec<(TypeId, bool)>,
    kids: Vec<TypeId>,
    /// Every variable created, in creation order.
    pub(crate) vars: Vec<TypeId>,
}

impl Infer {
    /// Extends the tables to cover every node of `types`; new nodes start as
    /// their own singleton class.
    fn sync(&mut self, types: &Types) {
        let n = types.len();
        let mut i = self.parent.len();
        while i < n {
            let raw = u32::try_from(i).unwrap_or(u32::MAX);
            self.parent.push(raw);
            self.rank.push(0);
            self.repr.push(raw);
            self.class
                .push(types.node(TypeId::from_raw(raw)).small.min(FLOAT));
            i += 1;
        }
    }

    /// A fresh variable of `class`.
    pub(crate) fn fresh(&mut self, types: &mut Types, class: u8) -> TypeId {
        let v = types.fresh_var(class);
        // Register it now: its class must be readable before it is ever
        // unified.
        self.sync(types);
        self.vars.push(v);
        v
    }

    /// The root of `t`'s class. Union by rank keeps trees `O(log n)` deep;
    /// paths are not compressed, so lookups never write (and never need
    /// journaling).
    pub(crate) fn find(&self, t: TypeId) -> u32 {
        let mut x = t.raw();
        loop {
            match self.parent.get(x as usize) {
                Some(&p) if p != x => x = p,
                _ => return x,
            }
        }
    }

    /// The node representing `t`'s class: `t`'s binding if it is a bound
    /// variable (to any depth), else `t`'s class representative.
    pub(crate) fn resolve(&self, t: TypeId) -> TypeId {
        let root = self.find(t);
        TypeId::from_raw(self.repr.get(root as usize).copied().unwrap_or(root))
    }

    /// The variable class of an unresolved variable's class.
    pub(crate) fn class_of(&self, t: TypeId) -> u8 {
        let root = self.find(t);
        self.class.get(root as usize).copied().unwrap_or(GENERAL)
    }

    fn write_parent(&mut self, i: u32, v: u32) {
        if let Some(slot) = self.parent.get_mut(i as usize) {
            self.journal.push(Undo::Parent(i, *slot));
            *slot = v;
        }
    }

    fn write_rank(&mut self, i: u32, v: u8) {
        if let Some(slot) = self.rank.get_mut(i as usize) {
            self.journal.push(Undo::Rank(i, *slot));
            *slot = v;
        }
    }

    fn write_repr(&mut self, i: u32, v: u32) {
        if let Some(slot) = self.repr.get_mut(i as usize) {
            self.journal.push(Undo::Repr(i, *slot));
            *slot = v;
        }
    }

    fn write_class(&mut self, i: u32, v: u8) {
        if let Some(slot) = self.class.get_mut(i as usize) {
            self.journal.push(Undo::Class(i, *slot));
            *slot = v;
        }
    }

    /// Merges two roots; the merged class is represented by `repr` with
    /// variable class `class`.
    fn link(&mut self, a: u32, b: u32, repr: u32, class: u8) {
        let ra = self.rank.get(a as usize).copied().unwrap_or(0);
        let rb = self.rank.get(b as usize).copied().unwrap_or(0);
        let (root, child) = if ra >= rb { (a, b) } else { (b, a) };
        self.write_parent(child, root);
        if ra == rb {
            self.write_rank(root, ra.saturating_add(1));
        }
        self.write_repr(root, repr);
        self.write_class(root, class);
    }

    /// Opens a snapshot: changes after it can be rolled back together.
    pub(crate) fn snapshot(&mut self) -> usize {
        self.open += 1;
        self.journal.len()
    }

    /// Undoes every change since `snap` and closes the snapshot.
    pub(crate) fn rollback(&mut self, snap: usize) {
        self.undo_to(snap);
        self.close();
    }

    /// Keeps the changes since `snap` and closes the snapshot.
    pub(crate) fn commit(&mut self) {
        self.close();
    }

    fn close(&mut self) {
        self.open = self.open.saturating_sub(1);
        if self.open == 0 {
            self.journal.clear();
        }
    }

    fn undo_to(&mut self, snap: usize) {
        while self.journal.len() > snap {
            match self.journal.pop() {
                Some(Undo::Parent(i, v)) => set(&mut self.parent, i, v),
                Some(Undo::Rank(i, v)) => set(&mut self.rank, i, v),
                Some(Undo::Repr(i, v)) => set(&mut self.repr, i, v),
                Some(Undo::Class(i, v)) => set(&mut self.class, i, v),
                None => break,
            }
        }
    }

    /// Unifies `a` and `b`. `Ok(true)`: they are now equal. `Ok(false)`: they
    /// cannot be, and nothing changed. The error type unifies with anything
    /// (binding variables to it), so a mismatch is never reported against
    /// something already reported.
    pub(crate) fn unify(
        &mut self,
        types: &Types,
        cfg: &UnifyCfg<'_>,
        meter: &mut Meter,
        a: TypeId,
        b: TypeId,
    ) -> Result<bool, CheckError> {
        // Already equal: the common case at expected-type sites.
        if a == b || self.find(a) == self.find(b) {
            return Ok(true);
        }
        self.sync(types);
        let snap = self.snapshot();
        let result = self.unify_inner(types, cfg, meter, a, b);
        match result {
            Ok(true) => self.commit(),
            _ => self.rollback(snap),
        }
        result
    }

    fn unify_inner(
        &mut self,
        types: &Types,
        cfg: &UnifyCfg<'_>,
        meter: &mut Meter,
        a: TypeId,
        b: TypeId,
    ) -> Result<bool, CheckError> {
        self.work.clear();
        self.assumed.clear();
        self.work.push((a, b));
        while let Some((a, b)) = self.work.pop() {
            meter.tick(1)?;
            let (ra, rb) = (self.find(a), self.find(b));
            if ra == rb {
                continue;
            }
            let ta = TypeId::from_raw(self.repr.get(ra as usize).copied().unwrap_or(ra));
            let tb = TypeId::from_raw(self.repr.get(rb as usize).copied().unwrap_or(rb));
            let (na, nb) = (types.node(ta), types.node(tb));
            match (na.tag, nb.tag) {
                (Tag::Var, Tag::Var) => {
                    let (ca, cb) = (self.class_of(ta), self.class_of(tb));
                    let merged = match (ca, cb) {
                        (x, y) if x == y => x,
                        (GENERAL, y) => y,
                        (x, GENERAL) => x,
                        // INT with FLOAT: the literal becomes a float.
                        _ if cfg.int_to_float => FLOAT,
                        _ => return Ok(false),
                    };
                    self.link(ra, rb, ta.raw(), merged);
                }
                (Tag::Var, _) => {
                    if !self.bind(types, cfg, meter, ra, ta, tb)? {
                        return Ok(false);
                    }
                }
                (_, Tag::Var) => {
                    if !self.bind(types, cfg, meter, rb, tb, ta)? {
                        return Ok(false);
                    }
                }
                // `{error}` equals everything, but is never merged with a
                // non-variable class: that would poison a shared term. The
                // variables inside the other side become `{error}` too (they
                // stand for parts of something already reported), each
                // node once.
                (Tag::Error, _) | (_, Tag::Error) => {
                    let other = if na.tag == Tag::Error { tb } else { ta };
                    if types.node(other).has_var
                        && self.assumed.insert((other.raw(), TypeId::ERROR.raw()))
                    {
                        let work = &mut self.work;
                        types.for_each_child(other, |k| work.push((k, TypeId::ERROR)));
                    }
                }
                // Structural equality with a nominal record: compare fields,
                // but never merge the nominal type's class (it would then
                // stand for the other type everywhere). Pairs already being
                // compared in this call are assumed equal, which is what
                // makes recursive records terminate (coinduction).
                // Two instances of one nominal item: equal when their
                // arguments are.
                (Tag::Adt, Tag::Adt) if na.x == nb.x => {
                    if !self.decompose(types, cfg, ta, tb)? {
                        return Ok(false);
                    }
                    self.link(ra, rb, prefer_ground(types, ta, tb).raw(), GENERAL);
                }
                (Tag::Adt, _) | (_, Tag::Adt) => {
                    let pair = (ta.raw().min(tb.raw()), ta.raw().max(tb.raw()));
                    if self.assumed.insert(pair) && !self.decompose(types, cfg, ta, tb)? {
                        return Ok(false);
                    }
                }
                _ => {
                    if !self.decompose(types, cfg, ta, tb)? {
                        return Ok(false);
                    }
                    self.link(ra, rb, prefer_ground(types, ta, tb).raw(), GENERAL);
                }
            }
        }
        Ok(true)
    }

    /// Binds the variable class `root` (represented by `var`) to `term`.
    fn bind(
        &mut self,
        types: &Types,
        cfg: &UnifyCfg<'_>,
        meter: &mut Meter,
        root: u32,
        var: TypeId,
        term: TypeId,
    ) -> Result<bool, CheckError> {
        let n = types.node(term);
        let ok = match self.class_of(var) {
            _ if n.tag == Tag::Error => true,
            INT => {
                n.tag == Tag::Prim
                    && (is_int_code(n.small) || (cfg.int_to_float && is_float_code(n.small)))
            }
            FLOAT => n.tag == Tag::Prim && is_float_code(n.small),
            _ => !self.occurs(types, meter, root, term)?,
        };
        if ok {
            let term_root = self.find(term);
            self.link(root, term_root, term.raw(), GENERAL);
        }
        Ok(ok)
    }

    /// Pushes the child pairs of two non-variable nodes, or reports that
    /// their constructors differ.
    fn decompose(
        &mut self,
        types: &Types,
        cfg: &UnifyCfg<'_>,
        a: TypeId,
        b: TypeId,
    ) -> Result<bool, CheckError> {
        let (na, nb) = (types.node(a), types.node(b));
        let same_adt = na.tag == Tag::Adt && nb.tag == Tag::Adt && na.x == nb.x;
        if !same_adt
            && (na.tag == Tag::Adt
                || nb.tag == Tag::Adt
                || na.tag == Tag::Record
                || nb.tag == Tag::Record)
        {
            return Ok(self.decompose_records(types, cfg, a, b));
        }
        if na.tag != nb.tag || na.small != nb.small || na.len != nb.len {
            return Ok(false);
        }
        match na.tag {
            // Applied nominal types, interface references, projections,
            // opaque types, unions, intersections, and trait objects: equal
            // heads, then equal children in order. Unions and intersections
            // are kept sorted, so variable-free ones compare by id before
            // getting here; with variables inside, members are paired in
            // their stored order.
            Tag::Adt
            | Tag::Foreign
            | Tag::Extern
            | Tag::Trait
            | Tag::Proj
            | Tag::Opaque
            | Tag::Union
            | Tag::Inter
            | Tag::Dyn => {
                if na.x != nb.x || na.y != nb.y || na.z != nb.z {
                    return Ok(false);
                }
                let (ka, kb) = (types.kids_of(&na), types.kids_of(&nb));
                self.work.extend(ka.iter().copied().zip(kb.iter().copied()));
                Ok(true)
            }
            Tag::Tuple | Tag::Fn => {
                let (ka, kb) = (types.kids_of(&na), types.kids_of(&nb));
                self.work.extend(ka.iter().copied().zip(kb.iter().copied()));
                if na.tag == Tag::Fn {
                    self.work
                        .push((TypeId::from_raw(na.z), TypeId::from_raw(nb.z)));
                }
                Ok(true)
            }
            Tag::Array | Tag::Map => {
                self.work
                    .push((TypeId::from_raw(na.x), TypeId::from_raw(nb.x)));
                self.work
                    .push((TypeId::from_raw(na.y), TypeId::from_raw(nb.y)));
                Ok(true)
            }
            Tag::Slice
            | Tag::Ref
            | Tag::Ptr
            | Tag::Nullable
            | Tag::Async
            | Tag::Task
            | Tag::Gen
            | Tag::AsyncGen => {
                self.work
                    .push((TypeId::from_raw(na.x), TypeId::from_raw(nb.x)));
                Ok(true)
            }
            // Leaves are interned: distinct ids are distinct types.
            _ => Ok(a == b),
        }
    }

    /// Records: an anonymous record equals another with the same field
    /// names; with structural records, a record item equals any record of
    /// its shape.
    fn decompose_records(
        &mut self,
        types: &Types,
        cfg: &UnifyCfg<'_>,
        a: TypeId,
        b: TypeId,
    ) -> bool {
        let fields = |t: TypeId| -> Option<&[Field]> {
            let n = types.node(t);
            match n.tag {
                Tag::Record => Some(types.fields_of(&n)),
                Tag::Adt if cfg.structural => cfg.fields_of_item(n.x),
                _ => None,
            }
        };
        let (Some(fa), Some(fb)) = (fields(a), fields(b)) else {
            return false;
        };
        if fa.len() != fb.len() || fa.iter().zip(fb).any(|(x, y)| x.name != y.name) {
            return false;
        }
        self.work
            .extend(fa.iter().zip(fb).map(|(x, y)| (x.ty, y.ty)));
        true
    }

    /// Whether the class `var_root` occurs in `term`, through bindings.
    fn occurs(
        &mut self,
        types: &Types,
        meter: &mut Meter,
        var_root: u32,
        term: TypeId,
    ) -> Result<bool, CheckError> {
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            self.stamp.iter_mut().for_each(|s| *s = 0);
            self.epoch = 1;
        }
        if self.stamp.len() < types.len() {
            self.stamp.resize(types.len(), 0);
        }
        self.stack.clear();
        self.stack.push(term);
        while let Some(t) = self.stack.pop() {
            meter.tick(1)?;
            let root = self.find(t);
            if root == var_root {
                return Ok(true);
            }
            let rep = TypeId::from_raw(self.repr.get(root as usize).copied().unwrap_or(root));
            match self.stamp.get_mut(rep.index()) {
                Some(s) if *s == self.epoch => continue,
                Some(s) => *s = self.epoch,
                None => {}
            }
            if !types.node(rep).has_var {
                continue;
            }
            let stack = &mut self.stack;
            types.for_each_child(rep, |k| stack.push(k));
        }
        Ok(false)
    }

    /// Binds an unresolved variable (of any class) to `term` directly; used
    /// for literal defaults and for giving up on unresolvable variables.
    pub(crate) fn force(&mut self, types: &Types, var: TypeId, term: TypeId) {
        self.sync(types);
        let (rv, rt) = (self.find(var), self.find(term));
        if rv != rt {
            let _ = self.snapshot();
            self.link(rv, rt, term.raw(), GENERAL);
            self.commit();
        }
    }

    // ------------------------------------------------------------- zonking

    /// Returns the variable-free type equal to `t`, interning rebuilt nodes.
    /// Unresolved variables become `{error}` (the caller reports them
    /// first). Memoized in `memo` (indexed by node, `u32::MAX` = unknown),
    /// which must only be reused while no unification happens, so zonking
    /// every recorded type is linear in the type DAG.
    pub(crate) fn zonk(
        &mut self,
        types: &mut Types,
        memo: &mut Vec<u32>,
        meter: &mut Meter,
        t: TypeId,
    ) -> Result<TypeId, CheckError> {
        const UNKNOWN: u32 = u32::MAX;
        const BUSY: u32 = u32::MAX - 1;
        // Ids beyond the store (a host may pass ids of another store) read
        // as `{error}` and are never memoized, so the memo stays bounded by
        // this store's size.
        fn get(memo: &[u32], t: TypeId, len: usize) -> u32 {
            if t.index() >= len {
                TypeId::ERROR.raw()
            } else {
                memo.get(t.index()).copied().unwrap_or(UNKNOWN)
            }
        }
        fn set(memo: &mut Vec<u32>, t: TypeId, v: u32, len: usize) {
            if t.index() >= len {
                return;
            }
            if t.index() >= memo.len() {
                memo.resize(t.index() + 1, UNKNOWN);
            }
            if let Some(slot) = memo.get_mut(t.index()) {
                *slot = v;
            }
        }
        // Variable-free types (most of them, at the end) are their own
        // answer.
        if t.index() < types.len() {
            let rep = self.resolve(t);
            if !types.node(rep).has_var {
                return Ok(rep);
            }
        }
        let mut stack = core::mem::take(&mut self.walk);
        let mut kids = core::mem::take(&mut self.kids);
        stack.clear();
        stack.push((t, false));
        while let Some((x, expanded)) = stack.pop() {
            meter.tick(1)?;
            let len = types.len();
            if !expanded && get(memo, x, len) != UNKNOWN {
                continue;
            }
            let rep = self.resolve(x);
            let n = types.node(rep);
            if !n.has_var {
                set(memo, x, rep.raw(), len);
                continue;
            }
            if n.tag == Tag::Var {
                set(memo, x, TypeId::ERROR.raw(), len);
                continue;
            }
            if !expanded {
                set(memo, x, BUSY, len);
                stack.push((x, true));
                types.for_each_child(rep, |k| {
                    if get(memo, k, len) == UNKNOWN {
                        stack.push((k, false));
                    }
                });
                continue;
            }
            kids.clear();
            types.for_each_child(rep, |k| {
                let v = get(memo, k, len);
                // A child still busy would be a cycle, which the occurs check
                // rules out; it reads as `{error}` rather than looping.
                kids.push(if v >= BUSY {
                    TypeId::ERROR
                } else {
                    TypeId::from_raw(v)
                });
            });
            let rebuilt = types.rebuild(rep, &kids);
            let len = types.len();
            set(memo, x, rebuilt.raw(), len);
            set(memo, rep, rebuilt.raw(), len);
        }
        self.walk = stack;
        self.kids = kids;
        let v = get(memo, t, types.len());
        Ok(if v >= BUSY {
            TypeId::ERROR
        } else {
            TypeId::from_raw(v)
        })
    }

    /// Returns the root of the first unresolved general variable in `t`, if
    /// any; memoized like [`zonk`](Self::zonk) (`memo` values: `u32::MAX`
    /// unknown, `u32::MAX - 1` none, else a root).
    pub(crate) fn first_free(
        &mut self,
        types: &Types,
        memo: &mut Vec<u32>,
        meter: &mut Meter,
        t: TypeId,
    ) -> Result<Option<u32>, CheckError> {
        const UNKNOWN: u32 = u32::MAX;
        const NONE: u32 = u32::MAX - 1;
        if memo.len() < types.len() {
            memo.resize(types.len(), UNKNOWN);
        }
        let get = |memo: &Vec<u32>, t: TypeId| memo.get(t.index()).copied().unwrap_or(NONE);
        if !types.node(self.resolve(t)).has_var {
            return Ok(None);
        }
        let mut stack = core::mem::take(&mut self.walk);
        stack.clear();
        stack.push((t, false));
        while let Some((x, expanded)) = stack.pop() {
            meter.tick(1)?;
            if !expanded && get(memo, x) != UNKNOWN {
                continue;
            }
            let rep = self.resolve(x);
            let n = types.node(rep);
            let value = if !n.has_var {
                NONE
            } else if n.tag == Tag::Var {
                if self.class_of(rep) == GENERAL {
                    self.find(rep)
                } else {
                    NONE
                }
            } else if !expanded {
                if let Some(slot) = memo.get_mut(x.index()) {
                    *slot = NONE; // provisional; guards against cycles
                }
                stack.push((x, true));
                types.for_each_child(rep, |k| {
                    if get(memo, k) == UNKNOWN {
                        stack.push((k, false));
                    }
                });
                continue;
            } else {
                let mut found = NONE;
                types.for_each_child(rep, |k| {
                    let v = get(memo, k);
                    if found == NONE && v < NONE {
                        found = v;
                    }
                });
                found
            };
            if let Some(slot) = memo.get_mut(x.index()) {
                *slot = value;
            }
        }
        self.walk = stack;
        let v = get(memo, t);
        Ok((v < NONE).then_some(v))
    }

    /// Fails with the type-store budget error if `types` grew past it.
    pub(crate) fn check_size(types: &Types, meter: &Meter) -> Result<(), CheckError> {
        if types.footprint() > meter.budget.type_nodes {
            Err(CheckError::BudgetExceeded {
                limit: Limit::TypeNodes,
            })
        } else {
            Ok(())
        }
    }
}

/// Of two equal non-variable nodes, the one to represent their class: a
/// variable-free node when there is one, so a variable-free type resolves
/// to itself (or to an equally variable-free node) and its flags describe
/// what it reaches.
fn prefer_ground(types: &Types, a: TypeId, b: TypeId) -> TypeId {
    if types.node(a).has_var && !types.node(b).has_var {
        b
    } else {
        a
    }
}

fn set<T: Copy>(table: &mut [T], i: u32, v: T) {
    if let Some(slot) = table.get_mut(i as usize) {
        *slot = v;
    }
}

/// Prim codes (see `types::prim_code`) of the integer types.
pub(crate) const fn is_int_code(code: u8) -> bool {
    matches!(code, 1..=10)
}

/// Prim codes of the float types.
pub(crate) const fn is_float_code(code: u8) -> bool {
    matches!(code, 11 | 12)
}

#[cfg(test)]
mod tests {
    use hir_lang::{Effects, Prim};

    use super::*;
    use crate::error::Budget;

    fn cfg() -> UnifyCfg<'static> {
        UnifyCfg {
            int_to_float: false,
            structural: false,
            record_fields: &[],
            field_pool: &[],
        }
    }

    #[test]
    fn test_var_binds_and_resolves() {
        let mut types = Types::new();
        let mut inf = Infer::default();
        let mut meter = Meter::new(Budget::default());
        let v = inf.fresh(&mut types, GENERAL);
        let i32_ = TypeId::prim(Prim::I32);
        assert_eq!(inf.unify(&types, &cfg(), &mut meter, v, i32_), Ok(true));
        assert_eq!(inf.resolve(v), i32_);
    }

    #[test]
    fn test_mismatch_rolls_back_partial_merges() {
        let mut types = Types::new();
        let mut inf = Infer::default();
        let mut meter = Meter::new(Budget::default());
        let v = inf.fresh(&mut types, GENERAL);
        // (v, bool) ~ (i32, i32): v would bind, then bool ~ i32 fails.
        let a = types.tuple(&[v, TypeId::prim(Prim::Bool)]);
        let b = types.tuple(&[TypeId::prim(Prim::I32), TypeId::prim(Prim::I32)]);
        assert_eq!(inf.unify(&types, &cfg(), &mut meter, a, b), Ok(false));
        assert_eq!(inf.resolve(v), v, "binding rolled back");
        assert_ne!(inf.find(a), inf.find(b), "class merge rolled back");
    }

    #[test]
    fn test_occurs_check_rejects_cycles() {
        let mut types = Types::new();
        let mut inf = Infer::default();
        let mut meter = Meter::new(Budget::default());
        let v = inf.fresh(&mut types, GENERAL);
        let s = types.slice(v);
        assert_eq!(inf.unify(&types, &cfg(), &mut meter, v, s), Ok(false));
    }

    #[test]
    fn test_int_literal_class() {
        let mut types = Types::new();
        let mut inf = Infer::default();
        let mut meter = Meter::new(Budget::default());
        let v = inf.fresh(&mut types, INT);
        let f = TypeId::prim(Prim::F64);
        assert_eq!(inf.unify(&types, &cfg(), &mut meter, v, f), Ok(false));
        let widen = UnifyCfg {
            int_to_float: true,
            ..cfg()
        };
        assert_eq!(inf.unify(&types, &widen, &mut meter, v, f), Ok(true));
    }

    #[test]
    fn test_error_unifies_without_poisoning() {
        let mut types = Types::new();
        let mut inf = Infer::default();
        let mut meter = Meter::new(Budget::default());
        let t = types.tuple(&[TypeId::prim(Prim::I32)]);
        assert_eq!(
            inf.unify(&types, &cfg(), &mut meter, t, TypeId::ERROR),
            Ok(true)
        );
        assert_eq!(
            inf.resolve(t),
            t,
            "a shared term is never merged with {{error}}"
        );
    }

    /// ISSUES M39: unifying two `Pair(v, v)` doubling chains is linear.
    #[test]
    fn test_doubling_chain_is_linear() {
        let mut types = Types::new();
        let mut inf = Infer::default();
        let depth = 20_000;
        let (mut a, mut b) = (
            inf.fresh(&mut types, GENERAL),
            inf.fresh(&mut types, GENERAL),
        );
        let (a0, b0) = (a, b);
        for _ in 0..depth {
            a = types.tuple(&[a, a]);
            b = types.tuple(&[b, b]);
        }
        let mut meter = Meter::new(Budget::default());
        assert_eq!(inf.unify(&types, &cfg(), &mut meter, a, b), Ok(true));
        // Each level merges once and pushes two pairs, one of which is
        // already merged: a constant number of steps per level.
        assert!(meter.used <= 3 * depth + 4, "steps {}", meter.used);
        assert_eq!(inf.find(a0), inf.find(b0));
        // Binding the bottom now and zonking the top is linear too.
        assert_eq!(
            inf.unify(&types, &cfg(), &mut meter, a0, TypeId::prim(Prim::U8)),
            Ok(true)
        );
        let before = meter.used;
        let mut memo = Vec::new();
        let z = inf
            .zonk(&mut types, &mut memo, &mut meter, b)
            .unwrap_or(TypeId::ERROR);
        assert!(meter.used - before <= 4 * depth + 8);
        assert!(!types.node(z).has_var);
    }

    #[test]
    fn test_fn_types_unify_componentwise() {
        let mut types = Types::new();
        let mut inf = Infer::default();
        let mut meter = Meter::new(Budget::default());
        let v = inf.fresh(&mut types, GENERAL);
        let f1 = types.func(&[v], TypeId::UNIT, Effects::NONE);
        let f2 = types.func(&[TypeId::prim(Prim::Char)], TypeId::UNIT, Effects::NONE);
        assert_eq!(inf.unify(&types, &cfg(), &mut meter, f1, f2), Ok(true));
        assert_eq!(inf.resolve(v), TypeId::prim(Prim::Char));
        let f3 = types.func(&[TypeId::prim(Prim::Char)], TypeId::UNIT, Effects::ASYNC);
        assert_eq!(inf.unify(&types, &cfg(), &mut meter, f2, f3), Ok(false));
    }

    #[test]
    fn test_budget_stops_unification() {
        let mut types = Types::new();
        let mut inf = Infer::default();
        let v = inf.fresh(&mut types, GENERAL);
        let (mut a, mut b) = (TypeId::UNIT, v);
        for _ in 0..100 {
            a = types.slice(a);
            b = types.slice(b);
        }
        let mut meter = Meter::new(Budget {
            steps: 3,
            ..Budget::default()
        });
        let r = inf.unify(&types, &cfg(), &mut meter, a, b);
        assert_eq!(
            r,
            Err(CheckError::BudgetExceeded {
                limit: Limit::Steps
            })
        );
        assert_eq!(inf.resolve(v), v, "nothing kept after a budget stop");
    }
}
