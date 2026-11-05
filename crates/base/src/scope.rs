//! Scope sets, interned, and the changes adding or flipping scopes makes to them. Syntax keeps
//! such changes pending until it's taken apart, so a macro step doesn't copy what it's given.

use std::collections::HashMap;
use std::hash::Hash;

use ragwort_types::gc::{Charge, Mutation, OutOfMemory};

pub(crate) type Scope = u32;

/// The scope of everything read at the top level.
pub(crate) const TOP: Scope = 0;
/// The scope of what the built-in macros introduce, which nothing read can refer to.
pub(crate) const BASE: Scope = 1;

/// A set of scopes, sorted.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) struct Set(u32);

/// Changes to a set of scopes, made one after another, then folded to at most one per scope.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) struct Ops(u32);

impl Ops {
    pub(crate) const NONE: Self = Self(0);
}

impl Set {
    pub(crate) const EMPTY: Self = Self(0);
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Op {
    Add,
    Remove,
    Flip,
}

impl Op {
    /// This change after `first`, or `None` if together they change nothing.
    fn after(self, first: Option<Op>) -> Option<Op> {
        match (first, self) {
            (_, Op::Add) => Some(Op::Add),
            (_, Op::Remove) => Some(Op::Remove),
            (None, Op::Flip) => Some(Op::Flip),
            (Some(Op::Add), Op::Flip) => Some(Op::Remove),
            (Some(Op::Remove), Op::Flip) => Some(Op::Add),
            (Some(Op::Flip), Op::Flip) => None,
        }
    }
}

/// Values interned as small numbers, each with its memory charged to the arena's budget.
struct Interned<T: Eq + Hash + Clone> {
    all: Vec<Box<[T]>>,
    ids: HashMap<Box<[T]>, u32>,
}

impl<T: Eq + Hash + Clone> Interned<T> {
    fn new() -> Self {
        let empty: Box<[T]> = Box::new([]);
        Self { all: vec![empty.clone()], ids: HashMap::from([(empty, 0)]) }
    }

    fn get(&self, id: u32) -> &[T] {
        &self.all[id as usize]
    }

    fn intern(&mut self, charge: &mut Charge<'_>, items: Vec<T>) -> Result<u32, OutOfMemory> {
        if let Some(&id) = self.ids.get(items.as_slice()) {
            return Ok(id);
        }
        charge.grow(2 * size_of_val(items.as_slice()) + 64)?;
        let id = u32::try_from(self.all.len()).map_err(|_| OutOfMemory)?;
        let items = items.into_boxed_slice();
        self.all.push(items.clone());
        self.ids.insert(items, id);
        Ok(id)
    }
}

pub(crate) struct Scopes<'gc> {
    charge: Charge<'gc>,
    sets: Interned<Scope>,
    ops: Interned<(Scope, Op)>,
    applied: HashMap<(Set, Ops), Set>,
    composed: HashMap<(Ops, Ops), Ops>,
    next: Scope,
}

impl<'gc> Scopes<'gc> {
    pub(crate) fn new(mc: &Mutation<'gc>) -> Self {
        Self { charge: mc.charge(), sets: Interned::new(), ops: Interned::new(), applied: HashMap::new(), composed: HashMap::new(), next: BASE + 1 }
    }

    pub(crate) fn charge(&mut self, bytes: usize) -> Result<(), OutOfMemory> {
        self.charge.grow(bytes)
    }

    pub(crate) fn fresh(&mut self) -> Result<Scope, OutOfMemory> {
        let scope = self.next;
        self.next = self.next.checked_add(1).ok_or(OutOfMemory)?;
        Ok(scope)
    }

    pub(crate) fn set(&mut self, mut scopes: Vec<Scope>) -> Result<Set, OutOfMemory> {
        scopes.sort_unstable();
        scopes.dedup();
        self.sets.intern(&mut self.charge, scopes).map(Set)
    }

    pub(crate) fn scopes(&self, set: Set) -> &[Scope] {
        self.sets.get(set.0)
    }

    pub(crate) fn contains(&self, set: Set, scope: Scope) -> bool {
        self.scopes(set).binary_search(&scope).is_ok()
    }

    /// Whether every scope of `a` is in `b`.
    pub(crate) fn subset(&self, a: Set, b: Set) -> bool {
        let (a, b) = (self.scopes(a), self.scopes(b));
        let mut b = b.iter();
        a.len() <= b.len() && a.iter().all(|x| b.by_ref().any(|y| y == x))
    }

    pub(crate) fn op(&mut self, scope: Scope, op: Op) -> Result<Ops, OutOfMemory> {
        self.ops.intern(&mut self.charge, vec![(scope, op)]).map(Ops)
    }

    /// `first`'s changes, then `then`'s.
    pub(crate) fn compose(&mut self, first: Ops, then: Ops) -> Result<Ops, OutOfMemory> {
        if first == Ops::NONE || then == Ops::NONE {
            return Ok(if then == Ops::NONE { first } else { then });
        }
        if let Some(&ops) = self.composed.get(&(first, then)) {
            return Ok(ops);
        }
        let mut merged: Vec<(Scope, Op)> = self.ops.get(first.0).to_vec();
        for &(scope, op) in self.ops.get(then.0) {
            match merged.binary_search_by_key(&scope, |&(s, _)| s) {
                Ok(i) => match op.after(Some(merged[i].1)) {
                    Some(op) => merged[i].1 = op,
                    None => _ = merged.remove(i),
                },
                Err(i) => merged.insert(i, (scope, op)),
            }
        }
        let ops = Ops(self.ops.intern(&mut self.charge, merged)?);
        self.charge.grow(32)?;
        self.composed.insert((first, then), ops);
        Ok(ops)
    }

    /// `set` with `ops` made to it.
    pub(crate) fn apply(&mut self, set: Set, ops: Ops) -> Result<Set, OutOfMemory> {
        if ops == Ops::NONE {
            return Ok(set);
        }
        if let Some(&applied) = self.applied.get(&(set, ops)) {
            return Ok(applied);
        }
        let mut scopes = self.scopes(set).to_vec();
        for &(scope, op) in self.ops.get(ops.0) {
            match (scopes.binary_search(&scope), op) {
                (Ok(i), Op::Remove | Op::Flip) => _ = scopes.remove(i),
                (Err(i), Op::Add | Op::Flip) => scopes.insert(i, scope),
                _ => {}
            }
        }
        let applied = Set(self.sets.intern(&mut self.charge, scopes)?);
        self.charge.grow(32)?;
        self.applied.insert((set, ops), applied);
        Ok(applied)
    }
}
