//! Scope sets, interned, and the changes adding or flipping scopes makes to them. Syntax keeps
//! such changes pending until it's taken apart, so a macro step doesn't copy what it's given.

use std::collections::HashMap;
use std::hash::{BuildHasher, Hash, Hasher, RandomState};

use ragwort_types::gc::{Charge, Mutation, OutOfMemory};

pub(crate) type Scope = u32;

/// The scope of everything read at the top level.
pub(crate) const TOP: Scope = 0;
/// The scope of what the built-in macros introduce, which nothing read can refer to.
pub(crate) const BASE: Scope = 1;
/// The scope of the forms only the expander writes. No syntax a program is given has it, so no
/// program can name one of them.
pub(crate) const INTERNAL: Scope = 2;

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

/// The expander's tables, keyed by numbers it hands out itself: scopes, interned sets of them,
/// and symbols' words.
pub(crate) type Map<K, V> = HashMap<K, V, Seeded>;

/// Hashes by a folded multiply, which spreads every bit of a word over all of them and is far
/// cheaper than std's default on the long scope sets of deeply nested code. The seed is picked
/// per table, so the code being expanded can't line its keys up to collide.
#[derive(Clone, Copy)]
pub(crate) struct Seeded(u64);

impl Default for Seeded {
    fn default() -> Self {
        Seeded(RandomState::new().hash_one(0_u64))
    }
}

impl BuildHasher for Seeded {
    type Hasher = Folded;

    fn build_hasher(&self) -> Folded {
        Folded(self.0)
    }
}

pub(crate) struct Folded(u64);

impl Hasher for Folded {
    fn write(&mut self, bytes: &[u8]) {
        let (words, rest) = bytes.as_chunks::<8>();
        for &word in words {
            self.write_u64(u64::from_le_bytes(word));
        }
        if !rest.is_empty() {
            let mut last = [0; 8];
            last[..rest.len()].copy_from_slice(rest);
            self.write_u64(u64::from_le_bytes(last));
        }
    }

    fn write_u8(&mut self, value: u8) {
        self.write_u64(u64::from(value));
    }

    fn write_u32(&mut self, value: u32) {
        self.write_u64(u64::from(value));
    }

    fn write_usize(&mut self, value: usize) {
        self.write_u64(value as u64);
    }

    fn write_u64(&mut self, value: u64) {
        let product = u128::from(self.0 ^ value) * 0x9E37_79B9_7F4A_7C15;
        self.0 = (product >> 64) as u64 ^ product as u64;
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

/// Values interned as small numbers, each with its memory charged to the arena's budget. They're
/// found by their hash, so each is stored and hashed once, and growing the table moves only
/// numbers.
struct Interned<T: Eq + Hash + Clone> {
    all: Vec<Box<[T]>>,
    /// The last value interned with each hash; `same[id]` is the one before it with that hash.
    by_hash: Map<u64, u32>,
    same: Vec<u32>,
    hasher: Seeded,
}

const NO_MORE: u32 = u32::MAX;

impl<T: Eq + Hash + Clone> Interned<T> {
    fn new() -> Self {
        let mut interned = Self { all: Vec::new(), by_hash: Map::default(), same: Vec::new(), hasher: Seeded::default() };
        let hash = interned.hasher.hash_one(&[] as &[T]);
        interned.all.push(Box::new([]));
        interned.same.push(NO_MORE);
        interned.by_hash.insert(hash, 0);
        interned
    }

    fn get(&self, id: u32) -> &[T] {
        &self.all[id as usize]
    }

    /// The number of `items`, which are copied only if they're new.
    fn intern(&mut self, charge: &mut Charge<'_>, items: &[T]) -> Result<u32, OutOfMemory> {
        let hash = self.hasher.hash_one(items);
        let first = self.by_hash.get(&hash).copied().unwrap_or(NO_MORE);
        let mut id = first;
        while id != NO_MORE {
            if *self.all[id as usize] == *items {
                return Ok(id);
            }
            id = self.same[id as usize];
        }
        charge.grow(size_of_val(items) + 48)?;
        let id = u32::try_from(self.all.len()).ok().filter(|&id| id != NO_MORE).ok_or(OutOfMemory)?;
        self.all.push(items.into());
        self.same.push(first);
        self.by_hash.insert(hash, id);
        Ok(id)
    }
}

pub(crate) struct Scopes<'gc> {
    charge: Charge<'gc>,
    sets: Interned<Scope>,
    ops: Interned<(Scope, Op)>,
    applied: Map<(Set, Ops), Set>,
    composed: Map<(Ops, Ops), Ops>,
    next: Scope,
    /// What a set or changes being worked out is made in, kept from one to the next.
    scratch_set: Vec<Scope>,
    scratch_ops: Vec<(Scope, Op)>,
}

impl<'gc> Scopes<'gc> {
    pub(crate) fn new(mc: &Mutation<'gc>) -> Self {
        Self { charge: mc.charge(), sets: Interned::new(), ops: Interned::new(), applied: Map::default(), composed: Map::default(), next: INTERNAL + 1, scratch_set: Vec::new(), scratch_ops: Vec::new() }
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
        self.sets.intern(&mut self.charge, &scopes).map(Set)
    }

    pub(crate) fn scopes(&self, set: Set) -> &[Scope] {
        self.sets.get(set.0)
    }

    pub(crate) fn contains(&self, set: Set, scope: Scope) -> bool {
        self.scopes(set).binary_search(&scope).is_ok()
    }

    /// Whether every scope of `part` is in `whole`.
    pub(crate) fn subset(&self, part: Set, whole: Set) -> bool {
        let (part, whole) = (self.scopes(part), self.scopes(whole));
        let mut whole = whole.iter();
        part.len() <= whole.len() && part.iter().all(|scope| whole.by_ref().any(|other| other == scope))
    }

    pub(crate) fn op(&mut self, scope: Scope, op: Op) -> Result<Ops, OutOfMemory> {
        self.ops.intern(&mut self.charge, &[(scope, op)]).map(Ops)
    }

    /// `first`'s changes, then `then`'s.
    pub(crate) fn compose(&mut self, first: Ops, then: Ops) -> Result<Ops, OutOfMemory> {
        if first == Ops::NONE || then == Ops::NONE {
            return Ok(if then == Ops::NONE { first } else { then });
        }
        if let Some(&ops) = self.composed.get(&(first, then)) {
            return Ok(ops);
        }
        let (left, right) = (self.ops.get(first.0), self.ops.get(then.0));
        let mut merged = std::mem::take(&mut self.scratch_ops);
        merged.clear();
        let (mut i, mut j) = (0, 0);
        while i < left.len() && j < right.len() {
            let ((left_scope, earlier), (right_scope, later)) = (left[i], right[j]);
            if left_scope < right_scope {
                merged.push(left[i]);
                i += 1;
            } else if right_scope < left_scope {
                merged.push(right[j]);
                j += 1;
            } else {
                merged.extend(later.after(Some(earlier)).map(|op| (left_scope, op)));
                (i, j) = (i + 1, j + 1);
            }
        }
        merged.extend_from_slice(&left[i..]);
        merged.extend_from_slice(&right[j..]);
        let ops = self.ops.intern(&mut self.charge, &merged).map(Ops);
        self.scratch_ops = merged;
        let ops = ops?;
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
        let (have, changes) = (self.sets.get(set.0), self.ops.get(ops.0));
        let mut scopes = std::mem::take(&mut self.scratch_set);
        scopes.clear();
        let (mut i, mut j) = (0, 0);
        // A scope the set has stays unless removed or flipped; one it lacks comes in if added or
        // flipped.
        while i < have.len() && j < changes.len() {
            let (scope, (changed, op)) = (have[i], changes[j]);
            if scope < changed {
                scopes.push(scope);
                i += 1;
            } else if changed < scope {
                if op != Op::Remove {
                    scopes.push(changed);
                }
                j += 1;
            } else {
                if op == Op::Add {
                    scopes.push(scope);
                }
                (i, j) = (i + 1, j + 1);
            }
        }
        scopes.extend_from_slice(&have[i..]);
        scopes.extend(changes[j..].iter().filter(|&&(_, op)| op != Op::Remove).map(|&(changed, _)| changed));
        let applied = self.sets.intern(&mut self.charge, &scopes).map(Set);
        self.scratch_set = scopes;
        let applied = applied?;
        self.charge.grow(32)?;
        self.applied.insert((set, ops), applied);
        Ok(applied)
    }
}
