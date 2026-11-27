//! Tables: maps from keys to values that keep their entries in the order they were added.
//!
//! # Keys
//!
//! Any value can be a key. These rules, modeled on Lua's, decide whether two keys are the same key:
//!
//! - Strings are compared by their characters.
//! - Numbers are compared as `eqv?` compares them: by value and by exactness. So `1` and `1.0`
//!   are two keys.
//! - Symbols, characters, booleans and the other constants are compared by their value words.
//!   Symbols are interned, so two symbols with the same name have the same word.
//! - External references are compared as their kind specifies: by the host's `equal`, or by
//!   identity if the kind has none. See [`crate::external`].
//! - Every other object is compared by identity, which is also a comparison of value words. Two
//!   pairs with the same contents are two keys.
//!
//! # Layout
//!
//! A table has two arrays. Both are allocated when the first entry is added:
//!
//! - The entries array holds a key and a value for each entry, in the order they were added. A
//!   new entry is appended after the last one. A removed entry stays in place as a tombstone.
//! - The index is a hash table of entry numbers with linear probing. Each slot also stores the
//!   high half of its key's hash, so a probe rarely reads an entry other than the matching one.
//!
//! When the entries array is full, both arrays are rebuilt. The live entries are copied in
//! order, the tombstones are dropped, and the new index is at most half full. So a table grows
//! by doubling, and shrinks if most of its entries were removed.
//!
//! # Shapes
//!
//! Many tables have the same keys in the same order: the records of one kind that a program
//! makes, or the events of one kind that a host passes in. A [`Shape`] is such a list of keys with
//! its index. A table with a shape holds only its values and takes its keys from the shape:
//!
//! - **One shape for each sequence of keys.** The shapes of an arena form a tree. The root has no
//!   keys, and [`Shape::child`] leads from a shape to the shape with one key more. So two tables
//!   that got the same keys in the same order have the same shape, however they were made. A
//!   table with a shape lists the keys of the shape. For a long string, that is a string with the
//!   same characters, and not always the object that the table was given.
//! - **Tables made with all their values.** [`Tables::shaped`] makes a table from a shape and a
//!   value for each key. The table is one object: a reference to the shape and the values. With
//!   six keys it takes about 90 bytes, where a table with keys of its own takes 250 to 400.
//! - **Tables filled field by field.** A table from [`Tables::make`] starts with the root shape.
//!   A new key that is a field name moves the table to the child shape for that key. A symbol is
//!   always a field name, and [`Table::set_field`] adds a key of any other kind as one. The
//!   values are in an array that grows, so such a table is a little larger than one made with all
//!   its values.
//! - **Leaving the shape.** A table is used as a map when [`Table::set`] adds a key that is not a
//!   symbol, such as a string or a number: it then gets keys and an index of its own. The same
//!   happens for a key that a shape cannot hold. That is a key compared by identity, a key that
//!   was removed and is set again, which has to become the last entry, and key number
//!   [`SHAPE_KEYS`] or later. Programs see no difference.
//! - **Reads by position.** A key has the same position in every table of a shape. An instruction
//!   that reads a constant key remembers the shape and the position where it found the key. In
//!   the next table of that shape it reads the value at that position without comparing a key.
//!   See [`Table::get_hinted`].
//!
//! A host can give an external table a shape as well, with [`Tables::external_shaped`]. The
//! values read from the host are then cached by position, and the first read of a key of a new
//! table costs little more than a later read. See [`ExternalTable::get_at`].
//!
//! The keys of a shape are compared by value: strings, symbols, numbers, characters, booleans and
//! external references whose kind compares by value. A key that is compared by identity cannot
//! be in a shape, because its hash changes when a collection moves it.
//!
//! # Hashes
//!
//! Hashes are seeded with the seed of the arena's symbol table. The seed is random unless the
//! program that runs the arena chose it. So an outside party cannot predict which keys collide.
//!
//! An object that is compared by identity, such as a pair, is hashed by its object word. A symbol
//! is the exception: it is hashed by its name. The object word holds the object's index in the
//! arena, so a collection that moves the object changes its hash. A table that holds such a key
//! rebuilds its index on first use after a collection that moved objects. A table with no such
//! key never needs to.

//!
//! # External tables
//!
//! A table's entries can also be owned by the host, as an [`ExternalTable`]. Examples are a
//! payload that the host has decoded, or settings that the host keeps. A program uses such a
//! table like any other. Nothing is copied into the arena until it is read.
//!
//! ```
//! use ragwort_types::Error;
//! use ragwort_types::gc::{Arena, Mutation, Value};
//! use ragwort_types::table::{ExternalTable, Key, Tables};
//!
//! /// A message as the host received it. Its fields are read in place, without copying.
//! struct Message {
//!     id: i64,
//!     pinned: bool,
//! }
//!
//! impl ExternalTable for Message {
//!     fn len(&self) -> usize {
//!         2
//!     }
//!
//!     fn has(&self, key: Key<'_>) -> bool {
//!         matches!(key, Key::Symbol("id" | "pinned"))
//!     }
//!
//!     fn get<'gc>(&self, _: &Mutation<'gc>, key: Key<'_>) -> Result<Option<Value<'gc>>, Error> {
//!         Ok(match key {
//!             Key::Symbol("id") => Value::fixnum(self.id),
//!             Key::Symbol("pinned") => Some(if self.pinned { Value::TRUE } else { Value::FALSE }),
//!             _ => None,
//!         })
//!     }
//!
//!     fn keys(&self) -> impl Iterator<Item = Key<'_>> {
//!         [Key::Symbol("id"), Key::Symbol("pinned")].into_iter()
//!     }
//! }
//!
//! let mut arena = Arena::new(1 << 20, 0);
//! arena.mutate(|mc| {
//!     let table = Tables::new(mc).external(Message { id: 7, pinned: false }, 0).unwrap();
//!     assert_eq!(table.len(mc), 2);
//!     assert!(table.is_external() && !table.is_writable(mc));
//! });
//! ```
//!
//! What the arena does with an external table:
//!
//! - It caches each value it reads. A second read of a key returns the cached value without
//!   calling the host. So a nested table that the host created for a key stays the same object.
//! - It requests all the keys from the host at once when the table is iterated, as
//!   `table-for-each` or the printer does. It caches the result until the next write to the
//!   table. A host that implements [`ExternalTable::entries`] supplies the values in the same
//!   pass.
//! - It rejects a write to a table whose type does not set [`ExternalTable::WRITABLE`].
//!
//! What the host promises. The arena relies on these promises and cannot check them:
//!
//! - `has` returns `true` for a key exactly when `get` returns a value for it, and `len` is the
//!   number of keys that `keys` yields.
//! - `keys` yields each key once, in the same order on every call while the table is unchanged.
//! - Two different keys never refer to the same entry.
//! - The value that `get` returns for a key never changes, except through the table's own
//!   `set`, `delete` and `clear`. For a type that is not writable it never changes at all.
//! - No method calls back into the table it is called on.
//! - A table made with [`Tables::external_shaped`] has no key outside its shape when it is made,
//!   and `get_at` returns for a position what `get` returns for the key at that position.
//!
//! A broken promise makes the table return wrong or stale values. It cannot cause memory
//! unsafety.
//!
//! Only strings, symbols, integers that fit in an `i64`, flonums, characters and booleans can be
//! keys of an external table, because the host cannot hold any other arena value. A lookup of
//! any other key finds nothing, and setting one fails with [`TableError::Refused`].

use std::any::Any;
use std::cell::{Ref, RefCell};
use std::collections::HashMap;
use std::hash::Hasher;

use crate::Error;
use crate::external::ExternalRef;
use crate::gc::{Gc, Mutation, OutOfMemory, Slots, Value, slot};
use crate::num::{Nums, complex, int};
use crate::objects::{self, Data, ExternTableFields, ShapeChildrenFields, TableEntriesFields, TableFields, TableIndexFields, TableRecordFields, TableShapeFields};
use crate::string::{self, Strings};
use crate::symbol::{Symbol, Symbols};

#[cfg(test)]
#[path = "tests/table.rs"]
mod tests;

/// The minimum number of index slots in a table that has allocated its arrays.
const MIN_SLOTS: usize = 8;
/// The most keys that a [`Shape`] can have. A table that would need a shape with more keys keeps its keys itself, as a table without a shape does.
pub const SHAPE_KEYS: usize = 64;
/// The number of slots in the first list of a shape's children.
const CHILDREN: usize = 2;
/// The longest list of a shape's children that is searched from start to end. A longer list has a hash index.
const CHILD_SCAN: usize = 8;
/// The least number of value slots that a table in shape mode allocates.
const SHAPED_ROOM: usize = 4;
/// The `epoch` of a table in which no key is hashed by its object word. Such a table never rebuilds its index after a collection.
const STILL: u64 = u64::MAX;
/// Mask for the low half of an index slot, which holds an entry number plus one.
const ENTRY: u64 = u32::MAX as u64;
/// Mixed into a symbol's hash, so that a symbol and the string of its name hash differently.
const SYMBOL: u64 = 0x5851_F42D_4C95_7F2D;
/// Mixed into a string's hash before it is spread over a whole word. A string keeps 32 bits of hash.
const STRING: u64 = 0xD6E8_FEB8_6659_FD93;
/// Mixed into the hash that a host returns for an external value, so that the value and a number hash differently.
const EXTERNAL: u64 = 0x1405_7B7E_F767_814F;

/// The error of a failed table operation.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TableError {
    /// The table is an external table that programs cannot modify.
    Immutable,
    /// The host rejected the key or the value, or the key is of a kind that no external table accepts. See [`Refused`].
    Refused,
    Arena(Error),
}

impl From<Error> for TableError {
    fn from(error: Error) -> Self {
        Self::Arena(error)
    }
}

impl From<OutOfMemory> for TableError {
    fn from(error: OutOfMemory) -> Self {
        Self::Arena(error.into())
    }
}

/// The reason that a list of keys cannot be a [`Shape`]. Each variant gives the position of the key at fault.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ShapeError {
    /// The key is the same key as an earlier one.
    Duplicate(usize),
    /// The key is compared by identity, so its hash changes when a collection moves it.
    Identity(usize),
    /// The key would be key number [`SHAPE_KEYS`] or later.
    TooMany(usize),
    Arena(Error),
}

impl From<Error> for ShapeError {
    fn from(error: Error) -> Self {
        Self::Arena(error)
    }
}

impl From<OutOfMemory> for ShapeError {
    fn from(error: OutOfMemory) -> Self {
        Self::Arena(error.into())
    }
}

/// The keys that a group of tables has in common, in entry order, with the hash index that those tables share. See the [module docs](self).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Shape<'gc>(Gc<'gc, objects::TableShape>);

/// Where a lookup found a key. An instruction remembers a place to read the same key again without a search. See [`Table::get_hinted`].
///
/// - **With a shape:** every table of that shape has the key at `position`, and no key has to be compared.
/// - **Without a shape:** `position` is the number of an entry of the table that was searched. The entry at that position has the key only if its key is compared and found to be the same, in that table or in another one.
///
/// A lookup returns the place together with the value. So the shape of a place is always the layout that its position belongs to. Code that remembers a place must not ask the table for a shape afterwards and pair the two: for an external table, the cached values can have a layout of their own.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Place<'gc> {
    pub shape: Option<Shape<'gc>>,
    pub position: usize,
}

impl<'gc> Shape<'gc> {
    #[inline]
    pub fn of(value: Value<'gc>) -> Option<Self> {
        match Data::of(value) {
            Some(Data::TableShape(shape)) => Some(Self(shape)),
            _ => None,
        }
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        Value::object(mc, self.0)
    }

    /// Returns the number of keys.
    #[inline]
    pub fn len(self, mc: &Mutation<'gc>) -> usize {
        self.0.count(mc) as usize
    }

    pub fn is_empty(self, mc: &Mutation<'gc>) -> bool {
        self.len(mc) == 0
    }

    /// Returns the key at `position`, or `None` if `position` is not below the number of keys.
    pub fn key(self, mc: &Mutation<'gc>, position: usize) -> Option<Value<'gc>> {
        let pairs = self.0.pairs(mc)?.items(mc);
        if position < self.len(mc) { Some(pairs.get(2 * position)) } else { None }
    }

    /// Returns the position of `key`, or `None` if the shape does not have the key. This is the entry number of `key` in every table made from the shape.
    pub fn position(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<usize>, Error> {
        self.position_hashed(mc, key, hash(mc, self.0.seed(mc), key)?.hash)
    }

    /// Works like [`Shape::position`] for a key whose hash is `hash_of_key`.
    fn position_hashed(self, mc: &Mutation<'gc>, key: Value<'gc>, hash_of_key: u64) -> Result<Option<usize>, Error> {
        let Some(parts) = self.parts(mc) else { return Ok(None) };
        // The arrays can hold the keys of shapes made from this one as well. Those keys are past `len`.
        parts.find_below(mc, key, hash_of_key, self.len(mc))
    }

    /// Returns whether the key at `position` is `key`, compared by value. Nothing is hashed.
    fn has_at(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize) -> Result<bool, Error> {
        match self.key(mc, position) {
            Some(held) => same(mc, held, key),
            None => Ok(false),
        }
    }

    /// Returns the shape with one key fewer, or `None` for the shape with no keys.
    pub fn parent(self, mc: &Mutation<'gc>) -> Option<Self> {
        self.0.parent(mc).map(Self)
    }

    /// Returns the shape with the keys of this shape and then `key`. There is one such shape in the arena, so two tables that get the same keys in the same order have the same shape.
    ///
    /// A string or a number is the same key as an equal one here, as it is in a table. The shape keeps the key that it was given first, and every table of the shape lists that key. So a table can list a string that is equal to the string it was given, and is another object. Strings and numbers cannot be changed, so the two differ in nothing else.
    ///
    /// An external reference is the same key only if it is the same object. A host can tell two equal references apart, so a table must list the reference that it was given.
    ///
    /// Fails with the position that `key` would have if the shape cannot take it. See [`ShapeError`].
    pub fn child(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Self, ShapeError> {
        let key = stored(mc, key)?;
        let hashed = hash(mc, self.0.seed(mc), key)?;
        if self.position_hashed(mc, key, hashed.hash)?.is_some() {
            return Err(ShapeError::Duplicate(self.len(mc)));
        }
        self.child_absent(mc, key, &hashed)
    }

    /// Works like [`Shape::child`] for a key that the shape is known not to have. `hashed` is the hash of `key`.
    fn child_absent(self, mc: &Mutation<'gc>, key: Value<'gc>, hashed: &Hashed) -> Result<Self, ShapeError> {
        let count = self.len(mc);
        if hashed.by_place || key == Value::BROKEN {
            return Err(ShapeError::Identity(count));
        }
        if count >= SHAPE_KEYS {
            return Err(ShapeError::TooMany(count));
        }
        if let Some(child) = self.found(mc, key, hashed.hash)? {
            return Ok(child);
        }
        let child = self.extended(mc, key, hashed.hash)?;
        self.adopt(mc, child, hashed.hash)?;
        Ok(child)
    }

    /// Returns the living shape that was made from this one by adding `key`, if there is one. `hash_of_key` is the hash of `key`.
    fn found(self, mc: &Mutation<'gc>, key: Value<'gc>, hash_of_key: u64) -> Result<Option<Self>, Error> {
        let Some(children) = self.0.children(mc).map(|children| children.items(mc)) else { return Ok(None) };
        let listed = self.0.listed(mc) as usize;
        let Some(links) = self.0.links(mc).map(|links| links.items(mc)) else {
            // A short list is searched from start to end.
            for slot in 0..listed.min(children.len()) {
                if let Some(child) = children.get(slot)
                    && stands_for(mc, child.key(mc), key)?
                {
                    return Ok(Some(Self(child)));
                }
            }
            return Ok(None);
        };
        let mask = links.len().wrapping_sub(1);
        let tag = hash_of_key >> 32;
        let mut at = hash_of_key as usize & mask;
        for _ in 0..links.len() {
            let word = links.get(at);
            if word == 0 {
                return Ok(None);
            }
            let slot = ((word & ENTRY) as usize).wrapping_sub(1);
            if word >> 32 == tag
                && slot < listed.min(children.len())
                && let Some(child) = children.get(slot)
                && stands_for(mc, child.key(mc), key)?
            {
                return Ok(Some(Self(child)));
            }
            at = (at + 1) & mask;
        }
        Ok(None)
    }

    /// Adds `child` to the list of the shapes made from this one. `hash_of_key` is the hash of the child's key.
    ///
    /// The child takes the next unused slot. A full list is replaced by one with the living children and room for as many again. So the time to add a child does not grow with the number of children, and the slots of collected children are reclaimed.
    fn adopt(self, mc: &Mutation<'gc>, child: Self, hash_of_key: u64) -> Result<(), Error> {
        let listed = self.0.listed(mc) as usize;
        let children = self.0.children(mc).map(|children| children.items(mc));
        if let Some(children) = children
            && listed < children.len()
        {
            children.set(mc, listed, Some(child.0));
            if let Some(links) = self.0.links(mc) {
                link(mc, links.items(mc), hash_of_key, listed);
            }
            self.0.set_listed(mc, listed as u64 + 1);
            return Ok(());
        }
        let mut living: usize = 0;
        if let Some(children) = children {
            for slot in 0..listed {
                if children.get(slot).is_some() {
                    living += 1;
                }
            }
        }
        let room = (living + 1).checked_mul(2).ok_or_else(|| mc.out_of_memory())?.max(CHILDREN);
        let grown = objects::ShapeChildren::new(mc, room, None)?;
        // The index is at most half full, so every probe ends at a slot that was never used.
        let links = if room > CHILD_SCAN { Some(objects::TableIndex::new(mc, room.checked_mul(2).and_then(usize::checked_next_power_of_two).ok_or_else(|| mc.out_of_memory())?, 0)?) } else { None };
        let slots = grown.items(mc);
        let seed = self.0.seed(mc);
        let mut kept = 0;
        if let Some(children) = children {
            for slot in 0..listed {
                if let Some(sibling) = children.get(slot) {
                    slots.set(mc, kept, Some(sibling));
                    if let Some(links) = links {
                        link(mc, links.items(mc), hash(mc, seed, sibling.key(mc))?.hash, kept);
                    }
                    kept += 1;
                }
            }
        }
        slots.set(mc, kept, Some(child.0));
        if let Some(links) = links {
            link(mc, links.items(mc), hash_of_key, kept);
        }
        self.0.set_children(mc, Some(grown));
        self.0.set_links(mc, links);
        self.0.set_listed(mc, kept as u64 + 1);
        Ok(())
    }

    /// Makes the shape with the keys of this shape and then `key`, which this shape does not have. `hash` is the hash of `key`.
    ///
    /// The new shape shares the arrays of this shape if their next entry is unused, or holds `key` already: a shape made here earlier and collected since put it there. Otherwise another shape made from this one took that entry for another key, and the new shape gets a copy of the arrays.
    fn extended(self, mc: &Mutation<'gc>, key: Value<'gc>, hash_of_key: u64) -> Result<Self, Error> {
        let count = self.len(mc);
        let (index, pairs) = self.arrays_with(mc, key, hash_of_key)?;
        Ok(Self(objects::TableShape::new(mc, index, pairs, self.0.seed(mc), count as u64 + 1, Some(self.0), key, None, None, 0)?))
    }

    /// Returns the index and the key array for the shape with the keys of this shape and then `key`. They are the arrays of this shape
    /// with `key` added, if this shape can share them, and new arrays otherwise. See [`Shape::extended`].
    fn arrays_with(self, mc: &Mutation<'gc>, key: Value<'gc>, hash_of_key: u64) -> Result<Arrays<'gc>, Error> {
        let count = self.len(mc);
        let seed = self.0.seed(mc);
        let next = self.parts(mc).filter(|parts| count < parts.room()).map(|parts| parts.entries.get(2 * count));
        let shared = match (self.parts(mc), next) {
            (Some(parts), Some(held)) if held == Value::BROKEN => {
                parts.entries.set(mc, 2 * count, key);
                parts.link(mc, hash_of_key, count);
                true
            }
            (Some(_), Some(held)) => stands_for(mc, held, key)?,
            _ => false,
        };
        if shared {
            return Ok((self.0.index(mc), self.0.pairs(mc)));
        }
        let fresh = arrays(mc, count + 1)?;
        if let Some(parts) = self.parts(mc) {
            for position in 0..count {
                let held = parts.entries.get(2 * position);
                fresh.parts.entries.set(mc, 2 * position, held);
                fresh.parts.link(mc, hash(mc, seed, held)?.hash, position);
            }
        }
        fresh.parts.entries.set(mc, 2 * count, key);
        fresh.parts.link(mc, hash_of_key, count);
        Ok((Some(fresh.index), Some(fresh.entries)))
    }

    fn parts(self, mc: &Mutation<'gc>) -> Option<Parts<'gc>> {
        Some(Parts { index: self.0.index(mc)?.items(mc), entries: self.0.pairs(mc)?.items(mc) })
    }
}

/// The index and the key array of a shape.
type Arrays<'gc> = (Option<Gc<'gc, objects::TableIndex>>, Option<Gc<'gc, objects::TableEntries>>);

/// A table. Its entries are stored in the arena or owned by the host. See the [module docs](self).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Table<'gc>(Kept<'gc>);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kept<'gc> {
    Inside(Inside<'gc>),
    Record(Record<'gc>),
    Outside(Outside<'gc>),
}

impl<'gc> Table<'gc> {
    #[inline]
    pub fn of(value: Value<'gc>) -> Option<Self> {
        match Data::of(value) {
            Some(Data::Table(table)) => Some(Self(Kept::Inside(Inside(table)))),
            Some(Data::TableRecord(table)) => Some(Self(Kept::Record(Record(table)))),
            Some(Data::ExternTable(table)) => Some(Self(Kept::Outside(Outside(table)))),
            _ => None,
        }
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        match self.0 {
            Kept::Inside(table) => Value::object(mc, table.0),
            Kept::Record(table) => Value::object(mc, table.0),
            Kept::Outside(table) => Value::object(mc, table.0),
        }
    }

    /// Returns whether the entries are owned by the host.
    pub fn is_external(self) -> bool {
        matches!(self.0, Kept::Outside(_))
    }

    /// Returns whether the table can be modified. Only an external table can be read-only.
    pub fn is_writable(self, mc: &Mutation<'gc>) -> bool {
        match self.0 {
            Kept::Inside(_) | Kept::Record(_) => true,
            Kept::Outside(table) => table.0.writable(mc),
        }
    }

    /// Returns the host's value behind an external table, or `None` if the table is not external or the value is not a `T`.
    pub fn host<T: ExternalTable>(self, mc: &Mutation<'gc>) -> Option<Ref<'gc, T>> {
        let Kept::Outside(table) = self.0 else { return None };
        Ref::filter_map(table.0.host(mc)?.try_borrow().ok()?, |host| host.as_any().downcast_ref::<T>()).ok()
    }

    /// Returns the number of entries.
    pub fn len(self, mc: &Mutation<'gc>) -> usize {
        match self.0 {
            Kept::Inside(table) => table.len(mc),
            Kept::Record(table) => table.len(mc),
            Kept::Outside(table) => table.len(mc),
        }
    }

    /// Returns the shape whose positions the table's entries are at, or `None` if the table has no shape. A table made from a shape loses it when a key outside the shape is added. For an external table, the entries are the cached values. See [`Table::find`].
    ///
    /// The shape tells an instruction where to find a key in the next table of the same shape. See [`Table::get_hinted`].
    #[inline]
    pub fn shape(self, mc: &Mutation<'gc>) -> Option<Shape<'gc>> {
        match self.0 {
            Kept::Inside(table) => table.0.shape(mc).map(Shape),
            Kept::Record(table) => table.shape(mc),
            Kept::Outside(table) => table.shape(mc),
        }
    }

    pub fn is_empty(self, mc: &Mutation<'gc>) -> bool {
        self.len(mc) == 0
    }

    /// Returns the value of `key`, or `None` if the table has no such key.
    #[inline]
    pub fn get(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<Value<'gc>>, Error> {
        match self.0 {
            Kept::Inside(table) => table.get(mc, key),
            Kept::Record(table) => table.get(mc, key),
            Kept::Outside(table) => table.get(mc, key),
        }
    }

    /// Returns the value of `key` if the entry at `position` is the entry of `key`. Returns `None`
    /// for any other position, whether or not the table has the key.
    ///
    /// This is the fast path back to an entry that [`Table::find`] found earlier. It serves code
    /// that reads the same key repeatedly. It computes no hash and probes nothing. It only
    /// compares the key at `position` with `key` as two value words. So it finds only keys that
    /// always have the same word when they are the same key: symbols, fixnums, characters,
    /// booleans and strings short enough to be stored inline in the value word. A position
    /// becomes stale when entries are removed and the table is next rebuilt. This method then
    /// returns `None`.
    ///
    /// For an external table, `position` is a position in the table of cached values.
    #[inline]
    pub fn get_at(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize) -> Option<Value<'gc>> {
        match self.0 {
            Kept::Inside(table) => table.get_at(mc, key, position),
            Kept::Record(table) => table.get_at(mc, key, position),
            Kept::Outside(table) => table.cached(mc)?.get_at(mc, key, position),
        }
    }

    /// Works like [`Table::get_at`] for an instruction that also remembers the shape of the table in which it found `key` at `position`. `shape` is that shape's value, or any other value if the table had none.
    ///
    /// If the table has the same shape, `key` is at `position` and no key is compared. This is the usual case for code that reads one field of many records of one kind.
    #[inline(always)]
    pub fn get_hinted(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize, shape: Value<'gc>) -> Option<Value<'gc>> {
        match self.0 {
            Kept::Inside(table) => table.get_hinted(mc, key, position, shape),
            Kept::Record(table) => table.get_hinted(mc, key, position, shape),
            Kept::Outside(table) => table.cached(mc)?.get_hinted(mc, key, position, shape),
        }
    }

    /// Works like [`Table::find`], and tries `position` first. `position` is where `key` was found before, in this table or in another one.
    ///
    /// The key at `position` is compared with `key` by value, as a search compares keys. If it is the same key, nothing is hashed. That matters for a long string key, whose hash reads every character. It is how a read with a constant string key finds its entry again in a table without a shape, where [`Table::get_at`] does not: the table can hold an equal string that is another object.
    ///
    /// For an external table with a shape, this is the cheap way to read a key for the first time. If `key` is the key at `position` of the shape, the value is read from the host and cached at that position.
    pub fn find_from(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize) -> Result<Option<(Place<'gc>, Value<'gc>)>, Error> {
        match self.0 {
            Kept::Inside(table) => table.find_from(mc, key, position),
            Kept::Record(table) => table.find_from(mc, key, position),
            Kept::Outside(table) => match table.find_at(mc, key, position)? {
                AtPosition::Found(place, value) => Ok(Some((place, value))),
                AtPosition::Absent => Ok(None),
                AtPosition::Unknown => self.find(mc, key),
            },
        }
    }

    /// Returns the place of the entry of `key` and the entry's value, or `None` if the table
    /// has no such key. The place is for [`Table::get_hinted`] and [`Table::set_hinted`], and its
    /// position for [`Table::get_at`] and [`Table::set_at`].
    ///
    /// For an external table, the place is one of the cached values.
    pub fn find(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<(Place<'gc>, Value<'gc>)>, Error> {
        match self.0 {
            Kept::Inside(table) => table.find(mc, key),
            Kept::Record(table) => table.find(mc, key),
            Kept::Outside(table) => table.find(mc, key),
        }
    }

    /// Sets the value of `key` if the entry at `position` is the entry of `key`. Returns whether
    /// the value was set. Like [`Table::get_at`], this finds an entry only at the position where
    /// it was found earlier.
    ///
    /// Always returns `false` for an external table, because the host must be told of every change.
    #[inline]
    pub fn set_at(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize, value: Value<'gc>) -> bool {
        match self.0 {
            Kept::Inside(table) => table.set_at(mc, key, position, value),
            Kept::Record(table) => table.set_at(mc, key, position, value),
            Kept::Outside(_) => false,
        }
    }

    /// Works like [`Table::set_at`] for an instruction that also remembers the shape of the table in which it found `key`. See [`Table::get_hinted`].
    #[inline(always)]
    pub fn set_hinted(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize, shape: Value<'gc>, value: Value<'gc>) -> bool {
        match self.0 {
            Kept::Inside(table) => table.set_hinted(mc, key, position, shape, value),
            Kept::Record(table) => table.set_hinted(mc, key, position, shape, value),
            Kept::Outside(_) => false,
        }
    }

    /// Returns whether the table has an entry for `key`. For an external table, this does not read the value.
    #[inline]
    pub fn has(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<bool, Error> {
        match self.0 {
            Kept::Inside(table) => Ok(table.get(mc, key)?.is_some()),
            Kept::Record(table) => Ok(table.get(mc, key)?.is_some()),
            Kept::Outside(table) => table.has(mc, key),
        }
    }

    /// Sets the value of `key`. A key that the table does not have yet is appended as the last
    /// entry.
    ///
    /// Any value is stored as it is, including [`Value::NIL`]. In a language such as Lua, setting a
    /// key to nil removes the key. Such a language must check for nil itself and call
    /// [`Table::delete`].
    ///
    /// An external table can reject the write. A table that is not writable always does. A
    /// writable table does for a key or a value that the host cannot accept.
    ///
    /// # Tables with a shape
    ///
    /// A table with a shape that does not have `key` takes it in one of two ways:
    ///
    /// - **A symbol is a field name.** The table moves to the shape with `key` added, which every
    ///   table with the same keys in the same order shares. A host that fills a table from
    ///   [`Tables::make`] with symbol keys so gets the same shape for every such table.
    /// - **Any other key is the key of a map.** The table gets keys and an index of its own, and
    ///   has no shape from then on. [`Table::set_field`] adds such a key as a field name instead.
    pub fn set(self, mc: &Mutation<'gc>, key: Value<'gc>, value: Value<'gc>) -> Result<(), TableError> {
        self.set_finding(mc, key, value).map(drop)
    }

    /// Sets the value of `key` as [`Table::set`] does. Returns the place of the entry, as
    /// [`Table::find`] does. Returns `None` for an external table.
    pub fn set_finding(self, mc: &Mutation<'gc>, key: Value<'gc>, value: Value<'gc>) -> Result<Option<Place<'gc>>, TableError> {
        let key = stored(mc, key)?;
        match self.0 {
            Kept::Inside(table) => Ok(Some(table.set(mc, key, value)?)),
            Kept::Record(table) => Ok(Some(table.set(mc, key, value)?)),
            Kept::Outside(table) => table.set(mc, key, value).map(|()| None),
        }
    }

    /// Sets the value of `key` as [`Table::set`] does, and treats `key` as a field name whatever kind of value it is. Returns the place of the entry, as [`Table::set_finding`] does.
    ///
    /// Use it for a key that is not a symbol and is still one of a fixed set of names, such as the string keys of a JSON object whose fields are known. A table with a shape then keeps a shape when it gets such a key. A program's write with a constant key goes through this method.
    ///
    /// A table with a shape lists the keys of the shape. For a string key, that is a string with the same characters, and not always the object that was passed here. See [`Shape::child`].
    ///
    /// The table gets keys of its own, as it does in [`Table::set`], if a shape cannot take the key. See [`ShapeError`].
    pub fn set_field(self, mc: &Mutation<'gc>, key: Value<'gc>, value: Value<'gc>) -> Result<Option<Place<'gc>>, TableError> {
        let key = stored(mc, key)?;
        match self.0 {
            Kept::Inside(table) => Ok(Some(table.set_field(mc, key, value)?)),
            Kept::Record(table) => Ok(Some(table.set_field(mc, key, value)?)),
            Kept::Outside(table) => table.set(mc, key, value).map(|()| None),
        }
    }

    /// Removes the entry of `key`. Returns whether the table had one.
    pub fn delete(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<bool, TableError> {
        match self.0 {
            Kept::Inside(table) => Ok(table.delete(mc, key)?),
            Kept::Record(table) => Ok(table.delete(mc, key)?),
            Kept::Outside(table) => table.delete(mc, key),
        }
    }

    pub fn clear(self, mc: &Mutation<'gc>) -> Result<(), TableError> {
        match self.0 {
            Kept::Inside(table) => {
                table.clear(mc);
                Ok(())
            }
            Kept::Record(table) => Ok(table.clear(mc)?),
            Kept::Outside(table) => table.clear(mc),
        }
    }

    /// Returns a new table with the entries of this one, in the same order. The new table is held in the arena and can be changed, whatever this table is.
    ///
    /// The copy of a table with a shape has that shape, and is as small as a table from [`Tables::shaped`]. The copy of an external table with a shape gets its keys as fields, in the host's order. See [`Table::set_field`].
    pub fn copy(self, mc: &Mutation<'gc>) -> Result<Self, Error> {
        let tables = Tables::new(mc);
        let shape = self.shape(mc);
        if let Some(shape) = shape
            && !self.is_external()
        {
            return tables.shaped(shape, (0..shape.len(mc)).map(|position| self.held(mc, 2 * position + 1).filter(|&value| value != Value::BROKEN)));
        }
        let fielded = shape.is_some();
        let copy = tables.inside(if fielded { 0 } else { self.len(mc) })?;
        if fielded {
            copy.0.set_shape(mc, Some(tables.root()?.0));
        }
        for (key, value) in self.entries(mc)? {
            if fielded {
                copy.set_field(mc, key, value)?;
            } else {
                copy.set(mc, key, value)?;
            }
        }
        Ok(Self(Kept::Inside(copy)))
    }

    /// Returns an iterator over the entries in the order they were added. For an external table,
    /// the order is the host's order.
    ///
    /// For an external table, this reads every value that the arena has not cached yet.
    pub fn entries(self, mc: &Mutation<'gc>) -> Result<Entries<'gc>, Error> {
        match self.0 {
            Kept::Inside(table) => Ok(table.entries(mc)),
            Kept::Record(table) => Ok(table.entries(mc)),
            Kept::Outside(table) => {
                let walk = table.walk(mc)?;
                Ok(Entries { entries: Some(walk), values: None, at: 0, end: walk.len() / 2 })
            }
        }
    }

    /// Returns the value in slot `index` of the entries array, or `None` if `index` is past the
    /// last slot in use. Keys and values alternate, in the order of [`Table::entries`]. Both
    /// slots of a removed entry read as [`Value::BROKEN`]. This method is for code that traverses
    /// any container by position, such as a printer. Use [`Table::entries`] to read a table.
    ///
    /// For an external table, this returns `None` for every index if the entries cannot be read,
    /// for example because allocation fails.
    pub fn held(self, mc: &Mutation<'gc>, index: usize) -> Option<Value<'gc>> {
        match self.0 {
            Kept::Inside(table) => table.held(mc, index),
            Kept::Record(table) => table.held(mc, index),
            Kept::Outside(table) => {
                let walk = table.walk(mc).ok()?;
                if index < walk.len() { Some(walk.get(index)) } else { None }
            }
        }
    }

    /// Returns whether the next read or write rebuilds the index. That happens when a collection
    /// has moved objects since the index was built. The rebuild takes time proportional to the
    /// number of entries.
    pub fn is_stale(self, mc: &Mutation<'gc>) -> bool {
        match self.0 {
            Kept::Inside(table) => table.is_stale(mc),
            Kept::Record(table) => table.own(mc).is_some_and(|own| own.is_stale(mc)),
            Kept::Outside(_) => false,
        }
    }
}

/// A table whose entries are stored in the arena.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Inside<'gc>(Gc<'gc, objects::Table>);

impl<'gc> Inside<'gc> {
    fn len(self, mc: &Mutation<'gc>) -> usize {
        self.0.live(mc) as usize
    }

    /// Returns the value at `position` of a table in shape mode, or `None` if the table does not have the key at that position. The slots past the keys of the shape are unused, so a position past them has no value either.
    #[inline(always)]
    fn value_at(self, mc: &Mutation<'gc>, position: usize) -> Option<Value<'gc>> {
        let values = self.0.pairs(mc)?.items(mc);
        if position >= values.len() {
            return None;
        }
        let value = values.get(position);
        if value == Value::BROKEN { None } else { Some(value) }
    }

    /// Finds `key` in a table in shape mode, whose shape is `shape`.
    #[inline(never)]
    fn find_shaped(self, mc: &Mutation<'gc>, shape: Shape<'gc>, key: Value<'gc>) -> Result<Option<(Place<'gc>, Value<'gc>)>, Error> {
        let Some(position) = shape.position(mc, key)? else { return Ok(None) };
        Ok(self.value_at(mc, position).map(|value| (Place { shape: Some(shape), position }, value)))
    }

    #[inline]
    fn get(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<Value<'gc>>, Error> {
        if let Some(shape) = self.0.shape(mc) {
            return Ok(self.find_shaped(mc, Shape(shape), key)?.map(|(_, value)| value));
        }
        let Some(parts) = self.settled(mc)? else { return Ok(None) };
        let hashed = hash(mc, self.0.seed(mc), key)?;
        Ok(parts.find(mc, key, hashed.hash)?.map(|entry| parts.entries.get(2 * entry + 1)))
    }

    /// Returns the value of the entry at `position` if its key is the same value word as `key`.
    /// Unused slots and the slots of removed entries hold `Value::BROKEN`, which is never a key.
    /// So the check needs only the array length, not `used`.
    #[inline]
    fn get_at(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize) -> Option<Value<'gc>> {
        match self.0.shape(mc) {
            Some(shape) => self.get_at_shaped(mc, Shape(shape), key, position),
            None => self.get_at_own(mc, key, position),
        }
    }

    /// Does the work of [`Inside::get_at`] for a table with keys of its own: the key of the entry at `position` is compared with `key`.
    #[inline(always)]
    fn get_at_own(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize) -> Option<Value<'gc>> {
        let entries = self.0.pairs(mc)?.items(mc);
        let place = position.checked_mul(2)?;
        if place < entries.len() && entries.get(place) == key { Some(entries.get(place + 1)) } else { None }
    }

    /// Does the work of [`Inside::get_at`] for a table in shape mode, whose shape is `shape`: the key at `position` of the shape is compared with `key`.
    #[inline(never)]
    fn get_at_shaped(self, mc: &Mutation<'gc>, shape: Shape<'gc>, key: Value<'gc>, position: usize) -> Option<Value<'gc>> {
        if shape.key(mc, position) == Some(key) { self.value_at(mc, position) } else { None }
    }

    /// Works like [`Inside::get_at`]. If the table is in shape mode and its shape is the object `shape`, the key at `position` is `key`, and no key is read.
    #[inline(always)]
    fn get_hinted(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize, shape: Value<'gc>) -> Option<Value<'gc>> {
        match self.0.shape(mc) {
            Some(own) if Value::object(mc, own) == shape => self.value_at(mc, position),
            Some(own) => self.get_at_shaped(mc, Shape(own), key, position),
            None => self.get_at_own(mc, key, position),
        }
    }

    #[inline]
    fn set_at(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize, value: Value<'gc>) -> bool {
        if let Some(shape) = self.0.shape(mc) {
            return Shape(shape).key(mc, position) == Some(key) && self.replace(mc, position, value);
        }
        let Some(entries) = self.0.pairs(mc).map(|pairs| pairs.items(mc)) else { return false };
        let Some(place) = position.checked_mul(2).filter(|&place| place < entries.len() && entries.get(place) == key) else { return false };
        entries.set(mc, place + 1, value);
        true
    }

    /// Works like [`Inside::set_at`] for a write that remembers the shape `shape`. If that is the table's shape, the value at `position` is replaced without a look at the key. If it is the table's shape with `key` added, the write adds the key.
    #[inline(always)]
    fn set_hinted(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize, shape: Value<'gc>, value: Value<'gc>) -> bool {
        match self.0.shape(mc) {
            Some(own) if Value::object(mc, own) == shape => self.replace(mc, position, value),
            Some(own) => self.set_extending(mc, Shape(own), key, position, shape, value),
            None => self.set_at(mc, key, position, value),
        }
    }

    /// Finishes [`Inside::set_hinted`] for a table in shape mode whose shape `own` is not the remembered shape.
    #[inline(never)]
    fn set_extending(self, mc: &Mutation<'gc>, own: Shape<'gc>, key: Value<'gc>, position: usize, shape: Value<'gc>, value: Value<'gc>) -> bool {
        // The remembered shape has `key` as its last key, at `position`. If the rest of it is this table's shape, the table lacks only that key, and gets it by moving to the remembered shape. If the values array cannot be made longer, the caller's search reports the failure.
        if let Some(hinted) = Shape::of(shape)
            && hinted.parent(mc) == Some(own)
            && position + 1 == hinted.len(mc)
            && let Ok(values) = self.room_for(mc, position + 1)
        {
            values.set(mc, position, value);
            self.0.set_shape(mc, Some(hinted.0));
            self.0.set_live(mc, self.0.live(mc) + 1);
            return true;
        }
        own.key(mc, position) == Some(key) && self.replace(mc, position, value)
    }

    /// Replaces the value at `position` of a table in shape mode, if the table has the key at that position. Returns whether it did.
    #[inline(always)]
    fn replace(self, mc: &Mutation<'gc>, position: usize, value: Value<'gc>) -> bool {
        if self.value_at(mc, position).is_none() {
            return false;
        }
        if let Some(values) = self.0.pairs(mc) {
            values.items(mc).set(mc, position, value);
        }
        true
    }

    /// Works like [`Inside::find`], and tries `position` first. See [`Table::find_from`].
    fn find_from(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize) -> Result<Option<(Place<'gc>, Value<'gc>)>, Error> {
        if let Some(shape) = self.0.shape(mc).map(Shape) {
            if shape.has_at(mc, key, position)? {
                return Ok(self.value_at(mc, position).map(|value| (Place { shape: Some(shape), position }, value)));
            }
            return self.find_shaped(mc, shape, key);
        }
        // The entry at `position` of a table with keys of its own. A removed entry has no key.
        if let Some(entries) = self.0.pairs(mc).map(|pairs| pairs.items(mc))
            && let Some(place) = position.checked_mul(2).filter(|&place| place < entries.len())
        {
            let held = entries.get(place);
            if held != Value::BROKEN && same(mc, held, key)? {
                return Ok(Some((Place { shape: None, position }, entries.get(place + 1))));
            }
        }
        self.find(mc, key)
    }

    fn find(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<(Place<'gc>, Value<'gc>)>, Error> {
        if let Some(shape) = self.0.shape(mc) {
            return self.find_shaped(mc, Shape(shape), key);
        }
        let Some(parts) = self.settled(mc)? else { return Ok(None) };
        let hashed = hash(mc, self.0.seed(mc), key)?;
        Ok(parts.find(mc, key, hashed.hash)?.map(|entry| (Place { shape: None, position: entry }, parts.entries.get(2 * entry + 1))))
    }

    /// Sets the value of `key`, and returns the place of its entry. See [`Table::set`] for what happens to a table in shape mode that does not have `key`.
    #[inline]
    fn set(self, mc: &Mutation<'gc>, key: Value<'gc>, value: Value<'gc>) -> Result<Place<'gc>, Error> {
        self.put(mc, key, value, false)
    }

    /// Sets the value of `key` as [`Inside::set`] does, and treats `key` as a field name whatever kind of value it is. See [`Table::set_field`].
    fn set_field(self, mc: &Mutation<'gc>, key: Value<'gc>, value: Value<'gc>) -> Result<Place<'gc>, Error> {
        self.put(mc, key, value, true)
    }

    /// Sets the value of `key`, and returns the place of its entry. `field` says that the caller knows `key` to be a field name. A symbol is a field name in any case.
    fn put(self, mc: &Mutation<'gc>, key: Value<'gc>, value: Value<'gc>, field: bool) -> Result<Place<'gc>, Error> {
        if let Some(shape) = self.0.shape(mc) {
            if let Some(place) = self.put_shaped(mc, Shape(shape), key, value, field)? {
                return Ok(place);
            }
            self.leave_shape(mc)?;
        }
        let hashed = hash(mc, self.0.seed(mc), key)?;
        let parts = self.settled(mc)?;
        if let Some(parts) = parts
            && let Some(entry) = parts.find(mc, key, hashed.hash)?
        {
            parts.entries.set(mc, 2 * entry + 1, value);
            return Ok(Place { shape: None, position: entry });
        }
        let live = self.0.live(mc);
        let parts = match parts {
            Some(parts) if (self.0.used(mc) as usize) < parts.room() => parts,
            _ => self.rebuild(mc, live as usize + 1)?,
        };
        let entry = self.0.used(mc) as usize;
        if entry as u64 >= ENTRY {
            return Err(mc.out_of_memory().into());
        }
        parts.entries.set(mc, 2 * entry, key);
        parts.entries.set(mc, 2 * entry + 1, value);
        parts.link(mc, hashed.hash, entry);
        self.0.set_used(mc, entry as u64 + 1);
        self.0.set_live(mc, live + 1);
        if hashed.by_place && self.0.epoch(mc) == STILL {
            self.0.set_epoch(mc, mc.moves());
        }
        Ok(Place { shape: None, position: entry })
    }

    /// Sets the value of `key` in a table in shape mode, whose shape is `shape`. Returns the place of the key, or `None` if the table has to leave shape mode to take the key. The place has the shape of the table after the write.
    ///
    /// A key that the shape lacks is added if it is a field name: the table moves to the shape with `key` added. The table has to leave shape mode for a key that is not a field name, and for a key that the shape cannot take. See [`ShapeError`]. It also has to for a key that was removed from it earlier, because that key becomes the last entry.
    fn put_shaped(self, mc: &Mutation<'gc>, shape: Shape<'gc>, key: Value<'gc>, value: Value<'gc>, field: bool) -> Result<Option<Place<'gc>>, Error> {
        // The key is hashed once, for the search of the shape and for the search of the shapes made from it.
        let hashed = hash(mc, shape.0.seed(mc), key)?;
        if let Some(position) = shape.position_hashed(mc, key, hashed.hash)? {
            return Ok(if self.replace(mc, position, value) { Some(Place { shape: Some(shape), position }) } else { None });
        }
        if !field && Symbol::of(key).is_none() {
            return Ok(None);
        }
        let child = match shape.child_absent(mc, key, &hashed) {
            Ok(child) => child,
            Err(ShapeError::Arena(error)) => return Err(error),
            Err(ShapeError::Duplicate(_) | ShapeError::Identity(_) | ShapeError::TooMany(_)) => return Ok(None),
        };
        let position = shape.len(mc);
        let values = self.room_for(mc, position + 1)?;
        values.set(mc, position, value);
        self.0.set_shape(mc, Some(child.0));
        self.0.set_live(mc, self.0.live(mc) + 1);
        Ok(Some(Place { shape: Some(child), position }))
    }

    /// Returns the values array of a table in shape mode, with at least `count` slots. A larger array is allocated if the current one is too short.
    fn room_for(self, mc: &Mutation<'gc>, count: usize) -> Result<Slots<'gc>, Error> {
        let old = self.0.pairs(mc).map(|pairs| pairs.items(mc));
        if let Some(values) = old
            && values.len() >= count
        {
            return Ok(values);
        }
        let held = old.map_or(0, |values| values.len());
        let grown = objects::TableEntries::new(mc, count.max(2 * held).max(SHAPED_ROOM), Value::BROKEN)?;
        let values = grown.items(mc);
        if let Some(old) = old {
            for position in 0..held {
                values.set(mc, position, old.get(position));
            }
        }
        self.0.set_pairs(mc, Some(grown));
        Ok(values)
    }

    /// Takes a table out of shape mode: gives it an index and an entries array of its own, with the entries it has, in order.
    #[cold]
    #[inline(never)]
    fn leave_shape(self, mc: &Mutation<'gc>) -> Result<(), Error> {
        let fresh = arrays(mc, self.0.live(mc) as usize + 1)?;
        let seed = self.0.seed(mc);
        let mut kept = 0;
        for (key, value) in self.entries(mc) {
            fresh.parts.entries.set(mc, 2 * kept, key);
            fresh.parts.entries.set(mc, 2 * kept + 1, value);
            fresh.parts.link(mc, hash(mc, seed, key)?.hash, kept);
            kept += 1;
        }
        self.0.set_shape(mc, None);
        self.0.set_index(mc, Some(fresh.index));
        self.0.set_pairs(mc, Some(fresh.entries));
        self.0.set_used(mc, kept as u64);
        Ok(())
    }

    fn delete(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<bool, Error> {
        if let Some(shape) = self.0.shape(mc) {
            // The table keeps its shape. The slot of the key is marked unused.
            let Some((place, _)) = self.find_shaped(mc, Shape(shape), key)? else { return Ok(false) };
            if let Some(values) = self.0.pairs(mc) {
                values.items(mc).set(mc, place.position, Value::BROKEN);
            }
            self.0.set_live(mc, self.0.live(mc) - 1);
            return Ok(true);
        }
        let Some(parts) = self.settled(mc)? else { return Ok(false) };
        let hashed = hash(mc, self.0.seed(mc), key)?;
        let Some(entry) = parts.find(mc, key, hashed.hash)? else { return Ok(false) };
        // The index slot is kept, so probes continue past it. The entry becomes a tombstone, which the next rebuild drops.
        parts.entries.set(mc, 2 * entry, Value::BROKEN);
        parts.entries.set(mc, 2 * entry + 1, Value::BROKEN);
        self.0.set_live(mc, self.0.live(mc) - 1);
        Ok(true)
    }

    /// Removes every entry and releases the arrays. The table is afterwards an empty table without a shape.
    fn clear(self, mc: &Mutation<'gc>) {
        self.0.set_shape(mc, None);
        self.0.set_index(mc, None);
        self.0.set_pairs(mc, None);
        self.0.set_live(mc, 0);
        self.0.set_used(mc, 0);
        self.0.set_epoch(mc, STILL);
    }

    fn entries(self, mc: &Mutation<'gc>) -> Entries<'gc> {
        if let Some(shape) = self.0.shape(mc) {
            let values = self.0.pairs(mc).map(|values| values.items(mc));
            let keys = shape.pairs(mc).map(|keys| keys.items(mc));
            let end = values.map_or(0, |values| values.len().min(Shape(shape).len(mc)));
            return Entries { entries: keys.filter(|_| end > 0), values, at: 0, end };
        }
        Entries { entries: self.0.pairs(mc).map(|entries| entries.items(mc)), values: None, at: 0, end: self.0.used(mc) as usize }
    }

    fn held(self, mc: &Mutation<'gc>, index: usize) -> Option<Value<'gc>> {
        if let Some(shape) = self.0.shape(mc) {
            let count = Shape(shape).len(mc);
            if index / 2 >= count {
                return None;
            }
            let value = self.value_at(mc, index / 2).unwrap_or(Value::BROKEN);
            // A key that the table does not have reads as a removed entry: both its slots are `Value::BROKEN`.
            if index % 2 == 1 || value == Value::BROKEN {
                return Some(value);
            }
            return Shape(shape).key(mc, index / 2);
        }
        let entries = self.0.pairs(mc)?.items(mc);
        if index < 2 * self.0.used(mc) as usize { Some(entries.get(index)) } else { None }
    }

    #[inline]
    fn is_stale(self, mc: &Mutation<'gc>) -> bool {
        let epoch = self.0.epoch(mc);
        epoch != STILL && epoch != mc.moves()
    }

    #[inline]
    fn parts(self, mc: &Mutation<'gc>) -> Option<Parts<'gc>> {
        Some(Parts { index: self.0.index(mc)?.items(mc), entries: self.0.pairs(mc)?.items(mc) })
    }

    /// Returns the arrays. Rebuilds the index first if objects have moved since it was built.
    #[inline]
    fn settled(self, mc: &Mutation<'gc>) -> Result<Option<Parts<'gc>>, Error> {
        if self.is_stale(mc) { self.reindex(mc) } else { Ok(self.parts(mc)) }
    }

    /// Rebuilds the index from the current entries, in a new array of the same size.
    #[cold]
    #[inline(never)]
    fn reindex(self, mc: &Mutation<'gc>) -> Result<Option<Parts<'gc>>, Error> {
        let now = mc.moves();
        let Some(old) = self.parts(mc) else {
            self.0.set_epoch(mc, now);
            return Ok(None);
        };
        let index = objects::TableIndex::new(mc, old.index.len(), 0)?;
        let parts = Parts { index: index.items(mc), entries: old.entries };
        let seed = self.0.seed(mc);
        for entry in 0..self.0.used(mc) as usize {
            let key = old.entries.get(2 * entry);
            if key != Value::BROKEN {
                parts.link(mc, hash(mc, seed, key)?.hash, entry);
            }
        }
        self.0.set_index(mc, Some(index));
        self.0.set_epoch(mc, now);
        Ok(Some(parts))
    }

    /// Reallocates both arrays with room for `need` entries, so that the index is at most half
    /// full. Copies the live entries over in order. The table is unchanged if this fails.
    #[inline(never)]
    fn rebuild(self, mc: &Mutation<'gc>, need: usize) -> Result<Parts<'gc>, Error> {
        let fresh = arrays(mc, need)?;
        let seed = self.0.seed(mc);
        let mut kept = 0;
        for (key, value) in self.entries(mc) {
            fresh.parts.entries.set(mc, 2 * kept, key);
            fresh.parts.entries.set(mc, 2 * kept + 1, value);
            fresh.parts.link(mc, hash(mc, seed, key)?.hash, kept);
            kept += 1;
        }
        self.0.set_index(mc, Some(fresh.index));
        self.0.set_pairs(mc, Some(fresh.entries));
        self.0.set_used(mc, kept as u64);
        if self.0.epoch(mc) != STILL {
            self.0.set_epoch(mc, mc.moves());
        }
        Ok(fresh.parts)
    }
}

/// An iterator over the live entries of a table, returned by [`Table::entries`]. Each item is a
/// key and its value.
///
/// It reads the entries that the table had when the iterator was created. Entries that are set
/// or removed during iteration may or may not appear.
#[derive(Clone, Copy)]
pub struct Entries<'gc> {
    /// The keys, each followed by a value slot.
    entries: Option<Slots<'gc>>,
    /// The values of a record, one for each key. If this is `None`, the values are in `entries`.
    values: Option<Slots<'gc>>,
    at: usize,
    end: usize,
}

impl<'gc> Iterator for Entries<'gc> {
    type Item = (Value<'gc>, Value<'gc>);

    fn next(&mut self) -> Option<Self::Item> {
        let entries = self.entries?;
        while self.at < self.end {
            let key = entries.get(2 * self.at);
            let value = match self.values {
                Some(values) => values.get(self.at),
                None => entries.get(2 * self.at + 1),
            };
            self.at += 1;
            // A removed entry has no key. A key that a record does not have has no value.
            if key != Value::BROKEN && value != Value::BROKEN {
                return Some((key, value));
            }
        }
        None
    }
}

/// A table that holds only its values and takes its keys from a shape. See the [module docs](self).
///
/// A record that has grown past its shape keeps its entries in an ordinary table. Every method then passes the call on to that table.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Record<'gc>(Gc<'gc, objects::TableRecord>);

impl<'gc> Record<'gc> {
    /// Returns the ordinary table that holds the entries, if the record has grown past its shape.
    #[inline]
    fn own(self, mc: &Mutation<'gc>) -> Option<Inside<'gc>> {
        self.0.own(mc).map(Inside)
    }

    /// Returns the value at `position`, or `None` if the record does not have the key at that position. The record must not have grown.
    #[inline(always)]
    fn value_at(self, mc: &Mutation<'gc>, position: usize) -> Option<Value<'gc>> {
        let values = self.0.items(mc);
        if position >= values.len() {
            return None;
        }
        let value = values.get(position);
        if value == Value::BROKEN { None } else { Some(value) }
    }

    /// Returns the shape that gives the positions of the record's entries, if they have one. For a record that has grown, this is the shape of the table that took its entries.
    #[inline]
    fn shape(self, mc: &Mutation<'gc>) -> Option<Shape<'gc>> {
        match self.own(mc) {
            Some(own) => own.0.shape(mc).map(Shape),
            None => self.0.shape(mc).map(Shape),
        }
    }

    /// Returns the position of `key` in the record's shape, or `None` if the shape does not have the key or the record has grown.
    fn position(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<usize>, Error> {
        match self.0.shape(mc) {
            Some(shape) => Shape(shape).position(mc, key),
            None => Ok(None),
        }
    }

    fn len(self, mc: &Mutation<'gc>) -> usize {
        match self.own(mc) {
            Some(own) => own.len(mc),
            None => self.0.live(mc) as usize,
        }
    }

    fn get(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<Value<'gc>>, Error> {
        Ok(self.find(mc, key)?.map(|(_, value)| value))
    }

    /// Works like [`Record::find`], and tries `position` first. See [`Table::find_from`].
    fn find_from(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize) -> Result<Option<(Place<'gc>, Value<'gc>)>, Error> {
        if let Some(own) = self.own(mc) {
            return own.find_from(mc, key, position);
        }
        if let Some(shape) = self.0.shape(mc).map(Shape)
            && shape.has_at(mc, key, position)?
        {
            return Ok(self.value_at(mc, position).map(|value| (Place { shape: Some(shape), position }, value)));
        }
        self.find(mc, key)
    }

    fn find(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<(Place<'gc>, Value<'gc>)>, Error> {
        if let Some(own) = self.own(mc) {
            return own.find(mc, key);
        }
        let Some(shape) = self.0.shape(mc).map(Shape) else { return Ok(None) };
        let Some(position) = shape.position(mc, key)? else { return Ok(None) };
        Ok(self.value_at(mc, position).map(|value| (Place { shape: Some(shape), position }, value)))
    }

    #[inline(never)]
    fn get_at(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize) -> Option<Value<'gc>> {
        match self.0.shape(mc) {
            Some(shape) if Shape(shape).key(mc, position) == Some(key) => self.value_at(mc, position),
            Some(_) => None,
            None => self.own(mc)?.get_at(mc, key, position),
        }
    }

    /// Works like [`Record::get_at`]. If the record's shape is the object `shape`, the key at `position` is `key`, and no key is read.
    #[inline(always)]
    fn get_hinted(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize, shape: Value<'gc>) -> Option<Value<'gc>> {
        match self.0.shape(mc) {
            Some(own) if Value::object(mc, own) == shape => self.value_at(mc, position),
            Some(_) => self.get_at(mc, key, position),
            None => self.get_hinted_grown(mc, key, position, shape),
        }
    }

    /// Does the work of [`Record::get_hinted`] for a record that has grown. It is kept out of line, so that the read of a record that has not grown stays short.
    #[inline(never)]
    fn get_hinted_grown(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize, shape: Value<'gc>) -> Option<Value<'gc>> {
        self.own(mc)?.get_hinted(mc, key, position, shape)
    }

    /// Sets the value of `key`, and returns the place of its entry. See [`Table::set`] for what happens to a record that does not have `key`.
    fn set(self, mc: &Mutation<'gc>, key: Value<'gc>, value: Value<'gc>) -> Result<Place<'gc>, Error> {
        self.put(mc, key, value, false)
    }

    /// Sets the value of `key` as [`Record::set`] does, and treats `key` as a field name whatever kind of value it is. See [`Table::set_field`].
    fn set_field(self, mc: &Mutation<'gc>, key: Value<'gc>, value: Value<'gc>) -> Result<Place<'gc>, Error> {
        self.put(mc, key, value, true)
    }

    /// Sets the value of `key`, and returns the place of its entry. `field` says that the caller knows `key` to be a field name. A symbol is a field name in any case.
    ///
    /// A record has no room for a key that its shape lacks. For a field name, its values move to a table in shape mode with the same shape, which then adds the key and keeps a shape. For any other key, and for a key that was removed earlier, its entries move to a table with keys of its own.
    fn put(self, mc: &Mutation<'gc>, key: Value<'gc>, value: Value<'gc>, field: bool) -> Result<Place<'gc>, Error> {
        if let Some(own) = self.own(mc) {
            return own.put(mc, key, value, field);
        }
        let position = self.position(mc, key)?;
        if let Some(position) = position
            && self.value_at(mc, position).is_some()
        {
            self.0.items(mc).set(mc, position, value);
            return Ok(Place { shape: self.0.shape(mc).map(Shape), position });
        }
        if position.is_none()
            && (field || Symbol::of(key).is_some())
            && let Some(shape) = self.0.shape(mc).map(Shape)
        {
            let table = Tables::new(mc).inside(0)?;
            let count = shape.len(mc);
            let values = table.room_for(mc, count + 1)?;
            let held = self.0.items(mc);
            for position in 0..count.min(held.len()) {
                values.set(mc, position, held.get(position));
            }
            table.0.set_shape(mc, Some(shape.0));
            table.0.set_live(mc, self.0.live(mc));
            self.move_to(mc, table);
            return table.put(mc, key, value, true);
        }
        self.grow(mc)?.set(mc, key, value)
    }

    #[inline(never)]
    fn set_at(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize, value: Value<'gc>) -> bool {
        match self.0.shape(mc) {
            Some(shape) if Shape(shape).key(mc, position) == Some(key) => self.replace(mc, position, value),
            Some(_) => false,
            None => self.own(mc).is_some_and(|own| own.set_at(mc, key, position, value)),
        }
    }

    #[inline(always)]
    fn set_hinted(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize, shape: Value<'gc>, value: Value<'gc>) -> bool {
        match self.0.shape(mc) {
            Some(own) if Value::object(mc, own) == shape => self.replace(mc, position, value),
            Some(_) => self.set_at(mc, key, position, value),
            None => self.set_hinted_grown(mc, key, position, shape, value),
        }
    }

    /// Does the work of [`Record::set_hinted`] for a record that has grown. See [`Record::get_hinted_grown`].
    #[inline(never)]
    fn set_hinted_grown(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize, shape: Value<'gc>, value: Value<'gc>) -> bool {
        self.own(mc).is_some_and(|own| own.set_hinted(mc, key, position, shape, value))
    }

    /// Replaces the value at `position`, if the record has the key at that position. Returns whether it did.
    #[inline(always)]
    fn replace(self, mc: &Mutation<'gc>, position: usize, value: Value<'gc>) -> bool {
        if self.value_at(mc, position).is_none() {
            return false;
        }
        self.0.items(mc).set(mc, position, value);
        true
    }

    /// Removes the entry of `key`. The record keeps its shape. If the key is set again, [`Record::set`] appends it as the last entry, as an ordinary table does.
    fn delete(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<bool, Error> {
        if let Some(own) = self.own(mc) {
            return own.delete(mc, key);
        }
        let Some(position) = self.position(mc, key)? else { return Ok(false) };
        if self.value_at(mc, position).is_none() {
            return Ok(false);
        }
        self.0.items(mc).set(mc, position, Value::BROKEN);
        self.0.set_live(mc, self.0.live(mc) - 1);
        Ok(true)
    }

    fn clear(self, mc: &Mutation<'gc>) -> Result<(), Error> {
        match self.own(mc) {
            Some(own) => own.clear(mc),
            None => self.move_to(mc, Tables::new(mc).inside(0)?),
        }
        Ok(())
    }

    fn entries(self, mc: &Mutation<'gc>) -> Entries<'gc> {
        if let Some(own) = self.own(mc) {
            return own.entries(mc);
        }
        let values = self.0.items(mc);
        let keys = self.0.shape(mc).and_then(|shape| shape.pairs(mc)).map(|pairs| pairs.items(mc));
        Entries { entries: keys, values: Some(values), at: 0, end: values.len() }
    }

    fn held(self, mc: &Mutation<'gc>, index: usize) -> Option<Value<'gc>> {
        if let Some(own) = self.own(mc) {
            return own.held(mc, index);
        }
        let values = self.0.items(mc);
        if index / 2 >= values.len() {
            return None;
        }
        let value = values.get(index / 2);
        // A key that the record does not have reads as a removed entry: both its slots are `Value::BROKEN`.
        if index % 2 == 1 || value == Value::BROKEN {
            return Some(value);
        }
        Shape(self.0.shape(mc)?).key(mc, index / 2)
    }

    /// Moves the entries to an ordinary table with room for one more, and returns that table. The record then passes every call on to it.
    #[cold]
    #[inline(never)]
    fn grow(self, mc: &Mutation<'gc>) -> Result<Inside<'gc>, Error> {
        let table = Tables::new(mc).inside(self.0.live(mc) as usize + 1)?;
        for (key, value) in self.entries(mc) {
            table.set(mc, key, value)?;
        }
        self.move_to(mc, table);
        Ok(table)
    }

    /// Makes `table` the table that holds the record's entries from now on.
    fn move_to(self, mc: &Mutation<'gc>, table: Inside<'gc>) {
        self.0.set_own(mc, Some(table.0));
        self.0.set_shape(mc, None);
        self.0.set_live(mc, 0);
        // The record's own values are not read again. Clearing them lets the collector free what only they refer to.
        let values = self.0.items(mc);
        for position in 0..values.len() {
            values.set(mc, position, Value::BROKEN);
        }
    }

    /// Returns the slot at `position`: the value, or `Value::BROKEN` if the record does not have the key. Returns `None` if the record has grown or has no such position.
    fn slot(self, mc: &Mutation<'gc>, position: usize) -> Option<Value<'gc>> {
        self.0.shape(mc)?;
        let values = self.0.items(mc);
        if position < values.len() { Some(values.get(position)) } else { None }
    }

    /// Stores `value` at `position`, whether or not the record has the key at that position yet. The record must not have grown. Unlike [`Record::set`], this does not treat a key that the record lacks as a new last entry. It is for a cache, where the order of the entries does not matter.
    fn fill(self, mc: &Mutation<'gc>, position: usize, value: Value<'gc>) {
        let values = self.0.items(mc);
        if values.get(position) == Value::BROKEN {
            self.0.set_live(mc, self.0.live(mc) + 1);
        }
        values.set(mc, position, value);
    }
}

/// The cache of the values read from an external table: an ordinary table, or a record if the external table has a shape.
#[derive(Clone, Copy)]
enum Memo<'gc> {
    Plain(Inside<'gc>),
    Fields(Record<'gc>),
}

impl<'gc> Memo<'gc> {
    fn get(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<Value<'gc>>, Error> {
        match self {
            Self::Plain(table) => table.get(mc, key),
            Self::Fields(record) => record.get(mc, key),
        }
    }

    fn find(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<(Place<'gc>, Value<'gc>)>, Error> {
        match self {
            Self::Plain(table) => table.find(mc, key),
            Self::Fields(record) => record.find(mc, key),
        }
    }

    #[inline]
    fn get_at(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize) -> Option<Value<'gc>> {
        match self {
            Self::Plain(table) => table.get_at(mc, key, position),
            Self::Fields(record) => record.get_at(mc, key, position),
        }
    }

    #[inline(always)]
    fn get_hinted(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize, shape: Value<'gc>) -> Option<Value<'gc>> {
        match self {
            // The cache of a table without a shape is made without a shape, and never gets one.
            Self::Plain(table) => table.get_at_own(mc, key, position),
            Self::Fields(record) => record.get_hinted(mc, key, position, shape),
        }
    }

    fn delete(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<bool, Error> {
        match self {
            Self::Plain(table) => table.delete(mc, key),
            Self::Fields(record) => record.delete(mc, key),
        }
    }

    /// Caches `value` as the value of `key`, and returns the place of the entry. A record caches a key of its shape at the position of the shape.
    fn cache(self, mc: &Mutation<'gc>, key: Value<'gc>, value: Value<'gc>) -> Result<Place<'gc>, Error> {
        match self {
            Self::Plain(table) => table.set(mc, key, value),
            Self::Fields(record) => {
                if let Some(position) = record.position(mc, key)? {
                    record.fill(mc, position, value);
                    return Ok(Place { shape: record.0.shape(mc).map(Shape), position });
                }
                record.set(mc, key, value)
            }
        }
    }
}

/// Table operations for one step.
#[derive(Clone, Copy)]
pub struct Tables<'a, 'gc> {
    mc: &'a Mutation<'gc>,
}

impl<'a, 'gc> Tables<'a, 'gc> {
    pub fn new(mc: &'a Mutation<'gc>) -> Self {
        Self { mc }
    }

    pub fn table(&self, value: Value<'gc>) -> Option<Table<'gc>> {
        Table::of(value)
    }

    /// Returns an empty table. It allocates its arrays when the first entry is added.
    ///
    /// The table starts with the shape that has no keys. It keeps a shape for as long as the keys it gets are field names: symbols, and keys added with [`Table::set_field`]. The first other key gives it keys and an index of its own. See [`Table::set`].
    pub fn make(&self) -> Result<Table<'gc>, Error> {
        let table = self.inside(0)?;
        table.0.set_shape(self.mc, Some(self.root()?.0));
        Ok(Table(Kept::Inside(table)))
    }

    /// Returns an empty table that can hold `entries` entries before it has to grow. With room for no entries, this is [`Tables::make`]. Otherwise the table has keys and an index of its own from the start, as suits a table that is used as a map.
    pub fn with_room(&self, entries: usize) -> Result<Table<'gc>, Error> {
        if entries == 0 {
            return self.make();
        }
        Ok(Table(Kept::Inside(self.inside(entries)?)))
    }

    /// Returns the shape with `keys`, in order. It is the shape that [`Shape::child`] reaches from the shape with no keys, one key at a time. So a second call with equal keys returns the same shape. See [`ShapeError`] for the keys that a shape cannot have.
    pub fn shape(&self, keys: &[Value<'gc>]) -> Result<Shape<'gc>, ShapeError> {
        let mut shape = self.root()?;
        for &key in keys {
            shape = shape.child(self.mc, key)?;
        }
        Ok(shape)
    }

    /// Returns the shape with no keys, the root of the arena's tree of shapes. It is made on the first call and kept with the arena's symbol table.
    pub fn root(&self) -> Result<Shape<'gc>, Error> {
        let mc = self.mc;
        let symbols = Symbols::of_arena(mc)?;
        if let Some(root) = symbols.shapes(mc) {
            return Ok(Shape(root));
        }
        let root = objects::TableShape::new(mc, None, None, symbols.seed(mc), 0, None, Value::BROKEN, None, None, 0)?;
        symbols.set_shapes(mc, root);
        Ok(Shape(root))
    }

    /// Returns a table with the keys of `shape` and a value for each key, in the order of the keys. A `None` leaves its key out of the table, as if the key had been removed. Values past the number of keys are ignored, and keys without a value are left out.
    ///
    /// The table holds only the values. It takes its keys from `shape`. See the [module docs](self).
    pub fn shaped(&self, shape: Shape<'gc>, values: impl Iterator<Item = Option<Value<'gc>>>) -> Result<Table<'gc>, Error> {
        Ok(Table(Kept::Record(self.record(shape, values)?)))
    }

    fn record(&self, shape: Shape<'gc>, values: impl Iterator<Item = Option<Value<'gc>>>) -> Result<Record<'gc>, Error> {
        let mc = self.mc;
        let count = shape.len(mc);
        let record = objects::TableRecord::new(mc, Some(shape.0), None, 0, count, Value::BROKEN)?;
        let slots = record.items(mc);
        let mut live = 0;
        for (position, value) in values.take(count).enumerate() {
            if let Some(value) = value {
                slots.set(mc, position, value);
                live += 1;
            }
        }
        record.set_live(mc, live);
        Ok(Record(record))
    }

    /// Returns an empty table without a shape, with room for `entries` entries.
    fn inside(&self, entries: usize) -> Result<Inside<'gc>, Error> {
        let mc = self.mc;
        let seed = Symbols::of_arena(mc)?.seed(mc);
        let table = objects::Table::new(mc, None, None, 0, 0, seed, STILL, None)?;
        if entries > 0 {
            let fresh = arrays(mc, entries)?;
            table.set_index(mc, Some(fresh.index));
            table.set_pairs(mc, Some(fresh.entries));
        }
        Ok(Inside(table))
    }

    /// Returns a table whose entries are owned by `host`. See the [module docs](self).
    ///
    /// `bytes` is the size of the memory that `host` owns. It is charged to the arena's budget
    /// until the table is collected and `host` is dropped.
    pub fn external<T: ExternalTable>(&self, host: T, bytes: usize) -> Result<Table<'gc>, Error> {
        let mc = self.mc;
        let host: RefCell<Box<dyn Hosted>> = RefCell::new(Box::new(host));
        let table = objects::ExternTable::new(mc, None, None, None, None, T::WRITABLE, mc.frozen_owning(host, bytes)?)?;
        Ok(Table(Kept::Outside(Outside(table))))
    }

    /// Returns a table whose entries are owned by `host` and whose keys are the keys of `shape`. It works like [`Tables::external`], and reads are cheaper:
    ///
    /// - The values read from the host are cached by position, in a table that shares the index of `shape`.
    /// - An instruction that reads a constant key finds the key at the same position in every table of the shape. Its first read of a new table needs no hash, and asks the host by position if the host implements [`ExternalTable::get_at`].
    ///
    /// The host promises that the table has no key outside `shape` when it is made. The table can have fewer keys, and a writable table can gain other keys later.
    pub fn external_shaped<T: ExternalTable>(&self, shape: Shape<'gc>, host: T, bytes: usize) -> Result<Table<'gc>, Error> {
        let mc = self.mc;
        let host: RefCell<Box<dyn Hosted>> = RefCell::new(Box::new(host));
        let table = objects::ExternTable::new(mc, None, None, None, Some(shape.0), T::WRITABLE, mc.frozen_owning(host, bytes)?)?;
        Ok(Table(Kept::Outside(Outside(table))))
    }
}

/// A key of an external table, in the form that is passed to the host.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Key<'a> {
    String(&'a str),
    Symbol(&'a str),
    /// An integer that fits in an `i64`.
    Integer(i64),
    Float(f64),
    Char(char),
    Boolean(bool),
}

/// The error that a host returns when it rejects a key or a value passed to `set`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Refused;

/// A table whose entries are owned by the host. See the [module docs](self) for what the arena
/// does with an external table and what the host promises.
///
/// A type is read-only unless it sets [`ExternalTable::WRITABLE`]. A read-only type implements
/// `len`, `has`, `get` and `keys`, and keeps the default implementations of the other methods.
pub trait ExternalTable: 'static {
    /// Whether programs can modify the table. It is read once, when the table is created.
    const WRITABLE: bool = false;

    /// Returns the number of entries.
    fn len(&self) -> usize;

    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns whether there is an entry for `key`.
    fn has(&self, key: Key<'_>) -> bool;

    /// Returns the value of `key`, allocated in the arena, or `None` if there is no such entry.
    fn get<'gc>(&self, mc: &Mutation<'gc>, key: Key<'_>) -> Result<Option<Value<'gc>>, Error>;

    /// Returns an iterator over every key. Each key is yielded once.
    fn keys(&self) -> impl Iterator<Item = Key<'_>>;

    /// Returns an iterator over every entry, as a key and its value. Each entry is yielded once,
    /// in the order of [`ExternalTable::keys`]. Each value is the value that
    /// [`ExternalTable::get`] returns for its key.
    ///
    /// Returns `None` if the host cannot iterate its entries more efficiently than by calling
    /// `keys` and then `get` for each key. That is the default, and the arena then does exactly
    /// that. A host that has each value available while it iterates its entries should implement
    /// this method. An iteration then calls the host once, instead of once more for every entry.
    fn entries<'gc>(&self, mc: &Mutation<'gc>) -> Option<impl Iterator<Item = Result<(Key<'_>, Value<'gc>), Error>>> {
        let _ = mc;
        None::<std::iter::Empty<Result<(Key<'_>, Value<'gc>), Error>>>
    }

    /// Returns the value of the key at `position` of the table's shape, or `Some(Ok(None))` if the
    /// table has no entry for that key. It is only called for a table made with
    /// [`Tables::external_shaped`], and it must agree with [`ExternalTable::get`] for the same key.
    ///
    /// Returns `None` if the host cannot look a value up by position. That is the default, and
    /// the arena then calls `get` with the key. A host that stores its fields in the order of
    /// the shape should implement this method. A read then needs no key, so nothing is hashed
    /// and no key text is copied for the host.
    fn get_at<'gc>(&self, mc: &Mutation<'gc>, position: usize) -> Option<Result<Option<Value<'gc>>, Error>> {
        let _ = (mc, position);
        None
    }

    /// Sets the value of `key`. The host must copy the data it needs out of `value` during the
    /// call. It cannot keep `value` itself.
    fn set<'gc>(&mut self, mc: &Mutation<'gc>, key: Key<'_>, value: Value<'gc>) -> Result<(), Refused> {
        let _ = (mc, key, value);
        Err(Refused)
    }

    /// Removes the entry of `key`. Returns whether there was one.
    fn delete(&mut self, key: Key<'_>) -> bool {
        let _ = key;
        false
    }

    /// Removes every entry.
    fn clear(&mut self) {}
}

/// A type-erased [`ExternalTable`], as stored in a table object.
pub(crate) trait Hosted: 'static {
    fn count(&self) -> usize;
    fn contains(&self, key: Key<'_>) -> bool;
    fn fetch<'gc>(&self, mc: &Mutation<'gc>, key: Key<'_>) -> Result<Option<Value<'gc>>, Error>;
    fn fetch_at<'gc>(&self, mc: &Mutation<'gc>, position: usize) -> Option<Result<Option<Value<'gc>>, Error>>;
    /// Appends every key to `listed`, as an arena value. If the host implements
    /// [`ExternalTable::entries`], each key is followed by its value, and this returns `true`.
    /// Otherwise this returns `false`.
    fn list<'gc>(&self, mc: &Mutation<'gc>, listed: &mut Vec<Value<'gc>>) -> Result<bool, Error>;
    fn store<'gc>(&mut self, mc: &Mutation<'gc>, key: Key<'_>, value: Value<'gc>) -> Result<(), Refused>;
    fn remove(&mut self, key: Key<'_>) -> bool;
    fn empty(&mut self);
    fn as_any(&self) -> &dyn Any;
}

impl<T: ExternalTable> Hosted for T {
    fn count(&self) -> usize {
        self.len()
    }

    fn contains(&self, key: Key<'_>) -> bool {
        self.has(key)
    }

    fn fetch<'gc>(&self, mc: &Mutation<'gc>, key: Key<'_>) -> Result<Option<Value<'gc>>, Error> {
        self.get(mc, key)
    }

    fn fetch_at<'gc>(&self, mc: &Mutation<'gc>, position: usize) -> Option<Result<Option<Value<'gc>>, Error>> {
        self.get_at(mc, position)
    }

    fn list<'gc>(&self, mc: &Mutation<'gc>, listed: &mut Vec<Value<'gc>>) -> Result<bool, Error> {
        if let Some(entries) = self.entries(mc) {
            for entry in entries {
                let (key, value) = entry?;
                listed.extend([key.value(mc)?, value]);
            }
            return Ok(true);
        }
        for key in self.keys() {
            listed.push(key.value(mc)?);
        }
        Ok(false)
    }

    fn store<'gc>(&mut self, mc: &Mutation<'gc>, key: Key<'_>, value: Value<'gc>) -> Result<(), Refused> {
        self.set(mc, key, value)
    }

    fn remove(&mut self, key: Key<'_>) -> bool {
        self.delete(key)
    }

    fn empty(&mut self) {
        self.clear();
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Key<'_> {
    /// Returns the key as an arena value.
    fn value<'gc>(self, mc: &Mutation<'gc>) -> Result<Value<'gc>, Error> {
        let strings = Strings::new(mc);
        Ok(match self {
            Key::String(text) => string::from_str(&strings, text)?.value(),
            Key::Symbol(name) => Symbols::of_arena(mc)?.intern_str(&strings, name)?.value(mc),
            Key::Integer(number) => match Value::fixnum(number) {
                Some(fixnum) => fixnum,
                None => int::from_i128(&Nums::new(mc), i128::from(number))?.value(),
            },
            Key::Float(number) => Value::flonum(mc, number)?,
            Key::Char(character) => Value::char(character),
            Key::Boolean(flag) => {
                if flag {
                    Value::TRUE
                } else {
                    Value::FALSE
                }
            }
        })
    }
}

/// The longest text, in UTF-8 bytes, that a [`Text`] holds without allocating.
const SHORT: usize = 40;

/// The text of a string or of a symbol's name, copied out of the arena as UTF-8.
///
/// Arena strings are packed, so a host cannot borrow their characters. Text of up to [`SHORT`]
/// bytes is copied into the value itself. Longer text is copied into a `String`.
struct Text {
    short: [u8; SHORT],
    len: usize,
    /// The whole text if it is longer than [`SHORT`] bytes. It is empty otherwise.
    long: String,
}

impl Text {
    fn copy<'gc>(strings: &Strings<'_, 'gc>, string: string::Str<'gc>) -> Self {
        let mut short = [0; SHORT];
        match string::copy_utf8(strings, string, &mut short) {
            Some(len) => Self { short, len, long: String::new() },
            None => Self { short, len: 0, long: string::to_string(strings, string) },
        }
    }

    fn as_str(&self) -> &str {
        if self.long.is_empty() {
            std::str::from_utf8(&self.short[..self.len]).expect("a whole string was copied in")
        } else {
            &self.long
        }
    }
}

/// An arena key in the form that a host accepts. The text of a string or of a symbol's name is
/// copied out of the arena.
enum HostKey {
    String(Text),
    Symbol(Text),
    Plain(Key<'static>),
}

impl HostKey {
    /// Converts `key` for the host. Returns `None` if `key` is of a kind that no external table accepts.
    fn of<'gc>(mc: &Mutation<'gc>, key: Value<'gc>) -> Option<Self> {
        if let Some(number) = key.as_fixnum() {
            return Some(Self::Plain(Key::Integer(number)));
        }
        let strings = Strings::new(mc);
        if let Some(symbol) = Symbol::of(key) {
            return Some(Self::Symbol(Text::copy(&strings, symbol.name(mc))));
        }
        if let Some(text) = strings.string(key) {
            return Some(Self::String(Text::copy(&strings, text)));
        }
        if let Some(character) = key.as_char() {
            return Some(Self::Plain(Key::Char(character)));
        }
        if key == Value::TRUE || key == Value::FALSE {
            return Some(Self::Plain(Key::Boolean(key == Value::TRUE)));
        }
        if key.is_flonum() {
            return key.as_flonum(mc).map(|number| Self::Plain(Key::Float(number)));
        }
        // An integer outside the fixnum range that still fits in an `i64`.
        let nums = Nums::new(mc);
        let number = int::to_i64(&nums, nums.integer(key)?)?;
        Some(Self::Plain(Key::Integer(number)))
    }

    fn key(&self) -> Key<'_> {
        match self {
            Self::String(text) => Key::String(text.as_str()),
            Self::Symbol(name) => Key::Symbol(name.as_str()),
            Self::Plain(key) => *key,
        }
    }
}

/// The result of reading a key of an external table at a position of the table's shape. See [`Outside::find_at`].
enum AtPosition<'gc> {
    /// The key has this value, which is now cached at this place.
    Found(Place<'gc>, Value<'gc>),
    /// The host has no entry for the key.
    Absent,
    /// The position does not answer the read. The table has no shape, the key is not at the position, or the host is asked by key. The key has to be found the general way.
    Unknown,
}

/// A table whose entries are owned by the host.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Outside<'gc>(Gc<'gc, objects::ExternTable>);

impl<'gc> Outside<'gc> {
    /// Returns the shape that gives the positions of the cached values, if they have one.
    ///
    /// This is the shape that the host gave the table, until the program gives the table a key outside that shape. The cache then has a layout of its own. Its positions must not be remembered together with the host's shape: a position of the cache would be read in another table of that shape, where it belongs to another key.
    #[inline]
    fn shape(self, mc: &Mutation<'gc>) -> Option<Shape<'gc>> {
        match self.0.fields(mc) {
            Some(fields) => Record(fields).shape(mc),
            None => self.0.shape(mc).map(Shape),
        }
    }

    fn len(self, mc: &Mutation<'gc>) -> usize {
        self.0.host(mc).and_then(|host| host.try_borrow().ok()).map_or(0, |host| host.count())
    }

    /// Returns the cache of the values read from the host so far, or `None` if nothing has been cached yet.
    #[inline(always)]
    fn cached(self, mc: &Mutation<'gc>) -> Option<Memo<'gc>> {
        match self.0.fields(mc) {
            Some(fields) => Some(Memo::Fields(Record(fields))),
            None => self.0.memo(mc).map(|memo| Memo::Plain(Inside(memo))),
        }
    }

    /// Returns the cache of the values read from the host so far. Creates it if it does not exist yet: a record for a table with a shape, and an ordinary table otherwise.
    fn memo(self, mc: &Mutation<'gc>) -> Result<Memo<'gc>, Error> {
        if let Some(memo) = self.cached(mc) {
            return Ok(memo);
        }
        let tables = Tables::new(mc);
        match self.0.shape(mc) {
            Some(shape) => {
                // The record starts without any of its keys. A key is added when its value is read.
                let fields = tables.record(Shape(shape), std::iter::empty())?;
                self.0.set_fields(mc, Some(fields.0));
                Ok(Memo::Fields(fields))
            }
            None => {
                let memo = tables.inside(0)?;
                self.0.set_memo(mc, Some(memo.0));
                Ok(Memo::Plain(memo))
            }
        }
    }

    /// Returns the cached value of `key`, or `None` if the value of `key` has not been read from the host.
    fn known(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<Value<'gc>>, Error> {
        match self.cached(mc) {
            Some(memo) => memo.get(mc, key),
            None => Ok(None),
        }
    }

    /// Reads `key` at `position` of the table's shape, without hashing `key`. The key at that position is compared with `key` by value. The value comes from the cache, or from the host by position.
    fn find_at(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize) -> Result<AtPosition<'gc>, Error> {
        let Some(shape) = self.0.shape(mc) else { return Ok(AtPosition::Unknown) };
        if !Shape(shape).has_at(mc, key, position)? {
            return Ok(AtPosition::Unknown);
        }
        // The cache is a record of the shape. It has a slot for the key at `position`, unless the program gave the table a key outside the shape and the record grew.
        let Memo::Fields(fields) = self.memo(mc)? else { return Ok(AtPosition::Unknown) };
        let Some(known) = fields.slot(mc, position) else { return Ok(AtPosition::Unknown) };
        // The record has not grown, so the position is a position of the record's shape.
        let place = Place { shape: fields.0.shape(mc).map(Shape), position };
        if known != Value::BROKEN {
            return Ok(AtPosition::Found(place, known));
        }
        let Some(host) = self.0.host(mc) else { return Ok(AtPosition::Unknown) };
        let Ok(host) = host.try_borrow() else { return Ok(AtPosition::Unknown) };
        let fetched = host.fetch_at(mc, position);
        drop(host);
        // A host that does not look values up by position is asked by key. The value is cached at the position either way.
        let value = match fetched {
            Some(fetched) => fetched?,
            None => self.fetch(mc, key)?,
        };
        let Some(value) = value else { return Ok(AtPosition::Absent) };
        fields.fill(mc, position, value);
        Ok(AtPosition::Found(place, value))
    }

    /// Reads the value of `key` from the host. Returns `None` if the host has no entry for `key`, or if `key` is of a kind that no external table has.
    fn fetch(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<Value<'gc>>, Error> {
        let (Some(host_key), Some(host)) = (HostKey::of(mc, key), self.0.host(mc)) else { return Ok(None) };
        let Ok(host) = host.try_borrow() else { return Ok(None) };
        host.fetch(mc, host_key.key())
    }

    /// Returns the place of `key` in the cache and the value of `key`. The value is read from the host and cached if it was not cached yet.
    fn find(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<(Place<'gc>, Value<'gc>)>, Error> {
        if let Some(memo) = self.cached(mc)
            && let Some(found) = memo.find(mc, key)?
        {
            return Ok(Some(found));
        }
        let Some(value) = self.fetch(mc, key)? else { return Ok(None) };
        Ok(Some((self.memo(mc)?.cache(mc, key, value)?, value)))
    }

    fn get(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<Value<'gc>>, Error> {
        if let Some(known) = self.known(mc, key)? {
            return Ok(Some(known));
        }
        let Some(value) = self.fetch(mc, key)? else { return Ok(None) };
        // Only present keys are cached. A missing key is requested from the host again on every read. Otherwise a program could fill the arena by reading an unbounded number of missing keys.
        self.memo(mc)?.cache(mc, key, value)?;
        Ok(Some(value))
    }

    fn has(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<bool, Error> {
        if self.known(mc, key)?.is_some() {
            return Ok(true);
        }
        let (Some(host_key), Some(host)) = (HostKey::of(mc, key), self.0.host(mc)) else { return Ok(false) };
        Ok(host.try_borrow().is_ok_and(|host| host.contains(host_key.key())))
    }

    fn set(self, mc: &Mutation<'gc>, key: Value<'gc>, value: Value<'gc>) -> Result<(), TableError> {
        if !self.0.writable(mc) {
            return Err(TableError::Immutable);
        }
        let (Some(host_key), Some(host)) = (HostKey::of(mc, key), self.0.host(mc)) else { return Err(TableError::Refused) };
        host.try_borrow_mut().map_err(|_| TableError::Refused)?.store(mc, host_key.key(), value).map_err(|Refused| TableError::Refused)?;
        self.0.set_walk(mc, None);
        // Cache the value that the program stored. A later read then returns that same value, as it does for a table in the arena.
        self.memo(mc)?.cache(mc, key, value)?;
        Ok(())
    }

    fn delete(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<bool, TableError> {
        if !self.0.writable(mc) {
            return Err(TableError::Immutable);
        }
        let (Some(host_key), Some(host)) = (HostKey::of(mc, key), self.0.host(mc)) else { return Ok(false) };
        let removed = host.try_borrow_mut().map_err(|_| TableError::Refused)?.remove(host_key.key());
        self.0.set_walk(mc, None);
        if let Some(memo) = self.cached(mc) {
            memo.delete(mc, key)?;
        }
        Ok(removed)
    }

    fn clear(self, mc: &Mutation<'gc>) -> Result<(), TableError> {
        if !self.0.writable(mc) {
            return Err(TableError::Immutable);
        }
        if let Some(host) = self.0.host(mc) {
            host.try_borrow_mut().map_err(|_| TableError::Refused)?.empty();
        }
        self.0.set_walk(mc, None);
        self.0.set_memo(mc, None);
        self.0.set_fields(mc, None);
        Ok(())
    }

    /// Returns the keys and values in the host's order, as alternating key and value slots. They
    /// are read from the host once and cached until the next write to the table.
    fn walk(self, mc: &Mutation<'gc>) -> Result<Slots<'gc>, Error> {
        if let Some(walk) = self.0.walk(mc) {
            return Ok(walk.items(mc));
        }
        let mut listed = Vec::new();
        let mut with_values = false;
        if let Some(host) = self.0.host(mc) {
            let Ok(host) = host.try_borrow() else {
                // The host is mutably borrowed by a write in progress, so it cannot be read. Return an empty walk without caching it. The next walk then reads from the host again.
                return Ok(objects::TableEntries::new(mc, 0, Value::BROKEN)?.items(mc));
            };
            with_values = host.list(mc, &mut listed)?;
        }
        let slots = if with_values { listed.len() } else { 2 * listed.len() };
        let walk = objects::TableEntries::new(mc, slots, Value::BROKEN)?;
        let items = walk.items(mc);
        let mut place = 0;
        if with_values {
            let memo = self.memo(mc)?;
            for &[key, given] in listed.as_chunks::<2>().0 {
                // A value that is already cached takes precedence over the value the host just returned, so that a nested table keeps its identity. Any other value is cached as returned.
                let value = match self.known(mc, key)? {
                    Some(known) => known,
                    None => {
                        memo.cache(mc, key, given)?;
                        given
                    }
                };
                items.set(mc, place, key);
                items.set(mc, place + 1, value);
                place += 2;
            }
        } else {
            for key in listed {
                // Skip a key that the host lists but returns no value for. The two slots reserved for it stay unused at the end of the walk.
                if let Some(value) = self.get(mc, key)? {
                    items.set(mc, place, key);
                    items.set(mc, place + 1, value);
                    place += 2;
                }
            }
        }
        self.0.set_walk(mc, Some(walk));
        Ok(items)
    }
}

/// Newly allocated arrays for a table, with the slot views of both.
struct Fresh<'gc> {
    index: Gc<'gc, objects::TableIndex>,
    entries: Gc<'gc, objects::TableEntries>,
    parts: Parts<'gc>,
}

/// Allocates empty arrays with room for `need` entries, so that the index is at most half full.
fn arrays<'gc>(mc: &Mutation<'gc>, need: usize) -> Result<Fresh<'gc>, Error> {
    let slots = need.checked_mul(2).and_then(usize::checked_next_power_of_two).ok_or_else(|| mc.out_of_memory())?.max(MIN_SLOTS);
    let index = objects::TableIndex::new(mc, slots, 0)?;
    // The entries array has room for three quarters as many entries as the index has slots. So the index always has a slot that was never used, and every probe ends there.
    let entries = objects::TableEntries::new(mc, 2 * (slots / 4 * 3), Value::BROKEN)?;
    Ok(Fresh { index, entries, parts: Parts { index: index.items(mc), entries: entries.items(mc) } })
}

/// The slot views of a table's two arrays.
#[derive(Clone, Copy)]
struct Parts<'gc> {
    index: Slots<'gc, slot::u64>,
    entries: Slots<'gc>,
}

impl<'gc> Parts<'gc> {
    /// Returns the number of entries that the arrays have room for.
    fn room(self) -> usize {
        self.entries.len() / 2
    }

    /// Returns the number of the live entry whose key is `key`, or `None` if there is none. `hash` is the hash of `key`.
    #[inline]
    fn find(self, mc: &Mutation<'gc>, key: Value<'gc>, hash: u64) -> Result<Option<usize>, Error> {
        self.find_below(mc, key, hash, self.room())
    }

    /// Works like [`Parts::find`], and looks only at the entries with a number below `limit`.
    #[inline]
    fn find_below(self, mc: &Mutation<'gc>, key: Value<'gc>, hash: u64, limit: usize) -> Result<Option<usize>, Error> {
        let mask = self.index.len().wrapping_sub(1);
        let tag = hash >> 32;
        let mut at = hash as usize & mask;
        // A corrupted index may have no unused slot. So the probe stops after one pass over the index.
        for _ in 0..self.index.len() {
            let word = self.index.get(at);
            if word == 0 {
                return Ok(None);
            }
            let entry = ((word & ENTRY) as usize).wrapping_sub(1);
            if word >> 32 == tag && entry < limit {
                let held = self.entries.get(2 * entry);
                if held != Value::BROKEN && same(mc, held, key)? {
                    return Ok(Some(entry));
                }
            }
            at = (at + 1) & mask;
        }
        Ok(None)
    }

    /// Records in the index that entry number `entry` has a key that hashes to `hash`.
    fn link(self, mc: &Mutation<'gc>, hash: u64, entry: usize) {
        link(mc, self.index, hash, entry);
    }
}

/// Gives a table that was loaded from an image the hash seed `seed`, which is the seed of the arena, and rebuilds its index with it.
/// The index was built with the seed of the arena that saved the image, and the hashes of the loaded keys are those of this arena.
pub(crate) fn reseed_table<'gc>(mc: &Mutation<'gc>, table: Gc<'gc, objects::Table>, seed: u64) -> Result<(), Error> {
    table.set_seed(mc, seed);
    let still = table.epoch(mc) == STILL;
    // A table in shape mode has no index of its own.
    if table.shape(mc).is_none() {
        Inside(table).reindex(mc)?;
    }
    // Rebuilding the index marks the table as one that hashes keys by their place. A table that has no such key stays unmarked.
    if still {
        table.set_epoch(mc, STILL);
    }
    Ok(())
}

/// Gives a table shape that was loaded from an image the hash seed `seed`, as [`reseed_table`] does for a table. A shape shares its index
/// with other shapes. `rebuilt` maps each index that has been rebuilt to its replacement, so every shape that shared an index shares the
/// new one.
///
/// `borrowed` is whether the shape's arrays belong to an image that was loaded earlier. Those arrays have the arena's seed already, and
/// [`reshare_shape`] deals with them.
pub(crate) fn reseed_shape<'gc>(mc: &Mutation<'gc>, shape: Gc<'gc, objects::TableShape>, seed: u64, borrowed: bool, rebuilt: &mut HashMap<u64, Gc<'gc, objects::TableIndex>>) -> Result<(), Error> {
    shape.set_seed(mc, seed);
    if let (Some(index), Some(pairs), false) = (shape.index(mc), shape.pairs(mc), borrowed) {
        let old = Value::object(mc, index).to_bits();
        let fresh = match rebuilt.get(&old) {
            Some(&fresh) => fresh,
            None => {
                let fresh = objects::TableIndex::new(mc, index.items(mc).len(), 0)?;
                let entries = pairs.items(mc);
                // The array holds the keys of every shape that shares it. A slot that no shape has used holds `Value::BROKEN`.
                for position in 0..entries.len() / 2 {
                    let key = entries.get(2 * position);
                    if key != Value::BROKEN {
                        link(mc, fresh.items(mc), hash(mc, seed, key)?.hash, position);
                    }
                }
                rebuilt.insert(old, fresh);
                fresh
            }
        };
        shape.set_index(mc, Some(fresh));
    }
    if let (Some(links), Some(children)) = (shape.links(mc), shape.children(mc)) {
        let fresh = objects::TableIndex::new(mc, links.items(mc).len(), 0)?;
        let slots = children.items(mc);
        for slot in 0..shape.listed(mc) as usize {
            if let Some(child) = slots.get(slot) {
                link(mc, fresh.items(mc), hash(mc, seed, child.key(mc))?.hash, slot);
            }
        }
        shape.set_links(mc, Some(fresh));
    }
    Ok(())
}

/// Gives a loaded table shape its arrays again, if they belong to an image that was loaded earlier. Such a shape shared the arrays of its
/// parent when it was made, and its key was added to them. That image was saved before, so its arrays do not hold the key in this arena.
/// The key is added here as it was when the shape was made: to the parent's arrays if they have room for it, and to new arrays otherwise.
/// Call this for the shapes with fewer keys first, so that the parent of a shape has its arrays.
pub(crate) fn reshare_shape<'gc>(mc: &Mutation<'gc>, shape: Gc<'gc, objects::TableShape>) -> Result<(), Error> {
    let Some(parent) = shape.parent(mc).map(Shape) else { return Ok(()) };
    let key = shape.key(mc);
    let (index, pairs) = parent.arrays_with(mc, key, hash(mc, parent.0.seed(mc), key)?.hash)?;
    shape.set_index(mc, index);
    shape.set_pairs(mc, pairs);
    Ok(())
}

/// Returns the number of keys of a loaded table shape, for the order in which [`reshare_shape`] is called.
pub(crate) fn shape_keys<'gc>(mc: &Mutation<'gc>, shape: Gc<'gc, objects::TableShape>) -> u64 {
    shape.count(mc)
}

/// Returns the key array of a table shape as a value, or `None` if the shape has none.
pub(crate) fn shape_array<'gc>(mc: &Mutation<'gc>, shape: Gc<'gc, objects::TableShape>) -> Option<Value<'gc>> {
    shape.pairs(mc).map(|pairs| Value::object(mc, pairs))
}

/// Makes a table shape that was loaded from an image known to its parent, if the parent does not list it. The parent of a loaded shape
/// can be a shape of an image that was loaded earlier. That shape was not saved again with its new child. Call this once the loaded
/// shapes have their seed.
pub(crate) fn rejoin_shape<'gc>(mc: &Mutation<'gc>, shape: Gc<'gc, objects::TableShape>) -> Result<(), Error> {
    let shape = Shape(shape);
    let Some(parent) = shape.parent(mc) else { return Ok(()) };
    let key = shape.0.key(mc);
    let hashed = hash(mc, parent.0.seed(mc), key)?;
    // If the arena made a shape with this key from the parent in the meantime, that shape stays the parent's child.
    if parent.found(mc, key, hashed.hash)?.is_none() {
        parent.adopt(mc, shape, hashed.hash)?;
    }
    Ok(())
}

/// Records in `index` that entry number `entry` has a key that hashes to `hash`.
fn link<'gc>(mc: &Mutation<'gc>, index: Slots<'gc, slot::u64>, hash: u64, entry: usize) {
    let mask = index.len().wrapping_sub(1);
    let mut at = hash as usize & mask;
    for _ in 0..index.len() {
        if index.get(at) == 0 {
            index.set(mc, at, hash >> 32 << 32 | (entry as u64 + 1));
            return;
        }
        at = (at + 1) & mask;
    }
}

/// A key's hash. `by_place` is whether the hash was computed from the key's object word, which changes when a collection moves the object.
struct Hashed {
    hash: u64,
    by_place: bool,
}

/// Hashes `key`. Two keys that are the same key under [`same`] have the same hash.
#[inline]
fn hash<'gc>(mc: &Mutation<'gc>, seed: u64, key: Value<'gc>) -> Result<Hashed, Error> {
    if key.is_fixnum() {
        return Ok(Hashed { hash: mix(key.to_bits() ^ seed), by_place: false });
    }
    // A symbol stores the hash of its name, which is already seeded with the arena's seed.
    if let Some(symbol) = Symbol::of(key) {
        return Ok(Hashed { hash: mix(symbol.hash(mc) ^ SYMBOL), by_place: false });
    }
    // A string keeps its hash, which is seeded with the arena's seed. That is the seed of every table of the arena.
    let strings = Strings::new(mc);
    if let Some(text) = strings.string(key) {
        return Ok(Hashed { hash: mix(u64::from(strings.hash(text)?) ^ STRING), by_place: false });
    }
    Ok(hash_other(mc, seed, key))
}

/// Hashes a key that is not a fixnum, symbol or string. A number is hashed by its value. An
/// external reference is hashed as its kind specifies. Any other key is hashed by its value word,
/// which for an object holds the object's index in the arena.
#[inline(never)]
fn hash_other<'gc>(mc: &Mutation<'gc>, seed: u64, key: Value<'gc>) -> Hashed {
    let nums = Nums::new(mc);
    if let Some(number) = nums.number(key) {
        let mut state = Mixer(seed);
        complex::hash(&nums, number, &mut state);
        return Hashed { hash: state.finish(), by_place: false };
    }
    if let Some(hash) = ExternalRef::of(key).and_then(|external| external.hash(mc)) {
        return Hashed { hash: mix(hash ^ seed ^ EXTERNAL), by_place: false };
    }
    Hashed { hash: mix(key.to_bits() ^ seed), by_place: key.object_parts().is_some() }
}

/// Returns the key that a table or a shape stores for `key`. A rope is stored as its interned string, so the string keys that are held in the arena are interned strings, and two of them are the same key exactly when they are the same value. Any other key is stored as it is.
fn stored<'gc>(mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Value<'gc>, Error> {
    let strings = Strings::new(mc);
    match strings.string(key) {
        Some(text) => Ok(strings.intern(text)?.value()),
        None => Ok(key),
    }
}

/// Returns whether `held`, a key of a shape, is the key that the tables of the shape list for `key`. See [`Shape::child`].
fn stands_for<'gc>(mc: &Mutation<'gc>, held: Value<'gc>, key: Value<'gc>) -> Result<bool, Error> {
    if held == key {
        return Ok(true);
    }
    if ExternalRef::of(key).is_some() {
        return Ok(false);
    }
    same(mc, held, key)
}

/// Returns whether `held` and `key` are the same key. See the [module docs](self).
#[inline]
fn same<'gc>(mc: &Mutation<'gc>, held: Value<'gc>, key: Value<'gc>) -> Result<bool, Error> {
    if held == key {
        return Ok(true);
    }
    // Two fixnums with different words are different numbers. A fixnum is also never the same key as a number of any other kind.
    if held.is_fixnum() || key.is_fixnum() {
        return Ok(false);
    }
    same_contents(mc, held, key)
}

/// Compares two values that have different words. Returns whether they are strings with the
/// same characters, numbers with the same value and exactness, or external references that
/// their kind reports as equal.
#[inline(never)]
fn same_contents<'gc>(mc: &Mutation<'gc>, held: Value<'gc>, key: Value<'gc>) -> Result<bool, Error> {
    let strings = Strings::new(mc);
    if let (Some(first), Some(second)) = (strings.string(held), strings.string(key)) {
        return string::equal(&strings, first, second);
    }
    let nums = Nums::new(mc);
    if let (Some(first), Some(second)) = (nums.number(held), nums.number(key)) {
        return Ok(complex::eqv(&nums, first, second));
    }
    match (ExternalRef::of(held), ExternalRef::of(key)) {
        (Some(first), Some(second)) => Ok(first.same(mc, second)),
        _ => Ok(false),
    }
}

/// Mixes `word` so that every bit of it affects both halves of the result.
#[inline]
fn mix(word: u64) -> u64 {
    let product = u128::from(word) * 0x9E37_79B9_7F4A_7C15;
    (product >> 64) as u64 ^ product as u64
}

/// A [`Hasher`] over the words that make up a number.
struct Mixer(u64);

impl Hasher for Mixer {
    fn write(&mut self, bytes: &[u8]) {
        for &byte in bytes {
            self.write_u64(u64::from(byte));
        }
    }

    fn write_u64(&mut self, word: u64) {
        self.0 = mix(self.0 ^ word);
    }

    fn finish(&self) -> u64 {
        self.0
    }
}
