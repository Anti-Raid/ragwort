//! Tables: maps from keys to values that keep their entries in the order they were added.
//!
//! # Keys
//!
//! Any value can be a key. Two keys are the same key under these rules, which are Lua's:
//!
//! - Strings are compared by their characters.
//! - Numbers are compared as `eqv?` compares them: by value and by exactness. So `1` and `1.0`
//!   are two keys.
//! - Symbols, characters, booleans and the other constants are compared by what they are.
//! - External references are compared as their kind says: by the host's `equal`, or by
//!   identity if the kind has none. See [`crate::external`].
//! - Everything else is compared by identity. Two pairs with the same contents are two keys.
//!
//! # Layout
//!
//! A table has two arrays, both made when the first entry is added:
//!
//! - The entries hold a key and a value each, in the order they were added. A new entry goes
//!   after the last one. A removed entry stays in place as a dead one.
//! - The index is a hash table of entry numbers, probed linearly. Each slot also keeps the high
//!   half of its key's hash, so most probes read no entry but the right one.
//!
//! When the entries are full, both arrays are made again. The live entries are copied in order,
//! the dead ones are dropped, and the index ends at most half full. So a table grows by
//! doubling, and shrinks if most of its entries were removed.
//!
//! # Hashes
//!
//! Hashes are seeded with the seed of the arena's symbols, which is random unless the program
//! running the arena chose it. So which keys collide cannot be planned from outside.
//!
//! A key compared by identity is hashed by where it is. A collection can move it, and its hash
//! changes with that. A table that holds such a key makes its index again on first use after a
//! collection that moved objects. A table with no such key never needs to.

//!
//! # External tables
//!
//! A table's entries can also live with the host, as an [`ExternalTable`]: a payload the host
//! has decoded, or settings it keeps. A program uses such a table like any other. Nothing is
//! copied into the arena until it is read.
//!
//! ```
//! use ragwort_types::Error;
//! use ragwort_types::gc::{Arena, Mutation, Value};
//! use ragwort_types::table::{ExternalTable, Key, Tables};
//!
//! /// A message as the host received it: its fields are read where they are.
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
//! - It keeps each value it reads. A second read of a key gives the same value without asking
//!   the host, so a nested table the host made for a key stays the same object.
//! - It asks the host for all the keys at once when the table is walked, as `table-for-each`
//!   or the printer walks it, and keeps the result until the table is next written.
//! - It refuses to write to a table whose type does not say [`ExternalTable::WRITABLE`].
//!
//! What the host promises, which the arena relies on and cannot check:
//!
//! - `has` holds for a key exactly when `get` gives a value for it, and `len` is the number of
//!   keys that `keys` yields.
//! - `keys` yields each key once, in the same order on every call while the table is unchanged.
//! - Two different keys never name the same entry.
//! - What `get` gives for a key never changes, except through the table's own `set`, `delete`
//!   and `clear`. For a type that is not writable it never changes at all.
//! - No method reaches back into the table it is called on.
//!
//! A broken promise makes the table give wrong or stale values. It cannot cause memory
//! unsafety.
//!
//! Only strings, symbols, fixnums, flonums, characters and booleans can be keys of an external
//! table, because the host cannot hold anything else of the arena's. Any other key is not in
//! the table, and cannot be set.

use std::any::Any;
use std::cell::{Ref, RefCell};
use std::hash::Hasher;

use crate::Error;
use crate::external::ExternalRef;
use crate::gc::{Gc, Mutation, OutOfMemory, Slots, Value, slot};
use crate::num::{Nums, complex, int};
use crate::objects::{self, Data, ExternTableFields, TableEntriesFields, TableFields, TableIndexFields};
use crate::string::{self, Strings};
use crate::symbol::{Symbol, Symbols};

#[cfg(test)]
#[path = "tests/table.rs"]
mod tests;

/// Fewest index slots a table that holds anything has.
const MIN_SLOTS: usize = 8;
/// The epoch of a table with no key hashed by where it is.
const STILL: u64 = u64::MAX;
/// The half of an index slot that holds an entry's number plus one.
const ENTRY: u64 = u32::MAX as u64;
/// Mixed into a symbol's hash, so that a symbol and the string of its name hash apart.
const SYMBOL: u64 = 0x5851_F42D_4C95_7F2D;
/// Mixed into the hash a host gives an external value, so that it hashes apart from a number.
const EXTERNAL: u64 = 0x1405_7B7E_F767_814F;

/// What a table operation fails with.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TableError {
    /// The table is an external one that programs cannot change.
    Immutable,
    /// The host did not take the key or the value. See [`Refused`].
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

/// A table, whose entries are in the arena or with the host. See the [module docs](self).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Table<'gc>(Kept<'gc>);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kept<'gc> {
    Inside(Inside<'gc>),
    Outside(Outside<'gc>),
}

impl<'gc> Table<'gc> {
    #[inline]
    pub fn of(value: Value<'gc>) -> Option<Self> {
        match Data::of(value) {
            Some(Data::Table(table)) => Some(Self(Kept::Inside(Inside(table)))),
            Some(Data::ExternTable(table)) => Some(Self(Kept::Outside(Outside(table)))),
            _ => None,
        }
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        match self.0 {
            Kept::Inside(table) => Value::object(mc, table.0),
            Kept::Outside(table) => Value::object(mc, table.0),
        }
    }

    /// Whether the entries are with the host.
    pub fn is_external(self) -> bool {
        matches!(self.0, Kept::Outside(_))
    }

    /// Whether the table can be changed. Only an external table can be one that cannot.
    pub fn is_writable(self, mc: &Mutation<'gc>) -> bool {
        match self.0 {
            Kept::Inside(_) => true,
            Kept::Outside(table) => table.0.writable(mc),
        }
    }

    /// The host's value behind an external table, if it is a `T`.
    pub fn host<T: ExternalTable>(self, mc: &Mutation<'gc>) -> Option<Ref<'gc, T>> {
        let Kept::Outside(table) = self.0 else { return None };
        Ref::filter_map(table.0.host(mc)?.try_borrow().ok()?, |host| host.as_any().downcast_ref::<T>()).ok()
    }

    /// The number of entries.
    pub fn len(self, mc: &Mutation<'gc>) -> usize {
        match self.0 {
            Kept::Inside(table) => table.len(mc),
            Kept::Outside(table) => table.len(mc),
        }
    }

    pub fn is_empty(self, mc: &Mutation<'gc>) -> bool {
        self.len(mc) == 0
    }

    /// The value of `key`, or `None` if the table has no such key.
    #[inline]
    pub fn get(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<Value<'gc>>, Error> {
        match self.0 {
            Kept::Inside(table) => table.get(mc, key),
            Kept::Outside(table) => table.get(mc, key),
        }
    }

    /// Whether the table has an entry for `key`. For an external table this does not read the value.
    #[inline]
    pub fn has(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<bool, Error> {
        match self.0 {
            Kept::Inside(table) => Ok(table.get(mc, key)?.is_some()),
            Kept::Outside(table) => table.has(mc, key),
        }
    }

    /// Sets the value of `key`. A key the table does not have yet becomes its last entry.
    ///
    /// Any value is stored as it is, [`Value::NIL`] included. A language in which setting a key to
    /// nil removes it, as Lua has it, makes that check itself and calls [`Table::delete`].
    ///
    /// An external table can refuse: one that is not writable always does, and a writable one
    /// does for a key or a value the host cannot take.
    pub fn set(self, mc: &Mutation<'gc>, key: Value<'gc>, value: Value<'gc>) -> Result<(), TableError> {
        match self.0 {
            Kept::Inside(table) => Ok(table.set(mc, key, value)?),
            Kept::Outside(table) => table.set(mc, key, value),
        }
    }

    /// Removes the entry of `key`. Returns whether the table had one.
    pub fn delete(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<bool, TableError> {
        match self.0 {
            Kept::Inside(table) => Ok(table.delete(mc, key)?),
            Kept::Outside(table) => table.delete(mc, key),
        }
    }

    /// Removes every entry.
    pub fn clear(self, mc: &Mutation<'gc>) -> Result<(), TableError> {
        match self.0 {
            Kept::Inside(table) => {
                table.clear(mc);
                Ok(())
            }
            Kept::Outside(table) => table.clear(mc),
        }
    }

    /// The entries, in the order they were added, or for an external table, in the host's order.
    ///
    /// For an external table this reads every value the arena has not read yet.
    pub fn entries(self, mc: &Mutation<'gc>) -> Result<Entries<'gc>, Error> {
        match self.0 {
            Kept::Inside(table) => Ok(table.entries(mc)),
            Kept::Outside(table) => {
                let walk = table.walk(mc)?;
                Ok(Entries { entries: Some(walk), at: 0, end: walk.len() / 2 })
            }
        }
    }

    /// The `index`th value the table holds, or `None` past the last. Keys and values alternate,
    /// in the order of [`Table::entries`]. Both places of a removed entry read as
    /// [`Value::BROKEN`]. This is for code that walks any container by position, as a printer
    /// does; [`Table::entries`] is the way to read a table.
    ///
    /// An external table whose entries cannot be read, for want of memory, holds nothing here.
    pub fn held(self, mc: &Mutation<'gc>, index: usize) -> Option<Value<'gc>> {
        match self.0 {
            Kept::Inside(table) => table.held(mc, index),
            Kept::Outside(table) => {
                let walk = table.walk(mc).ok()?;
                (index < walk.len()).then(|| walk.get(index))
            }
        }
    }

    /// Whether the next read or write makes the index again, because a collection has moved
    /// objects since it was made. That takes time in proportion to the number of entries.
    pub fn is_stale(self, mc: &Mutation<'gc>) -> bool {
        match self.0 {
            Kept::Inside(table) => table.is_stale(mc),
            Kept::Outside(_) => false,
        }
    }
}

/// A table whose entries are in the arena.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Inside<'gc>(Gc<'gc, objects::Table>);

impl<'gc> Inside<'gc> {
    fn len(self, mc: &Mutation<'gc>) -> usize {
        self.0.live(mc) as usize
    }

    #[inline]
    fn get(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<Value<'gc>>, Error> {
        let Some(parts) = self.settled(mc)? else { return Ok(None) };
        let hashed = hash(mc, self.0.seed(mc), key)?;
        Ok(parts.find(mc, key, hashed.hash)?.map(|entry| parts.entries.get(2 * entry + 1)))
    }

    fn set(self, mc: &Mutation<'gc>, key: Value<'gc>, value: Value<'gc>) -> Result<(), Error> {
        let hashed = hash(mc, self.0.seed(mc), key)?;
        let parts = self.settled(mc)?;
        if let Some(parts) = parts
            && let Some(entry) = parts.find(mc, key, hashed.hash)?
        {
            parts.entries.set(mc, 2 * entry + 1, value);
            return Ok(());
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
        Ok(())
    }

    fn delete(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<bool, Error> {
        let Some(parts) = self.settled(mc)? else { return Ok(false) };
        let hashed = hash(mc, self.0.seed(mc), key)?;
        let Some(entry) = parts.find(mc, key, hashed.hash)? else { return Ok(false) };
        // The index slot stays, and probes go on past it. The next rebuild drops the dead entry.
        parts.entries.set(mc, 2 * entry, Value::BROKEN);
        parts.entries.set(mc, 2 * entry + 1, Value::BROKEN);
        self.0.set_live(mc, self.0.live(mc) - 1);
        Ok(true)
    }

    /// Removes every entry, and gives up the arrays that held them.
    fn clear(self, mc: &Mutation<'gc>) {
        self.0.set_index(mc, None);
        self.0.set_pairs(mc, None);
        self.0.set_live(mc, 0);
        self.0.set_used(mc, 0);
        self.0.set_epoch(mc, STILL);
    }

    fn entries(self, mc: &Mutation<'gc>) -> Entries<'gc> {
        Entries { entries: self.0.pairs(mc).map(|entries| entries.items(mc)), at: 0, end: self.0.used(mc) as usize }
    }

    fn held(self, mc: &Mutation<'gc>, index: usize) -> Option<Value<'gc>> {
        let entries = self.0.pairs(mc)?.items(mc);
        (index < 2 * self.0.used(mc) as usize).then(|| entries.get(index))
    }

    fn is_stale(self, mc: &Mutation<'gc>) -> bool {
        let epoch = self.0.epoch(mc);
        epoch != STILL && epoch != mc.moves()
    }

    fn parts(self, mc: &Mutation<'gc>) -> Option<Parts<'gc>> {
        Some(Parts { index: self.0.index(mc)?.items(mc), entries: self.0.pairs(mc)?.items(mc) })
    }

    /// The arrays, with the index made again first if objects have moved since it was made.
    #[inline]
    fn settled(self, mc: &Mutation<'gc>) -> Result<Option<Parts<'gc>>, Error> {
        if self.is_stale(mc) { self.reindex(mc) } else { Ok(self.parts(mc)) }
    }

    /// Makes the index again from the entries as they are, in a new array of the same size.
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

    /// Makes both arrays again with room for `need` entries at half full or less, and copies the
    /// live entries over in order. The table is unchanged if this fails.
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

/// The live entries of a table, as [`Table::entries`] gives them: a key and its value each.
///
/// It reads the entries the table had when it was made. Entries that are set or removed in
/// the meantime may or may not show.
#[derive(Clone, Copy)]
pub struct Entries<'gc> {
    entries: Option<Slots<'gc>>,
    at: usize,
    end: usize,
}

impl<'gc> Iterator for Entries<'gc> {
    type Item = (Value<'gc>, Value<'gc>);

    fn next(&mut self) -> Option<Self::Item> {
        let entries = self.entries?;
        while self.at < self.end {
            let key = entries.get(2 * self.at);
            self.at += 1;
            if key != Value::BROKEN {
                return Some((key, entries.get(2 * self.at - 1)));
            }
        }
        None
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

    /// An empty table. It allocates its arrays when the first entry is added.
    pub fn make(&self) -> Result<Table<'gc>, Error> {
        self.with_room(0)
    }

    /// An empty table that can take `entries` entries before it has to grow.
    pub fn with_room(&self, entries: usize) -> Result<Table<'gc>, Error> {
        let mc = self.mc;
        let seed = Symbols::of_arena(mc)?.seed(mc);
        let table = objects::Table::new(mc, None, None, 0, 0, seed, STILL)?;
        if entries > 0 {
            let fresh = arrays(mc, entries)?;
            table.set_index(mc, Some(fresh.index));
            table.set_pairs(mc, Some(fresh.entries));
        }
        Ok(Table(Kept::Inside(Inside(table))))
    }

    /// A table whose entries are `host`'s. See the [module docs](self).
    ///
    /// `bytes` is charged to the arena's budget for what `host` owns, until the table is
    /// collected and `host` dropped.
    pub fn external<T: ExternalTable>(&self, host: T, bytes: usize) -> Result<Table<'gc>, Error> {
        let mc = self.mc;
        let host: RefCell<Box<dyn Hosted>> = RefCell::new(Box::new(host));
        let table = objects::ExternTable::new(mc, None, None, T::WRITABLE, mc.frozen_owning(host, bytes)?)?;
        Ok(Table(Kept::Outside(Outside(table))))
    }
}

/// A key of an external table, as its host sees it.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Key<'a> {
    String(&'a str),
    Symbol(&'a str),
    /// A fixnum.
    Integer(i64),
    Float(f64),
    Char(char),
    Boolean(bool),
}

/// What a host answers when it does not take a key or a value it is asked to set.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Refused;

/// A table whose entries the host holds. See the [module docs](self) for what the arena does with
/// one and what the host promises.
///
/// A type is read-only unless it sets [`ExternalTable::WRITABLE`]. A read-only type implements the
/// first four methods and leaves the rest as they are.
pub trait ExternalTable: 'static {
    /// Whether programs can change the table. It is read once, when the table is made.
    const WRITABLE: bool = false;

    /// The number of entries.
    fn len(&self) -> usize;

    /// Whether there is an entry for `key`.
    fn has(&self, key: Key<'_>) -> bool;

    /// The value of `key`, made in the arena, or `None` if there is no such entry.
    fn get<'gc>(&self, mc: &Mutation<'gc>, key: Key<'_>) -> Result<Option<Value<'gc>>, Error>;

    /// Every key, once each.
    fn keys(&self) -> impl Iterator<Item = Key<'_>>;

    /// Sets the value of `key`. The host reads what it needs out of `value` now: it cannot keep
    /// the value itself.
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

/// An [`ExternalTable`] with its type forgotten, as a table object keeps it.
pub(crate) trait Hosted: 'static {
    fn count(&self) -> usize;
    fn contains(&self, key: Key<'_>) -> bool;
    fn fetch<'gc>(&self, mc: &Mutation<'gc>, key: Key<'_>) -> Result<Option<Value<'gc>>, Error>;
    /// Appends every key, as a value of the arena, to `keys`.
    fn list<'gc>(&self, mc: &Mutation<'gc>, keys: &mut Vec<Value<'gc>>) -> Result<(), Error>;
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

    fn list<'gc>(&self, mc: &Mutation<'gc>, keys: &mut Vec<Value<'gc>>) -> Result<(), Error> {
        for key in self.keys() {
            keys.push(key.value(mc)?);
        }
        Ok(())
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
    /// The key as a value of the arena.
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

/// A key of the arena as a host can take it, with the characters of a string or a symbol's name
/// copied out, since the arena holds them in its own way.
enum HostKey {
    String(String),
    Symbol(String),
    Plain(Key<'static>),
}

impl HostKey {
    /// `key` for the host, or `None` if it is of a kind no external table has.
    fn of<'gc>(mc: &Mutation<'gc>, key: Value<'gc>) -> Option<Self> {
        if let Some(number) = key.as_fixnum() {
            return Some(Self::Plain(Key::Integer(number)));
        }
        let strings = Strings::new(mc);
        if let Some(symbol) = Symbol::of(key) {
            return Some(Self::Symbol(string::display(&strings, symbol.name(mc)).to_string()));
        }
        if let Some(text) = strings.string(key) {
            return Some(Self::String(string::display(&strings, text).to_string()));
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
        None
    }

    fn key(&self) -> Key<'_> {
        match self {
            Self::String(text) => Key::String(text),
            Self::Symbol(name) => Key::Symbol(name),
            Self::Plain(key) => *key,
        }
    }
}

/// A table whose entries are with the host.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Outside<'gc>(Gc<'gc, objects::ExternTable>);

impl<'gc> Outside<'gc> {
    fn len(self, mc: &Mutation<'gc>) -> usize {
        self.0.host(mc).and_then(|host| host.try_borrow().ok()).map_or(0, |host| host.count())
    }

    /// The values read so far, in a table that is made at the first read.
    fn memo(self, mc: &Mutation<'gc>) -> Result<Inside<'gc>, Error> {
        if let Some(memo) = self.0.memo(mc) {
            return Ok(Inside(memo));
        }
        let Kept::Inside(memo) = Tables::new(mc).make()?.0 else { unreachable!("a made table is in the arena") };
        self.0.set_memo(mc, Some(memo.0));
        Ok(memo)
    }

    fn get(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<Value<'gc>>, Error> {
        if let Some(memo) = self.0.memo(mc)
            && let Some(known) = Inside(memo).get(mc, key)?
        {
            return Ok(Some(known));
        }
        let (Some(host_key), Some(host)) = (HostKey::of(mc, key), self.0.host(mc)) else { return Ok(None) };
        let Ok(host) = host.try_borrow() else { return Ok(None) };
        let Some(value) = host.fetch(mc, host_key.key())? else { return Ok(None) };
        drop(host);
        // Only values that are there are kept. A key that is not there is asked for again, so that asking for keys without end cannot fill the arena.
        self.memo(mc)?.set(mc, key, value)?;
        Ok(Some(value))
    }

    fn has(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<bool, Error> {
        if let Some(memo) = self.0.memo(mc)
            && Inside(memo).get(mc, key)?.is_some()
        {
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
        // The value the program gave is the one it reads back, as from a table in the arena.
        Ok(self.memo(mc)?.set(mc, key, value)?)
    }

    fn delete(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<bool, TableError> {
        if !self.0.writable(mc) {
            return Err(TableError::Immutable);
        }
        let (Some(host_key), Some(host)) = (HostKey::of(mc, key), self.0.host(mc)) else { return Ok(false) };
        let removed = host.try_borrow_mut().map_err(|_| TableError::Refused)?.remove(host_key.key());
        self.0.set_walk(mc, None);
        if let Some(memo) = self.0.memo(mc) {
            Inside(memo).delete(mc, key)?;
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
        Ok(())
    }

    /// The keys and values in the host's order, a key and then its value. They are read from the
    /// host once, and kept until the table is next written.
    fn walk(self, mc: &Mutation<'gc>) -> Result<Slots<'gc>, Error> {
        if let Some(walk) = self.0.walk(mc) {
            return Ok(walk.items(mc));
        }
        let mut keys = Vec::new();
        if let Some(host) = self.0.host(mc).and_then(|host| host.try_borrow().ok()) {
            host.list(mc, &mut keys)?;
        }
        let mut pairs = Vec::with_capacity(2 * keys.len());
        for key in keys {
            // A key the host lists and then has no value for is left out.
            if let Some(value) = self.get(mc, key)? {
                pairs.extend([key, value]);
            }
        }
        let walk = objects::TableEntries::new(mc, pairs.len(), Value::BROKEN)?;
        let items = walk.items(mc);
        for (place, &value) in pairs.iter().enumerate() {
            items.set(mc, place, value);
        }
        self.0.set_walk(mc, Some(walk));
        Ok(items)
    }
}

/// New arrays for a table, and the views of them.
struct Fresh<'gc> {
    index: Gc<'gc, objects::TableIndex>,
    entries: Gc<'gc, objects::TableEntries>,
    parts: Parts<'gc>,
}

/// Empty arrays with room for `need` entries at half full or less.
fn arrays<'gc>(mc: &Mutation<'gc>, need: usize) -> Result<Fresh<'gc>, Error> {
    let slots = need.checked_mul(2).and_then(usize::checked_next_power_of_two).ok_or_else(|| mc.out_of_memory())?.max(MIN_SLOTS);
    let index = objects::TableIndex::new(mc, slots, 0)?;
    // Three quarters of the slots can be taken, so a probe always ends at a slot never used.
    let entries = objects::TableEntries::new(mc, 2 * (slots / 4 * 3), Value::BROKEN)?;
    Ok(Fresh { index, entries, parts: Parts { index: index.items(mc), entries: entries.items(mc) } })
}

/// The two arrays of a table.
#[derive(Clone, Copy)]
struct Parts<'gc> {
    index: Slots<'gc, slot::u64>,
    entries: Slots<'gc>,
}

impl<'gc> Parts<'gc> {
    /// The number of entries the arrays have room for.
    fn room(self) -> usize {
        self.entries.len() / 2
    }

    /// The number of the live entry whose key is `key`, which hashes to `hash`.
    #[inline]
    fn find(self, mc: &Mutation<'gc>, key: Value<'gc>, hash: u64) -> Result<Option<usize>, Error> {
        let mask = self.index.len().wrapping_sub(1);
        let tag = hash >> 32;
        let mut at = hash as usize & mask;
        // An index whose words were damaged may have no unused slot, so a probe stops after one lap.
        for _ in 0..self.index.len() {
            let word = self.index.get(at);
            if word == 0 {
                return Ok(None);
            }
            let entry = ((word & ENTRY) as usize).wrapping_sub(1);
            if word >> 32 == tag && entry < self.room() {
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
        let mask = self.index.len().wrapping_sub(1);
        let mut at = hash as usize & mask;
        for _ in 0..self.index.len() {
            if self.index.get(at) == 0 {
                self.index.set(mc, at, hash >> 32 << 32 | (entry as u64 + 1));
                return;
            }
            at = (at + 1) & mask;
        }
    }
}

/// A key's hash, and whether it depends on where the key is.
struct Hashed {
    hash: u64,
    by_place: bool,
}

/// Hashes `key` so that keys that are [`same`] hash the same.
#[inline]
fn hash<'gc>(mc: &Mutation<'gc>, seed: u64, key: Value<'gc>) -> Result<Hashed, Error> {
    if key.is_fixnum() {
        return Ok(Hashed { hash: mix(key.to_bits() ^ seed), by_place: false });
    }
    // A symbol keeps the hash of its name, which the arena's seed went into.
    if let Some(symbol) = Symbol::of(key) {
        return Ok(Hashed { hash: mix(symbol.hash(mc) ^ SYMBOL), by_place: false });
    }
    let strings = Strings::new(mc);
    if let Some(text) = strings.string(key) {
        return Ok(Hashed { hash: string::hash(&strings, text, seed)?, by_place: false });
    }
    Ok(hash_other(mc, seed, key))
}

/// Hashes a key that is no fixnum, symbol or string: a number by its value, an external
/// reference as its kind says, anything else by its word, which for an object says where it is.
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

/// Whether `held` and `key` are the same key. See the [module docs](self).
#[inline]
fn same<'gc>(mc: &Mutation<'gc>, held: Value<'gc>, key: Value<'gc>) -> Result<bool, Error> {
    if held == key {
        return Ok(true);
    }
    // Two fixnums of different words differ, and a fixnum is no other kind of number's equal.
    if held.is_fixnum() || key.is_fixnum() {
        return Ok(false);
    }
    same_contents(mc, held, key)
}

/// Whether two values of different words are strings of the same characters, numbers of the
/// same value and exactness, or external references their kind says are equal.
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

/// Mixes a word so that every bit of it reaches both halves of the result.
#[inline]
fn mix(word: u64) -> u64 {
    let product = u128::from(word) * 0x9E37_79B9_7F4A_7C15;
    (product >> 64) as u64 ^ product as u64
}

/// A hasher of the words that make up a number.
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
