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

use std::hash::Hasher;

use crate::Error;
use crate::external::ExternalRef;
use crate::gc::{Gc, Mutation, Slots, Value, slot};
use crate::num::{Nums, complex};
use crate::objects::{self, Data, TableEntriesFields, TableFields, TableIndexFields};
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

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Table<'gc>(Gc<'gc, objects::Table>);

impl<'gc> Table<'gc> {
    #[inline]
    pub fn of(value: Value<'gc>) -> Option<Self> {
        match Data::of(value) {
            Some(Data::Table(table)) => Some(Self(table)),
            _ => None,
        }
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        Value::object(mc, self.0)
    }

    /// The number of entries.
    pub fn len(self, mc: &Mutation<'gc>) -> usize {
        self.0.live(mc) as usize
    }

    pub fn is_empty(self, mc: &Mutation<'gc>) -> bool {
        self.len(mc) == 0
    }

    /// The value of `key`, or `None` if the table has no such key.
    #[inline]
    pub fn get(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<Value<'gc>>, Error> {
        let Some(parts) = self.settled(mc)? else { return Ok(None) };
        let hashed = hash(mc, self.0.seed(mc), key)?;
        Ok(parts.find(mc, key, hashed.hash)?.map(|entry| parts.entries.get(2 * entry + 1)))
    }

    /// Sets the value of `key`. A key the table does not have yet becomes its last entry.
    pub fn set(self, mc: &Mutation<'gc>, key: Value<'gc>, value: Value<'gc>) -> Result<(), Error> {
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

    /// Removes the entry of `key`. Returns whether the table had one.
    pub fn delete(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<bool, Error> {
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
    pub fn clear(self, mc: &Mutation<'gc>) {
        self.0.set_index(mc, None);
        self.0.set_pairs(mc, None);
        self.0.set_live(mc, 0);
        self.0.set_used(mc, 0);
        self.0.set_epoch(mc, STILL);
    }

    /// The entries, in the order they were added.
    pub fn entries(self, mc: &Mutation<'gc>) -> Entries<'gc> {
        Entries { entries: self.0.pairs(mc).map(|entries| entries.items(mc)), at: 0, end: self.0.used(mc) as usize }
    }

    /// The `index`th value the table holds, or `None` past the last. Keys and values alternate,
    /// in the order the entries were added. Both places of a removed entry read as
    /// [`Value::BROKEN`]. This is for code that walks any container by position, as a printer
    /// does; [`Table::entries`] is the way to read a table.
    pub fn held(self, mc: &Mutation<'gc>, index: usize) -> Option<Value<'gc>> {
        let entries = self.0.pairs(mc)?.items(mc);
        (index < 2 * self.0.used(mc) as usize).then(|| entries.get(index))
    }

    /// Whether the next read or write makes the index again, because a collection has moved
    /// objects since it was made. That takes time in proportion to the number of entries.
    pub fn is_stale(self, mc: &Mutation<'gc>) -> bool {
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
        Ok(Table(table))
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
