//! Hash tables in the arena, by linear probing over numbered slots. A table keeps each slot's
//! probe key, the hash with its low bit set, in a word array, so a probe reads only words until
//! a key matches, and the entries in a second array whose kind decides how they hold on:
//! [`Strong`] pairs, [`Ephemerons`], or [`WeakObjects`] that die with their objects.
//!
//! A dead entry keeps its probe key until the table is rebuilt, so probes go on past it, and
//! the next insertion that passes it takes its slot. Rebuilding sizes the table to stay at most
//! half full, and inserting keeps it at most three quarters full, counting dead slots.
//!
//! Hashes are the caller's, and must stay the same while an entry is in the table, except in an
//! identity table, [`Table::new_eq`]: its keys hash by what they are, which moving an object
//! changes, so it rehashes on first use after a collection that moved objects.

use std::marker::PhantomData;

use crate::gc::raw::Raw;
use crate::gc::slot;
use crate::gc::{Desc, Gc, Items, Mutation, Object, OutOfMemory, Slots, Value};

#[cfg(test)]
#[path = "tests/table.rs"]
mod tests;

crate::gc::objects! {
    /// The collector's own containers.
    pub kind Containers at 2;

    /// A table's handle: its probe keys and entries, which rebuilding replaces, the slots with a
    /// key, and for an identity table, the evacuation count it last hashed at.
    pub struct TableHead { keys: Member<Keys>, buf: Value, used: u64, epoch: u64 }
    /// Probe keys, 0 for a slot never used.
    pub struct Keys {} items u64
    /// A key and a value per slot, both `Value::BROKEN` once removed.
    pub struct Pairs {} items Value
    pub struct EphemeronPairs {} items Ephemeron
}

/// Fewest slots a table that holds anything has.
const MIN_SLOTS: usize = 8;
/// What an identity table's epoch is set to by tables of caller hashes.
const NOT_EQ: u64 = u64::MAX;

mod sealed {
    pub trait Sealed {}
}

/// How a table holds its entries.
pub trait Kind: sealed::Sealed + 'static {
    type Entry<'gc>: Copy;
    #[doc(hidden)]
    type Buf: Object;

    #[doc(hidden)]
    fn alloc<'gc>(mc: &Mutation<'gc>, slots: usize) -> Result<Gc<'gc, Self::Buf>, OutOfMemory>;

    /// The entry in slot `index`, unless it's dead.
    #[doc(hidden)]
    fn entry<'gc>(mc: &Mutation<'gc>, buf: Gc<'gc, Self::Buf>, index: usize) -> Option<Self::Entry<'gc>>;

    #[doc(hidden)]
    fn set<'gc>(mc: &Mutation<'gc>, buf: Gc<'gc, Self::Buf>, index: usize, entry: Self::Entry<'gc>);

    #[doc(hidden)]
    fn kill<'gc>(mc: &Mutation<'gc>, buf: Gc<'gc, Self::Buf>, index: usize);

    /// What an identity table hashes the entry by.
    #[doc(hidden)]
    fn identity<'gc>(mc: &Mutation<'gc>, entry: Self::Entry<'gc>) -> Value<'gc>;
}

/// Keys and values both held strongly.
pub struct Strong;

/// Values held only while their keys are reachable some other way.
pub struct Ephemerons;

/// Objects of type `U`, each gone once nothing else holds it, as a symbol table holds symbols.
pub struct WeakObjects<U>(PhantomData<fn() -> U>);

/// `WeakObjects`' entries.
#[doc(hidden)]
pub struct WeakSlots<U>(PhantomData<fn() -> U>);

impl<U: Object> Object for WeakSlots<U> {
    const DESC: Desc = Desc::layout::<Self>(&[], Items::Weaks);
}

impl sealed::Sealed for Strong {}

impl Kind for Strong {
    type Entry<'gc> = (Value<'gc>, Value<'gc>);
    type Buf = Pairs;

    fn alloc<'gc>(mc: &Mutation<'gc>, slots: usize) -> Result<Gc<'gc, Pairs>, OutOfMemory> {
        Pairs::new(mc, 2 * slots, Value::BROKEN)
    }

    #[inline]
    fn entry<'gc>(mc: &Mutation<'gc>, buf: Gc<'gc, Pairs>, index: usize) -> Option<Self::Entry<'gc>> {
        let items = buf.items(mc);
        let key = items.get(2 * index);
        (key != Value::BROKEN).then(|| (key, items.get(2 * index + 1)))
    }

    #[inline]
    fn set<'gc>(mc: &Mutation<'gc>, buf: Gc<'gc, Pairs>, index: usize, (key, value): Self::Entry<'gc>) {
        let items = buf.items(mc);
        items.set(mc, 2 * index, key);
        items.set(mc, 2 * index + 1, value);
    }

    fn kill<'gc>(mc: &Mutation<'gc>, buf: Gc<'gc, Pairs>, index: usize) {
        Self::set(mc, buf, index, (Value::BROKEN, Value::BROKEN));
    }

    fn identity<'gc>(_: &Mutation<'gc>, (key, _): Self::Entry<'gc>) -> Value<'gc> {
        key
    }
}

impl sealed::Sealed for Ephemerons {}

impl Kind for Ephemerons {
    type Entry<'gc> = (Value<'gc>, Value<'gc>);
    type Buf = EphemeronPairs;

    fn alloc<'gc>(mc: &Mutation<'gc>, slots: usize) -> Result<Gc<'gc, EphemeronPairs>, OutOfMemory> {
        EphemeronPairs::new(mc, slots)
    }

    #[inline]
    fn entry<'gc>(mc: &Mutation<'gc>, buf: Gc<'gc, EphemeronPairs>, index: usize) -> Option<Self::Entry<'gc>> {
        buf.entry(mc, index)
    }

    #[inline]
    fn set<'gc>(mc: &Mutation<'gc>, buf: Gc<'gc, EphemeronPairs>, index: usize, (key, value): Self::Entry<'gc>) {
        buf.set_entry(mc, index, key, value);
    }

    fn kill<'gc>(mc: &Mutation<'gc>, buf: Gc<'gc, EphemeronPairs>, index: usize) {
        buf.set_entry(mc, index, Value::BROKEN, Value::BROKEN);
    }

    fn identity<'gc>(_: &Mutation<'gc>, (key, _): Self::Entry<'gc>) -> Value<'gc> {
        key
    }
}

impl<U: Object> sealed::Sealed for WeakObjects<U> {}

impl<U: Object> Kind for WeakObjects<U> {
    type Entry<'gc> = Gc<'gc, U>;
    type Buf = WeakSlots<U>;

    fn alloc<'gc>(mc: &Mutation<'gc>, slots: usize) -> Result<Gc<'gc, WeakSlots<U>>, OutOfMemory> {
        mc.alloc_items::<WeakSlots<U>, 0>([], slots, Value::from_bits(0))
    }

    #[inline]
    fn entry<'gc>(mc: &Mutation<'gc>, buf: Gc<'gc, WeakSlots<U>>, index: usize) -> Option<Gc<'gc, U>> {
        buf.item_slots::<slot::Weak<U>>(mc).get(index)
    }

    #[inline]
    fn set<'gc>(mc: &Mutation<'gc>, buf: Gc<'gc, WeakSlots<U>>, index: usize, entry: Gc<'gc, U>) {
        buf.item_slots::<slot::Weak<U>>(mc).set(mc, index, Some(entry));
    }

    fn kill<'gc>(mc: &Mutation<'gc>, buf: Gc<'gc, WeakSlots<U>>, index: usize) {
        buf.item_slots::<slot::Weak<U>>(mc).set(mc, index, None);
    }

    fn identity<'gc>(mc: &Mutation<'gc>, entry: Gc<'gc, U>) -> Value<'gc> {
        Value::object(mc, entry)
    }
}

/// A hash of what `value` is, rather than what it holds, for identity tables: two values hash
/// the same if they're the same word.
#[inline]
pub fn eq_hash(value: Value<'_>) -> u64 {
    let product = value.to_bits().wrapping_mul(0x9E37_79B9_7F4A_7C15);
    product ^ product >> 29
}

/// Where a probe for a key ended.
enum Probe<E> {
    Found(usize, E),
    /// Not there: the first dead or unused slot on the way, if there's room for it.
    Missing(Option<usize>),
}

/// A hash table of `K` entries.
pub struct Table<'gc, K> {
    head: Gc<'gc, TableHead>,
    _marker: PhantomData<fn() -> K>,
}

impl<K> Clone for Table<'_, K> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K> Copy for Table<'_, K> {}

impl<'gc, K: Kind> Table<'gc, K> {
    /// An empty table for hashes the caller computes.
    pub fn new(mc: &Mutation<'gc>) -> Result<Self, OutOfMemory> {
        Ok(Self::of(TableHead::new(mc, None, Value::FALSE, 0, NOT_EQ)?))
    }

    /// An empty identity table, used through the `_eq` methods, which hash with [`eq_hash`].
    pub fn new_eq(mc: &Mutation<'gc>) -> Result<Self, OutOfMemory> {
        Ok(Self::of(TableHead::new(mc, None, Value::FALSE, 0, mc.heap.m.evacuations.get())?))
    }

    /// The table `head` is the handle of. Read as the wrong kind, it's a table of nothing.
    pub fn of(head: Gc<'gc, TableHead>) -> Self {
        Self { head, _marker: PhantomData }
    }

    pub fn head(self) -> Gc<'gc, TableHead> {
        self.head
    }

    fn parts(self, mc: &Mutation<'gc>) -> Option<(Slots<'gc, slot::u64>, Gc<'gc, K::Buf>)> {
        let keys = self.head.keys(mc)?.items(mc);
        let buf = self.head.buf(mc).downcast::<K::Buf>(mc)?;
        Some((keys, buf))
    }

    /// Slots, used or not.
    pub fn capacity(self, mc: &Mutation<'gc>) -> usize {
        self.parts(mc).map_or(0, |(keys, _)| keys.len())
    }

    /// Live entries, counted.
    pub fn count(self, mc: &Mutation<'gc>) -> usize {
        self.entries(mc).count()
    }

    /// The live entries, in slot order. Inserting while iterating may skip or repeat some.
    pub fn entries<'m>(self, mc: &'m Mutation<'gc>) -> impl Iterator<Item = K::Entry<'gc>> + use<'m, 'gc, K> {
        let parts = self.parts(mc);
        let len = parts.map_or(0, |(keys, _)| keys.len());
        (0..len).filter_map(move |i| {
            let (keys, buf) = parts?;
            if keys.get(i) == 0 { None } else { K::entry(mc, buf, i) }
        })
    }

    /// The live entry with this hash that `same` accepts.
    pub fn find<E>(
        self,
        mc: &Mutation<'gc>,
        hash: u64,
        same: impl FnMut(K::Entry<'gc>) -> Result<bool, E>,
    ) -> Result<Option<K::Entry<'gc>>, E> {
        Ok(match self.probe(mc, key_of(hash), same)? {
            Probe::Found(_, entry) => Some(entry),
            Probe::Missing(_) => None,
        })
    }

    /// The live entry with this hash that `same` accepts, or the one `make` makes, which the table
    /// then keeps. Neither callback may change the table.
    pub fn find_or_insert<E: From<OutOfMemory>>(
        self,
        mc: &Mutation<'gc>,
        hash: u64,
        same: impl FnMut(K::Entry<'gc>) -> Result<bool, E>,
        make: impl FnOnce() -> Result<K::Entry<'gc>, E>,
    ) -> Result<K::Entry<'gc>, E> {
        let key = key_of(hash);
        match self.probe(mc, key, same)? {
            Probe::Found(_, entry) => Ok(entry),
            Probe::Missing(free) => {
                let entry = make()?;
                self.put(mc, key, free, entry)?;
                Ok(entry)
            }
        }
    }

    /// Removes the live entry with this hash that `same` accepts, and returns it.
    pub fn remove<E>(
        self,
        mc: &Mutation<'gc>,
        hash: u64,
        same: impl FnMut(K::Entry<'gc>) -> Result<bool, E>,
    ) -> Result<Option<K::Entry<'gc>>, E> {
        match self.probe(mc, key_of(hash), same)? {
            Probe::Found(index, entry) => {
                if let Some((_, buf)) = self.parts(mc) {
                    K::kill(mc, buf, index);
                }
                Ok(Some(entry))
            }
            Probe::Missing(_) => Ok(None),
        }
    }

    /// Probes from the key's home, past slots with other keys and dead entries. A table whose
    /// words were damaged may have no unused slot, so it stops after one lap.
    #[inline]
    fn probe<E>(
        self,
        mc: &Mutation<'gc>,
        key: u64,
        mut same: impl FnMut(K::Entry<'gc>) -> Result<bool, E>,
    ) -> Result<Probe<K::Entry<'gc>>, E> {
        let Some((keys, buf)) = self.parts(mc) else { return Ok(Probe::Missing(None)) };
        let mask = keys.len().wrapping_sub(1);
        let mut index = home(key, mask);
        let mut free = None;
        for _ in 0..keys.len() {
            match keys.get(index) {
                0 => return Ok(Probe::Missing(free.or(Some(index)))),
                stored if stored == key => match K::entry(mc, buf, index) {
                    Some(entry) if same(entry)? => return Ok(Probe::Found(index, entry)),
                    Some(_) => {}
                    None => free = free.or(Some(index)),
                },
                _ if free.is_none() && K::entry(mc, buf, index).is_none() => free = Some(index),
                _ => {}
            }
            index = (index + 1) & mask;
        }
        Ok(Probe::Missing(free))
    }

    /// Stores a new entry in `free`, the slot a probe for its key ended at, unless counting it
    /// would leave the table too full, in which case it rebuilds.
    fn put(self, mc: &Mutation<'gc>, key: u64, free: Option<usize>, entry: K::Entry<'gc>) -> Result<(), OutOfMemory> {
        let used = self.head.used(mc) as usize;
        let capacity = self.capacity(mc);
        let reused = free.zip(self.parts(mc)).is_some_and(|(index, (keys, _))| keys.get(index) != 0);
        let index = match free {
            Some(index) if reused => index,
            Some(index) if (used + 1) * 4 <= capacity * 3 => {
                self.head.set_used(mc, used as u64 + 1);
                index
            }
            _ => {
                self.rebuild(mc, false)?;
                self.head.set_used(mc, self.head.used(mc) + 1);
                self.unused_slot(mc, key).ok_or_else(|| mc.out_of_memory())?
            }
        };
        if let Some((keys, buf)) = self.parts(mc) {
            keys.set(mc, index, key);
            K::set(mc, buf, index, entry);
        }
        Ok(())
    }

    fn unused_slot(self, mc: &Mutation<'gc>, key: u64) -> Option<usize> {
        let (keys, _) = self.parts(mc)?;
        let mask = keys.len().wrapping_sub(1);
        let mut index = home(key, mask);
        for _ in 0..keys.len() {
            if keys.get(index) == 0 {
                return Some(index);
            }
            index = (index + 1) & mask;
        }
        None
    }

    /// Copies the live entries into new arrays with room for one more while staying at most half
    /// full, by their old keys or, for an identity table, by hashing them again.
    fn rebuild(self, mc: &Mutation<'gc>, rehash: bool) -> Result<(), OutOfMemory> {
        let old = self.parts(mc);
        let live = self.count(mc);
        let len = (2 * (live + 1)).next_power_of_two().max(MIN_SLOTS);
        let keys = Keys::new(mc, len, 0)?;
        let buf = K::alloc(mc, len)?;
        self.head.set_keys(mc, Some(keys));
        self.head.set_buf(mc, Value::object(mc, buf));
        self.head.set_used(mc, live as u64);
        let Some((old_keys, old_buf)) = old else { return Ok(()) };
        for j in 0..old_keys.len() {
            let Some(entry) = (old_keys.get(j) != 0).then(|| K::entry(mc, old_buf, j)).flatten() else { continue };
            let key = if rehash { key_of(eq_hash(K::identity(mc, entry))) } else { old_keys.get(j) };
            if let Some(index) = self.unused_slot(mc, key) {
                keys.items(mc).set(mc, index, key);
                K::set(mc, buf, index, entry);
            }
        }
        Ok(())
    }

    /// For an identity table: hashes the entries again if objects have moved since it last did.
    #[inline]
    fn rehashed(self, mc: &Mutation<'gc>) -> Result<(), OutOfMemory> {
        let now = mc.heap.m.evacuations.get();
        let epoch = self.head.epoch(mc);
        if epoch != NOT_EQ && epoch != now {
            if self.parts(mc).is_some() {
                self.rebuild(mc, true)?;
            }
            self.head.set_epoch(mc, now);
        }
        Ok(())
    }
}

/// Maps, whose entries are a key and a value.
impl<'gc, K: for<'a> Kind<Entry<'a> = (Value<'a>, Value<'a>)>> Table<'gc, K> {
    /// The value of the live entry with this hash whose key `same` accepts.
    pub fn get<E>(
        self,
        mc: &Mutation<'gc>,
        hash: u64,
        mut same: impl FnMut(Value<'gc>) -> Result<bool, E>,
    ) -> Result<Option<Value<'gc>>, E> {
        Ok(self.find(mc, hash, |(key, _)| same(key))?.map(|(_, value)| value))
    }

    /// Sets the value of the live entry with this hash whose key `same` accepts, or adds an
    /// entry, and returns the value it replaced.
    pub fn insert<E: From<OutOfMemory>>(
        self,
        mc: &Mutation<'gc>,
        hash: u64,
        mut same: impl FnMut(Value<'gc>) -> Result<bool, E>,
        key: Value<'gc>,
        value: Value<'gc>,
    ) -> Result<Option<Value<'gc>>, E> {
        let key_word = key_of(hash);
        match self.probe(mc, key_word, |(old, _)| same(old))? {
            Probe::Found(index, (old_key, old)) => {
                if let Some((_, buf)) = self.parts(mc) {
                    K::set(mc, buf, index, (old_key, value));
                }
                Ok(Some(old))
            }
            Probe::Missing(free) => {
                self.put(mc, key_word, free, (key, value))?;
                Ok(None)
            }
        }
    }

    /// In an identity table, the value for `key`.
    pub fn get_eq(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<Value<'gc>>, OutOfMemory> {
        self.rehashed(mc)?;
        self.get(mc, eq_hash(key), |candidate| Ok(candidate == key))
    }

    /// In an identity table, sets `key`'s value and returns the one it replaced.
    pub fn insert_eq(self, mc: &Mutation<'gc>, key: Value<'gc>, value: Value<'gc>) -> Result<Option<Value<'gc>>, OutOfMemory> {
        self.rehashed(mc)?;
        self.insert(mc, eq_hash(key), |candidate| Ok(candidate == key), key, value)
    }

    /// In an identity table, removes `key`'s entry and returns its value.
    pub fn remove_eq(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<Value<'gc>>, OutOfMemory> {
        self.rehashed(mc)?;
        Ok(self.remove(mc, eq_hash(key), |(candidate, _)| Ok::<_, OutOfMemory>(candidate == key))?.map(|(_, value)| value))
    }
}

impl<'gc, U: Object> Table<'gc, WeakObjects<U>> {
    /// In an identity table, adds `object` unless it's there.
    pub fn insert_eq(self, mc: &Mutation<'gc>, object: Gc<'gc, U>) -> Result<(), OutOfMemory> {
        self.rehashed(mc)?;
        let hash = eq_hash(Value::object(mc, object));
        self.find_or_insert(mc, hash, |candidate| Ok(candidate == object), || Ok(object)).map(drop)
    }

    /// In an identity table, whether `object` is there.
    pub fn contains_eq(self, mc: &Mutation<'gc>, object: Gc<'gc, U>) -> Result<bool, OutOfMemory> {
        self.rehashed(mc)?;
        let hash = eq_hash(Value::object(mc, object));
        Ok(self.find(mc, hash, |candidate| Ok::<_, OutOfMemory>(candidate == object))?.is_some())
    }
}

/// Zero means unused, so the low bit is always set.
fn key_of(hash: u64) -> u64 {
    hash | 1
}

/// Where probes for `key` start. Its low bit is always set, so it's left out.
fn home(key: u64, mask: usize) -> usize {
    (key >> 1) as usize & mask
}
