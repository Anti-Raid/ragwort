//! Hash tables in the arena, with linear probing over numbered slots. A table keeps the probe key of each slot
//! in a word array. The probe key is the hash with its low bit set. So a probe reads only words until
//! a key matches. The entries are in a second array. The table's [`Kind`] decides how that array holds the entries:
//! as [`Strong`] pairs, as [`Ephemerons`], or as [`WeakObjects`], which are removed when their objects die.
//!
//! A removed or dead entry is a tombstone. It keeps its probe key until the table is rebuilt, so probes continue past it.
//! The next insertion whose probe passes the tombstone reuses its slot. A rebuild sizes the table to be at most
//! half full. Insertion keeps the table at most three quarters full, counting tombstones.
//!
//! The caller computes the hashes. A hash must stay the same while its entry is in the table. The exception is an
//! identity table, made by [`Table::new_eq`]. It hashes a key by the key's value word, which changes when a collection moves the object.
//! So an identity table rehashes on first use after a collection that moved objects.

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

    /// The head of a table. `keys` holds the probe keys and `buf` holds the entries. A rebuild replaces both. `used` is the number of slots that have a
    /// probe key. In an identity table, `epoch` is the evacuation count at which the table last hashed its entries.
    pub struct TableHead { keys: Member<Keys>, buf: Value, used: u64, epoch: u64 }
    /// The probe keys of a table. 0 marks a slot that was never used.
    pub struct Keys {} items u64
    /// The entries of a strong table: a key and a value per slot. Both are `Value::BROKEN` in an unused slot and in a removed entry.
    pub struct Pairs {} items Value
    pub struct EphemeronPairs {} items Ephemeron
}

/// The minimum number of slots in a table that has allocated its arrays.
const MIN_SLOTS: usize = 8;
/// The `epoch` sentinel of a table that uses caller-computed hashes. It marks the table as not an identity table.
const NOT_EQ: u64 = u64::MAX;

mod sealed {
    pub trait Sealed {}
}

/// The way a table holds its entries: strongly, as ephemerons, or weakly.
pub trait Kind: sealed::Sealed + 'static {
    type Entry<'gc>: Copy;
    #[doc(hidden)]
    type Buf: Object;

    #[doc(hidden)]
    fn alloc<'gc>(mc: &Mutation<'gc>, slots: usize) -> Result<Gc<'gc, Self::Buf>, OutOfMemory>;

    /// Returns the entry in slot `index`, or `None` if the entry is dead or removed.
    #[doc(hidden)]
    fn entry<'gc>(mc: &Mutation<'gc>, buf: Gc<'gc, Self::Buf>, index: usize) -> Option<Self::Entry<'gc>>;

    #[doc(hidden)]
    fn set<'gc>(mc: &Mutation<'gc>, buf: Gc<'gc, Self::Buf>, index: usize, entry: Self::Entry<'gc>);

    #[doc(hidden)]
    fn kill<'gc>(mc: &Mutation<'gc>, buf: Gc<'gc, Self::Buf>, index: usize);

    /// Returns the value whose word an identity table hashes for `entry`.
    #[doc(hidden)]
    fn identity<'gc>(mc: &Mutation<'gc>, entry: Self::Entry<'gc>) -> Value<'gc>;
}

/// A table kind that holds both keys and values strongly.
pub struct Strong;

/// A table kind whose entries are ephemerons. A value is held only while its key is reachable in some other way.
pub struct Ephemerons;

/// A table kind that holds objects of type `U` weakly. An entry is removed once nothing else holds its object. A symbol table holds its symbols this way.
pub struct WeakObjects<U>(PhantomData<fn() -> U>);

/// The entry array of a `WeakObjects` table.
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
        if key != Value::BROKEN {
            Some((key, items.get(2 * index + 1)))
        } else {
            None
        }
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

/// Returns the identity hash of `value`, for identity tables. The hash is computed from the value's word, not from the contents of an object. Two values have
/// the same hash if they are the same word.
#[inline]
pub fn eq_hash(value: Value<'_>) -> u64 {
    let product = value.to_bits().wrapping_mul(0x9E37_79B9_7F4A_7C15);
    product ^ product >> 29
}

/// The result of a probe for a key.
enum Probe<E> {
    Found(usize, E),
    /// The key is not in the table. Holds the first tombstone or unused slot on the probe path, where a new entry can go, or `None` if the probe found no such slot.
    Missing(Option<usize>),
}

/// A hash table of kind `K`.
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
    /// Creates an empty table that uses hashes computed by the caller.
    pub fn new(mc: &Mutation<'gc>) -> Result<Self, OutOfMemory> {
        Ok(Self::of(TableHead::new(mc, None, Value::FALSE, 0, NOT_EQ)?))
    }

    /// Creates an empty identity table. Use it through the `_eq` methods, which hash with [`eq_hash`].
    pub fn new_eq(mc: &Mutation<'gc>) -> Result<Self, OutOfMemory> {
        Ok(Self::of(TableHead::new(mc, None, Value::FALSE, 0, mc.heap.m.evacuations.get())?))
    }

    /// Returns the table whose head is `head`. If `K` is not the kind that the table was created with, the table reads as empty.
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

    /// Returns the number of slots, used or not.
    pub fn capacity(self, mc: &Mutation<'gc>) -> usize {
        self.parts(mc).map_or(0, |(keys, _)| keys.len())
    }

    /// Returns the number of live entries. This takes a pass over all the slots.
    pub fn count(self, mc: &Mutation<'gc>) -> usize {
        self.entries(mc).count()
    }

    /// Returns the live entries, in slot order. Inserting while iterating may skip or repeat some entries.
    pub fn entries<'m>(self, mc: &'m Mutation<'gc>) -> impl Iterator<Item = K::Entry<'gc>> + use<'m, 'gc, K> {
        let parts = self.parts(mc);
        let len = parts.map_or(0, |(keys, _)| keys.len());
        (0..len).filter_map(move |i| {
            let (keys, buf) = parts?;
            if keys.get(i) == 0 {
                None
            } else {
                K::entry(mc, buf, i)
            }
        })
    }

    /// Returns the live entry that has hash `hash` and that `same` accepts, or `None` if there is none.
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

    /// Returns the live entry that has hash `hash` and that `same` accepts. If there is none, inserts the entry that `make` returns, and returns that
    /// entry. Neither callback may change the table.
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

    /// Removes the live entry that has hash `hash` and that `same` accepts, and returns it. Returns `None` if there is none.
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

    /// Probes from the home slot of `key`, past slots with other keys and past tombstones. A table whose
    /// words were corrupted may have no unused slot, so the probe stops after one pass over the slots.
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

    /// Stores the new entry `entry` in `free`, the slot where a probe for `key` ended. If `free` is an unused slot and using it
    /// would leave the table more than three quarters full, or if `free` is `None`, the table is rebuilt first and the entry goes into the new arrays.
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

    /// Copies the live entries into new arrays. The new arrays have room for one more entry while staying at most half
    /// full. Each entry keeps its old probe key. If `rehash` is true, as for an identity table, each entry is hashed again instead.
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
            if old_keys.get(j) == 0 {
                continue;
            }
            let Some(entry) = K::entry(mc, old_buf, j) else { continue };
            let key = if rehash {
                key_of(eq_hash(K::identity(mc, entry)))
            } else {
                old_keys.get(j)
            };
            if let Some(index) = self.unused_slot(mc, key) {
                keys.items(mc).set(mc, index, key);
                K::set(mc, buf, index, entry);
            }
        }
        Ok(())
    }

    /// Rehashes the entries of an identity table if a collection has moved objects since the table last hashed them. Does nothing for any other table.
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

/// Methods for maps: tables whose entries are a key and a value.
impl<'gc, K: for<'a> Kind<Entry<'a> = (Value<'a>, Value<'a>)>> Table<'gc, K> {
    /// Returns the value of the live entry that has hash `hash` and whose key `same` accepts.
    pub fn get<E>(
        self,
        mc: &Mutation<'gc>,
        hash: u64,
        mut same: impl FnMut(Value<'gc>) -> Result<bool, E>,
    ) -> Result<Option<Value<'gc>>, E> {
        Ok(self.find(mc, hash, |(key, _)| same(key))?.map(|(_, value)| value))
    }

    /// Sets the value of the live entry that has hash `hash` and whose key `same` accepts, and returns the value it replaced. If there is no such entry, adds an
    /// entry for `key` and `value`, and returns `None`.
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

    /// Returns the value for `key` in an identity table.
    pub fn get_eq(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<Value<'gc>>, OutOfMemory> {
        self.rehashed(mc)?;
        self.get(mc, eq_hash(key), |candidate| Ok(candidate == key))
    }

    /// Sets the value for `key` in an identity table, and returns the value it replaced.
    pub fn insert_eq(self, mc: &Mutation<'gc>, key: Value<'gc>, value: Value<'gc>) -> Result<Option<Value<'gc>>, OutOfMemory> {
        self.rehashed(mc)?;
        self.insert(mc, eq_hash(key), |candidate| Ok(candidate == key), key, value)
    }

    /// Removes the entry for `key` from an identity table, and returns its value.
    pub fn remove_eq(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<Value<'gc>>, OutOfMemory> {
        self.rehashed(mc)?;
        Ok(self.remove(mc, eq_hash(key), |(candidate, _)| Ok::<_, OutOfMemory>(candidate == key))?.map(|(_, value)| value))
    }
}

impl<'gc, U: Object> Table<'gc, WeakObjects<U>> {
    /// Adds `object` to an identity table, unless the table already holds it.
    pub fn insert_eq(self, mc: &Mutation<'gc>, object: Gc<'gc, U>) -> Result<(), OutOfMemory> {
        self.rehashed(mc)?;
        let hash = eq_hash(Value::object(mc, object));
        self.find_or_insert(mc, hash, |candidate| Ok(candidate == object), || Ok(object)).map(drop)
    }

    /// Returns whether an identity table holds `object`.
    pub fn contains_eq(self, mc: &Mutation<'gc>, object: Gc<'gc, U>) -> Result<bool, OutOfMemory> {
        self.rehashed(mc)?;
        let hash = eq_hash(Value::object(mc, object));
        Ok(self.find(mc, hash, |candidate| Ok::<_, OutOfMemory>(candidate == object))?.is_some())
    }
}

/// Returns the probe key for `hash`. A probe key of 0 means an unused slot, so the low bit is always set.
fn key_of(hash: u64) -> u64 {
    hash | 1
}

/// Returns the slot where probes for `key` start. The low bit of `key` is always set, so it is shifted out.
fn home(key: u64, mask: usize) -> usize {
    (key >> 1) as usize & mask
}
