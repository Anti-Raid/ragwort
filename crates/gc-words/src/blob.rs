//! Write-once storage outside the region: arrays of units, such as a string's characters or a
//! bignum's digits, and any other value that doesn't change once made. An object holds one in a
//! field, and reading it lends `&'gc [U]` or `&'gc T` for the rest of the step.
//!
//! That takes no unsafe code because nothing is freed during a step. Each array sits in a slot
//! that's set once, and only `Arena::finish`, which borrows the arena mutably, empties the slots
//! a collection found dead, so the borrow checker rules out a lent slice outliving its array.
//!
//! A blob is live while an object holding it is, which tracing finds: a minor collection frees
//! the blobs made since the last collection that no surviving object holds, and a major one any
//! blob no live object holds.

use std::any::Any;
use std::cell::{Cell, OnceCell, RefCell};
use std::marker::PhantomData;

use crate::{Brand, OutOfMemory};
use crate::budget::Budget;

/// Slots per chunk of the table.
const CHUNK: usize = 1024;
/// Freed arrays up to this many units are kept for reuse, by unit and length, so the blobs a
/// step makes and a minor collection frees cost no allocation once the pools fill.
const POOL_LEN: usize = 64;
/// What a blob is charged beyond its contents: its slot, and the allocation's header.
pub(crate) const BLOB_COST: usize = size_of::<BlobSlot>() + 16;

/// What a blob slot holds. Public only for `Unit`'s hidden methods.
#[doc(hidden)]
pub enum Blob {
    U8(Box<[u8]>),
    U16(Box<[u16]>),
    U32(Box<[u32]>),
    U64(Box<[u64]>),
    Any(Box<dyn Any>),
}

#[derive(Default)]
pub(crate) struct BlobSlot {
    data: OnceCell<Blob>,
    marked: Cell<bool>,
    cost: Cell<usize>,
}

mod sealed {
    pub trait Sealed {}
}

/// What a blob can be an array of.
pub trait Unit: sealed::Sealed + Copy + Default + 'static {
    /// Which pool its arrays go to.
    #[doc(hidden)]
    const POOL: usize;
    #[doc(hidden)]
    fn wrap(units: Box<[Self]>) -> Blob;
    #[doc(hidden)]
    fn unwrap(blob: Blob) -> Option<Box<[Self]>>;
    #[doc(hidden)]
    fn view(blob: &Blob) -> Option<&[Self]>;
}

macro_rules! units {
    ($($ty:ident => $variant:ident $pool:literal,)*) => {$(
        impl sealed::Sealed for $ty {}

        impl Unit for $ty {
            const POOL: usize = $pool;

            fn wrap(units: Box<[Self]>) -> Blob {
                Blob::$variant(units)
            }

            fn unwrap(blob: Blob) -> Option<Box<[Self]>> {
                match blob {
                    Blob::$variant(units) => Some(units),
                    _ => None,
                }
            }

            #[inline]
            fn view(blob: &Blob) -> Option<&[Self]> {
                match blob {
                    Blob::$variant(units) => Some(units),
                    _ => None,
                }
            }
        }
    )*};
}

units! {
    u8 => U8 0,
    u16 => U16 1,
    u32 => U32 2,
    u64 => U64 3,
}

/// Freed arrays kept for reuse.
struct Pool {
    /// By unit, then length.
    arrays: Vec<Vec<Blob>>,
    bytes: usize,
    max: usize,
    /// What the lists themselves take, as of the last `free_dead` that changed them.
    lists: usize,
}

impl Pool {
    fn index(blob: &Blob) -> Option<(usize, usize)> {
        let (pool, len, size) = match blob {
            Blob::U8(u) => (0, u.len(), 1),
            Blob::U16(u) => (1, u.len(), 2),
            Blob::U32(u) => (2, u.len(), 4),
            Blob::U64(u) => (3, u.len(), 8),
            Blob::Any(_) => return None,
        };
        (1..=POOL_LEN).contains(&len).then(|| (pool * POOL_LEN + len - 1, len * size + 16))
    }

    fn take<U: Unit>(&mut self, len: usize) -> Option<Box<[U]>> {
        if !(1..=POOL_LEN).contains(&len) {
            return None;
        }
        let blob = self.arrays.get_mut(U::POOL * POOL_LEN + len - 1)?.pop()?;
        self.bytes -= len * size_of::<U>() + 16;
        U::unwrap(blob)
    }

    /// Keeps `blob` if it's a small array and there's room, and drops it otherwise.
    fn put(&mut self, blob: Blob) {
        if let Some((i, bytes)) = Self::index(&blob)
            && self.bytes + bytes <= self.max
            && let Some(arrays) = self.arrays.get_mut(i)
        {
            arrays.push(blob);
            self.bytes += bytes;
        }
    }
}

/// A blob of `U`s made this step, for a constructor to store in a field.
pub struct BlobRef<'gc, U> {
    id: u32,
    _marker: PhantomData<(Brand<'gc>, fn() -> U)>,
}

/// A frozen `T` made this step, for a constructor to store in a field.
pub struct FrozenRef<'gc, T> {
    id: u32,
    _marker: PhantomData<(Brand<'gc>, fn() -> T)>,
}

macro_rules! handle {
    ($name:ident) => {
        impl<T> Clone for $name<'_, T> {
            fn clone(&self) -> Self {
                *self
            }
        }

        impl<T> Copy for $name<'_, T> {}

        impl<T> $name<'_, T> {
            pub(crate) fn new(id: u32) -> Self {
                Self { id, _marker: PhantomData }
            }

            /// The word a blob field holds: the id plus one, so 0 is none.
            pub fn to_word(self) -> u64 {
                u64::from(self.id) + 1
            }
        }
    };
}

handle!(BlobRef);
handle!(FrozenRef);

/// The table of blobs, in chunks made as they're needed, so slots never move.
pub(crate) struct Blobs {
    chunks: Box<[OnceCell<Box<[BlobSlot]>>]>,
    /// One past the highest id handed out.
    next: Cell<usize>,
    free: RefCell<Vec<u32>>,
    /// Made since the last collection, for a minor one to check.
    young: RefCell<Vec<u32>>,
    /// Found dead, emptied by `free_dead`.
    dead: RefCell<Vec<u32>>,
    pool: RefCell<Pool>,
    /// Chunks made so far, for charging: counting them would take a pass over the table, after
    /// every step.
    made: Cell<usize>,
    /// What the blobs that outlived a collection, and weren't found dead since, are charged.
    /// Young ones are left out: a minor collection frees those.
    live: Cell<usize>,
    /// What the first so many young blobs are charged, and how many: `young_bytes` counts on
    /// from there, so `add` doesn't have to.
    young_counted: Cell<(usize, usize)>,
}

impl Blobs {
    /// Room for as many blobs as `limit` bytes pay for.
    pub(crate) fn new(limit: usize) -> Self {
        let max = (limit / BLOB_COST).clamp(CHUNK, u32::MAX as usize - 1);
        let chunks = (0..max.div_ceil(CHUNK)).map(|_| OnceCell::new()).collect();
        let pool = Pool { arrays: (0..4 * POOL_LEN).map(|_| Vec::new()).collect(), bytes: 0, max: (limit / 64).clamp(64 << 10, 4 << 20), lists: 0 };
        Self {
            chunks,
            next: Cell::new(0),
            free: RefCell::default(),
            young: RefCell::default(),
            dead: RefCell::default(),
            pool: RefCell::new(pool),
            made: Cell::new(0),
            live: Cell::new(0),
            young_counted: Cell::new((0, 0)),
        }
    }

    #[inline]
    fn slot(&self, word: u64) -> Option<&BlobSlot> {
        let id = (word as u32).checked_sub(1)? as usize;
        self.chunks.get(id / CHUNK)?.get()?.get(id % CHUNK)
    }

    /// The units a blob field's word names, or none if it names no blob of `U`s.
    #[inline]
    pub(crate) fn units<U: Unit>(&self, word: u64) -> &[U] {
        self.slot(word).and_then(|s| s.data.get()).and_then(U::view).unwrap_or(&[])
    }

    #[inline]
    pub(crate) fn frozen<T: Any>(&self, word: u64) -> Option<&T> {
        match self.slot(word)?.data.get()? {
            Blob::Any(value) => value.downcast_ref(),
            _ => None,
        }
    }

    /// Stores `blob`, charged `cost`, and returns its id.
    fn add(&self, budget: &Budget, blob: Blob, cost: usize, marked: bool) -> Result<u32, OutOfMemory> {
        let id = match self.free.borrow_mut().pop() {
            Some(id) => id,
            None => {
                let id = self.next.get();
                if id >= self.chunks.len() * CHUNK {
                    return Err(budget.fail());
                }
                self.next.set(id + 1);
                id as u32
            }
        };
        let chunk = self.chunks[id as usize / CHUNK].get_or_init(|| {
            self.made.set(self.made.get() + 1);
            (0..CHUNK).map(|_| BlobSlot::default()).collect()
        });
        let slot = &chunk[id as usize % CHUNK];
        if slot.data.set(blob).is_err() {
            unreachable!("a free blob slot is empty");
        }
        slot.marked.set(marked);
        slot.cost.set(cost);
        budget.force(cost);
        self.young.borrow_mut().push(id);
        Ok(id)
    }

    pub(crate) fn mark(&self, word: u64) {
        if let Some(slot) = self.slot(word) {
            slot.marked.set(true);
        }
    }

    pub(crate) fn clear_marks(&self) {
        for chunk in self.chunks.iter().filter_map(OnceCell::get) {
            chunk.iter().for_each(|s| s.marked.set(false));
        }
    }

    /// After a minor collection: blobs made since the last one that nothing marked are dead,
    /// and the rest are old.
    pub(crate) fn sweep_young(&self) {
        let mut dead = self.dead.borrow_mut();
        let mut live = self.live.get();
        for id in self.young.borrow_mut().drain(..) {
            let Some(slot) = self.slot(u64::from(id) + 1) else { continue };
            if slot.marked.get() {
                live += slot.cost.get();
            } else {
                dead.push(id);
            }
        }
        self.live.set(live);
        self.young_counted.set((0, 0));
    }

    /// After a major collection's marking: every unmarked blob is dead. That includes those a
    /// minor collection found and `free_dead` hasn't emptied yet, so they're listed again.
    pub(crate) fn sweep_all(&self) {
        let mut dead = self.dead.borrow_mut();
        dead.clear();
        let mut live = 0;
        for (c, chunk) in self.chunks.iter().enumerate() {
            let Some(chunk) = chunk.get() else { continue };
            for (i, slot) in chunk.iter().enumerate() {
                if slot.data.get().is_none() {
                    continue;
                }
                if slot.marked.get() {
                    live += slot.cost.get();
                } else {
                    dead.push((c * CHUNK + i) as u32);
                }
            }
        }
        self.live.set(live);
        self.young.borrow_mut().clear();
        self.young_counted.set((0, 0));
    }

    /// Empties the slots of up to `max` dead blobs, between steps, when nothing can be
    /// borrowing them.
    pub(crate) fn free_dead(&mut self, budget: &Budget, max: usize) {
        let (free, pool, dead) = (self.free.get_mut(), self.pool.get_mut(), self.dead.get_mut());
        if dead.is_empty() {
            return;
        }
        let keep = dead.len().saturating_sub(max);
        for id in dead.drain(keep..) {
            let slot = self.chunks.get_mut(id as usize / CHUNK).and_then(OnceCell::get_mut).and_then(|c| c.get_mut(id as usize % CHUNK));
            if let Some(slot) = slot
                && let Some(blob) = slot.data.take()
            {
                budget.refund(slot.cost.take());
                free.push(id);
                pool.put(blob);
            }
        }
        pool.lists = pool.arrays.iter().map(|a| a.capacity() * size_of::<Blob>()).sum();
    }

    /// What the blobs not yet freed were charged.
    #[cfg(test)]
    pub(crate) fn charged(&self) -> usize {
        self.chunks.iter().filter_map(OnceCell::get).flat_map(|c| c.iter()).map(|s| s.cost.get()).sum()
    }

    pub(crate) fn live(&self) -> usize {
        self.live.get()
    }

    /// What the blobs made since the last collection are charged.
    pub(crate) fn young_bytes(&self) -> usize {
        let young = self.young.borrow();
        let (mut bytes, counted) = self.young_counted.get();
        for &id in &young[counted..] {
            bytes += self.slot(u64::from(id) + 1).map_or(0, |s| s.cost.get());
        }
        self.young_counted.set((bytes, young.len()));
        bytes
    }

    pub(crate) fn count(&self) -> usize {
        self.next.get() - self.free.borrow().len()
    }

    /// The bytes the table, its lists and its pools take, beyond the blobs' own charges.
    pub(crate) fn table_bytes(&self) -> usize {
        let chunks = self.made.get();
        let pool = self.pool.borrow();
        pool.bytes
            + pool.lists
            + self.chunks.len() * size_of::<OnceCell<Box<[BlobSlot]>>>()
            + chunks * CHUNK * size_of::<BlobSlot>()
            + (self.free.borrow().capacity() + self.young.borrow().capacity() + self.dead.borrow().capacity()) * size_of::<u32>()
    }

    pub(crate) fn alloc_units<U: Unit>(
        &self,
        budget: &Budget,
        marked: bool,
        len: usize,
        init: impl FnOnce(&mut [U]) -> usize,
    ) -> Result<u32, OutOfMemory> {
        budget.count_allocation()?;
        let bytes = len.checked_mul(size_of::<U>()).ok_or_else(|| budget.fail())?;
        budget.ensure(bytes.saturating_add(BLOB_COST))?;
        let pooled = self.pool.borrow_mut().take::<U>(len);
        let mut units = match pooled {
            Some(mut units) => {
                units.fill(U::default());
                units
            }
            None => {
                let mut units = Vec::new();
                units.try_reserve_exact(len).map_err(|_| budget.fail())?;
                units.resize(len, U::default());
                units.into_boxed_slice()
            }
        };
        let kept = init(&mut units).min(len);
        if kept < len {
            let mut shorter = units.into_vec();
            shorter.truncate(kept);
            units = shorter.into_boxed_slice();
        }
        self.add(budget, U::wrap(units), kept * size_of::<U>() + BLOB_COST, marked)
    }

    pub(crate) fn alloc_frozen<T: Any>(&self, budget: &Budget, marked: bool, value: T, owned: usize) -> Result<u32, OutOfMemory> {
        budget.count_allocation()?;
        let cost = (size_of::<T>() + BLOB_COST).saturating_add(owned);
        budget.ensure(cost)?;
        self.add(budget, Blob::Any(Box::new(value)), cost, marked)
    }
}
