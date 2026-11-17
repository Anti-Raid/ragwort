//! Frozen values: write-once values stored outside the region, such as the text of a source file or the positions where its lines start. An
//! object holds a frozen value in a `Frozen<T>` field. A read returns `&'gc T`, which is valid for the rest of the step.
//!
//! This needs no unsafe code, because no frozen value is freed during a step. Each value is in a slot
//! that is set once. Only `Arena::finish` empties the slots of the values that a collection found dead, and it borrows the arena mutably.
//! So the borrow checker rules out a reference that outlives its value.
//!
//! A frozen value is live while a live object holds it. Tracing finds these values. A minor collection
//! frees the values created since the last collection that no surviving object holds. A major collection
//! frees every value that no live object holds.

use std::any::Any;
use std::cell::{Cell, OnceCell, RefCell};
use std::marker::PhantomData;

use crate::gc::budget::Budget;
use crate::gc::{Brand, OutOfMemory};

/// Slots per chunk of the table.
const CHUNK: usize = 1024;
/// The bytes charged for a frozen value beyond its own size. They cover its slot and the allocation's header.
pub(crate) const FROZEN_COST: usize = size_of::<Slot>() + 16;

#[derive(Default)]
struct Slot {
    value: OnceCell<Box<dyn Any>>,
    marked: Cell<bool>,
    cost: Cell<usize>,
}

/// A reference to a frozen `T` created in this step. A constructor stores it in a field.
pub struct FrozenRef<'gc, T> {
    id: u32,
    _marker: PhantomData<(Brand<'gc>, fn() -> T)>,
}

impl<T> Clone for FrozenRef<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for FrozenRef<'_, T> {}

impl<T> FrozenRef<'_, T> {
    pub(crate) fn new(id: u32) -> Self {
        Self { id, _marker: PhantomData }
    }

    /// Returns the word that a frozen field holds: the id plus one, so that 0 means no value.
    pub fn to_word(self) -> u64 {
        u64::from(self.id) + 1
    }
}

/// The table of frozen values. It is made of chunks that are allocated as they are needed, so a slot never moves.
pub(crate) struct FrozenTable {
    chunks: Box<[OnceCell<Box<[Slot]>>]>,
    /// One past the highest id handed out.
    next: Cell<usize>,
    free: RefCell<Vec<u32>>,
    /// The ids of the values created since the last collection. A minor collection checks only these.
    young: RefCell<Vec<u32>>,
    /// The ids of the values that a collection found dead. `free_dead` empties their slots.
    dead: RefCell<Vec<u32>>,
    /// The number of chunks allocated so far, kept for charging. Counting the chunks instead would take a pass over the table after
    /// every step.
    made: Cell<usize>,
    /// The bytes charged for the old values: the values that survived a collection and have not been found dead since.
    /// Young values are not included, because a minor collection can free them.
    live: Cell<usize>,
    /// The bytes charged for the young values.
    young_bytes: Cell<usize>,
}

impl FrozenTable {
    /// Creates a table with room for as many values as `limit` bytes can pay for.
    pub(crate) fn new(limit: usize) -> Self {
        let max = (limit / FROZEN_COST).clamp(CHUNK, u32::MAX as usize - 1);
        Self {
            chunks: (0..max.div_ceil(CHUNK)).map(|_| OnceCell::new()).collect(),
            next: Cell::new(0),
            free: RefCell::default(),
            young: RefCell::default(),
            dead: RefCell::default(),
            made: Cell::new(0),
            live: Cell::new(0),
            young_bytes: Cell::new(0),
        }
    }

    #[inline]
    fn slot(&self, word: u64) -> Option<&Slot> {
        let id = (word as u32).checked_sub(1)? as usize;
        self.chunks.get(id / CHUNK)?.get()?.get(id % CHUNK)
    }

    /// Returns the value that the frozen field word `word` refers to, or `None` if `word` does not refer to a `T`.
    #[inline]
    pub(crate) fn get<T: Any>(&self, word: u64) -> Option<&T> {
        self.slot(word)?.value.get()?.downcast_ref()
    }

    /// Returns the value that the frozen field word `word` refers to, whatever its type, and the bytes charged for it.
    pub(crate) fn any(&self, word: u64) -> Option<(&dyn Any, usize)> {
        let slot = self.slot(word)?;
        Some((&**slot.value.get()?, slot.cost.get()))
    }

    pub(crate) fn alloc<T: Any>(&self, budget: &Budget, marked: bool, value: T, owned: usize) -> Result<u32, OutOfMemory> {
        budget.count_allocation()?;
        let cost = (size_of::<T>() + FROZEN_COST).saturating_add(owned);
        budget.ensure(cost)?;
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
            (0..CHUNK).map(|_| Slot::default()).collect()
        });
        let slot = &chunk[id as usize % CHUNK];
        if slot.value.set(Box::new(value)).is_err() {
            unreachable!("a free frozen slot is empty");
        }
        slot.marked.set(marked);
        slot.cost.set(cost);
        budget.force(cost);
        self.young.borrow_mut().push(id);
        self.young_bytes.set(self.young_bytes.get() + cost);
        Ok(id)
    }

    pub(crate) fn mark(&self, word: u64) {
        if let Some(slot) = self.slot(word) {
            slot.marked.set(true);
        }
    }

    pub(crate) fn clear_marks(&self) {
        for chunk in self.chunks.iter().filter_map(OnceCell::get) {
            chunk.iter().for_each(|slot| slot.marked.set(false));
        }
    }

    /// Runs after a minor collection. A value created since the last collection is dead if it was not marked.
    /// Every other young value becomes old.
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
        self.young_bytes.set(0);
    }

    /// Runs after the marking of a major collection. Every unmarked value is dead. That includes the values that a
    /// minor collection found dead and `free_dead` has not emptied yet, so the dead list is rebuilt from scratch.
    pub(crate) fn sweep_all(&self) {
        let mut dead = self.dead.borrow_mut();
        dead.clear();
        let mut live = 0;
        for (chunk_index, chunk) in self.chunks.iter().enumerate() {
            let Some(chunk) = chunk.get() else { continue };
            for (i, slot) in chunk.iter().enumerate() {
                if slot.value.get().is_none() {
                    continue;
                }
                if slot.marked.get() {
                    live += slot.cost.get();
                } else {
                    dead.push((chunk_index * CHUNK + i) as u32);
                }
            }
        }
        self.live.set(live);
        self.young.borrow_mut().clear();
        self.young_bytes.set(0);
    }

    /// Empties the slots of up to `max` dead values. It runs between steps, when nothing can
    /// borrow the values.
    pub(crate) fn free_dead(&mut self, budget: &Budget, max: usize) {
        let (free, dead) = (self.free.get_mut(), self.dead.get_mut());
        let keep = dead.len().saturating_sub(max);
        for id in dead.drain(keep..) {
            let slot = self.chunks.get_mut(id as usize / CHUNK).and_then(OnceCell::get_mut).and_then(|chunk| chunk.get_mut(id as usize % CHUNK));
            if let Some(slot) = slot
                && slot.value.take().is_some()
            {
                budget.refund(slot.cost.take());
                free.push(id);
            }
        }
    }

    /// Returns the bytes charged for the values not yet freed.
    #[cfg(test)]
    pub(crate) fn charged(&self) -> usize {
        self.chunks.iter().filter_map(OnceCell::get).flat_map(|chunk| chunk.iter()).map(|slot| slot.cost.get()).sum()
    }

    pub(crate) fn live(&self) -> usize {
        self.live.get()
    }

    /// Returns the bytes charged for the values created since the last collection.
    pub(crate) fn young_bytes(&self) -> usize {
        self.young_bytes.get()
    }

    pub(crate) fn count(&self) -> usize {
        self.next.get() - self.free.borrow().len()
    }

    /// Returns the bytes that the table and its lists take, beyond the charges of the values themselves.
    pub(crate) fn table_bytes(&self) -> usize {
        self.chunks.len() * size_of::<OnceCell<Box<[Slot]>>>()
            + self.made.get() * CHUNK * size_of::<Slot>()
            + (self.free.borrow().capacity() + self.young.borrow().capacity() + self.dead.borrow().capacity()) * size_of::<u32>()
    }
}
