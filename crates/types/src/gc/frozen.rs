//! Write-once values outside the region, such as a source's text or where its lines start. An
//! object holds one in a `Frozen<T>` field, and reading it lends `&'gc T` for the rest of the step.
//!
//! That takes no unsafe code because nothing is freed during a step. Each value sits in a slot
//! that's set once, and only `Arena::finish`, which borrows the arena mutably, empties the slots
//! a collection found dead, so the borrow checker rules out a lent reference outliving its value.
//!
//! A frozen value is live while an object holding it is, which tracing finds: a minor collection
//! frees those made since the last collection that no surviving object holds, and a major one
//! any that no live object holds.

use std::any::Any;
use std::cell::{Cell, OnceCell, RefCell};
use std::marker::PhantomData;

use crate::gc::budget::Budget;
use crate::gc::{Brand, OutOfMemory};

/// Slots per chunk of the table.
const CHUNK: usize = 1024;
/// What a frozen value is charged beyond itself: its slot, and the allocation's header.
pub(crate) const FROZEN_COST: usize = size_of::<Slot>() + 16;

#[derive(Default)]
struct Slot {
    value: OnceCell<Box<dyn Any>>,
    marked: Cell<bool>,
    cost: Cell<usize>,
}

/// A frozen `T` made this step, for a constructor to store in a field.
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

    /// The word a frozen field holds: the id plus one, so 0 is none.
    pub fn to_word(self) -> u64 {
        u64::from(self.id) + 1
    }
}

/// The table of frozen values, in chunks made as they're needed, so slots never move.
pub(crate) struct FrozenTable {
    chunks: Box<[OnceCell<Box<[Slot]>>]>,
    /// One past the highest id handed out.
    next: Cell<usize>,
    free: RefCell<Vec<u32>>,
    /// Made since the last collection, for a minor one to check.
    young: RefCell<Vec<u32>>,
    /// Found dead, emptied by `free_dead`.
    dead: RefCell<Vec<u32>>,
    /// Chunks made so far, for charging: counting them would take a pass over the table, after
    /// every step.
    made: Cell<usize>,
    /// What the values that outlived a collection, and weren't found dead since, are charged.
    /// Young ones are left out: a minor collection frees those.
    live: Cell<usize>,
    /// What the first so many young values are charged, and how many: `young_bytes` counts on
    /// from there, so `add` doesn't have to.
    young_counted: Cell<(usize, usize)>,
}

impl FrozenTable {
    /// Room for as many values as `limit` bytes pay for.
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
            young_counted: Cell::new((0, 0)),
        }
    }

    #[inline]
    fn slot(&self, word: u64) -> Option<&Slot> {
        let id = (word as u32).checked_sub(1)? as usize;
        self.chunks.get(id / CHUNK)?.get()?.get(id % CHUNK)
    }

    /// The value a frozen field's word names, or none if it names no `T`.
    #[inline]
    pub(crate) fn get<T: Any>(&self, word: u64) -> Option<&T> {
        self.slot(word)?.value.get()?.downcast_ref()
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

    /// After a minor collection: values made since the last one that nothing marked are dead,
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

    /// After a major collection's marking: every unmarked value is dead. That includes those a
    /// minor collection found and `free_dead` hasn't emptied yet, so they're listed again.
    pub(crate) fn sweep_all(&self) {
        let mut dead = self.dead.borrow_mut();
        dead.clear();
        let mut live = 0;
        for (c, chunk) in self.chunks.iter().enumerate() {
            let Some(chunk) = chunk.get() else { continue };
            for (i, slot) in chunk.iter().enumerate() {
                if slot.value.get().is_none() {
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

    /// Empties the slots of up to `max` dead values, between steps, when nothing can be
    /// borrowing them.
    pub(crate) fn free_dead(&mut self, budget: &Budget, max: usize) {
        let (free, dead) = (self.free.get_mut(), self.dead.get_mut());
        let keep = dead.len().saturating_sub(max);
        for id in dead.drain(keep..) {
            let slot = self.chunks.get_mut(id as usize / CHUNK).and_then(OnceCell::get_mut).and_then(|c| c.get_mut(id as usize % CHUNK));
            if let Some(slot) = slot
                && slot.value.take().is_some()
            {
                budget.refund(slot.cost.take());
                free.push(id);
            }
        }
    }

    /// What the values not yet freed were charged.
    #[cfg(test)]
    pub(crate) fn charged(&self) -> usize {
        self.chunks.iter().filter_map(OnceCell::get).flat_map(|c| c.iter()).map(|s| s.cost.get()).sum()
    }

    pub(crate) fn live(&self) -> usize {
        self.live.get()
    }

    /// What the values made since the last collection are charged.
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

    /// The bytes the table and its lists take, beyond the values' own charges.
    pub(crate) fn table_bytes(&self) -> usize {
        self.chunks.len() * size_of::<OnceCell<Box<[Slot]>>>()
            + self.made.get() * CHUNK * size_of::<Slot>()
            + (self.free.borrow().capacity() + self.young.borrow().capacity() + self.dead.borrow().capacity()) * size_of::<u32>()
    }
}
