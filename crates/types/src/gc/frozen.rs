//! Frozen values: write-once values stored outside the region, such as the text of a source file or the positions where its lines start. An
//! object holds a frozen value in a `Frozen<T>` field. A read returns `&'gc T`, which is valid for the rest of the step.
//!
//! This needs no unsafe code, because no frozen value is freed during a step. Each value is in a slot
//! that is set once. Only `Arena::finish` empties the slots of the values that a collection found dead, and it borrows the arena mutably.
//! So the borrow checker rules out a reference that outlives its value.
//!
//! # Shared values
//!
//! An arena that loads an [image template](crate::gc::image::Template) holds the template's frozen values without copies of them: its table
//! refers to the template's list of values, which every such arena shares. An arena can hold many such lists, one for each template that it
//! loaded. The id of a shared value has the `SHARED` bit set, and holds the number of the list and the value's position in it. A shared
//! value is not freed while the arena lives, even when no object holds it any more. It takes none of the arena's memory, so nothing is lost.
//!
//! A frozen value is live while a live object holds it. Tracing finds these values. A minor collection
//! frees the values created since the last collection that no surviving object holds. A major collection
//! frees every value that no live object holds.

use std::any::Any;
use std::cell::{Cell, OnceCell, RefCell};
use std::marker::PhantomData;
use std::rc::Rc;

use crate::gc::budget::Budget;
use crate::gc::{Brand, OutOfMemory};

#[cfg(test)]
#[path = "tests/frozen_table.rs"]
mod tests;

/// The number of slots in the first chunk of the table. Each of the next chunks is twice as large as the one before it, up to `LARGEST`
/// slots. Every chunk after that has `LARGEST` slots.
///
/// So an arena with few frozen values has a small table, and the table of an arena with many values grows in steps of bounded size.
const FIRST: usize = 64;
/// The number of chunks that are smaller than `LARGEST`, counted from the first.
const DOUBLING: usize = 7;
const LARGEST: usize = FIRST << DOUBLING;
/// The number of slots in the chunks that are smaller than `LARGEST`.
const SMALL: usize = LARGEST - FIRST;

/// Returns the chunk that holds slot `number`, and the place of the slot in the chunk.
#[inline]
fn place(number: usize) -> (usize, usize) {
    if number < SMALL {
        // Chunk `k` holds the slots from `(FIRST << k) - FIRST` up to `(FIRST << (k + 1)) - FIRST`.
        let shifted = number + FIRST;
        let chunk = (shifted / FIRST).ilog2() as usize;
        (chunk, shifted - (FIRST << chunk))
    } else {
        (DOUBLING + (number - SMALL) / LARGEST, (number - SMALL) % LARGEST)
    }
}

/// Returns the number of slots in chunk `chunk`.
fn size(chunk: usize) -> usize {
    if chunk < DOUBLING { FIRST << chunk } else { LARGEST }
}

/// Returns the number of the first slot of chunk `chunk`.
fn first(chunk: usize) -> usize {
    if chunk < DOUBLING { (FIRST << chunk) - FIRST } else { SMALL + (chunk - DOUBLING) * LARGEST }
}
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

/// The bit of an id that says that the value is a shared one. The bits below it hold the number of the value's list, and the lowest
/// `POSITION_BITS` bits the position of the value in the list.
const SHARED: usize = 1 << 31;
const POSITION_BITS: u32 = 20;
/// The lists of shared values are kept in groups of this many, and there are this many groups. A group is allocated when its first list is added.
const GROUP: usize = 32;

/// One group of lists of shared values.
type Group = [OnceCell<Rc<[Shared]>>; GROUP];

/// A frozen value that arenas share, with the bytes that each of them is charged for it.
pub(crate) struct Shared {
    pub(crate) value: Box<dyn Any>,
    pub(crate) cost: usize,
}

/// The table of frozen values. It is made of chunks that are allocated as they are needed, so a slot never moves.
pub(crate) struct FrozenTable {
    /// The lists of values that the arena shares with others: one for each template that it loaded, in groups of `GROUP`.
    shared: [OnceCell<Box<Group>>; GROUP],
    /// The number of lists in `shared`.
    lists: Cell<usize>,
    /// The number of the shared values, and the bytes charged for them.
    shared_count: Cell<usize>,
    shared_cost: Cell<usize>,
    chunks: Box<[OnceCell<Box<[Slot]>>]>,
    /// One past the highest id handed out.
    next: Cell<usize>,
    free: RefCell<Vec<u32>>,
    /// The ids of the values created since the last collection. A minor collection checks only these.
    young: RefCell<Vec<u32>>,
    /// The ids of the values that a collection found dead. `free_dead` empties their slots.
    dead: RefCell<Vec<u32>>,
    /// The most slots that the table can have.
    room: usize,
    /// The number of slots in the chunks allocated so far, kept for charging. Counting them instead would take a pass over the table
    /// after every step.
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
        // The id of one of the arena's own values is the number of its slot, which must not reach the `SHARED` bit.
        let room = (limit / FROZEN_COST).clamp(LARGEST, SHARED - 1);
        let (last, _) = place(room - 1);
        Self {
            shared: [const { OnceCell::new() }; GROUP],
            lists: Cell::new(0),
            shared_count: Cell::new(0),
            shared_cost: Cell::new(0),
            chunks: (0..=last).map(|_| OnceCell::new()).collect(),
            room,
            next: Cell::new(0),
            free: RefCell::default(),
            young: RefCell::default(),
            dead: RefCell::default(),
            made: Cell::new(0),
            live: Cell::new(0),
            young_bytes: Cell::new(0),
        }
    }

    /// Returns the shared value with the id `id`, or `None` if the id is of one of the arena's own values or of no value.
    #[inline]
    fn shared(&self, id: usize) -> Option<&Shared> {
        if id & SHARED == 0 {
            return None;
        }
        let (list, position) = ((id & !SHARED) >> POSITION_BITS, id & ((1 << POSITION_BITS) - 1));
        self.shared.get(list / GROUP)?.get()?[list % GROUP].get()?.get(position)
    }

    /// Returns the arena's own slot with the number `number`, or `None` if its chunk has not been allocated.
    #[inline]
    fn own(&self, number: usize) -> Option<&Slot> {
        let (chunk, at) = place(number);
        self.chunks.get(chunk)?.get()?.get(at)
    }

    /// Returns the value that the frozen field word `word` refers to, or `None` if `word` does not refer to a `T`.
    #[inline]
    pub(crate) fn get<T: Any>(&self, word: u64) -> Option<&T> {
        let id = (word as u32).checked_sub(1)? as usize;
        if id & SHARED != 0 {
            return self.shared(id)?.value.downcast_ref();
        }
        self.own(id)?.value.get()?.downcast_ref()
    }

    /// Returns the value that the frozen field word `word` refers to, whatever its type, and the bytes charged for it.
    pub(crate) fn any(&self, word: u64) -> Option<(&dyn Any, usize)> {
        let id = (word as u32).checked_sub(1)? as usize;
        if id & SHARED != 0 {
            let shared = self.shared(id)?;
            return Some((&*shared.value, shared.cost));
        }
        let slot = self.own(id)?;
        Some((&**slot.value.get()?, slot.cost.get()))
    }

    /// Adds `shared` to the lists of values that the arena shares with others, and charges the arena for the values. Returns the id of
    /// the first value. The ids of the others follow it in order. Returns `None` if the arena holds as many lists as it can, or if the list
    /// is too long.
    pub(crate) fn share(&self, budget: &Budget, shared: &Rc<[Shared]>) -> Result<Option<u32>, OutOfMemory> {
        let list = self.lists.get();
        if list >= GROUP * GROUP || shared.len() > 1 << POSITION_BITS {
            return Ok(None);
        }
        let cost = shared.iter().fold(0usize, |total, value| total.saturating_add(value.cost));
        budget.count_allocation()?;
        budget.ensure(cost)?;
        let group = self.shared[list / GROUP].get_or_init(|| Box::new([const { OnceCell::new() }; GROUP]));
        if group[list % GROUP].set(shared.clone()).is_err() {
            unreachable!("the next list of shared values is not set yet");
        }
        budget.force(cost);
        self.lists.set(list + 1);
        self.shared_count.set(self.shared_count.get() + shared.len());
        self.shared_cost.set(self.shared_cost.get() + cost);
        Ok(Some((SHARED | list << POSITION_BITS) as u32))
    }

    pub(crate) fn alloc<T: Any>(&self, budget: &Budget, marked: bool, value: T, owned: usize) -> Result<u32, OutOfMemory> {
        let cost = (size_of::<T>() + FROZEN_COST).saturating_add(owned);
        self.alloc_boxed(budget, marked, Box::new(value), cost)
    }

    /// Stores `value` as one of the arena's own values, and charges `cost` bytes for it.
    pub(crate) fn alloc_boxed(&self, budget: &Budget, marked: bool, value: Box<dyn Any>, cost: usize) -> Result<u32, OutOfMemory> {
        budget.count_allocation()?;
        budget.ensure(cost)?;
        let slot = match self.free.borrow_mut().pop() {
            Some(slot) => slot as usize,
            None => {
                let slot = self.next.get();
                if slot >= self.room {
                    return Err(budget.fail());
                }
                self.next.set(slot + 1);
                slot
            }
        };
        let (chunk, at) = place(slot);
        let slots = self.chunks[chunk].get_or_init(|| {
            self.made.set(self.made.get() + size(chunk));
            (0..size(chunk)).map(|_| Slot::default()).collect()
        });
        let held = &slots[at];
        if held.value.set(value).is_err() {
            unreachable!("a free frozen slot is empty");
        }
        held.marked.set(marked);
        held.cost.set(cost);
        budget.force(cost);
        self.young.borrow_mut().push(slot as u32);
        self.young_bytes.set(self.young_bytes.get() + cost);
        Ok(slot as u32)
    }

    /// Marks the value that the frozen field word `word` refers to. A shared value needs no mark.
    pub(crate) fn mark(&self, word: u64) {
        let Some(id) = (word as u32).checked_sub(1) else { return };
        if id as usize & SHARED == 0
            && let Some(slot) = self.own(id as usize)
        {
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
        // The young list and the dead list hold slot numbers.
        for number in self.young.borrow_mut().drain(..) {
            let Some(slot) = self.own(number as usize) else { continue };
            if slot.marked.get() {
                live += slot.cost.get();
            } else {
                dead.push(number);
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
                    dead.push((first(chunk_index) + i) as u32);
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
            let (chunk, at) = place(id as usize);
            let slot = self.chunks.get_mut(chunk).and_then(OnceCell::get_mut).and_then(|slots| slots.get_mut(at));
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
        self.chunks.iter().filter_map(OnceCell::get).flat_map(|chunk| chunk.iter()).map(|slot| slot.cost.get()).sum::<usize>() + self.shared_cost.get()
    }

    /// Returns the bytes charged for the old values and for the shared values.
    pub(crate) fn live(&self) -> usize {
        self.live.get() + self.shared_cost.get()
    }

    /// Returns the bytes charged for the values created since the last collection.
    pub(crate) fn young_bytes(&self) -> usize {
        self.young_bytes.get()
    }

    /// Returns the number of values that the arena holds: its own values not yet freed, and the shared values.
    pub(crate) fn count(&self) -> usize {
        self.next.get() - self.free.borrow().len() + self.shared_count.get()
    }

    /// Returns the bytes that the table and its lists take, beyond the charges of the values themselves.
    pub(crate) fn table_bytes(&self) -> usize {
        self.chunks.len() * size_of::<OnceCell<Box<[Slot]>>>()
            + self.made.get() * size_of::<Slot>()
            + (self.free.borrow().capacity() + self.young.borrow().capacity() + self.dead.borrow().capacity()) * size_of::<u32>()
    }
}
