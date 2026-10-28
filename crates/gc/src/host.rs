use std::any::Any;
use std::cell::{Cell, RefCell};
use std::fmt;
use std::marker::PhantomData;
use std::mem::size_of;
use std::ptr::NonNull;

use super::budget::Budget;
use super::table::Table;
use super::{Invariant, Mutation, OutOfMemory, Plain, Trace, Tracer};

const NO_SLOT: u32 = u32::MAX;

/// Names a host value: its slot, and the slot's generation when the value went in, so an id
/// that outlived its value matches nothing.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct HostId {
    index: u32,
    generation: u32,
}

impl fmt::Debug for HostId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}#{}", self.index, self.generation)
    }
}

enum Slot {
    Used { generation: u32, marked: bool, cost: usize, value: Box<dyn Any> },
    Free { next: u32 },
}

/// Host values referenced from the arena. Lives outside the region, so heap objects only
/// ever hold an index and generation. Free slots form a list through the table itself,
/// lowest index first, so the table needs no memory beyond its charged capacity.
pub(crate) struct Hosts {
    slots: RefCell<Table<Slot>>,
    free: Cell<u32>,
    generation: Cell<u32>,
}

impl Hosts {
    pub(crate) fn new() -> Self {
        Self { slots: RefCell::new(Table::new()), free: Cell::new(NO_SLOT), generation: Cell::new(0) }
    }

    /// Takes ownership of `value` and charges `cost` for it, plus any growth of the table.
    fn insert(&self, budget: &Budget, value: Box<dyn Any>, cost: usize, marked: bool) -> Result<HostId, OutOfMemory> {
        let mut slots = self.slots.borrow_mut();
        let head = self.free.get();
        let growth = if head == NO_SLOT { slots.growth_cost(1) } else { 0 };
        if head == NO_SLOT && slots.len() >= NO_SLOT as usize {
            return Err(budget.fail());
        }
        budget.ensure(cost + growth)?;
        let generation = self.generation.get();
        self.generation.set(generation.wrapping_add(1));
        let used = Slot::Used { generation, marked, cost, value };
        let index = if head == NO_SLOT {
            slots.push(budget, used)?;
            slots.len() - 1
        } else {
            let slot = &mut slots[head as usize];
            let Slot::Free { next } = *slot else { unreachable!("host free list points at a used slot") };
            self.free.set(next);
            *slot = used;
            head as usize
        };
        budget.charge(cost)?;
        Ok(HostId { index: index as u32, generation })
    }

    /// The value's address. It stays put while the slot is used, since the box doesn't move
    /// when the table grows, and slots are only freed between steps.
    fn get<T: 'static>(&self, id: HostId) -> Option<NonNull<T>> {
        match self.slots.borrow().get(id.index as usize)? {
            Slot::Used { generation, value, .. } if *generation == id.generation => value.downcast_ref::<T>().map(NonNull::from),
            _ => None,
        }
    }

    pub(crate) fn mark(&self, id: HostId) -> bool {
        match self.slots.borrow_mut().get_mut(id.index as usize) {
            Some(Slot::Used { generation, marked, .. }) if *generation == id.generation => {
                *marked = true;
                true
            }
            _ => false,
        }
    }

    #[cfg(any(test, feature = "gc-verify"))]
    pub(crate) fn is_live(&self, id: HostId) -> bool {
        matches!(self.slots.borrow().get(id.index as usize), Some(Slot::Used { generation, .. }) if *generation == id.generation)
    }

    #[cfg(any(test, feature = "gc-verify"))]
    pub(crate) fn is_marked(&self, id: HostId) -> bool {
        let slots = self.slots.borrow();
        matches!(slots.get(id.index as usize), Some(Slot::Used { generation, marked: true, .. }) if *generation == id.generation)
    }

    /// Unmarks every value, at the start of a major cycle.
    pub(crate) fn clear_marks(&self) {
        for slot in self.slots.borrow_mut().iter_mut() {
            if let Slot::Used { marked, .. } = slot {
                *marked = false;
            }
        }
    }

    /// Frees unmarked values and refunds what was freed. Marks stay set, so a value that
    /// survives a collection counts as old until the next major cycle. Returns the values to
    /// drop, so their destructors run once the collector is done.
    pub(crate) fn sweep(&self, budget: &Budget) -> Vec<Box<dyn Any>> {
        let mut slots = self.slots.borrow_mut();
        let mut dropped = Vec::new();
        for slot in slots.iter_mut() {
            if let Slot::Used { marked: false, cost, .. } = slot {
                budget.refund(*cost);
                if let Slot::Used { value, .. } = std::mem::replace(slot, Slot::Free { next: NO_SLOT }) {
                    dropped.push(value);
                }
            }
        }
        while matches!(slots.last(), Some(Slot::Free { .. })) {
            slots.pop();
        }
        slots.shrink(budget);
        let mut head = NO_SLOT;
        for (index, slot) in slots.iter_mut().enumerate().rev() {
            if let Slot::Free { next } = slot {
                *next = head;
                head = index as u32;
            }
        }
        self.free.set(head);
        dropped
    }

    /// Bytes charged for the table and the values in it.
    #[cfg(test)]
    pub(crate) fn charged(&self) -> usize {
        let slots = self.slots.borrow();
        slots.charged() + slots.iter().map(|s| if let Slot::Used { cost, .. } = s { *cost } else { 0 }).sum::<usize>()
    }

    #[cfg(test)]
    pub(crate) fn capacity(&self) -> usize {
        self.slots.borrow().charged() / size_of::<Slot>()
    }

    pub(crate) fn len(&self) -> usize {
        self.slots.borrow().iter().filter(|s| matches!(s, Slot::Used { .. })).count()
    }
}

/// A reference from the arena to a host value, checked on every access.
pub struct HostRef<'gc, T: 'static> {
    id: HostId,
    _marker: PhantomData<(Invariant<'gc>, fn() -> T)>,
}

impl<'gc, T: 'static> HostRef<'gc, T> {
    pub fn get(self, mc: &Mutation<'gc>) -> Option<&'gc T> {
        // SAFETY: [steps] `get` checked the slot's generation and type. The box doesn't move or get
        // freed until a collection, which can't run while `mc` is borrowed for `'gc`.
        mc.heap.hosts.get::<T>(self.id).map(|p| unsafe { p.as_ref() })
    }

    #[cfg(test)]
    pub(crate) fn to_bits_for_test(self) -> (u32, u32) {
        (self.id.index, self.id.generation)
    }

    #[cfg(test)]
    pub(crate) fn from_bits_for_test((index, generation): (u32, u32)) -> Self {
        Self { id: HostId { index, generation }, _marker: PhantomData }
    }
}

impl<T> Clone for HostRef<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for HostRef<'_, T> {}

impl<T> fmt::Debug for HostRef<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "HostRef({:?})", self.id)
    }
}

// SAFETY: [plain, brand] a `HostId`, two `u32`s, and a marker, so no padding and every bit pattern
// valid: a bad id just fails to look up. The brand is `'gc`.
unsafe impl<'gc, T> Plain<'gc> for HostRef<'gc, T> {}

// SAFETY: [trace] traces the one host reference it holds.
unsafe impl<T> Trace for HostRef<'_, T> {
    fn trace(&mut self, t: &mut Tracer<'_>) {
        t.trace_host(self.id);
    }
}

/// A reference to a host value of any type. Downcasts check the type.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct AnyHostRef<'gc> {
    id: HostId,
    _brand: Invariant<'gc>,
}

impl<'gc> AnyHostRef<'gc> {
    pub fn is<T: 'static>(self, mc: &Mutation<'gc>) -> bool {
        self.downcast_ref::<T>(mc).is_some()
    }

    /// The value, if it's still alive and a `T`.
    pub fn downcast_ref<T: 'static>(self, mc: &Mutation<'gc>) -> Option<&'gc T> {
        self.downcast::<T>(mc)?.get(mc)
    }

    pub fn downcast<T: 'static>(self, mc: &Mutation<'gc>) -> Option<HostRef<'gc, T>> {
        mc.heap.hosts.get::<T>(self.id)?;
        Some(HostRef { id: self.id, _marker: PhantomData })
    }
}

impl<'gc, T> From<HostRef<'gc, T>> for AnyHostRef<'gc> {
    fn from(r: HostRef<'gc, T>) -> Self {
        Self { id: r.id, _brand: PhantomData }
    }
}

impl fmt::Debug for AnyHostRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AnyHostRef({:?})", self.id)
    }
}

// SAFETY: as for `HostRef`.
unsafe impl<'gc> Plain<'gc> for AnyHostRef<'gc> {}

// SAFETY: as for `HostRef`.
unsafe impl Trace for AnyHostRef<'_> {
    fn trace(&mut self, t: &mut Tracer<'_>) {
        t.trace_host(self.id);
    }
}

impl<'gc> Mutation<'gc> {
    /// Moves `value` into the host table. It's dropped once nothing in the arena reaches it.
    pub fn host<T: 'static>(&self, value: T) -> Result<HostRef<'gc, T>, OutOfMemory> {
        self.heap.budget.count_allocation()?;
        let cost = size_of::<T>();
        let marked = self.heap.is_marking();
        let id = self.heap.hosts.insert(&self.heap.budget, Box::new(value), cost, marked)?;
        self.heap.demand(cost);
        Ok(HostRef { id, _marker: PhantomData })
    }
}
