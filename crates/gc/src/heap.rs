//! The heap: one arena's region of objects and the collector for it, in parts that each keep
//! their own state.

mod pages;
mod object;
mod types;
mod space;
mod alloc;
mod mark;
mod barrier;
mod evacuate;
mod cycle;
mod stats;
#[cfg(any(test, feature = "gc-verify"))]
mod verify;
#[cfg(test)]
mod check;

use std::cell::{Cell, RefCell};
use std::ptr::NonNull;
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};

use super::budget::Budget;
use super::host::Hosts;
use super::layout::REGION;
use super::root::RootEntry;
use super::stack::StackRecord;
use super::table::Table;
use cycle::State;
use mark::Gray;
use pages::Pages;
use space::Space;
use stats::Stats;
use types::Types;

pub(crate) use alloc::Made;
#[cfg(any(test, feature = "gc-verify"))]
pub(crate) use verify::Verify;
pub(crate) use mark::GRAY_BYTES;
#[cfg(test)]
pub(crate) use pages::META;

static NEXT_ID: AtomicU64 = AtomicU64::new(1);

pub(crate) struct Heap {
    pub(crate) budget: Budget,
    pub(crate) id: u64,
    pub(crate) base: NonNull<u8>,
    space: Space,
    pages: Pages,
    types: Types,
    gray: Gray,
    state: Cell<State>,
    stats: Stats,
    pub(crate) roots: RefCell<Table<Rc<dyn RootEntry>>>,
    pub(crate) stacks: RefCell<Table<Rc<StackRecord>>>,
    pub(crate) hosts: Hosts,
    corrupted: Cell<bool>,
    pub(crate) stress: Cell<Option<usize>>,
    pub(crate) evacuate_all: Cell<bool>,
}

impl Heap {
    pub(crate) fn new(limit: usize) -> Option<Self> {
        let space = Space::new()?;
        let limit = limit.min(REGION);
        let budget = Budget::new(limit);
        budget.charge(GRAY_BYTES).ok()?;
        Some(Self {
            budget,
            id: NEXT_ID.fetch_add(1, Ordering::Relaxed),
            base: space.base(),
            space,
            pages: Pages::new(),
            types: Types::new(),
            gray: Gray::new(),
            state: Cell::new(State::Idle),
            stats: Stats::new(limit),
            roots: RefCell::new(Table::new()),
            stacks: RefCell::new(Table::new()),
            hosts: Hosts::new(),
            corrupted: Cell::new(false),
            stress: Cell::new(None),
            evacuate_all: Cell::new(false),
        })
    }

    pub(crate) fn corrupted(&self) -> bool {
        self.corrupted.get()
    }

    pub(crate) fn corrupt(&self) {
        self.corrupted.set(true);
    }
}

/// Tables the heap fills in as it grows. Zeroed memory comes from the allocator untouched,
/// so the OS only commits the parts that get used.
///
/// # Safety
/// All-zero bytes must be a valid value of the type.
unsafe trait Zeroed {}

fn zeroed<T: Zeroed>() -> Box<T> {
    // SAFETY: `Zeroed` promises all-zero bytes are a valid `T`.
    unsafe { Box::new_zeroed().assume_init() }
}

/// A panic in user `Trace` code would leave a collection half done, so the heap can't be trusted.
struct CorruptOnUnwind<'a>(&'a Heap);

impl Drop for CorruptOnUnwind<'_> {
    fn drop(&mut self) {
        self.0.corrupt();
    }
}

/// Proof that a collection is running, which only the heap's collection entry points make.
/// They take the heap mutably, so no step is running and nothing borrows arena memory.
pub(crate) struct Collecting(());
