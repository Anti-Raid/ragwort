//! Marking: the gray stack, tracing, roots and ephemerons.

use std::cell::Cell;
use std::rc::Rc;

use crate::layout::{Addr, GRANULE, LINE, VTable};
use crate::root::ROOT_COST;
use crate::trace::Mode;
use crate::{Trace, Tracer};
use super::object::Obj;
use super::pages::{Kind, OVERFLOW, PENDING, PageIndex, each_bit};
use super::{Collecting, Heap};

const GRAY_CAPACITY: usize = 1024;

/// The gray stack has a fixed size, charged when the arena is made.
pub(crate) const GRAY_BYTES: usize = GRAY_CAPACITY * size_of::<u32>();

/// Marked objects whose contents still need tracing. When it's full, their pages are flagged
/// [`OVERFLOW`] instead, and traced whole.
pub(super) struct Gray {
    stack: Box<[Cell<u32>; GRAY_CAPACITY]>,
    len: Cell<usize>,
    limit: Cell<usize>,
    overflowed: Cell<bool>,
}

impl Gray {
    pub(super) fn new() -> Self {
        Self {
            stack: Box::new([const { Cell::new(0) }; GRAY_CAPACITY]),
            len: Cell::new(0),
            limit: Cell::new(GRAY_CAPACITY),
            overflowed: Cell::new(false),
        }
    }
}

impl Heap {
    #[inline]
    pub(super) fn is_marked(&self, obj: Obj) -> bool {
        self.page(obj.page).mark.get(obj.granule)
    }

    /// Whether `offset` is a marked object. A bad offset marks the arena corrupted and
    /// counts as live, so nothing is cleared because of it.
    pub(crate) fn is_live(&self, offset: u32) -> bool {
        match self.object_at(offset) {
            Some(obj) => self.is_marked(obj),
            None => {
                self.corrupt();
                true
            }
        }
    }

    #[inline]
    pub(super) fn mark_object(&self, obj: Obj, size: usize) {
        let p = self.page(obj.page);
        p.mark.set(obj.granule);
        if p.kind.get() == Kind::Lines {
            let at = obj.granule * GRANULE;
            p.marked_lines.set_range(at / LINE, (at + size).div_ceil(LINE));
        }
        self.stats.marks.set(self.stats.marks.get() + 1);
    }

    #[inline]
    pub(super) fn push_gray(&self, offset: u32, page: PageIndex) {
        let len = self.gray.len.get();
        if len < self.gray.limit.get() {
            self.gray.stack[len].set(offset);
            self.gray.len.set(len + 1);
        } else {
            self.page(page).add(OVERFLOW);
            self.gray.overflowed.set(true);
        }
    }

    #[inline]
    fn pop_gray(&self) -> Option<u32> {
        let len = self.gray.len.get().checked_sub(1)?;
        self.gray.len.set(len);
        Some(self.gray.stack[len].get())
    }

    pub(crate) fn shade(&self, offset: u32) {
        let Some(obj) = self.object_at(offset) else { return self.corrupt() };
        if self.is_marked(obj) {
            return;
        }
        let Some((vtable, size)) = self.size_of(obj) else { return self.corrupt() };
        self.mark_object(obj, size);
        if vtable.needs_trace {
            self.push_gray(offset, obj.page);
        }
    }

    /// Flags the page holding the object with an ephemeron whose key isn't marked yet.
    pub(crate) fn pending(&self, slot: Addr) {
        if let Some(page) = self.offset_of(slot).and_then(|offset| self.page_of(offset)) {
            self.page(self.page(page).head(page)).add(PENDING);
        }
    }

    /// Traces an object's contents, or only what overlaps `range` of it. Returns its size.
    pub(super) fn trace_object(&self, offset: u32, mode: Mode, range: Option<(usize, usize)>) -> usize {
        let Some(obj) = self.object_at(offset) else {
            self.corrupt();
            return 0;
        };
        let Some((vtable, size)) = self.size_of(obj) else {
            self.corrupt();
            return 0;
        };
        self.trace_with(obj, vtable, range, &mut Tracer::new(self, mode));
        size
    }

    /// The vtable matches the object's header and its size fits where it sits. Collections
    /// only run between steps, when nothing borrows arena memory, so tracing may take `&mut`.
    pub(super) fn trace_with(&self, obj: Obj, vtable: &VTable, range: Option<(usize, usize)>, t: &mut Tracer<'_>) {
        let header = self.header_ptr(obj.offset);
        match range {
            // SAFETY: as above, the header starts an object of the vtable's type, which
            // nothing else references while it's traced.
            Some((from, to)) => unsafe { (vtable.trace_range)(header, from, to, t) },
            // SAFETY: as for `trace_range`.
            None => unsafe { (vtable.trace)(header, t) },
        }
    }

    /// Traces every marked object whose header is on `page`, whole.
    fn trace_marked(&self, page: PageIndex, mode: Mode) -> usize {
        let mut work = 0;
        each_bit(&self.page(page).live(), |g| work += self.trace_object(page.granule(g), mode, None));
        work.max(1)
    }

    /// Traces gray objects until about `budget` bytes are done. Returns what's left.
    pub(super) fn drain(&self, budget: usize) -> usize {
        let mut left = budget;
        loop {
            while left > 0 && !self.corrupted.get() {
                let Some(offset) = self.pop_gray() else { break };
                left = left.saturating_sub(self.trace_object(offset, Mode::Mark, None).max(1));
            }
            if left == 0 || self.corrupted.get() || !self.gray.overflowed.replace(false) {
                return left;
            }
            for page in self.page_indexes() {
                if self.page(page).remove(OVERFLOW) {
                    left = left.saturating_sub(self.trace_marked(page, Mode::Mark));
                }
            }
        }
    }

    /// Traces the values of ephemerons whose keys got marked, until nothing new is marked.
    fn settle_ephemerons(&self) {
        loop {
            let before = self.stats.marks.get();
            let mut any = false;
            for page in self.page_indexes() {
                if self.page(page).remove(PENDING) {
                    any = true;
                    self.trace_marked(page, Mode::Mark);
                }
            }
            self.drain(usize::MAX);
            if !any || self.stats.marks.get() == before || self.corrupted.get() {
                return;
            }
        }
    }

    /// Clears ephemerons whose keys stayed unmarked.
    pub(super) fn clear_dead_ephemerons(&self) {
        for page in self.page_indexes() {
            if self.page(page).remove(PENDING) {
                self.trace_marked(page, Mode::Clear);
            }
        }
    }

    pub(super) fn trace_roots<R: Trace>(&self, root: &mut R, mode: Mode, c: &Collecting) {
        let mut t = Tracer::new(self, mode);
        root.trace(&mut t);
        let mut roots = self.roots.borrow_mut();
        let before = roots.len();
        roots.retain(|entry| Rc::strong_count(entry) > 1);
        self.budget.refund((before - roots.len()) * ROOT_COST);
        roots.shrink(&self.budget);
        for entry in roots.iter() {
            entry.trace(&mut t);
        }
        let mut stacks = self.stacks.borrow_mut();
        for stack in stacks.iter() {
            stack.trace(self, &mut t, c);
        }
        // A dropped stack's frames were written without a barrier, so it's only let go after
        // this last trace.
        if mode == Mode::Mark {
            let before = stacks.len();
            stacks.retain(|stack| Rc::strong_count(stack) > 1);
            self.budget.refund((before - stacks.len()) * ROOT_COST);
            stacks.shrink(&self.budget);
        }
    }

    /// Marks everything reachable that isn't marked yet, and settles ephemerons.
    pub(super) fn mark_all<R: Trace>(&self, root: &mut R, c: &Collecting) -> usize {
        self.trace_roots(root, Mode::Mark, c);
        self.scan_cards(Mode::Mark);
        let work = 1 + (usize::MAX - self.drain(usize::MAX));
        self.settle_ephemerons();
        #[cfg(any(test, feature = "gc-verify"))]
        self.verify(root, c);
        work
    }

    #[cfg(test)]
    pub(super) fn gray_is_empty(&self) -> bool {
        !self.gray.overflowed.get() && self.gray.len.get() == 0
    }

    #[cfg(test)]
    pub(crate) fn set_gray_limit(&self, limit: usize) {
        self.gray.limit.set(limit.min(GRAY_CAPACITY));
    }

    /// Whether the object is marked, which outside a major cycle means it survived a collection.
    #[cfg(test)]
    pub(crate) fn is_old(&self, offset: u32) -> bool {
        self.object_at(offset).is_some_and(|obj| self.is_marked(obj))
    }
}
