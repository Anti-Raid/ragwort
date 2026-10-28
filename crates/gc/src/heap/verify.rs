//! Checked builds' check of marking: that everything reachable is marked, and nothing reachable
//! moved.

use crate::layout::GRANULE;
use crate::{Trace, Tracer};
use super::pages::PageIndex;
use super::{Collecting, Heap};

pub(crate) struct Verify {
    seen: Vec<u64>,
    work: Vec<u32>,
}

impl Verify {
    /// A visitor with room for every object in the heap's pages.
    pub(crate) fn new(heap: &Heap) -> Self {
        let words = PageIndex::at(heap.page_count()).start() / GRANULE / 64 + 1;
        Self { seen: vec![0; words], work: Vec::new() }
    }

    /// How many distinct objects it was shown and hasn't checked yet.
    #[cfg(test)]
    pub(crate) fn visited(&self) -> usize {
        self.work.len()
    }

    pub(crate) fn visit(&mut self, heap: &Heap, offset: u32) {
        if heap.object_at(offset).is_none() {
            return heap.corrupt();
        }
        let bit = offset as usize / GRANULE;
        let (word, mask) = (bit / 64, 1u64 << (bit % 64));
        if self.seen[word] & mask == 0 {
            self.seen[word] |= mask;
            self.work.push(offset);
        }
    }
}

impl Heap {
    /// Asserts that everything the roots reach is marked and was not moved.
    pub(super) fn verify<R: Trace>(&self, root: &mut R, c: &Collecting) {
        if self.corrupted.get() {
            return;
        }
        let mut v = Verify::new(self);
        root.trace(&mut Tracer::verifying(self, &mut v));
        for entry in self.roots.borrow().iter() {
            entry.trace(&mut Tracer::verifying(self, &mut v));
        }
        for stack in self.stacks.borrow().iter() {
            stack.trace(self, &mut Tracer::verifying(self, &mut v), c);
        }
        while let Some(offset) = v.work.pop() {
            if self.corrupted.get() {
                return;
            }
            let Some(obj) = self.object_at(offset) else { return self.corrupt() };
            assert!(self.is_marked(obj), "gc verify: reachable object {offset:#x} is not marked");
            assert!(!self.moved(offset), "gc verify: reachable object {offset:#x} was moved");
            let Some((vtable, _)) = self.size_of(obj) else { return self.corrupt() };
            self.trace_with(obj, vtable, None, &mut Tracer::verifying(self, &mut v));
        }
    }
}
