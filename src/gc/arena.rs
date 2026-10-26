use std::marker::PhantomData;
use std::mem::ManuallyDrop;
use std::ptr::NonNull;

use super::heap::Heap;
use super::{Gc, Inline, Invariant, Member, OutOfMemory, Plain, Trace};

const STEP_MUL: usize = 2;
const MIN_SLICE: usize = 64 * 1024;

pub trait Rootable: 'static {
    type Root<'gc>: Trace;
}

#[derive(Debug)]
pub enum StepError<E> {
    OutOfMemory,
    /// The collector found the heap in an impossible state. The arena should be dropped.
    Corrupted,
    Failed(E),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Phase {
    Idle,
    Marking,
    Sweeping,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Metrics {
    /// Bytes charged: committed pages, page metadata, roots and host values.
    pub used: usize,
    pub peak: usize,
    pub limit: usize,
    /// Bytes in lines and page runs the allocator can't hand out: live objects, garbage not
    /// yet swept, and the rest of the run being allocated into.
    pub live: usize,
    pub objects: usize,
    pub pages: usize,
    pub hosts: usize,
    /// Full (major) collections finished.
    pub collections: u64,
    /// Young-only collections finished.
    pub minor_collections: u64,
    /// The next major cycle starts once `used` reaches this.
    pub threshold: usize,
    pub phase: Phase,
    pub corrupted: bool,
}

// The root is declared first so it's dropped before the heap.
pub struct Arena<R: Rootable> {
    root: R::Root<'static>,
    heap: Box<Heap>,
}

impl<R: Rootable> Arena<R> {
    pub fn new(
        limit: usize,
        init: impl for<'gc> FnOnce(&Mutation<'gc>) -> Result<R::Root<'gc>, OutOfMemory>,
    ) -> Result<Self, OutOfMemory> {
        let heap = Box::new(Heap::new(limit).ok_or(OutOfMemory)?);
        let root = ManuallyDrop::new(init(&Mutation::new(&heap))?);
        let root = unsafe { (&raw const *root).cast::<R::Root<'static>>().read() };
        Ok(Self { root, heap })
    }

    pub fn mutate<T>(&mut self, f: impl for<'gc> FnOnce(&Mutation<'gc>, &R::Root<'gc>) -> T) -> T {
        let root = unsafe { &*(&raw const self.root).cast::<R::Root<'_>>() };
        f(&Mutation::new(&self.heap), root)
    }

    pub fn mutate_root<T>(&mut self, f: impl for<'gc> FnOnce(&Mutation<'gc>, &mut R::Root<'gc>) -> T) -> T {
        let root = unsafe { &mut *(&raw mut self.root).cast::<R::Root<'_>>() };
        f(&Mutation::new(&self.heap), root)
    }

    /// Runs `f`, then a slice of collection work. If any allocation failed, the result is
    /// discarded, a full collection runs, and `f` runs once more, so `f` must not change
    /// existing objects before an allocation that can fail.
    pub fn step<T, E>(
        &mut self,
        mut f: impl for<'gc> FnMut(&Mutation<'gc>, &R::Root<'gc>) -> Result<T, E>,
    ) -> Result<T, StepError<E>> {
        let mut retried = false;
        loop {
            if self.heap.corrupted() {
                return Err(StepError::Corrupted);
            }
            self.heap.budget.clear_failed();
            let result = self.mutate(|mc, root| f(mc, root));
            if !self.heap.budget.failed() {
                self.pace();
                if self.heap.corrupted() {
                    return Err(StepError::Corrupted);
                }
                return result.map_err(StepError::Failed);
            }
            drop(result);
            if retried {
                return Err(StepError::OutOfMemory);
            }
            self.collect();
            retried = true;
        }
    }

    fn pace(&mut self) {
        let heap = &*self.heap;
        let root = &mut self.root;
        let allocated = heap.take_allocated();
        if let Some(work) = heap.stress.get() {
            heap.minor(root);
            heap.start(root);
            heap.work(root, work);
            return;
        }
        // A minor collection comes first, so a major cycle only starts if what survives
        // young collections has grown past the threshold.
        let due = heap.young() >= heap.nursery() || heap.budget.used() >= heap.threshold();
        if heap.phase() == Phase::Idle && due && heap.young() > 0 {
            heap.minor(root);
        }
        if heap.phase() == Phase::Idle && heap.budget.used() >= heap.threshold() {
            heap.start(root);
        }
        if heap.phase() != Phase::Idle {
            heap.work(root, allocated.saturating_mul(STEP_MUL).max(MIN_SLICE));
        }
    }

    /// Finishes any cycle in progress, then runs a full one.
    pub fn collect(&mut self) {
        self.finish();
        self.heap.start(&mut self.root);
        self.finish();
        self.heap.clear_allocated();
    }

    /// Collects young objects only, if no major cycle is running.
    pub fn collect_minor(&mut self) {
        self.heap.minor(&mut self.root);
    }

    fn finish(&mut self) {
        while self.heap.phase() != Phase::Idle && !self.heap.corrupted() {
            self.heap.work(&mut self.root, usize::MAX);
        }
    }

    /// Starts a cycle if none is running, then does about `work` bytes of it.
    pub fn collect_slice(&mut self, work: usize) {
        self.heap.start(&mut self.root);
        self.heap.work(&mut self.root, work);
    }

    /// Runs a cycle slice of `work` bytes after every step, for testing barriers.
    #[doc(hidden)]
    pub fn set_stress(&mut self, work: Option<usize>) {
        self.heap.stress.set(work);
    }

    pub fn metrics(&self) -> Metrics {
        let heap = &*self.heap;
        Metrics {
            used: heap.budget.used(),
            peak: heap.budget.peak(),
            limit: heap.budget.limit(),
            live: heap.live(),
            objects: heap.objects(),
            pages: heap.committed(),
            hosts: heap.hosts.len(),
            collections: heap.collections(),
            minor_collections: heap.minor_collections(),
            threshold: heap.threshold(),
            phase: heap.phase(),
            corrupted: heap.corrupted(),
        }
    }

    /// Testing: compact every page in each major cycle.
    #[doc(hidden)]
    pub fn set_evacuate_all(&mut self, on: bool) {
        self.heap.evacuate_all.set(on);
    }

    #[cfg(test)]
    pub(crate) fn heap(&self) -> &Heap {
        &self.heap
    }
}

pub struct Mutation<'gc> {
    pub(crate) heap: &'gc Heap,
    pub(crate) base: NonNull<u8>,
    _brand: Invariant<'gc>,
}

impl<'gc> Mutation<'gc> {
    fn new(heap: &'gc Heap) -> Self {
        Self { heap, base: heap.base, _brand: PhantomData }
    }

    pub fn alloc<T: Trace + Plain<'gc> + 'gc>(&self, value: T) -> Result<Gc<'gc, T>, OutOfMemory> {
        let ptr = self.heap.alloc(value)?;
        Ok(unsafe { Gc::from_raw(ptr) })
    }

    pub fn alloc_inline<T: Inline + Plain<'gc> + 'gc>(
        &self,
        head: T,
        len: usize,
        fill: impl FnMut(usize) -> T::Item,
    ) -> Result<Gc<'gc, T>, OutOfMemory>
    where
        T::Item: Plain<'gc>,
    {
        let ptr = self.heap.alloc_inline(head, len, fill)?;
        Ok(unsafe { Gc::from_raw(ptr) })
    }

    pub fn alloc_inline_from<T: Inline + Plain<'gc> + 'gc>(&self, head: T, items: &[T::Item]) -> Result<Gc<'gc, T>, OutOfMemory>
    where
        T::Item: Plain<'gc> + Copy,
    {
        self.alloc_inline(head, items.len(), |i| items[i])
    }

    /// Has `object` traced again before the next collection finishes. Call it in the same
    /// step as any `Lock::set_unbarriered` on the object's fields, after the last such write.
    pub fn retrace<T>(&self, object: Gc<'gc, T>) {
        self.heap.retrace(Member::new(self, object).to_bits().get());
    }

    pub fn ensure(&self, bytes: usize) -> Result<(), OutOfMemory> {
        self.heap.budget.ensure(bytes)
    }

    pub fn used(&self) -> usize {
        self.heap.budget.used()
    }

    pub fn limit(&self) -> usize {
        self.heap.budget.limit()
    }
}
