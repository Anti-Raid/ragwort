use std::fmt;
use std::marker::PhantomData;
use std::mem::ManuallyDrop;
use std::ptr::NonNull;

use super::heap::{Heap, Made};
use super::layout;
use super::{Charge, Gc, Inline, Invariant, OutOfMemory, Plain, Trace};

const STEP_MUL: usize = 2;
const MIN_SLICE: usize = 64 * 1024;

pub trait Rootable: 'static {
    type Root<'gc>: Trace;
}

/// The collector found the heap in an impossible state, from a bug, damaged memory, or a
/// `Trace` impl that panicked. References may be half rewritten, so the arena can't be entered
/// again and should be dropped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Corrupted;

impl fmt::Display for Corrupted {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("arena is corrupted")
    }
}

impl std::error::Error for Corrupted {}

#[derive(Debug)]
pub enum StepError<E> {
    OutOfMemory,
    /// The collector found the heap in an impossible state. The arena should be dropped.
    Corrupted,
    Failed(E),
}

impl<E> From<Corrupted> for StepError<E> {
    fn from(_: Corrupted) -> Self {
        Self::Corrupted
    }
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
    /// The last bytes under `limit` kept for steps to finish in. See [`Arena::set_reserve`].
    pub reserve: usize,
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
        // SAFETY: [brand] `Root<'gc>` differs from `Root<'static>` only in a brand, which changes
        // neither layout nor validity. The root is read once out of the `ManuallyDrop`, so it
        // isn't dropped twice, and stored beside the heap its handles refer to.
        let root = unsafe { (&raw const *root).cast::<R::Root<'static>>().read() };
        Ok(Self { root, heap })
    }

    /// Runs `f` with the root. Fails without running it if the arena is corrupted, and drops
    /// its result if the arena was found corrupted while it ran, since it may have read damaged
    /// data.
    pub fn mutate<T>(&mut self, f: impl for<'gc> FnOnce(&Mutation<'gc>, &R::Root<'gc>) -> T) -> Result<T, Corrupted> {
        self.check()?;
        // SAFETY: [brand, unwind] only the brand changes. `f` is generic over `'gc`, so the root's
        // handles can only meet the `Mutation` of this heap, and neither outlives the call. The
        // arena isn't corrupted, so every reference the root reaches was fully rewritten.
        let root = unsafe { &*(&raw const self.root).cast::<R::Root<'_>>() };
        let result = f(&Mutation::new(&self.heap), root);
        self.check().map(|()| result)
    }

    /// [`Arena::mutate`] with the root borrowed mutably.
    pub fn mutate_root<T>(&mut self, f: impl for<'gc> FnOnce(&Mutation<'gc>, &mut R::Root<'gc>) -> T) -> Result<T, Corrupted> {
        self.check()?;
        // SAFETY: [brand] as in `mutate`. The root is borrowed mutably through `&mut self`, so
        // nothing else reads it meanwhile.
        let root = unsafe { &mut *(&raw mut self.root).cast::<R::Root<'_>>() };
        let result = f(&Mutation::new(&self.heap), root);
        self.check().map(|()| result)
    }

    #[inline(always)]
    fn check(&self) -> Result<(), Corrupted> {
        if self.heap.corrupted() { Err(Corrupted) } else { Ok(()) }
    }

    /// Runs `f` once, then a slice of collection work, or a full collection if `f` drew on
    /// the reserve (see [`Mutation::collection_due`]). If an allocation failed, even one `f`
    /// went on without, the result is dropped, a full collection runs, and the step fails
    /// with [`StepError::OutOfMemory`]. Whatever `f` did before the failure stays done, so
    /// the caller picks up from there: an interpreter runs the failed instruction again, which
    /// is safe if the instruction changes nothing before its allocations succeed.
    pub fn step<T, E>(&mut self, f: impl for<'gc> FnOnce(&Mutation<'gc>, &R::Root<'gc>) -> Result<T, E>) -> Result<T, StepError<E>> {
        self.heap.budget.clear_failed();
        let result = self.mutate(f)?;
        if self.heap.budget.failed() {
            drop(result);
            self.collect();
            return Err(if self.heap.corrupted() { StepError::Corrupted } else { StepError::OutOfMemory });
        }
        if self.heap.budget.collection_due() {
            self.collect();
        } else {
            self.pace();
        }
        self.check()?;
        result.map_err(StepError::Failed)
    }

    fn pace(&mut self) {
        let heap = &mut *self.heap;
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

    /// Keeps the last `bytes` under the limit for a step to finish in once the rest is used,
    /// so a heap full of garbage doesn't fail the step. Optional allocations, such as a
    /// vector growing by more than it needs, don't draw on it. It starts at a sixteenth of
    /// the limit.
    pub fn set_reserve(&mut self, bytes: usize) {
        self.heap.budget.set_reserve(bytes);
    }

    /// Finishes any cycle in progress, then runs a full one.
    pub fn collect(&mut self) {
        self.finish();
        self.heap.start(&mut self.root);
        self.finish();
        self.heap.clear_allocated();
        self.heap.budget.clear_due();
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
            reserve: heap.budget.reserve(),
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

    /// Testing: lets `allocations` more allocations through, then fails the next one, once.
    /// Objects, inline objects, host values and roots all count.
    #[doc(hidden)]
    pub fn fail_after(&mut self, allocations: Option<u64>) {
        self.heap.budget.fail_after(allocations);
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

/// The largest length [`Mutation::alloc_inline`] accepts for `T`, or 0 if it can't allocate `T`.
pub const fn max_items<T: Inline>() -> usize {
    if layout::fits_inline::<T>() { layout::max_items::<T>() } else { 0 }
}

impl<'gc> Mutation<'gc> {
    fn new(heap: &'gc Heap) -> Self {
        Self { heap, base: heap.base, _brand: PhantomData }
    }

    pub fn alloc<T: Trace + Plain<'gc> + 'gc>(&self, value: T) -> Result<Gc<'gc, T>, OutOfMemory> {
        self.heap.alloc(value).map(|ptr| self.made(ptr))
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
        self.heap.alloc_inline(head, len, fill).map(|ptr| self.made(ptr))
    }

    pub fn alloc_inline_from<T: Inline + Plain<'gc> + 'gc>(&self, head: T, items: &[T::Item]) -> Result<Gc<'gc, T>, OutOfMemory>
    where
        T::Item: Plain<'gc> + Copy,
    {
        self.alloc_inline(head, items.len(), |i| items[i])
    }

    /// Allocates `len` items set to `item`, lets `init` fill them in, and keeps the first
    /// items as many as `init` returns. For results whose length is only known once computed.
    pub fn alloc_inline_with<T: Inline + Plain<'gc> + 'gc>(
        &self,
        head: T,
        len: usize,
        item: T::Item,
        init: impl FnOnce(&mut [T::Item]) -> usize,
    ) -> Result<Gc<'gc, T>, OutOfMemory>
    where
        T::Item: Plain<'gc> + Copy,
    {
        self.heap.alloc_inline_with(head, len, item, init).map(|ptr| self.made(ptr))
    }

    /// Runs allocations the caller can do without, such as growing a buffer by more than it
    /// needs: failing them doesn't fail the step, and they don't draw on the reserve.
    pub fn optional<R>(&self, f: impl FnOnce() -> Result<R, OutOfMemory>) -> Result<R, OutOfMemory> {
        self.heap.budget.quiet(f)
    }

    /// Fails the step as a failed allocation would, for a request too large to even size.
    pub fn out_of_memory(&self) -> OutOfMemory {
        self.heap.budget.fail()
    }

    fn made<T: Plain<'gc>>(&self, new: Made<T>) -> Gc<'gc, T> {
        // SAFETY: [memory] only the heap's builder makes a `Made`, for the value of an object it
        // just finished in this arena's region.
        unsafe { Gc::from_raw(new.get()) }
    }

    /// Has `object` traced again before the next collection finishes. Call it in the same
    /// step as any `Lock::set_unbarriered` on the object's fields.
    #[cfg(test)]
    pub(crate) fn retrace<T>(&self, object: Gc<'gc, T>) {
        self.heap.retrace(super::Member::new(self, object).to_bits().get());
    }

    /// Whether an allocation has drawn on the reserve, so a full collection is due. An
    /// interpreter checks it between instructions and ends the step, which collects.
    pub fn collection_due(&self) -> bool {
        self.heap.budget.collection_due()
    }

    /// A charge of nothing yet against the budget, for memory kept outside the arena. See
    /// [`Charge`].
    pub fn charge(&self) -> Charge<'gc> {
        Charge::new(&self.heap.budget)
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
