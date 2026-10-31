use std::cell::Cell;
use std::fmt;
use std::marker::PhantomData;
use std::mem::size_of_val;
use std::num::NonZeroU32;
use std::ops::{Index, Range};
use std::ptr;
use std::rc::Rc;

use super::heap::{Collecting, Heap};
use super::root::ROOT_COST;
use super::trace::Mode;
use super::{Gc, Inline, Lock, Member, Mutation, OutOfMemory, Plain, Trace, Tracer, Value};

/// The registers a frame can address, so a `u8` register number always indexes in bounds.
pub const WINDOW: usize = 256;

/// One segment of a [`Stack`]: a run of value slots in the arena.
#[derive(Plain)]
pub struct Segment<'gc> {
    /// Set while a stack uses the segment. A stack that was dropped leaves it set, so a set
    /// flag is checked against the live stacks.
    attached: Lock<u32>,
    /// Slots exposed through `Gc::items` lie below this, so they're voided above `top` like
    /// frames. Frames keep their own bound in the stack's record.
    written: Lock<u32>,
    _brand: PhantomData<Value<'gc>>,
}

impl<'gc> Segment<'gc> {
    /// A segment of `len` void slots. Frames need [`WINDOW`] slots from their base.
    pub fn new(mc: &Mutation<'gc>, len: usize) -> Result<Gc<'gc, Self>, OutOfMemory> {
        let head = Segment { attached: Lock::new(0), written: Lock::new(0), _brand: PhantomData };
        mc.alloc_inline(head, len, |_| Lock::new(Value::VOID))
    }
}

// SAFETY: the head contains only integers and a brand; the heap traces the inline values.
unsafe impl Trace for Segment<'_> {
    const NEEDS_TRACE: bool = false;
    const INLINE: bool = true;

    fn trace(&mut self, _: &mut Tracer<'_>) {}
}

// SAFETY: `Trace` covers only the head; the items are traced by the heap.
unsafe impl<'gc> Inline for Segment<'gc> {
    type Item = Lock<Value<'gc>>;

    fn items_accessed(&self, len: usize) {
        self.note_written(len);
    }
}

impl Segment<'_> {
    fn note_written(&self, end: usize) {
        // SAFETY: this is an integer, so the write introduces no reference needing a barrier.
        unsafe { self.written.set_unbarriered(self.written.get().max(end.min(u32::MAX as usize) as u32)) };
    }
}

/// Marks `segment` as used by the stack with `record`. Panics if another live stack uses it.
fn attach<'gc>(mc: &Mutation<'gc>, segment: Gc<'gc, Segment<'gc>>, record: &StackRecord) {
    if segment.attached.get() != 0 {
        let offset = Member::new(mc, segment).to_bits();
        let stacks = mc.heap.stacks.borrow();
        for other in stacks.iter().filter(|s| s.segment.get() == offset && !ptr::eq(&***s, record)) {
            assert!(Rc::strong_count(other) == 1, "segment is already in use by another stack");
            // A dropped stack still waiting for its last trace. Retiring it now means that trace
            // can't void what the new stack writes.
            other.retire(mc, segment);
            other.parked.set(true);
        }
    }
    segment.attached.set(mc, 1);
}

/// What the collector knows about a stack. The heap holds one reference and the [`Stack`]
/// the other.
pub(crate) struct StackRecord {
    segment: Cell<NonZeroU32>,
    base: Cell<u32>,
    top: Cell<u32>,
    parked: Cell<bool>,
    /// Slots frames wrote without a barrier lie below this. It's kept here, outside the arena,
    /// so taking a frame doesn't touch the segment.
    written: Cell<u32>,
    #[cfg(test)]
    cleared: Cell<usize>,
}

impl StackRecord {
    /// `base..top`, clamped to a segment of `len` slots.
    fn live(&self, len: usize) -> Range<usize> {
        let base = (self.base.get() as usize).min(len);
        base..(self.top.get() as usize).clamp(base, len)
    }

    /// Where the slots that may need voiding end: the higher of the bound frames keep here and
    /// the one `Gc::items` keeps in the segment, clamped to `live.end..len`.
    fn written_end(&self, segment: u32, live: &Range<usize>, len: usize) -> usize {
        (self.written.get().max(segment) as usize).min(len).max(live.end)
    }

    /// Traces the segment and the live slots, and voids the slots above `top`, which were
    /// written without a barrier and aren't traced.
    pub(crate) fn trace(&self, heap: &Heap, t: &mut Tracer<'_>, c: &Collecting) {
        let mut segment = self.segment.get();
        t.member(&mut segment);
        self.segment.set(segment);
        if self.parked.get() {
            return;
        }
        // SAFETY: [steps, alias] the collection holds no other view of the segment's slots while
        // this one is used, and the `Collecting` token means no step does either.
        let Some((head, slots)) = (unsafe { heap.inline_mut::<Segment<'static>>(segment.get(), c) }) else {
            return heap.corrupt();
        };
        let live = self.live(slots.len());
        for slot in &mut slots[live.clone()] {
            slot.get_mut().trace(t);
        }
        if t.mode() == Mode::Mark {
            let end = self.written_end(head.written.get(), &live, slots.len());
            #[cfg(test)]
            self.cleared.set(self.cleared.get() + end - live.end);
            for slot in &mut slots[live.end..end] {
                *slot.get_mut() = Value::VOID;
            }
            *head.written.get_mut() = live.end as u32;
            self.written.set(live.end as u32);
        }
    }

    /// Turns the live frames into ordinary arena memory: the barrier the writes skipped, for
    /// all of them at once. Slots above `top` are voided rather than traced.
    fn retire<'gc>(&self, mc: &Mutation<'gc>, segment: Gc<'gc, Segment<'gc>>) {
        if self.parked.get() {
            return;
        }
        // SAFETY: retirement only reads or clears slots; it never introduces new values.
        let slots = unsafe { segment.items_untracked() };
        let live = self.live(slots.len());
        Lock::barrier_range(mc, &slots[live.clone()], true);
        let end = self.written_end(segment.written.get(), &live, slots.len());
        #[cfg(test)]
        self.cleared.set(self.cleared.get() + end - live.end);
        Lock::fill(mc, &slots[live.end..end], Value::VOID);
        // Keep the bounds until collection: a raw item slice obtained earlier in this step
        // can still write after retirement without calling the access hook again.
    }
}

/// A VM stack made of [`Segment`]s, as in Chez Scheme. Frames on it are written without a
/// write barrier: the collector traces the live part, `base..top` of the current segment,
/// as a root in every collection.
///
/// Below `base` are frames handed to continuations by [`Stack::capture`]. They can only be
/// read through the stack; continuations copy them back with [`Stack::write`].
///
/// A stack holds no brand, so it can live outside the arena root, such as in a task. Using
/// it with another arena's [`Mutation`] panics.
pub struct Stack {
    arena: u64,
    record: Rc<StackRecord>,
}

impl<'gc> Mutation<'gc> {
    /// A stack on `segment`, with `base` 0 and `top` at the end of the segment. Panics if
    /// another stack uses the segment.
    pub fn stack(&self, segment: Gc<'gc, Segment<'gc>>) -> Result<Stack, OutOfMemory> {
        let budget = &self.heap.budget;
        budget.count_allocation()?;
        budget.ensure(ROOT_COST + self.heap.stacks.borrow().growth_cost(1))?;
        let record = Rc::new(StackRecord {
            segment: Cell::new(Member::new(self, segment).to_bits()),
            base: Cell::new(0),
            top: Cell::new(segment.len() as u32),
            parked: Cell::new(false),
            written: Cell::new(0),
            #[cfg(test)]
            cleared: Cell::new(0),
        });
        attach(self, segment, &record);
        let mut stacks = self.heap.stacks.borrow_mut();
        stacks.push(budget, record.clone())?;
        budget.charge(ROOT_COST)?;
        self.heap.demand(ROOT_COST);
        Ok(Stack { arena: self.heap.id, record })
    }
}

impl Stack {
    #[cfg(test)]
    pub(crate) fn cleared_slots(&self) -> usize {
        self.record.cleared.get()
    }

    fn slots<'s, 'gc: 's>(&'s self, mc: &Mutation<'gc>) -> &'s [Lock<Value<'gc>>] {
        // SAFETY: reads don't change slots; `live` records every range exposed for writes.
        unsafe { self.segment(mc).items_untracked() }
    }

    pub fn segment<'gc>(&self, mc: &Mutation<'gc>) -> Gc<'gc, Segment<'gc>> {
        assert_eq!(self.arena, mc.heap.id, "stack belongs to a different arena");
        // SAFETY: [refs, stacks] the record holds its segment's offset, which the collector traces
        // and rewrites when the segment moves, and the stack belongs to this arena.
        unsafe { Member::from_offset(self.record.segment.get()) }.get(mc)
    }

    /// Where the frames this stack can write start.
    pub fn base(&self) -> usize {
        self.record.base.get() as usize
    }

    /// Where the live frames end. Slots from `top` up are voided by the next collection.
    pub fn top(&self) -> usize {
        self.record.top.get() as usize
    }

    /// Set it before the step ends; within a step it doesn't matter. It unparks the stack, so
    /// the next collection voids what's above it.
    pub fn set_top(&self, top: usize) {
        self.record.top.set(top.try_into().unwrap_or(u32::MAX));
        self.record.parked.set(false);
    }

    /// The frame starting at slot `fp`, or `None` unless `base <= fp` and `fp + WINDOW` slots
    /// fit in the segment.
    #[inline]
    pub fn frame<'s, 'gc: 's>(&'s self, mc: &Mutation<'gc>, fp: usize) -> Option<Frame<'s, 'gc>> {
        Some(Frame { slots: self.live(mc, fp, <[_]>::first_chunk)? })
    }

    /// The slots `pick` takes from those from `at`, which must be at or above `base`, for
    /// writing without a barrier.
    #[inline]
    fn live<'s, 'gc: 's, S: ?Sized>(
        &'s self,
        mc: &Mutation<'gc>,
        at: usize,
        pick: impl FnOnce(&'s [Lock<Value<'gc>>]) -> Option<&'s S>,
    ) -> Option<Live<'s, S>> {
        if at < self.base() {
            return None;
        }
        let slots = pick(self.slots(mc).get(at..)?)?;
        let end = (at + size_of_val(slots) / size_of::<Lock<Value<'gc>>>()) as u32;
        self.record.written.set(self.record.written.get().max(end));
        self.record.parked.set(false);
        Some(Live(slots))
    }

    pub fn get<'gc>(&self, mc: &Mutation<'gc>, index: usize) -> Option<Value<'gc>> {
        self.slots(mc).get(index).map(Lock::get)
    }

    /// Sets a slot at or above `base`. Returns whether it was in range.
    pub fn set<'gc>(&self, mc: &Mutation<'gc>, index: usize, value: Value<'gc>) -> bool {
        let Some(slot) = self.live(mc, index, |slots| slots.first_chunk::<1>()) else { return false };
        slot.set(0, value);
        true
    }

    /// Copies `src` to the slots from `at`, which must be at or above `base`, such as frames
    /// of a continuation. Returns whether it was in range.
    pub fn write<'gc>(&self, mc: &Mutation<'gc>, at: usize, src: &[Lock<Value<'gc>>]) -> bool {
        let n = src.len();
        let Some(dst) = self.live(mc, at, |slots| slots.get(..n)) else { return false };
        // `src` may overlap the slots.
        let copy = |i: usize| dst.set(i, src[i].get());
        if dst.0.as_ptr() > src.as_ptr() {
            (0..n).rev().for_each(copy);
        } else {
            (0..n).for_each(copy);
        }
        true
    }

    /// Hands the frames in `base..at` to a continuation: they become ordinary arena memory,
    /// and `base` moves up to `at`. Returns the captured range, or `None` if `at` is below
    /// `base` or past the segment.
    pub fn capture<'gc>(&mut self, mc: &Mutation<'gc>, at: usize) -> Option<Range<usize>> {
        let base = self.base();
        let slots = self.slots(mc);
        let captured = slots.get(base..at)?;
        Lock::barrier_range(mc, captured, true);
        self.record.base.set(at as u32);
        self.record.top.set(self.record.top.get().max(at as u32));
        Some(base..at)
    }

    /// Moves to a new segment, as when the current one overflows, with `base` 0 and `top` at
    /// its end. The old segment's live frames become ordinary arena memory. Panics if another
    /// stack uses the segment.
    pub fn switch<'gc>(&mut self, mc: &Mutation<'gc>, segment: Gc<'gc, Segment<'gc>>) {
        let old = self.segment(mc);
        attach(mc, segment, &self.record);
        self.retire(mc);
        if !Gc::ptr_eq(old, segment) {
            old.attached.set(mc, 0);
        }
        self.record.segment.set(Member::new(mc, segment).to_bits());
        self.record.base.set(0);
        self.record.top.set(segment.len() as u32);
        self.record.parked.set(false);
    }

    /// Stops collections from tracing the live frames as a root until the stack is written
    /// again, for a task that's waiting. The frames stay alive through the segment.
    pub fn park<'gc>(&mut self, mc: &Mutation<'gc>) {
        self.retire(mc);
        self.record.parked.set(true);
    }

    fn retire(&self, mc: &Mutation<'_>) {
        self.record.retire(mc, self.segment(mc));
    }
}

impl fmt::Debug for Stack {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let r = &self.record;
        f.debug_struct("Stack").field("base", &r.base.get()).field("top", &r.top.get()).field("parked", &r.parked.get()).finish()
    }
}

/// [`WINDOW`] registers from a frame's base. Writes skip the barrier, and a `u8` register
/// number needs no bounds check.
#[derive(Clone, Copy)]
pub struct Frame<'s, 'gc> {
    slots: Live<'s, [Lock<Value<'gc>>; WINDOW]>,
}

impl<'s, 'gc> Frame<'s, 'gc> {
    #[inline]
    pub fn get(self, register: u8) -> Value<'gc> {
        self.slots.0[register as usize].get()
    }

    #[inline]
    pub fn set(self, register: u8, value: Value<'gc>) {
        self.slots.set(register as usize, value);
    }

    /// The registers as locks, for bulk reads. Writes through them take the barrier.
    pub fn slots(self) -> &'s [Lock<Value<'gc>>; WINDOW] {
        self.slots.0
    }
}

/// Slots at or above `base` of a stack's segment, borrowed from the stack, which makes them
/// only in [`Stack::live`]. The collector traces that part as a root in every
/// collection, so writes to it skip the barrier.
struct Live<'s, S: ?Sized>(&'s S);

impl<S: ?Sized> Clone for Live<'_, S> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<S: ?Sized> Copy for Live<'_, S> {}

impl<'gc, S: ?Sized + Index<usize, Output = Lock<Value<'gc>>>> Live<'_, S> {
    #[inline]
    fn set(self, i: usize, value: Value<'gc>) {
        // SAFETY: [stacks] the slot is at or above `base`, in the part of the stack every
        // collection traces as a root, so it needs no barrier.
        unsafe { self.0[i].set_unbarriered(value) }
    }
}
