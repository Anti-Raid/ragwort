use std::cell::Cell;
use std::fmt;
use std::marker::PhantomData;
use std::ops::Range;
use std::ptr;
use std::rc::Rc;

use super::raw::Raw;
use super::{Brand, Desc, Gc, Heap, Items, Mutation, Object, OutOfMemory, Slots, Value, WINDOW, Work};

/// One segment of a [`Stack`]: a run of value slots in the arena. Its one field is set while a
/// stack uses it.
pub struct Segment;

impl Object for Segment {
    const DESC: Desc = Desc::of::<Segment>(1).items(Items::Values).numbered(1);
}

impl Segment {
    /// A segment of `len` void slots. Frames need [`WINDOW`] slots from their base.
    pub fn new<'gc>(mc: &Mutation<'gc>, len: usize) -> Result<Gc<'gc, Segment>, OutOfMemory> {
        mc.alloc_items::<Segment, 1>([0], len, Value::VOID)
    }
}

/// What a stack is charged, beyond its segment.
pub(crate) const STACK_COST: usize = 64;

/// What the collector knows about a stack. The arena holds one reference and the [`Stack`]
/// the other, so a record whose stack was dropped is pruned once traced.
pub(crate) struct StackRecord {
    /// The segment's index, updated when it moves.
    segment: Cell<u32>,
    base: Cell<u32>,
    top: Cell<u32>,
    parked: Cell<bool>,
    /// Slots frames wrote without a barrier lie below this.
    written: Cell<u32>,
}

impl StackRecord {
    /// `base..top`, clamped to a segment of `len` slots.
    fn live(&self, len: usize) -> Range<usize> {
        let base = (self.base.get() as usize).min(len);
        base..(self.top.get() as usize).clamp(base, len)
    }

    /// Where the slots that may need voiding end.
    fn written_end(&self, live: &Range<usize>, len: usize) -> usize {
        (self.written.get() as usize).min(len).max(live.end)
    }

    /// Marks the segment, traces the live slots as roots, and voids those above `top`, which
    /// were written without a barrier and are dead.
    pub(crate) fn trace(&self, heap: Heap<'_>, work: &mut Work) {
        let segment = self.segment.get();
        heap.mark(segment, work);
        if self.parked.get() {
            return;
        }
        let slots = heap.segment_slots(segment);
        let live = self.live(slots.len());
        for slot in &slots[live.clone()] {
            heap.visit(slot, work);
        }
        for slot in &slots[live.end..self.written_end(&live, slots.len())] {
            slot.set(Value::VOID.word);
        }
        self.written.set(live.end as u32);
    }

    /// After evacuation: follows the segment if it moved, and fixes the live slots, which may
    /// have been written since the segment was traced.
    pub(crate) fn fix(&self, heap: Heap<'_>) {
        let segment = heap.resolve(self.segment.get());
        self.segment.set(segment);
        if self.parked.get() {
            return;
        }
        let slots = heap.segment_slots(segment);
        for slot in &slots[self.live(slots.len())] {
            heap.fix_value(slot);
        }
    }

    /// Turns the live frames into ordinary arena memory: the barrier the writes skipped, for
    /// all of them at once. Slots above `top` are voided rather than kept.
    fn retire(&self, heap: Heap<'_>) {
        if self.parked.get() {
            return;
        }
        let segment = self.segment.get();
        let slots = heap.segment_slots(segment);
        let live = self.live(slots.len());
        heap.barrier_range(segment as usize + 2 + live.start, &slots[live.clone()], segment);
        for slot in &slots[live.end..self.written_end(&live, slots.len())] {
            slot.set(Value::VOID.word);
        }
    }
}

impl<'a> Heap<'a> {
    /// A segment's slots.
    #[inline]
    fn segment_slots(self, segment: u32) -> &'a [Cell<u64>] {
        let s = segment as usize;
        let len = self.words.get(s).map_or(0, |h| (h.get() >> 32) as usize);
        self.words.get(s + 2..s + 2 + len).unwrap_or(&[])
    }
}

/// Marks `segment` as used by the stack with `record`. Panics if another live stack uses it.
fn attach<'gc>(mc: &Mutation<'gc>, segment: Gc<'gc, Segment>, record: &StackRecord) {
    if segment.word(mc, 0) != 0 {
        let stacks = mc.heap.m.stacks.borrow();
        for other in stacks.iter().filter(|s| s.segment.get() == segment.index && !ptr::eq(&***s, record)) {
            assert!(Rc::strong_count(other) == 1, "segment is already in use by another stack");
            // A dropped stack still waiting for its last trace. Retiring it now means that trace
            // can't void what the new stack writes.
            other.retire(mc.heap);
            other.parked.set(true);
        }
    }
    segment.set_word(mc, 0, 1);
}

/// A VM stack made of [`Segment`]s, as in Chez Scheme. Frames on it are written without a
/// write barrier: the collector traces the live part, `base..top` of the current segment, as
/// a root in every collection, and voids what's above `top`.
///
/// Below `base` are frames handed to continuations by [`Stack::capture`]. They can only be
/// read through the stack; continuations copy them back with [`Stack::write`].
///
/// A stack holds no brand, so it can live outside the arena, such as in a task. Using it with
/// another arena's [`Mutation`] panics. Dropping it frees it at the next collection.
pub struct Stack {
    arena: u64,
    record: Rc<StackRecord>,
}

impl<'gc> Mutation<'gc> {
    /// A stack on `segment`, with `base` 0 and `top` at the end of the segment. Panics if
    /// another stack uses the segment.
    pub fn stack(&self, segment: Gc<'gc, Segment>) -> Result<Stack, OutOfMemory> {
        let m = self.heap.m;
        m.budget.count_allocation()?;
        m.budget.charge(STACK_COST)?;
        let record = Rc::new(StackRecord {
            segment: Cell::new(segment.index),
            base: Cell::new(0),
            top: Cell::new(segment.len(self).try_into().unwrap_or(u32::MAX)),
            parked: Cell::new(false),
            written: Cell::new(0),
        });
        attach(self, segment, &record);
        m.stacks.borrow_mut().push(record.clone());
        Ok(Stack { arena: m.id, record })
    }
}

impl Stack {
    #[inline]
    fn check(&self, mc: &Mutation<'_>) {
        assert_eq!(self.arena, mc.heap.m.id, "stack belongs to a different arena");
    }

    pub fn segment<'gc>(&self, mc: &Mutation<'gc>) -> Gc<'gc, Segment> {
        self.check(mc);
        Gc::new(self.record.segment.get())
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
    /// fit in the segment. It borrows the stack, so the stack can't capture, park or switch
    /// while the frame can still write without a barrier.
    #[inline]
    pub fn frame<'s, 'gc: 's>(&'s self, mc: &Mutation<'gc>, fp: usize) -> Option<Frame<'s, 'gc>> {
        Some(Frame { slots: self.live(mc, fp, WINDOW)?.first_chunk()?, _brand: PhantomData })
    }

    /// `n` slots from `at`, which must be at or above `base`, for writing without a barrier.
    #[inline]
    fn live<'gc>(&self, mc: &Mutation<'gc>, at: usize, n: usize) -> Option<&'gc [Cell<u64>]> {
        self.check(mc);
        let record = &*self.record;
        if at < record.base.get() as usize {
            return None;
        }
        let end = at.checked_add(n)?;
        let slots = mc.heap.segment_slots(record.segment.get()).get(at..end)?;
        if record.written.get() < end as u32 {
            record.written.set(end as u32);
        }
        record.parked.set(false);
        Some(slots)
    }

    pub fn get<'gc>(&self, mc: &Mutation<'gc>, index: usize) -> Option<Value<'gc>> {
        self.check(mc);
        mc.heap.segment_slots(self.record.segment.get()).get(index).map(|s| Value::from_bits(s.get()))
    }

    /// Sets a slot at or above `base`. Returns whether it was in range.
    pub fn set<'gc>(&self, mc: &Mutation<'gc>, index: usize, value: Value<'gc>) -> bool {
        let Some(slot) = self.live(mc, index, 1) else { return false };
        slot[0].set(value.word);
        true
    }

    /// Copies `src` to the slots from `at`, which must be at or above `base`, such as the frames
    /// of a continuation. `src` may overlap them. Returns whether it was in range.
    pub fn write<'gc>(&self, mc: &Mutation<'gc>, at: usize, src: Slots<'gc>) -> bool {
        let Some(dst) = self.live(mc, at, src.len()) else { return false };
        let dst_at = self.record.segment.get() as usize + 2 + at;
        if dst_at > src.at {
            dst.iter().zip(src.words).rev().for_each(|(d, s)| d.set(s.get()));
        } else {
            dst.iter().zip(src.words).for_each(|(d, s)| d.set(s.get()));
        }
        true
    }

    /// Hands the frames in `base..at` to a continuation: they become ordinary arena memory,
    /// and `base` moves up to `at`. Returns the captured range, or `None` if `at` is below
    /// `base` or past the segment.
    pub fn capture<'gc>(&mut self, mc: &Mutation<'gc>, at: usize) -> Option<Range<usize>> {
        self.check(mc);
        let record = &*self.record;
        let (base, segment) = (record.base.get() as usize, record.segment.get());
        let captured = mc.heap.segment_slots(segment).get(base..at)?;
        mc.heap.barrier_range(segment as usize + 2 + base, captured, segment);
        record.base.set(at as u32);
        record.top.set(record.top.get().max(at as u32));
        Some(base..at)
    }

    /// Moves to a new segment, as when the current one overflows, with `base` 0 and `top` at
    /// its end. The old segment's live frames become ordinary arena memory. Panics if another
    /// stack uses the segment.
    pub fn switch<'gc>(&mut self, mc: &Mutation<'gc>, segment: Gc<'gc, Segment>) {
        let old = self.segment(mc);
        attach(mc, segment, &self.record);
        self.record.retire(mc.heap);
        if old != segment {
            old.set_word(mc, 0, 0);
        }
        let record = &*self.record;
        record.segment.set(segment.index);
        record.base.set(0);
        record.top.set(segment.len(mc).try_into().unwrap_or(u32::MAX));
        record.parked.set(false);
    }

    /// Stops collections from tracing the live frames as a root until the stack is written
    /// again, for a task that's waiting. The frames stay alive through the segment.
    pub fn park(&mut self, mc: &Mutation<'_>) {
        self.check(mc);
        self.record.retire(mc.heap);
        self.record.parked.set(true);
    }
}

impl fmt::Debug for Stack {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let r = &self.record;
        f.debug_struct("Stack")
            .field("base", &r.base.get())
            .field("top", &r.top.get())
            .field("parked", &r.parked.get())
            .finish()
    }
}

/// [`WINDOW`] registers from a frame's base. Writes take no barrier: the stack's live part is
/// a root, rescanned by every collection, and none runs during a step.
///
/// A frame borrows its stack, so it can't outlive a capture, park or switch, after which its
/// slots are ordinary memory that needs the barrier:
///
/// ```
/// # use ragwort_gc_words::*;
/// let mut arena = Arena::new(1 << 20, 1);
/// arena.mutate(|mc| {
///     let mut stack = mc.stack(Segment::new(mc, 512).unwrap()).unwrap();
///     let frame = stack.frame(mc, 0).unwrap();
///     frame.set(0, Value::NIL);
///     stack.capture(mc, 8);
/// });
/// ```
///
/// ```compile_fail
/// # use ragwort_gc_words::*;
/// let mut arena = Arena::new(1 << 20, 1);
/// arena.mutate(|mc| {
///     let mut stack = mc.stack(Segment::new(mc, 512).unwrap()).unwrap();
///     let frame = stack.frame(mc, 0).unwrap();
///     stack.capture(mc, 8);
///     frame.set(0, Value::NIL);
/// });
/// ```
#[derive(Clone, Copy)]
pub struct Frame<'s, 'gc> {
    slots: &'s [Cell<u64>; WINDOW],
    _brand: Brand<'gc>,
}

impl<'gc> Frame<'_, 'gc> {
    #[inline]
    pub fn get(self, r: u8) -> Value<'gc> {
        Value::from_bits(self.slots[r as usize].get())
    }

    #[inline]
    pub fn set(self, r: u8, value: Value<'gc>) {
        self.slots[r as usize].set(value.word);
    }
}
