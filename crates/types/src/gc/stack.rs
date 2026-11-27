use std::cell::Cell;
use std::fmt;
use std::marker::PhantomData;
use std::ops::Range;
use std::rc::Rc;

use super::raw::Raw;
use super::slot::Refs;
use super::{Brand, Desc, Gc, Heap, Items, Mutation, Object, OutOfMemory, Slots, Value, WINDOW, Work};

/// The flag set in a segment's field word while a stack uses the segment. The low 32 bits of the word hold the end of the segment's
/// ordinary arena slots. The ordinary slots are `0..base` while the stack is unparked, and `0..top` once it is retired.
const ATTACHED: u64 = 1 << 32;

/// One segment of a [`Stack`]: a run of value slots in the arena. Its one field holds the
/// `ATTACHED` flag while a stack uses the segment. The low 32 bits of the field hold the end of the segment's ordinary arena slots.
pub struct Segment;

impl Object for Segment {
    const DESC: Desc = Desc::of::<Segment>(1).items(Items::Values).numbered(1);
}

impl Segment {
    /// Creates a segment of `len` slots, each holding void. A frame needs [`WINDOW`] slots from its base.
    pub fn new<'gc>(mc: &Mutation<'gc>, len: usize) -> Result<Gc<'gc, Segment>, OutOfMemory> {
        mc.alloc_items::<Segment, 1>([0], len, Value::VOID)
    }

    /// Creates a segment of exactly `frames.len()` slots that holds a copy of `frames`. Use it for frames that no stack runs on, such as the frames
    /// of a continuation.
    ///
    /// All of its slots are ordinary arena memory, so the collector traces them. A segment from
    /// [`Segment::new`] has no ordinary slots until a stack uses it, and values copied into it are
    /// not kept alive.
    pub fn holding<'gc>(mc: &Mutation<'gc>, frames: Slots<'gc>) -> Result<Gc<'gc, Segment>, OutOfMemory> {
        let ordinary = u32::try_from(frames.len()).map_err(|_| OutOfMemory)?;
        let segment = mc.alloc_items::<Segment, 1>([u64::from(ordinary)], frames.len(), Value::VOID)?;
        segment.slots(mc).copy_from(mc, frames);
        Ok(segment)
    }
}

/// The bytes charged for a stack, in addition to its segment.
pub(crate) const STACK_COST: usize = 64;

/// The collector's record of a stack. The arena holds one reference to the record and the [`Stack`]
/// holds the other. So the arena can tell when the stack was dropped. It then traces the record one last time and removes it.
pub(crate) struct StackRecord {
    /// The index of the segment. It is updated when the segment moves.
    segment: Cell<u32>,
    base: Cell<u32>,
    top: Cell<u32>,
    parked: Cell<bool>,
    /// Every slot that a frame wrote without a barrier is below this index.
    written: Cell<u32>,
}

impl StackRecord {
    /// Returns `base..top`, clamped to a segment of `len` slots.
    fn live(&self, len: usize) -> Range<usize> {
        let base = (self.base.get() as usize).min(len);
        base..(self.top.get() as usize).clamp(base, len)
    }

    /// Returns the end of the slots that may need to be reset to void. It is `written`, clamped to `len` and to at least `live.end`.
    fn written_end(&self, live: &Range<usize>, len: usize) -> usize {
        (self.written.get() as usize).min(len).max(live.end)
    }

    fn set_ordinary(&self, heap: Heap<'_>, end: usize, attached: bool) {
        if let Some(word) = heap.words().get(self.segment.get() as usize + 1) {
            let flag = if attached { ATTACHED } else { 0 };
            word.set(flag | u64::from(end.try_into().unwrap_or(u32::MAX)));
        }
    }

    /// Marks the segment and traces the live slots as roots. Resets the slots above `top` to void, because they
    /// were written without a barrier and are dead. If `dropped` is true, this is the last trace of a dropped stack. It detaches the segment and leaves the live slots as ordinary arena memory.
    pub(crate) fn trace(&self, heap: Heap<'_>, work: &mut Work, dropped: bool) {
        let segment = self.segment.get();
        heap.mark(segment, work);
        if self.parked.get() {
            if dropped {
                let end = heap.words().get(segment as usize + 1).map_or(0, |word| word.get() as u32 as usize);
                self.set_ordinary(heap, end, false);
            }
            return;
        }
        let slots = heap.segment_slots(segment);
        let live = self.live(slots.len());
        let evacuating = dropped && heap.m.evacuating.get();
        for (offset, slot) in slots[live.clone()].iter().enumerate() {
            let word = slot.get();
            if word & super::TAG == super::OBJECT {
                let target = (word >> 32) as u32;
                heap.mark(target, work);
                if evacuating && heap.in_evacuation(target) {
                    // The record of a dropped stack is removed after this trace, so `fix` never runs for it. Its slots are recorded as fixups instead.
                    // The fixup position is the slot's word offset from the segment's header: 1 for the header, 1 for the field, then the slot's index.
                    work.fixups.push((segment, (2 + live.start + offset) as u32));
                }
            }
        }
        for slot in &slots[live.end..self.written_end(&live, slots.len())] {
            slot.set(Value::VOID.word);
        }
        self.written.set(live.end as u32);
        if dropped {
            self.set_ordinary(heap, live.end, false);
            self.parked.set(true);
        } else {
            self.set_ordinary(heap, live.start, true);
        }
    }

    /// Runs after evacuation. Updates the segment's index if the segment moved, and updates the references in the live slots. The live slots may
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

    /// Turns the live frames into ordinary arena memory. It applies the write barrier that the frame writes skipped, to
    /// all live slots at once. The slots above `top` are reset to void, not kept.
    fn retire(&self, heap: Heap<'_>) {
        if self.parked.get() {
            return;
        }
        let segment = self.segment.get();
        let slots = heap.segment_slots(segment);
        let live = self.live(slots.len());
        heap.barrier_range(segment as usize + 2 + live.start, &slots[live.clone()], segment, Refs::Values);
        for slot in &slots[live.end..self.written_end(&live, slots.len())] {
            slot.set(Value::VOID.word);
        }
        self.written.set(live.end as u32);
        self.set_ordinary(heap, live.end, true);
    }
}

impl<'a> Heap<'a> {
    /// Returns the slots of `segment`.
    #[inline]
    fn segment_slots(self, segment: u32) -> &'a [Cell<u64>] {
        let at = segment as usize;
        let len = self.words().get(at).map_or(0, |header| (header.get() >> 32) as usize);
        self.words().get(at + 2..at + 2 + len).unwrap_or(&[])
    }
}

/// Retires any dropped stack that is still attached to `segment`. Panics if another live stack uses `segment`.
/// If `mine` is true, the caller's own stack is on `segment` and does not count as another stack.
#[inline]
fn ensure_free<'gc>(mc: &Mutation<'gc>, segment: Gc<'gc, Segment>, mine: bool) {
    if segment.word(mc, 0) & ATTACHED != 0 {
        retire_dropped(mc, segment, mine);
    }
}

#[cold]
#[inline(never)]
fn retire_dropped<'gc>(mc: &Mutation<'gc>, segment: Gc<'gc, Segment>, mine: bool) {
    let stacks = mc.heap.m.stacks.borrow();
    let mut live = 0;
    for other in stacks.iter().filter(|stack| stack.segment.get() == segment.index) {
        if Rc::strong_count(other) == 1 {
            // This is a dropped stack that is still waiting for its last trace. Retire it now, so that the
            // last trace cannot reset the slots that the new stack writes.
            other.retire(mc.heap);
            other.parked.set(true);
        } else {
            live += 1;
        }
    }
    assert!(live <= usize::from(mine), "segment is already in use by another stack");
}

/// Marks `segment` as used by the stack with `record`. [`ensure_free`] must have freed the segment first.
/// Sets `record.written` to the end of the segment's ordinary slots, which the segment's field holds from the last retire.
fn attach<'gc>(mc: &Mutation<'gc>, segment: Gc<'gc, Segment>, record: &StackRecord) {
    record.written.set(segment.word(mc, 0) as u32);
    segment.set_word(mc, 0, ATTACHED);
}

/// A VM stack made of [`Segment`]s, as in Chez Scheme. Frames on the stack are written without a
/// write barrier. Instead, every collection traces the live part of the stack as a root. The live part is `base..top` of the current segment.
/// Every collection also resets the slots above `top` to void.
///
/// The frames below `base` were handed to continuations by [`Stack::capture`]. The stack can read them
/// but cannot write them. A continuation copies its frames back with [`Stack::write`]. If nothing
/// else holds the frames, the continuation can instead take them back in place with [`Stack::reclaim`] and [`Stack::resume`],
/// as Chez does for one-shot continuations.
///
/// A stack has no brand, so it can live outside the arena, such as in a task. Using it with
/// another arena's [`Mutation`] panics. A dropped stack is freed at the next collection.
pub struct Stack {
    arena: u64,
    record: Rc<StackRecord>,
}

impl<'gc> Mutation<'gc> {
    /// Creates a stack on `segment`, with `base` 0 and `top` at the end of the segment. Panics if
    /// another stack uses the segment.
    pub fn stack(&self, segment: Gc<'gc, Segment>) -> Result<Stack, OutOfMemory> {
        let meta = self.heap.m;
        meta.budget.count_allocation()?;
        meta.budget.charge(STACK_COST)?;
        let record = Rc::new(StackRecord {
            segment: Cell::new(segment.index),
            base: Cell::new(0),
            top: Cell::new(segment.len(self).try_into().unwrap_or(u32::MAX)),
            parked: Cell::new(false),
            written: Cell::new(0),
        });
        ensure_free(self, segment, false);
        attach(self, segment, &record);
        meta.stacks.borrow_mut().push(record.clone());
        Ok(Stack { arena: meta.id, record })
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

    /// Returns the index of the first slot that the stack can write.
    pub fn base(&self) -> usize {
        self.record.base.get() as usize
    }

    /// Returns the end of the live frames. The next collection resets the slots from `top` up to void.
    pub fn top(&self) -> usize {
        self.record.top.get() as usize
    }

    /// Sets the end of the live frames to `top`. Call it before the step ends. Within a step, the value does not matter. The call also unparks the stack, so
    /// the next collection resets the slots above `top` to void.
    pub fn set_top(&self, top: usize) {
        self.record.top.set(top.try_into().unwrap_or(u32::MAX));
        self.record.parked.set(false);
    }

    /// Returns the frame that starts at slot `fp`. Returns `None` if `fp` is below `base`, or if `fp + WINDOW` is
    /// past the end of the segment. The frame borrows the stack. So the stack cannot capture, park or switch
    /// while the frame can still write without a barrier.
    #[inline]
    pub fn frame<'s, 'gc: 's>(&'s self, mc: &Mutation<'gc>, fp: usize) -> Option<Frame<'s, 'gc>> {
        Some(Frame { slots: self.live(mc, fp, WINDOW)?.first_chunk()?, _brand: PhantomData })
    }

    /// Returns `count` slots from `at`, for writing without a barrier. Returns `None` if `at` is below `base` or the slots do not fit in the segment. Also unparks the stack.
    #[inline]
    fn live<'gc>(&self, mc: &Mutation<'gc>, at: usize, count: usize) -> Option<&'gc [Cell<u64>]> {
        self.check(mc);
        let record = &*self.record;
        if at < record.base.get() as usize {
            return None;
        }
        let end = at.checked_add(count)?;
        let slots = mc.heap.segment_slots(record.segment.get()).get(at..end)?;
        if record.written.get() < end as u32 {
            record.written.set(end as u32);
        }
        if record.parked.replace(false) {
            record.set_ordinary(mc.heap, record.base.get() as usize, true);
        }
        Some(slots)
    }

    pub fn get<'gc>(&self, mc: &Mutation<'gc>, index: usize) -> Option<Value<'gc>> {
        self.check(mc);
        mc.heap.segment_slots(self.record.segment.get()).get(index).map(|slot| Value::from_bits(slot.get()))
    }

    /// Sets slot `index`, which must be at or above `base`, to `value`. Returns whether `index` was in range.
    pub fn set<'gc>(&self, mc: &Mutation<'gc>, index: usize, value: Value<'gc>) -> bool {
        let Some(slot) = self.live(mc, index, 1) else { return false };
        slot[0].set(value.word);
        true
    }

    /// Copies `src`, such as the frames of a continuation, to the slots from `at`. `at` must be at or above `base`.
    /// `src` may overlap the destination. Returns whether the destination was in range.
    pub fn write<'gc>(&self, mc: &Mutation<'gc>, at: usize, src: Slots<'gc>) -> bool {
        let Some(dst) = self.live(mc, at, src.len()) else { return false };
        let dst_at = self.record.segment.get() as usize + 2 + at;
        if dst_at > src.at {
            dst.iter().zip(src.words).rev().for_each(|(target, source)| target.set(source.get()));
        } else {
            dst.iter().zip(src.words).for_each(|(target, source)| target.set(source.get()));
        }
        true
    }

    /// Hands the frames in `base..at` to a continuation. The frames become ordinary arena memory,
    /// and `base` moves up to `at`. Returns the captured range, or `None` if `at` is below
    /// `base` or past the end of the segment.
    pub fn capture<'gc>(&mut self, mc: &Mutation<'gc>, at: usize) -> Option<Range<usize>> {
        self.check(mc);
        let record = &*self.record;
        let (base, segment) = (record.base.get() as usize, record.segment.get());
        let captured = mc.heap.segment_slots(segment).get(base..at)?;
        mc.heap.barrier_range(segment as usize + 2 + base, captured, segment, Refs::Values);
        record.base.set(at as u32);
        record.top.set(record.top.get().max(at as u32));
        if !record.parked.get() {
            record.set_ordinary(mc.heap, at, true);
        }
        Some(base..at)
    }

    /// Takes back the frames in `at..base`, which [`Stack::capture`] handed to a continuation.
    /// `base` moves down to `at`, so the stack writes those frames in place. Use it when the continuation is resumed and nothing else holds
    /// it. Returns whether `at` was at or below `base`.
    pub fn reclaim(&mut self, mc: &Mutation<'_>, at: usize) -> bool {
        self.check(mc);
        let record = &*self.record;
        let old_base = record.base.get();
        if at > old_base as usize {
            return false;
        }
        record.written.set(record.written.get().max(old_base));
        record.base.set(at as u32);
        record.parked.set(false);
        record.set_ordinary(mc.heap, at, true);
        true
    }

    /// Moves the stack to `segment` like [`Stack::switch`], but sets the stack's base to `base`. Use it to return to a
    /// segment that the stack left, when nothing else holds the segment's slots from `base` up. The slots below `base` stay
    /// with the continuations that captured them. Returns whether `base` was within the segment.
    pub fn resume<'gc>(&mut self, mc: &Mutation<'gc>, segment: Gc<'gc, Segment>, base: usize) -> bool {
        if base > segment.len(mc) {
            return false;
        }
        self.switch(mc, segment);
        self.record.base.set(base as u32);
        self.record.set_ordinary(mc.heap, base, true);
        true
    }

    /// Moves the stack to `segment`, with `base` 0 and `top` at
    /// the end of the segment. Use it when the current segment overflows, for example. The live frames of the old segment become ordinary arena memory. Panics if another
    /// stack uses `segment`.
    pub fn switch<'gc>(&mut self, mc: &Mutation<'gc>, segment: Gc<'gc, Segment>) {
        let old = self.segment(mc);
        let mine = old == segment;
        ensure_free(mc, segment, mine);
        self.record.retire(mc.heap);
        if !mine {
            old.set_word(mc, 0, old.word(mc, 0) & !ATTACHED);
        }
        attach(mc, segment, &self.record);
        let record = &*self.record;
        record.segment.set(segment.index);
        record.base.set(0);
        record.top.set(segment.len(mc).try_into().unwrap_or(u32::MAX));
        record.parked.set(false);
    }

    /// Parks the stack, for a task that is waiting. Collections stop tracing the live frames as a root until the stack is written
    /// again. The frames stay alive as ordinary memory of the segment.
    pub fn park(&mut self, mc: &Mutation<'_>) {
        self.check(mc);
        self.record.retire(mc.heap);
        self.record.parked.set(true);
    }
}

impl fmt::Debug for Stack {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let record = &self.record;
        formatter.debug_struct("Stack")
            .field("base", &record.base.get())
            .field("top", &record.top.get())
            .field("parked", &record.parked.get())
            .finish()
    }
}

/// The [`WINDOW`] registers from a frame's base. A write applies no barrier. The live part of the stack is
/// a root that every collection rescans, and no collection runs during a step.
///
/// A frame borrows its stack, so it cannot outlive a capture, park or switch. After any of those, the frame's
/// slots are ordinary memory, and a write to them needs the barrier:
///
/// ```
/// # use ragwort_types::gc::*;
/// let mut arena = Arena::new(1 << 20, 1);
/// arena.mutate(|mc| {
///     let mut stack = mc.stack(Segment::new(mc, 512).unwrap()).unwrap();
///     let frame = stack.frame(mc, 0).unwrap();
///     frame.set(0, Value::NULL);
///     stack.capture(mc, 8);
/// });
/// ```
///
/// ```compile_fail
/// # use ragwort_types::gc::*;
/// let mut arena = Arena::new(1 << 20, 1);
/// arena.mutate(|mc| {
///     let mut stack = mc.stack(Segment::new(mc, 512).unwrap()).unwrap();
///     let frame = stack.frame(mc, 0).unwrap();
///     stack.capture(mc, 8);
///     frame.set(0, Value::NULL);
/// });
/// ```
#[derive(Clone, Copy)]
pub struct Frame<'s, 'gc> {
    slots: &'s [Cell<u64>; WINDOW],
    _brand: Brand<'gc>,
}

impl<'gc> Frame<'_, 'gc> {
    #[inline]
    pub fn get(self, register: u8) -> Value<'gc> {
        Value::from_bits(self.slots[usize::from(register) % WINDOW].get())
    }

    #[inline]
    pub fn set(self, register: u8, value: Value<'gc>) {
        self.slots[usize::from(register) % WINDOW].set(value.word);
    }
}
