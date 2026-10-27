use std::cell::Cell;
use std::fmt;
use std::marker::PhantomData;
use std::num::NonZeroU32;
use std::ops::Range;
use std::ptr;
use std::rc::Rc;

use super::heap::Heap;
use super::root::ROOT_COST;
use super::trace::Mode;
use super::{Gc, Lock, Member, Mutation, OutOfMemory, Plain, Trace, Tracer, Value};

/// The registers a frame can address, so a `u8` register number always indexes in bounds.
pub const WINDOW: usize = 256;

/// One segment of a [`Stack`]: a run of value slots in the arena.
#[derive(Trace, Plain)]
#[gc(items = Lock<Value<'gc>>)]
pub struct Segment<'gc> {
    /// Set while a stack uses the segment. A stack that was dropped leaves it set, so a set
    /// flag is checked against the live stacks.
    attached: Lock<u32>,
    _brand: PhantomData<Value<'gc>>,
}

impl<'gc> Segment<'gc> {
    /// A segment of `len` void slots. Frames need [`WINDOW`] slots from their base.
    pub fn new(mc: &Mutation<'gc>, len: usize) -> Result<Gc<'gc, Self>, OutOfMemory> {
        let head = Segment { attached: Lock::new(0), _brand: PhantomData };
        mc.alloc_inline(head, len, |_| Lock::new(Value::VOID))
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
}

impl StackRecord {
    /// `base..top`, clamped to a segment of `len` slots.
    fn live(&self, len: usize) -> Range<usize> {
        let base = (self.base.get() as usize).min(len);
        base..(self.top.get() as usize).clamp(base, len)
    }

    /// Traces the segment and the live slots, and voids the slots above `top`, which were
    /// written without a barrier and aren't traced.
    pub(crate) fn trace(&self, heap: &Heap, t: &mut Tracer<'_>) {
        let mut segment = self.segment.get();
        t.member(&mut segment);
        self.segment.set(segment);
        if self.parked.get() {
            return;
        }
        // Collections run between steps, when nothing borrows arena memory.
        let Some(slots) = (unsafe { heap.items_mut::<Segment<'static>>(segment.get()) }) else {
            return heap.corrupt();
        };
        let live = self.live(slots.len());
        let (used, dead) = slots.split_at_mut(live.end);
        for slot in &mut used[live.start..] {
            slot.get_mut().trace(t);
        }
        if t.mode() == Mode::Mark {
            for slot in dead {
                *slot.get_mut() = Value::VOID;
            }
        }
    }

    /// Turns the live frames into ordinary arena memory: the barrier the writes skipped, for
    /// all of them at once. Slots above `top` are voided rather than traced.
    fn retire<'gc>(&self, mc: &Mutation<'gc>, segment: Gc<'gc, Segment<'gc>>) {
        if self.parked.get() {
            return;
        }
        let slots = segment.items();
        let live = self.live(slots.len());
        Lock::barrier_range(mc, &slots[live.clone()], true);
        Lock::fill(mc, &slots[live.end..], Value::VOID);
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
        budget.ensure(ROOT_COST + self.heap.stacks.borrow().growth_cost(1))?;
        let record = Rc::new(StackRecord {
            segment: Cell::new(Member::new(self, segment).to_bits()),
            base: Cell::new(0),
            top: Cell::new(segment.len() as u32),
            parked: Cell::new(false),
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
    fn slots<'s, 'gc: 's>(&'s self, mc: &Mutation<'gc>) -> &'s [Lock<Value<'gc>>] {
        self.segment(mc).items()
    }

    pub fn segment<'gc>(&self, mc: &Mutation<'gc>) -> Gc<'gc, Segment<'gc>> {
        assert_eq!(self.arena, mc.heap.id, "stack belongs to a different arena");
        Member::from_offset(self.record.segment.get()).get(mc)
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
        if fp < self.base() {
            return None;
        }
        let slots = self.slots(mc).get(fp..)?.first_chunk()?;
        self.record.parked.set(false);
        Some(Frame { slots })
    }

    pub fn get<'gc>(&self, mc: &Mutation<'gc>, index: usize) -> Option<Value<'gc>> {
        self.slots(mc).get(index).map(Lock::get)
    }

    /// Sets a slot at or above `base`. Returns whether it was in range.
    pub fn set<'gc>(&self, mc: &Mutation<'gc>, index: usize, value: Value<'gc>) -> bool {
        let Some(slot) = self.slots(mc).get(index).filter(|_| index >= self.base()) else { return false };
        self.record.parked.set(false);
        // The slot is in the live part of the segment, which the collector traces as a root.
        unsafe { slot.set_unbarriered(value) };
        true
    }

    /// Copies `src` to the slots from `at`, which must be at or above `base`, such as frames
    /// of a continuation. Returns whether it was in range.
    pub fn write<'gc>(&self, mc: &Mutation<'gc>, at: usize, src: &[Lock<Value<'gc>>]) -> bool {
        let slots = self.slots(mc);
        let Some(dst) = at.checked_add(src.len()).and_then(|end| slots.get(at..end)) else { return false };
        if at < self.base() {
            return false;
        }
        self.record.parked.set(false);
        let copy = |(d, s): (&Lock<Value<'gc>>, &Lock<Value<'gc>>)| unsafe { d.set_unbarriered(s.get()) };
        // The slots are in the live part of the segment, as in `set`. `src` may overlap them.
        if dst.as_ptr() > src.as_ptr() {
            dst.iter().zip(src).rev().for_each(copy);
        } else {
            dst.iter().zip(src).for_each(copy);
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
    slots: &'s [Lock<Value<'gc>>; WINDOW],
}

impl<'s, 'gc> Frame<'s, 'gc> {
    #[inline]
    pub fn get(self, register: u8) -> Value<'gc> {
        self.slots[register as usize].get()
    }

    #[inline]
    pub fn set(self, register: u8, value: Value<'gc>) {
        // A frame only comes from `Stack::frame`, at or above `base`, and borrows the stack, so
        // it can't outlive the slot being live.
        unsafe { self.slots[register as usize].set_unbarriered(value) }
    }

    /// The registers as locks, for bulk reads. Writes through them take the barrier.
    pub fn slots(self) -> &'s [Lock<Value<'gc>>; WINDOW] {
        self.slots
    }
}
