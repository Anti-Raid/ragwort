//! Segmented stack implementation based on Chez Scheme. Active execution frames reside on the current
//! stack segment, while older continuation frames are reified into a linked chain of immutable
//! [`Frames`] records.
//!
//! The frame at the stack's `base` contains a sentinel [`Link::BOTTOM`] return link, causing a return
//! to trigger an underflow that restores the topmost continuation record from the chain. Reifying
//! frames cuts the active stack rather than copying it, and continuation records are immutable,
//! allowing continuations to be invoked multiple times. One-shot continuation records (unreferenced by
//! any stored continuation) are reclaimed in place, while multi-shot records are copied back onto the
//! stack in chunks of [`CHUNK`] slots as needed.
//!
//! Continuation marks (analogous to Chez Scheme continuation attachments) are maintained as an
//! association list in the task. Each continuation record preserves the mark list of its top frame
//! and restores it upon resumption. Frames that set marks for a call store them directly beneath the
//! callee's frame, ensuring stack cuts preserve mark state across delimited extents.

use ragwort_types::gc::raw::Raw;
use ragwort_types::gc::{Frame, Gc, Mutation, Segment, Stack, Value, WINDOW};
use ragwort_types::pair::{Pair, Pairs};

use crate::Fault;
use crate::frame::{self, Kept, Link};
use crate::objects::{Frames, FramesFields, Native, NativeFields, Spill, SpillFields, Task, TaskFields};
use crate::wind::Kind;

/// The maximum number of stack slots copied from a multi-shot continuation record at one time. The
/// topmost frame is always copied in full, while deep continuations are copied back incrementally in
/// chunks as frames return.
pub const CHUNK: usize = 1024;

/// Resume state for the inner loop, specifying the active frame pointer `fp` and instruction counter
/// `pc`.
pub(crate) struct Resume {
    pub(crate) fp: usize,
    pub(crate) pc: usize,
}

/// Encapsulates a task's active stack segment and its underlying chain of continuation records.
pub(crate) struct Segments<'a, 'gc> {
    pub(crate) mc: &'a Mutation<'gc>,
    pub(crate) stack: &'a mut Stack,
    pub(crate) task: Gc<'gc, Task>,
    /// The capacity (in slots) allocated for newly created stack segments.
    pub(crate) size: usize,
}

impl<'gc> Segments<'_, 'gc> {
    /// Reifies the live stack frames below `end` into a one-shot continuation record on the chain,
    /// writing `link` as the return link for the frame at `end`. If no frames exist below `end`, the frame
    /// at `end` is already at the base of the stack and the chain remains unchanged.
    pub(crate) fn reify(&mut self, end: usize, link: Link) -> Result<(), Fault> {
        let start = self.stack.base();
        if end <= start {
            return Ok(());
        }
        let segment = self.stack.segment(self.mc);
        let marks = self.marks_under(end, link)?;
        self.stack.capture(self.mc, end).ok_or(Fault::Malformed)?;
        self.push(segment, start, end, link, marks, false)
    }

    /// Handles segment overflow by transferring the call frame at `fp` (up to `end`) onto a new stack
    /// segment as the bottom frame, requiring `need` slots. Frames below `fp` are reified into a one-shot
    /// record owning the remainder of the current segment. Returns the frame's new pointer on the fresh
    /// segment.
    pub(crate) fn overflow(&mut self, fp: usize, end: usize, need: usize) -> Result<usize, Fault> {
        let mc = self.mc;
        let len = end.checked_sub(fp).filter(|&n| n <= WINDOW).ok_or(Fault::Malformed)?;
        let (start, old) = (self.stack.base(), self.stack.segment(mc));
        let caller = self.frame(fp)?;
        let link = frame::link_of(mc, caller)?;
        let marks = if fp > start { self.marks_under(fp, link)? } else { Value::NIL };
        let mut moved = [Value::VOID; WINDOW];
        for (i, slot) in moved[..len].iter_mut().enumerate() {
            *slot = caller.get(i as u8);
        }
        self.stack.set_top(fp);
        self.move_to(need)?;
        if fp > start {
            self.push(old, start, fp, link, marks, true)?;
        }
        let at = self.stack.base();
        let dst = self.frame(at)?;
        for (i, &val) in moved[..len].iter().enumerate() {
            dst.set(i as u8, val);
        }
        frame::set_link(mc, dst, Link::BOTTOM)?;
        Ok(at)
    }

    /// Handles stack underflow by restoring the topmost continuation record from the chain (analogous to
    /// Chez Scheme's `dounderflow`), restoring its continuation marks. Reclaims one-shot records in
    /// place; splits deep multi-shot records and copies their topmost frames onto the stack. Returns
    /// `None` if the continuation chain is empty.
    pub(crate) fn underflow(&mut self) -> Result<Option<Resume>, Fault> {
        let (mc, task) = (self.mc, self.task);
        let head = task.chain(mc);
        if head == Value::FALSE {
            return Ok(None);
        }
        let record = head.downcast::<Frames>(mc).ok_or(Fault::Malformed)?;
        let segment = record.segment(mc).ok_or(Fault::Malformed)?;
        let (start, end) = (record.start(mc) as usize, record.end(mc) as usize);
        let link = Link::of(record.link(mc)).ok_or(Fault::Malformed)?;
        let below = |at: usize, base: u8| at.checked_sub(usize::from(base)).filter(|&b| b >= start && base > 0).ok_or(Fault::Malformed);
        let top = below(end, link.base)?;
        task.set_attachments(mc, record.attachments(mc));
        if record.one_shot(mc) {
            let current = self.stack.segment(mc);
            if segment == current && end == self.stack.base() {
                if !self.stack.reclaim(mc, start) {
                    return Err(Fault::Malformed);
                }
                task.set_chain(mc, record.next(mc));
                return Ok(Some(Resume { fp: top, pc: link.pc }));
            }
            if segment != current && record.owns(mc) {
                let base = self.stack.base();
                self.stack.set_top(base);
                task.set_spare(mc, Some(current));
                task.set_spare_base(mc, slot(base)?);
                if !self.stack.resume(mc, segment, start) {
                    return Err(Fault::Malformed);
                }
                task.set_chain(mc, record.next(mc));
                return Ok(Some(Resume { fp: top, pc: link.pc }));
            }
        }
        let slots = segment.slots(mc);
        if end > slots.len() {
            return Err(Fault::Malformed);
        }
        let (mut split, mut marks) = (top, record.attachments(mc));
        let rest = loop {
            if split <= start {
                break record.next(mc);
            }
            let link = frame::link_at(mc, slots, split)?;
            let under = below(split, link.base)?;
            let caller_marks = if link.marks { slots.get(Kept::under(split, start)?.marks) } else { marks };
            if end - under > CHUNK {
                let (start, at, link, one_shot) = (slot(start)?, slot(split)?, link.value().ok_or(Fault::Malformed)?, record.one_shot(mc));
                break Value::object(mc, Frames::new(mc, Some(segment), start, at, link, caller_marks, one_shot, false, record.next(mc))?);
            }
            (split, marks) = (under, caller_marks);
        };
        let at = self.bottom(end - split)?;
        if !self.stack.write(mc, at, slots.slice(split..end).ok_or(Fault::Malformed)?) {
            return Err(Fault::Malformed);
        }
        self.own_spills(at..at + (end - split))?;
        frame::set_link(mc, self.frame(at)?, Link::BOTTOM)?;
        task.set_chain(mc, rest);
        Ok(Some(Resume { fp: at + (top - split), pc: link.pc }))
    }

    /// Duplicates spill tables for frames copied into `slots`, ensuring newly active frames have
    /// independent spill storage while preserving original spills in multi-shot continuation records for
    /// future resumptions.
    fn own_spills(&self, slots: std::ops::Range<usize>) -> Result<(), Fault> {
        let mc = self.mc;
        for i in slots {
            let Some(spill) = self.stack.get(mc, i).and_then(|v| v.downcast::<Spill>(mc)) else { continue };
            let items = spill.items(mc);
            let copy = Spill::new(mc, items.len(), Value::VOID)?;
            let copied = copy.items(mc);
            for slot in 0..items.len() {
                copied.set(mc, slot, items.get(slot));
            }
            if !self.stack.set(mc, i, Value::object(mc, copy)) {
                return Err(Fault::Malformed);
            }
        }
        Ok(())
    }

    /// Returns whether a base frame with `len` underlying slots can fit within the current stack segment.
    pub(crate) fn fits(&self, len: usize) -> bool {
        self.stack.base() + len + WINDOW <= self.stack.segment(self.mc).len(self.mc)
    }

    /// Determines the frame pointer for a bottom frame requiring `len` underlying slots: places it at the
    /// current segment base if space permits, or allocates a new segment.
    pub(crate) fn bottom(&mut self, len: usize) -> Result<usize, Fault> {
        let base = self.stack.base();
        if self.fits(len) {
            return Ok(base);
        }
        self.stack.set_top(base);
        self.move_to(len + WINDOW)?;
        Ok(self.stack.base())
    }

    /// Sets continuation mark `key` on the base stack frame. Replaces any existing mark for `key`
    /// belonging to this frame rather than prepending a new entry, ensuring tail-recursive loops setting
    /// marks operate in constant space.
    pub(crate) fn set_mark(&self, key: Value<'gc>, value: Value<'gc>) -> Result<(), Fault> {
        let (mc, task) = (self.mc, self.task);
        let restored = restored(mc, task.chain(mc));
        let (pairs, mut at, mut own) = (Pairs::new(mc), task.attachments(mc), Vec::new());
        while at != restored {
            let cell = Pair::of(at).ok_or(Fault::Malformed)?;
            own.push(Pair::of(cell.head(mc)).ok_or(Fault::Malformed)?);
            at = cell.tail(mc);
        }
        let mut marks = task.attachments(mc);
        if own.iter().any(|mark| mark.head(mc) == key) {
            marks = restored;
            for mark in own.into_iter().rev() {
                let value = if mark.head(mc) == key { value } else { mark.tail(mc) };
                marks = pairs.cons(pairs.cons(mark.head(mc), value)?.value(mc), marks)?.value(mc);
            }
        } else {
            marks = pairs.cons(pairs.cons(key, value)?.value(mc), marks)?.value(mc);
        }
        task.set_attachments(mc, marks);
        Ok(())
    }

    pub(crate) fn frame(&self, fp: usize) -> Result<Frame<'_, 'gc>, Fault> {
        self.stack.frame(self.mc, fp).ok_or(Fault::Malformed)
    }

    /// Switches the stack to the task's spare segment if it provides `need` available slots, or allocates
    /// a new segment doubling the current capacity (up to `Segments.size`), allowing coroutine stacks to
    /// grow dynamically from an initial small size.
    fn move_to(&mut self, need: usize) -> Result<(), Fault> {
        let (mc, task) = (self.mc, self.task);
        if let Some(spare) = task.spare(mc) {
            task.set_spare(mc, None);
            let base = task.spare_base(mc) as usize;
            if base + need <= spare.len(mc) && self.stack.resume(mc, spare, base) {
                return Ok(());
            }
        }
        if need > self.size {
            return Err(Fault::Malformed);
        }
        let len = self.stack.segment(mc).len(mc).saturating_mul(2).clamp(need, self.size);
        self.stack.switch(mc, Segment::new(mc, len)?);
        Ok(())
    }

    /// Retrieves the continuation marks belonging to the caller of the frame at `fp` (governed by
    /// `link`): returns the task's active marks unless the call established marks, in which case previous
    /// marks were preserved directly beneath the frame.
    fn marks_under(&self, fp: usize, link: Link) -> Result<Value<'gc>, Fault> {
        if !link.marks {
            return Ok(self.task.attachments(self.mc));
        }
        self.stack.get(self.mc, Kept::under(fp, self.stack.base())?.marks).ok_or(Fault::Malformed)
    }

    fn push(&self, segment: Gc<'gc, Segment>, start: usize, end: usize, link: Link, marks: Value<'gc>, owns: bool) -> Result<(), Fault> {
        let (mc, task) = (self.mc, self.task);
        let (start, end, link) = (slot(start)?, slot(end)?, link.value().ok_or(Fault::Malformed)?);
        let record = Frames::new(mc, Some(segment), start, end, link, marks, true, owns, task.chain(mc))?;
        task.set_chain(mc, Value::object(mc, record));
        Ok(())
    }
}

/// Marks one-shot continuation records in `chain` as multi-shot, ensuring they are copied rather than
/// resumed in place when reinstated by captured continuations. Traversal stops at the first multi-shot
/// record since one-shot records only ever reside at the head of the chain.
pub(crate) fn promote<'gc>(mc: &Mutation<'gc>, mut chain: Value<'gc>) {
    loop {
        if let Some(record) = chain.downcast::<Frames>(mc) {
            if !record.one_shot(mc) {
                break;
            }
            record.set_one_shot(mc, false);
            chain = record.next(mc);
        } else if let Some(native) = chain.downcast::<Native>(mc) {
            chain = native.next(mc);
        } else {
            break;
        }
    }
}

/// Slices `chain` down to the continuation where `guard` was established, returning `None` if `guard`
/// is not present in `chain`. Unwinds either to the caller of the guarded frame (stored below its
/// frame) or below the [`Kind::Guarded`] native record. Discards intervening records while sharing
/// underlying records without copying.
pub(crate) fn cut_at<'gc>(mc: &Mutation<'gc>, mut chain: Value<'gc>, guard: Value<'gc>) -> Result<Option<Cut<'gc>>, Fault> {
    loop {
        if let Some(native) = chain.downcast::<Native>(mc) {
            if native.kind(mc) == Kind::Guarded as u32 && native.a(mc) == guard {
                let chain = native.next(mc);
                return Ok(Some(Cut { chain, marks: native.attachments(mc), free: free(mc, chain, None) }));
            }
            chain = native.next(mc);
            continue;
        }
        let Some(record) = chain.downcast::<Frames>(mc) else { return Ok(None) };
        let segment = record.segment(mc).ok_or(Fault::Malformed)?;
        let slots = segment.slots(mc);
        let (start, end) = (record.start(mc) as usize, record.end(mc) as usize);
        if end > slots.len() {
            return Err(Fault::Malformed);
        }
        let set_for = |at: usize, link: Link| match Kept::under(at, start) {
            Ok(kept) if link.marks && slots.get(kept.guard) == guard => Some(kept),
            _ => None,
        };
        let mut link = Link::of(record.link(mc)).ok_or(Fault::Malformed)?;
        if set_for(end, link).is_some() {
            return Ok(Some(Cut { chain, marks: record.attachments(mc), free: free(mc, chain, None) }));
        }
        let mut at = end;
        while link.base > 0 {
            at = at.checked_sub(usize::from(link.base)).filter(|&at| at >= start).ok_or(Fault::Malformed)?;
            link = frame::link_at(mc, slots, at)?;
            if let Some(kept) = set_for(at, link) {
                let (marks, value) = (slots.get(kept.marks), link.value().ok_or(Fault::Malformed)?);
                let cut = Frames::new(mc, Some(segment), slot(start)?, slot(at)?, value, marks, record.one_shot(mc), false, record.next(mc))?;
                return Ok(Some(Cut { chain: Value::object(mc, cut), marks, free: free(mc, chain, Some(at)) }));
            }
        }
        chain = record.next(mc);
    }
}

/// Represents a continuation sliced at a guard boundary via [`cut_at`]: contains the resumed
/// continuation chain, active marks, and, if the topmost record was one-shot, its segment bounds so
/// the stack can reclaim the freed segment space.
pub(crate) struct Cut<'gc> {
    pub(crate) chain: Value<'gc>,
    pub(crate) marks: Value<'gc>,
    pub(crate) free: Option<(Gc<'gc, Segment>, usize)>,
}

/// Returns the segment and free offset for the head record of `chain` if it is one-shot, returning
/// either `at` (if cut at a specific boundary) or the record's natural end offset.
fn free<'gc>(mc: &Mutation<'gc>, chain: Value<'gc>, at: Option<usize>) -> Option<(Gc<'gc, Segment>, usize)> {
    let record = chain.downcast::<Frames>(mc).filter(|record| record.one_shot(mc))?;
    Some((record.segment(mc)?, at.unwrap_or(record.end(mc) as usize)))
}

/// Returns the continuation marks restored by the topmost record in `chain`, or `Value::NIL` if the
/// chain is empty.
pub(crate) fn restored<'gc>(mc: &Mutation<'gc>, chain: Value<'gc>) -> Value<'gc> {
    if let Some(record) = chain.downcast::<Frames>(mc) {
        record.attachments(mc)
    } else if let Some(native) = chain.downcast::<Native>(mc) {
        native.attachments(mc)
    } else {
        Value::NIL
    }
}

fn slot(n: usize) -> Result<u32, Fault> {
    u32::try_from(n).map_err(|_| Fault::Malformed)
}
