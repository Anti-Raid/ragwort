//! Chez Scheme's segmented stack: the live frames on the current segment, and under them, the
//! chain of [`Frames`] records that hold the rest of the continuation.
//!
//! The frame at the stack's `base` has the [`Link::BOTTOM`] link, so returning from it
//! underflows into the record on top of the chain. Making a record is a cut of the stack, not
//! a copy, and no record is written again, so a continuation can be resumed any number of
//! times. A record no continuation holds is one-shot, and is resumed in place, as Chez resumes
//! one-shot continuations; any other is copied back a chunk at a time.
//!
//! Marks are Chez's continuation attachments: a list in the task, which each record keeps as its
//! top frame has it, and puts back when it's resumed, so marks set since are dropped. A frame
//! that sets one for a call keeps its own under the callee's frame, as its link says, so the
//! records cut between them keep those.

use ragwort_types::gc::raw::Raw;
use ragwort_types::gc::{Frame, Gc, Mutation, Segment, Stack, Value, WINDOW};
use ragwort_types::pair::{Pair, Pairs};

use crate::Fault;
use crate::frame::{self, Kept, Link};
use crate::objects::{Frames, FramesFields, Native, NativeFields, Task, TaskFields};
use crate::wind::Kind;

/// The most slots of a record copied back onto the stack at once. The top frame is always
/// copied whole; a deep continuation comes back a chunk at a time, as its frames return.
pub const CHUNK: usize = 1024;

/// Where the inner loop goes on: the frame at `fp`, at instruction `pc`.
pub(crate) struct Resume {
    pub(crate) fp: usize,
    pub(crate) pc: usize,
}

/// A task's stack and the records under it.
pub(crate) struct Segments<'a, 'gc> {
    pub(crate) mc: &'a Mutation<'gc>,
    pub(crate) stack: &'a mut Stack,
    pub(crate) task: Gc<'gc, Task>,
    /// How many slots a new segment has.
    pub(crate) size: usize,
}

impl<'gc> Segments<'_, 'gc> {
    /// Hands the live frames below `end` to a one-shot record on the chain, as Chez reifies a
    /// continuation; the frame at `end` would have had `link`. If there are none, the frame at
    /// `end` is the bottom one already, and the chain is its continuation as it is.
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

    /// Moves the frame at `fp`, with the slots up to `end` it holds a call in, to another
    /// segment, where it's the bottom frame, as Chez does when a segment overflows. The frames
    /// under it go to a one-shot record that owns the rest of this segment. `need` is how many
    /// slots it takes from `fp` on. Returns where the frame is now.
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

    /// Resumes the record on top of the chain, as Chez's `dounderflow` does, putting its marks
    /// back. A one-shot record is taken back in place; any other is split if it's deep, and its
    /// top frames copied to the stack. Returns `None` if the chain is empty.
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
        frame::set_link(mc, self.frame(at)?, Link::BOTTOM)?;
        task.set_chain(mc, rest);
        Ok(Some(Resume { fp: at + (top - split), pc: link.pc }))
    }

    /// Whether a bottom frame with `len` slots under it fits on this segment.
    pub(crate) fn fits(&self, len: usize) -> bool {
        self.stack.base() + len + WINDOW <= self.stack.segment(self.mc).len(self.mc)
    }

    /// Where a bottom frame goes with `len` slots under it: at the stack's base, or on another
    /// segment if this one has no room.
    pub(crate) fn bottom(&mut self, len: usize) -> Result<usize, Fault> {
        let base = self.stack.base();
        if self.fits(len) {
            return Ok(base);
        }
        self.stack.set_top(base);
        self.move_to(len + WINDOW)?;
        Ok(self.stack.base())
    }

    /// Sets the mark for `key` on the frame at the bottom of the stack, as Chez sets an
    /// attachment: the frame's own marks are the ones above those its continuation puts back,
    /// and one for `key` among them is replaced rather than pushed, so a loop that sets one in
    /// tail position stays in constant space.
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

    /// Moves the stack to the spare segment, if it has `need` slots past its base, or a new one,
    /// twice the size of the one it's on, up to the task's `size`, as a coroutine's stack starts
    /// small.
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

    /// The marks of the caller of the frame at `fp`, whose link is `link`: the task's, unless the
    /// call set a mark, and the caller kept its own under the frame.
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

/// Makes the records of `chain` multi-shot, as a continuation that holds them needs: they're
/// copied when resumed from then on, not taken back in place. One-shot records are only ever on
/// top of a chain, as in Chez, so this stops at the first that isn't.
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

/// The continuation `chain` goes on with from where `guard` was set, or `None` if it's not in
/// `chain`: from the caller of the frame it was set for, which keeps it under that frame, or
/// from under the [`Kind::Guarded`] record that holds it. What's above is dropped, and the
/// records under it are shared, not copied.
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

/// A continuation [`cut_at`] a guard: its chain and marks, and if the record on top is one-shot,
/// its segment from where it ends now. Those above it were one-shot too, and nothing else holds
/// what they had of the segment, so the stack can take it back.
pub(crate) struct Cut<'gc> {
    pub(crate) chain: Value<'gc>,
    pub(crate) marks: Value<'gc>,
    pub(crate) free: Option<(Gc<'gc, Segment>, usize)>,
}

/// Where the segment of the record on top of `chain` is free from, if it's one-shot: where it
/// ends, or `at` if it's cut there.
fn free<'gc>(mc: &Mutation<'gc>, chain: Value<'gc>, at: Option<usize>) -> Option<(Gc<'gc, Segment>, usize)> {
    let record = chain.downcast::<Frames>(mc).filter(|record| record.one_shot(mc))?;
    Some((record.segment(mc)?, at.unwrap_or(record.end(mc) as usize)))
}

/// The marks the record on top of `chain` puts back, or none if it's empty.
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
