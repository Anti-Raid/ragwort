use std::cell::Cell;
use std::fmt;
use std::mem::{size_of, size_of_val};

use super::layout::Addr;
use super::{Gc, Member, Mutation, Plain, Trace, Tracer};

#[repr(transparent)]
pub struct Lock<T>(Cell<T>);

impl<T: Copy> Lock<T> {
    pub const fn new(value: T) -> Self {
        Self(Cell::new(value))
    }

    #[inline]
    pub fn get(&self) -> T {
        self.0.get()
    }

    pub(crate) fn get_mut(&mut self) -> &mut T {
        self.0.get_mut()
    }
}

impl<T: Copy + Trace> Lock<T> {
    /// `T: 'gc` ties the value's arena to `mc`, so the barrier always runs on the right heap.
    #[inline]
    pub fn set<'gc>(&self, mc: &Mutation<'gc>, value: T)
    where
        T: 'gc,
    {
        self.0.set(value);
        if T::NEEDS_TRACE && value.holds_refs() {
            mc.heap.write_barrier(Addr::of(self.0.as_ptr()), |t| {
                let mut value = value;
                value.trace(t);
            });
        }
    }

    /// # Safety
    /// If the lock is inside an arena object, have that object retraced in the same step, as
    /// [`Mutation::batch`] and the stack do.
    #[inline]
    pub(crate) unsafe fn set_unbarriered(&self, value: T) {
        self.0.set(value);
    }

    /// Copies `src` into `dst`, which may overlap, with one barrier for the whole range.
    /// Panics if the lengths differ.
    pub fn copy<'gc>(mc: &Mutation<'gc>, dst: &[Self], src: &[Self])
    where
        T: 'gc,
    {
        assert_eq!(dst.len(), src.len(), "copy between slices of different lengths");
        if dst.as_ptr() > src.as_ptr() {
            for (d, s) in dst.iter().zip(src).rev() {
                d.0.set(s.get());
            }
        } else {
            for (d, s) in dst.iter().zip(src) {
                d.0.set(s.get());
            }
        }
        Self::barrier_range(mc, dst, T::NEEDS_TRACE && dst.iter().any(|d| d.get().holds_refs()));
    }

    /// Writes `src` into `dst`, with one barrier for the whole range. Panics if the lengths
    /// differ.
    pub fn write<'gc>(mc: &Mutation<'gc>, dst: &[Self], src: &[T])
    where
        T: 'gc,
    {
        assert_eq!(dst.len(), src.len(), "copy between slices of different lengths");
        for (d, s) in dst.iter().zip(src) {
            d.0.set(*s);
        }
        Self::barrier_range(mc, dst, T::NEEDS_TRACE && src.iter().any(T::holds_refs));
    }

    pub fn fill<'gc>(mc: &Mutation<'gc>, dst: &[Self], value: T)
    where
        T: 'gc,
    {
        for d in dst {
            d.0.set(value);
        }
        Self::barrier_range(mc, dst, T::NEEDS_TRACE && value.holds_refs());
    }

    pub(crate) fn barrier_range(mc: &Mutation<'_>, slots: &[Self], refs: bool) {
        if refs {
            mc.heap.barrier_range(Addr::of(slots.as_ptr()), size_of_val(slots), |t| {
                for slot in slots {
                    slot.get().trace(t);
                }
            });
        }
    }
}

/// Writes to the locks inside one arena object without a barrier each, for [`Mutation::batch`].
/// The object gets one barrier for all of them when the batch ends.
pub struct Batch<'b, 'gc> {
    mc: &'b Mutation<'gc>,
    object: u32,
    /// The object's address and size. A lock outside them takes the usual barrier.
    start: usize,
    len: usize,
    /// The addresses written without a barrier so far. Empty while the first is past the second.
    lo: usize,
    hi: usize,
}

impl<'gc> Mutation<'gc> {
    /// Runs `f` with a [`Batch`] for writing many locks inside `object`. Writes into the object
    /// skip the per-write barrier, and once `f` returns or panics the object gets one barrier
    /// covering everything written. Writes to locks anywhere else take the usual barrier.
    pub fn batch<T, R>(&self, object: Gc<'gc, T>, f: impl FnOnce(&mut Batch<'_, 'gc>) -> R) -> R {
        let offset = Member::new(self, object).to_bits().get();
        let span = self.heap.object_span(offset).unwrap_or(0..0);
        let start = self.base.as_ptr().addr() + span.start;
        f(&mut Batch { mc: self, object: offset, start, len: span.len(), lo: usize::MAX, hi: 0 })
    }
}

impl<'gc> Batch<'_, 'gc> {
    #[inline]
    pub fn set<T: Copy + Trace + 'gc>(&mut self, lock: &Lock<T>, value: T) {
        if !(T::NEEDS_TRACE && value.holds_refs()) {
            return lock.0.set(value);
        }
        let at = Addr::of(lock.0.as_ptr()).get();
        if self.len.checked_sub(size_of::<T>()).is_some_and(|room| at.wrapping_sub(self.start) <= room) {
            lock.0.set(value);
            self.lo = self.lo.min(at);
            self.hi = self.hi.max(at + size_of::<T>());
        } else {
            lock.set(self.mc, value);
        }
    }
}

impl Drop for Batch<'_, '_> {
    fn drop(&mut self) {
        if self.lo < self.hi {
            let base = self.mc.base.as_ptr().addr();
            self.mc.heap.retrace_part(self.object, self.lo - base..self.hi - base);
        }
    }
}

impl<'gc, T: 'gc> Lock<Option<Member<'gc, T>>> {
    pub fn load(&self, mc: &Mutation<'gc>) -> Option<Gc<'gc, T>>
    where
        T: Plain<'gc>,
    {
        self.get().map(|m| m.get(mc))
    }

    pub fn store(&self, mc: &Mutation<'gc>, value: Option<Gc<'gc, T>>) {
        self.set(mc, value.map(|gc| Member::new(mc, gc)));
    }
}

impl<'gc, T: 'gc> Lock<Member<'gc, T>> {
    pub fn load(&self, mc: &Mutation<'gc>) -> Gc<'gc, T>
    where
        T: Plain<'gc>,
    {
        self.get().get(mc)
    }

    pub fn store(&self, mc: &Mutation<'gc>, value: Gc<'gc, T>) {
        self.set(mc, Member::new(mc, value));
    }
}

impl<T: Copy + fmt::Debug> fmt::Debug for Lock<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Lock").field(&self.get()).finish()
    }
}

// SAFETY: [trace] traces what it holds, and claims to need tracing exactly when that does.
unsafe impl<T: Trace + Copy> Trace for Lock<T> {
    const NEEDS_TRACE: bool = T::NEEDS_TRACE;

    #[inline]
    fn trace(&mut self, t: &mut Tracer<'_>) {
        self.0.get_mut().trace(t);
    }
}

// SAFETY: [plain] a transparent `Cell<T>`, so it has `T`'s layout, padding and valid bit patterns.
unsafe impl<'gc, T: Plain<'gc>> Plain<'gc> for Lock<T> {
    const CHECK: () = T::CHECK;
}
