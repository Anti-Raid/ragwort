use std::cell::{BorrowError, BorrowMutError, Cell, Ref, RefCell, RefMut};
use std::fmt;
use std::mem::size_of_val;

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
            mc.heap.write_barrier(self.0.as_ptr().addr(), |t| {
                let mut value = value;
                value.trace(t);
            });
        }
    }

    /// # Safety
    /// If the lock is inside an arena object, call [`Mutation::retrace`] on that object in the
    /// same step, after the last such write.
    #[inline]
    pub unsafe fn set_unbarriered(&self, value: T) {
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

    fn barrier_range(mc: &Mutation<'_>, slots: &[Self], refs: bool) {
        if refs {
            mc.heap.barrier_range(slots.as_ptr().addr(), size_of_val(slots), |t| {
                for slot in slots {
                    slot.get().trace(t);
                }
            });
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

unsafe impl<T: Trace + Copy> Trace for Lock<T> {
    const NEEDS_TRACE: bool = T::NEEDS_TRACE;

    #[inline]
    fn trace(&mut self, t: &mut Tracer<'_>) {
        self.0.get_mut().trace(t);
    }
}

unsafe impl<'gc, T: Plain<'gc>> Plain<'gc> for Lock<T> {
    const CHECK: () = T::CHECK;
}

/// Interior mutability for host-side data, such as the root. It isn't `Plain`, so it can't
/// be stored in the arena, which is why writes through it need no barrier.
pub struct RefLock<T>(RefCell<T>);

impl<T: Trace> RefLock<T> {
    pub const fn new(value: T) -> Self {
        Self(RefCell::new(value))
    }

    pub fn borrow(&self) -> Result<Ref<'_, T>, BorrowError> {
        self.0.try_borrow()
    }

    pub fn borrow_mut(&self, _mc: &Mutation<'_>) -> Result<RefMut<'_, T>, BorrowMutError> {
        self.0.try_borrow_mut()
    }

    pub fn into_inner(self) -> T {
        self.0.into_inner()
    }
}

impl<T: fmt::Debug> fmt::Debug for RefLock<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0.try_borrow() {
            Ok(v) => f.debug_tuple("RefLock").field(&*v).finish(),
            Err(_) => f.write_str("RefLock(<borrowed>)"),
        }
    }
}

unsafe impl<T: Trace> Trace for RefLock<T> {
    const NEEDS_TRACE: bool = T::NEEDS_TRACE;

    fn trace(&mut self, t: &mut Tracer<'_>) {
        self.0.get_mut().trace(t);
    }
}
