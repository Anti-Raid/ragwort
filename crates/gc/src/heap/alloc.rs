//! Making objects: reserving, writing and coloring them.

use std::mem::{ManuallyDrop, needs_drop};
use std::ptr::NonNull;

use crate::layout::{Header, InlineVTable, Object, PAGE, REGION, SizedVTable, VTable};
use crate::{Inline, OutOfMemory, Plain, Trace, layout};
use super::Heap;

/// The value of an object the heap just made, which only it can hand out.
pub(crate) struct Made<T>(NonNull<T>);

impl<T> Made<T> {
    pub(crate) fn get(self) -> NonNull<T> {
        self.0
    }
}

/// An object being made: reserved, with its header written, but not yet colored, so the
/// collector doesn't know of it. Dropped unfinished, as when a fill panics, it's released.
struct Building<'h, T> {
    heap: &'h Heap,
    offset: u32,
    size: usize,
    /// How much of `size` the items kept take, and how many those are.
    marked: usize,
    len: u32,
    needs_trace: bool,
    object: Object<T>,
}

/// A [`Building`] of an inline object whose items aren't written yet, which it must be
/// before it can be finished.
struct Unfilled<'h, T>(Building<'h, T>);

impl<T> Building<'_, T> {
    /// Writes the value and colors the object, which is then the collector's.
    #[inline(always)]
    fn finish(self, value: T) -> Made<T> {
        let this = ManuallyDrop::new(self);
        let ptr = this.object.value();
        // SAFETY: there's room for the value after the header, and nothing else refers to
        // either until the object is colored below.
        unsafe {
            (*this.object.header()).len = this.len;
            ptr.write(value);
        }
        this.heap.color(this.offset, this.size, this.marked, this.needs_trace);
        Made(NonNull::new(ptr).expect("in the region"))
    }
}

impl<'h, T: Inline> Unfilled<'h, T> {
    /// Writes every item from `fill`, then lends them to `keep`, which may say to keep fewer.
    /// The rest of the reservation stays claimed until the next sweep, so pacing counts it,
    /// but marking doesn't keep it for another cycle.
    #[inline(always)]
    fn init_items(self, mut fill: impl FnMut(usize) -> T::Item, keep: impl FnOnce(&mut [T::Item]) -> Option<usize>) -> Building<'h, T> {
        let mut object = self.0;
        let items = object.object.items();
        // SAFETY: the header's length of items fit in what was reserved, and only this refers
        // to them. Each is written before the slice is made.
        let items = unsafe {
            let first = items.cast::<T::Item>();
            for i in 0..items.len() {
                first.add(i).write(fill(i));
            }
            &mut *items
        };
        if let Some(kept) = keep(items).filter(|&kept| kept < object.len as usize) {
            object.len = kept as u32;
            object.marked = layout::inline_size::<T>(kept).unwrap_or(object.size);
        }
        object
    }
}

impl<T> Drop for Building<'_, T> {
    fn drop(&mut self) {
        self.heap.release(self.offset);
    }
}

impl Heap {
    /// Objects allocated while marking are marked, since the mutator may already have stored
    /// them somewhere that was traced, and queued so their contents get traced.
    /// `size` is what the object took from the region, and `marked` ia how much of it is in use.
    #[inline]
    fn color(&self, offset: u32, size: usize, marked: usize, needs_trace: bool) {
        self.stats.allocated.set(self.stats.allocated.get() + size);
        if self.is_marking() {
            self.color_marked(offset, marked, needs_trace);
        } else {
            self.stats.young.set(self.stats.young.get() + size);
        }
    }

    #[inline(never)]
    fn color_marked(&self, offset: u32, size: usize, needs_trace: bool) {
        let obj = self.object_at(offset).expect("new object");
        self.mark_object(obj, size);
        if needs_trace {
            self.push_gray(offset, obj.page);
        }
    }

    pub(crate) fn alloc<'gc, T: Trace + Plain<'gc>>(&self, value: T) -> Result<Made<T>, OutOfMemory> {
        const {
            let () = T::CHECK;
            assert!(!T::INLINE, "inline types must use alloc_inline");
            assert!(layout::fits::<T>(), "type is too large or too aligned for the arena");
            assert!(!needs_drop::<T>(), "arena objects can't need drop; hold host data through a HostRef");
        };
        self.budget.count_allocation()?;
        let object = self.build::<T>(&SizedVTable::<T>::VTABLE, const { layout::sized_size::<T>() }, 0)?;
        Ok(object.finish(value))
    }

    pub(crate) fn alloc_inline<'gc, T: Inline + Plain<'gc>>(
        &self,
        head: T,
        len: usize,
        fill: impl FnMut(usize) -> T::Item,
    ) -> Result<Made<T>, OutOfMemory>
    where
        T::Item: Plain<'gc>,
    {
        Ok(self.build_inline::<T>(len)?.init_items(fill, |_| None).finish(head))
    }

    /// Like `alloc_inline` with every item `item`, then `init` gets the items to fill in and
    /// returns how many to keep, which shrinks the object.
    pub(crate) fn alloc_inline_with<'gc, T: Inline + Plain<'gc>>(
        &self,
        head: T,
        len: usize,
        item: T::Item,
        init: impl FnOnce(&mut [T::Item]) -> usize,
    ) -> Result<Made<T>, OutOfMemory>
    where
        T::Item: Plain<'gc> + Copy,
    {
        Ok(self.build_inline::<T>(len)?.init_items(|_| item, |items| Some(init(items))).finish(head))
    }

    #[inline(always)]
    fn build_inline<'gc, T: Inline + Plain<'gc>>(&self, len: usize) -> Result<Unfilled<'_, T>, OutOfMemory>
    where
        T::Item: Plain<'gc>,
    {
        const {
            let () = T::CHECK;
            let () = <T::Item as Plain<'gc>>::CHECK;
            assert!(T::INLINE, "type implements Inline but INLINE is false");
            assert!(layout::fits_inline::<T>(), "type is too large or too aligned for the arena");
            assert!(!needs_drop::<T>() && !needs_drop::<T::Item>(), "arena objects can't need drop");
        };
        self.budget.count_allocation()?;
        let size = layout::inline_size::<T>(len)
            .filter(|&size| size <= REGION - PAGE && len <= layout::max_items::<T>())
            .ok_or_else(|| self.budget.fail())?;
        Ok(Unfilled(self.build::<T>(&InlineVTable::<T>::VTABLE, size, len)?))
    }

    /// Reserves `size` bytes for a `T` with `len` items and writes the header.
    #[inline(always)]
    fn build<T>(&self, vtable: &'static VTable, size: usize, len: usize) -> Result<Building<'_, T>, OutOfMemory> {
        let ty = self.type_index(vtable)?;
        let offset = self.reserve(size)?;
        let header = self.header_ptr(offset);
        // SAFETY: `reserve` handed out `size` bytes at `offset`, room for the header, the value
        // and the items, which nothing else refers to. With its header written, it's the object
        // reserved for a `T` that `Object` asks for.
        let object = unsafe {
            header.write(Header { ty, flags: self.stamp(), len: len as u32 });
            Object::at(header)
        };
        Ok(Building { heap: self, offset, size, marked: size, len: len as u32, needs_trace: vtable.needs_trace, object })
    }
}
