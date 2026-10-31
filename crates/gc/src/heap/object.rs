//! Objects in the region: finding and checking them by offset.

use std::any::TypeId;
use std::ops::Range;
use std::ptr;

use crate::layout::{Addr, Check, GRANULE, Header, OFFSET_MASK, Object, PAGE, REGION, TypeIndex, VTable};
use crate::{Inline, layout};
use super::pages::{Kind, PageIndex};
use super::{Collecting, Heap};

/// A validated object: its offset, page and granule, and how many bytes it may span.
#[derive(Clone, Copy)]
pub(super) struct Obj {
    pub(super) offset: u32,
    pub(super) page: PageIndex,
    pub(super) granule: usize,
    pub(super) room: usize,
}

impl Heap {
    #[inline]
    pub(super) fn header_ptr(&self, offset: u32) -> *mut Header {
        self.base.as_ptr().wrapping_add(offset as usize).cast()
    }

    #[inline]
    pub(super) fn header(&self, obj: Obj) -> Header {
        self.header_at(obj.offset)
    }

    /// The header at `offset`, which only means something if an object starts there. Masked,
    /// the offset is aligned and below `REGION`, so the read stays inside the reservation, and
    /// every bit pattern is a valid `Header`.
    #[inline]
    fn header_at(&self, offset: u32) -> Header {
        // SAFETY: [memory, plain] as above, the read stays inside the reservation, and any bits are
        // a header.
        unsafe { self.header_ptr(offset & OFFSET_MASK).read() }
    }

    /// How far into the region `addr` is, if it's in it.
    #[inline]
    pub(crate) fn offset_of(&self, addr: Addr) -> Option<usize> {
        let offset = addr.get().wrapping_sub(self.base.as_ptr().addr());
        (offset < REGION).then_some(offset)
    }

    #[inline]
    pub(crate) fn in_region(&self, addr: Addr) -> bool {
        self.offset_of(addr).is_some()
    }

    /// The allocated object whose header is exactly at `offset`.
    #[inline]
    pub(super) fn object_at(&self, offset: u32) -> Option<Obj> {
        self.locate(offset).map(|(obj, _)| obj)
    }

    /// [`Heap::object_at`], with the start bits from the object's up to the end of their word,
    /// the object's own as the lowest.
    #[inline]
    fn locate(&self, offset: u32) -> Option<(Obj, u64)> {
        let offset = offset as usize;
        if !offset.is_multiple_of(GRANULE) {
            return None;
        }
        let page = self.page_of(offset)?;
        let p = self.page(page);
        let in_page = offset % PAGE;
        let room = match p.kind.get() {
            Kind::Lines => PAGE - in_page,
            Kind::Large(n) if in_page == 0 => n as usize * PAGE,
            _ => return None,
        };
        let granule = in_page / GRANULE;
        let starts = p.start.from(granule);
        (starts & 1 != 0).then_some((Obj { offset: offset as u32, page, granule, room }, starts))
    }

    /// The object's size, checked against its type and the space it can occupy.
    #[inline]
    pub(super) fn size_of(&self, obj: Obj) -> Option<(&'static VTable, usize)> {
        let (vtable, size) = self.claimed(obj)?;
        (size <= obj.room).then_some((vtable, size))
    }

    /// The object's vtable and the size its header claims, unchecked.
    #[inline]
    fn claimed(&self, obj: Obj) -> Option<(&'static VTable, usize)> {
        let header = self.header(obj);
        let vtable = self.vtable(header.ty)?;
        Some((vtable, (vtable.size)(header)?))
    }

    /// The object at `offset`, its vtable and its size, for the collector's views of it. With
    /// `gc-hardened`, they're [`Heap::checked_view`]'s.
    #[inline]
    pub(super) fn view_at(&self, offset: u32) -> Option<(Obj, &'static VTable, usize)> {
        if cfg!(feature = "gc-hardened") {
            return self.checked_view(offset);
        }
        let obj = self.object_at(offset)?;
        let (vtable, size) = self.size_of(obj)?;
        Some((obj, vtable, size))
    }

    /// [`Heap::view_at`], with the size also checked against where the next object starts,
    /// which the page records outside the region. A damaged header can then only claim the
    /// object's own bytes, and no view of it overlaps another object.
    #[inline]
    pub(super) fn checked_view(&self, offset: u32) -> Option<(Obj, &'static VTable, usize)> {
        let (obj, starts) = self.locate(offset)?;
        let (vtable, size) = self.claimed(obj)?;
        // The granules the start-bit word shows are the object's own: up to the next start, or
        // the word's end, which is never past the page's. Beyond them, it's checked further.
        let own = ((starts & !1).trailing_zeros() as usize).min(64 - obj.granule % 64);
        (size <= own * GRANULE || self.fits_far(obj, size)).then_some((obj, vtable, size))
    }

    /// [`Heap::checked_view`]'s check for an object whose granules go past their start-bit word. A
    /// large page's object, alone in its pages, only needs to fit them.
    #[cold]
    #[inline(never)]
    fn fits_far(&self, obj: Obj, size: usize) -> bool {
        let p = self.page(obj.page);
        size <= obj.room
            && (p.kind.get() != Kind::Lines || !p.start.any_in(obj.granule + 1, obj.granule + size.div_ceil(GRANULE)))
    }

    /// The check for a reference to the object at `offset`.
    #[inline]
    pub(crate) fn check_at(&self, offset: u32) -> Check {
        Check::of(self.header_at(offset))
    }

    /// Whether a reference's check matches its object's header. A mismatch means the
    /// reference outlived its object or was damaged, and marks the arena corrupted.
    #[inline]
    pub(crate) fn checks_out(&self, offset: u32, check: Check) -> bool {
        let ok = check.is_stamped() && self.check_at(offset) == check;
        if !ok {
            self.corrupt();
        }
        ok
    }

    /// Whether the object at `offset` is of the type `id` names. Offsets come from references
    /// the collector keeps valid, so only the header is checked.
    #[inline]
    pub(crate) fn has_type(&self, offset: u32, check: Check, id: fn() -> TypeId) -> bool {
        // Functions returning different ids can't be merged, so equal pointers mean equal
        // types. Unequal ones may still be copies of the same function.
        let vtable = self.vtable(check.ty());
        vtable.is_some_and(|vt| ptr::fn_addr_eq(vt.type_id, id) || (vt.type_id)() == id()) && self.checks_out(offset, check)
    }

    #[inline]
    pub(crate) fn has_type_index(&self, offset: u32, check: Check, ty: TypeIndex) -> bool {
        check.ty() == ty && self.checks_out(offset, check)
    }

    /// The head and items of the object at `offset`, if it's a `T`, for the collector.
    ///
    /// # Safety
    /// Nothing else in the collection may reference the object's memory while these views are in
    /// use. The mutator can't: collections hold the heap mutably.
    #[allow(clippy::mut_from_ref)]
    pub(crate) unsafe fn inline_mut<T: Inline>(&self, offset: u32, _: &Collecting) -> Option<(&mut T, &mut [T::Item])> {
        let (_, vtable, _) = self.view_at(offset)?;
        let id: fn() -> TypeId = layout::type_id::<T>;
        if !(ptr::fn_addr_eq(vtable.type_id, id) || (vtable.type_id)() == id()) {
            return None;
        }
        // SAFETY: [steps, alias, headers, extents] the vtable is `T`'s, so the header starts a
        // `T`, and its items are the object's. The caller holds no other view of it, and the
        // `Collecting` token means no step does.
        unsafe {
            let object = Object::<T>::at(self.header_ptr(offset));
            Some((&mut *object.value(), &mut *object.items()))
        }
    }

    /// Wipes the header of an object that's gone, so stale references to it don't check out.
    #[inline]
    pub(super) fn clear_header(&self, offset: u32) {
        // SAFETY: [memory, steps] only called for an object that was allocated, so the header is in
        // a committed page, and nothing borrows it.
        unsafe { self.header_ptr(offset).write(Header { ty: TypeIndex::new(0), flags: 0, len: 0 }) }
    }

    #[cfg(test)]
    pub(crate) fn vtable_size(&self, offset: u32) -> Option<usize> {
        let header = self.header(self.object_at(offset)?);
        (self.vtable(header.ty)?.size)(header)
    }

    /// The region offsets of the object at `offset`, or `None` if its header claims more than
    /// its own bytes.
    pub(crate) fn object_span(&self, offset: u32) -> Option<Range<usize>> {
        let (_, _, size) = self.checked_view(offset)?;
        Some(offset as usize..offset as usize + size)
    }

    #[cfg(test)]
    pub(crate) fn header_of(&self, offset: u32) -> *mut Header {
        self.header_ptr(offset)
    }
}
