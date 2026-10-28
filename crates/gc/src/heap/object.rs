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
        // SAFETY: as above, the read stays inside the reservation, and any bits are a header.
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
        p.start.get(granule).then_some(Obj { offset: offset as u32, page, granule, room })
    }

    /// The object's size, checked against its type and the space it can occupy.
    #[inline]
    pub(super) fn size_of(&self, obj: Obj) -> Option<(&'static VTable, usize)> {
        let header = self.header(obj);
        let vtable = self.vtable(header.ty)?;
        let size = (vtable.size)(header)?;
        (size <= obj.room).then_some((vtable, size))
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

    /// The items of the object at `offset`, if it's a `T`, for the collector.
    ///
    /// # Safety
    /// Nothing else in the collection may reference the object's memory while the slice is in
    /// use. The mutator can't: collections hold the heap mutably.
    #[allow(clippy::mut_from_ref)]
    pub(crate) unsafe fn items_mut<T: Inline>(&self, offset: u32, _: &Collecting) -> Option<&mut [T::Item]> {
        let obj = self.object_at(offset)?;
        let (vtable, _) = self.size_of(obj)?;
        let id: fn() -> TypeId = layout::type_id::<T>;
        if !(ptr::fn_addr_eq(vtable.type_id, id) || (vtable.type_id)() == id()) {
            return None;
        }
        // SAFETY: the vtable is `T`'s, so the header starts a `T`, and `size_of` checked that its
        // items fit in the object. The caller holds no other view of it, and the `Collecting`
        // token means no step does.
        unsafe { Some(&mut *Object::<T>::at(self.header_ptr(offset)).items()) }
    }

    /// Wipes the header of an object that's gone, so stale references to it don't check out.
    #[inline]
    pub(super) fn clear_header(&self, offset: u32) {
        // SAFETY: only called for an object that was allocated, so the header is in a committed
        // page, and nothing borrows it.
        unsafe { self.header_ptr(offset).write(Header { ty: TypeIndex::new(0), flags: 0, len: 0 }) }
    }

    #[cfg(test)]
    pub(crate) fn vtable_size(&self, offset: u32) -> Option<usize> {
        let header = self.header(self.object_at(offset)?);
        (self.vtable(header.ty)?.size)(header)
    }

    /// The region offsets of the object at `offset`. They end where the page metadata says the
    /// next object starts, or its page run ends, so a damaged header can't stretch them over
    /// another object.
    pub(crate) fn object_span(&self, offset: u32) -> Option<Range<usize>> {
        let obj = self.object_at(offset)?;
        let (_, size) = self.size_of(obj)?;
        let (start, mut end) = (offset as usize, offset as usize + size);
        let p = self.page(obj.page);
        if p.kind.get() == Kind::Lines
            && let Some(next) = p.start.next(obj.granule + 1)
        {
            end = end.min(obj.page.granule(next) as usize);
        }
        Some(start..end)
    }

    #[cfg(test)]
    pub(crate) fn header_of(&self, offset: u32) -> *mut Header {
        self.header_ptr(offset)
    }
}
