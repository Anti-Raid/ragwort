use std::any::TypeId;
use std::marker::PhantomData;
use std::mem::{align_of, size_of};
use std::ptr;

use super::{Inline, Trace, Tracer};

/// Usable bytes per arena. Every heap reference is an offset below this.
pub const REGION: usize = if cfg!(miri) { 4 << 20 } else { 64 << 20 };
// The upper half is never handed out, so a masked offset plus any object span stays reserved.
pub(crate) const RESERVE: usize = 2 * REGION;
pub(crate) const PAGE_SHIFT: u32 = 14;
pub(crate) const PAGE: usize = 1 << PAGE_SHIFT;
pub(crate) const MAX_PAGES: usize = REGION / PAGE - 1;
pub(crate) const HEADER: usize = size_of::<Header>();
pub(crate) const MAX_ALIGN: usize = 8;
pub(crate) const OFFSET_MASK: u32 = ((REGION - 1) & !7) as u32;

/// Objects start on 8-byte granules; each page has a start bit and a mark bit per granule.
pub(crate) const GRANULE: usize = 8;
pub(crate) const GRANULES: usize = PAGE / GRANULE;
pub(crate) const WORDS: usize = GRANULES / 64;
/// Allocation reuses free 128-byte lines.
pub(crate) const LINE: usize = 128;
pub(crate) const LINES: usize = PAGE / LINE;
/// Writes dirty 512-byte cards, which minor collections and compaction rescan.
pub(crate) const CARD: usize = 512;
pub(crate) const CARDS: usize = PAGE / CARD;
/// Bigger objects get their own run of pages.
pub(crate) const MAX_SMALL: usize = PAGE / 2;

/// Header flag: the object was copied elsewhere during compaction, and `len` holds its new offset.
pub(crate) const FORWARDED: u16 = 1;
/// The header flags above this hold a stamp, set when the object is allocated.
pub(crate) const STAMP_SHIFT: u16 = 4;
pub(crate) const STAMPS: u16 = 1 << (16 - STAMP_SHIFT);

/// What a reference holds to check that its object is still the one it was made for: the
/// type index and the stamp, 28 bits.
pub(crate) const fn check_bits(header: Header) -> u32 {
    header.ty as u32 | ((header.flags >> STAMP_SHIFT) as u32) << 16
}

// Every object starts with a header: [Header][T] or [Header][T][items].
// A `Member` holds the header's offset; a `Gc` points at T.
#[derive(Clone, Copy)]
#[repr(C)]
pub(crate) struct Header {
    pub(crate) ty: u16,
    pub(crate) flags: u16,
    pub(crate) len: u32,
}

pub(crate) struct VTable {
    /// The type's id with lifetimes erased. Constants can be duplicated across codegen units,
    /// so two vtables at different addresses may describe the same type.
    pub(crate) type_id: fn() -> TypeId,
    pub(crate) needs_trace: bool,
    pub(crate) trace: unsafe fn(*mut Header, &mut Tracer<'_>),
    /// Traces only what overlaps bytes `from..to` of the object, counted from its header.
    pub(crate) trace_range: unsafe fn(*mut Header, usize, usize, &mut Tracer<'_>),
    pub(crate) size: fn(Header) -> Option<usize>,
}

pub(crate) const fn round_up(n: usize, align: usize) -> usize {
    (n + align - 1) & !(align - 1)
}

pub(crate) const fn sized_size<T>() -> usize {
    round_up(HEADER + size_of::<T>(), MAX_ALIGN)
}

pub(crate) const fn items_offset<T: Inline>() -> usize {
    round_up(size_of::<T>(), align_of::<T::Item>())
}

/// Whether `T` can sit in the arena: any reference to it from an offset below `REGION` then
/// stays inside the reservation and is aligned.
pub(crate) const fn fits<T>() -> bool {
    align_of::<T>() <= MAX_ALIGN && sized_size::<T>() <= REGION
}

/// [`fits`], plus the same for the items: the fixed part fits in a page, so items start
/// within one page of the header and [`max_items`] of them end inside the reservation.
pub(crate) const fn fits_inline<T: Inline>() -> bool {
    fits::<T>() && align_of::<T::Item>() <= MAX_ALIGN && HEADER + items_offset::<T>() <= PAGE
}

/// The largest length `alloc_inline` accepts.
pub(crate) const fn max_items<T: Inline>() -> usize {
    let item = size_of::<T::Item>();
    let room = REGION - PAGE - (HEADER + items_offset::<T>());
    room / if item == 0 { 1 } else { item }
}

pub(crate) fn inline_size<T: Inline>(len: usize) -> Option<usize> {
    let items = size_of::<T::Item>().checked_mul(len)?;
    let size = (HEADER + items_offset::<T>()).checked_add(items)?;
    Some(size.checked_add(MAX_ALIGN - 1)? & !(MAX_ALIGN - 1))
}

/// `TypeId::of` for types with lifetimes. Ids ignore lifetimes anyway, and arena types only
/// use them as brands, so two types that differ only in lifetimes are the same type here.
pub(crate) fn type_id<T: ?Sized>() -> TypeId {
    trait Erased {
        fn id(&self) -> TypeId
        where
            Self: 'static;
    }
    impl<T: ?Sized> Erased for PhantomData<T> {
        fn id(&self) -> TypeId
        where
            Self: 'static,
        {
            TypeId::of::<T>()
        }
    }
    let marker: &dyn Erased = &PhantomData::<T>;
    // Only the bound changes; `id` never sees a value of `T`.
    let marker: &(dyn Erased + 'static) = unsafe { std::mem::transmute(marker) };
    marker.id()
}

pub(crate) fn value_ptr<T>(header: *const Header) -> *mut T {
    header.cast::<u8>().wrapping_add(HEADER).cast::<T>().cast_mut()
}

pub(crate) fn header_ptr<T>(value: *const T) -> *const Header {
    value.cast::<u8>().wrapping_sub(HEADER).cast::<Header>()
}

pub(crate) fn inline_items<T: Inline>(value: *const T) -> *mut T::Item {
    value.cast::<u8>().wrapping_add(items_offset::<T>()).cast::<T::Item>().cast_mut()
}

pub(crate) struct SizedVTable<T>(PhantomData<T>);

impl<T: Trace> SizedVTable<T> {
    pub(crate) const VTABLE: VTable = VTable {
        type_id: type_id::<T>,
        needs_trace: T::NEEDS_TRACE,
        trace: Self::trace,
        trace_range: Self::trace_range,
        size: Self::size,
    };

    unsafe fn trace(header: *mut Header, t: &mut Tracer<'_>) {
        unsafe { (*value_ptr::<T>(header)).trace(t) }
    }

    unsafe fn trace_range(header: *mut Header, _: usize, _: usize, t: &mut Tracer<'_>) {
        unsafe { Self::trace(header, t) }
    }

    fn size(_: Header) -> Option<usize> {
        Some(sized_size::<T>())
    }
}

pub(crate) struct InlineVTable<T>(PhantomData<T>);

impl<T: Inline> InlineVTable<T> {
    pub(crate) const VTABLE: VTable = VTable {
        type_id: type_id::<T>,
        needs_trace: T::NEEDS_TRACE || <T::Item as Trace>::NEEDS_TRACE,
        trace: Self::trace,
        trace_range: Self::trace_range,
        size: Self::size,
    };

    unsafe fn trace(header: *mut Header, t: &mut Tracer<'_>) {
        unsafe { Self::trace_range(header, 0, usize::MAX, t) }
    }

    unsafe fn trace_range(header: *mut Header, from: usize, to: usize, t: &mut Tracer<'_>) {
        unsafe {
            let value = value_ptr::<T>(header);
            let items_at = HEADER + items_offset::<T>();
            if from < items_at {
                (*value).trace(t);
            }
            let item = size_of::<T::Item>();
            if <T::Item as Trace>::NEEDS_TRACE && item > 0 {
                let len = ((*header).len as usize).min(max_items::<T>());
                let first = from.saturating_sub(items_at) / item;
                let last = to.saturating_sub(items_at).div_ceil(item).min(len);
                if first < last {
                    let items = inline_items::<T>(value).add(first);
                    for item in &mut *ptr::slice_from_raw_parts_mut(items, last - first) {
                        item.trace(t);
                    }
                }
            }
        }
    }

    fn size(header: Header) -> Option<usize> {
        inline_size::<T>(header.len as usize)
    }
}
