use std::fmt;
use std::marker::PhantomData;
use std::num::NonZeroU32;
use std::ops::Deref;
use std::ptr::NonNull;

use super::layout::{self, Check, HEADER, Object, OFFSET_MASK, TypeIndex, type_id};
use super::{Inline, Invariant, Mutation, OutOfMemory, Plain, Trace, Tracer};

/// A full pointer to an arena object, for use inside a step. Store a [`Member`] instead.
pub struct Gc<'gc, T> {
    ptr: NonNull<T>,
    _brand: Invariant<'gc>,
}

impl<'gc, T> Gc<'gc, T> {
    /// # Safety
    /// `ptr` must point at the value of an object in the current arena's region.
    pub(crate) unsafe fn from_raw(ptr: NonNull<T>) -> Self
    where
        T: Plain<'gc>,
    {
        // Corrupted region bytes can produce a `Member<T>` for any `T`, allocated or not, so
        // the layout is checked here, where every reference into the arena is made.
        const {
            let () = T::CHECK;
            assert!(layout::fits::<T>(), "type is too large or too aligned for the arena");
        };
        Self { ptr, _brand: PhantomData }
    }

    #[allow(clippy::should_implement_trait)]
    pub fn as_ref(this: Self) -> &'gc T {
        // SAFETY: [refs, steps, alias] `from_raw` made it for a `T` in this arena's region. Objects
        // only move or die in collections, which can't run during `'gc`, and arena memory is only
        // written through cells then, so a shared borrow holds.
        unsafe { this.ptr.as_ref() }
    }

    pub fn as_ptr(this: Self) -> *const T {
        this.ptr.as_ptr()
    }

    pub fn ptr_eq(a: Self, b: Self) -> bool {
        a.ptr == b.ptr
    }
}

impl<'gc, T: Inline> Gc<'gc, T> {
    fn object(self) -> Object<T> {
        const { assert!(T::INLINE && layout::fits_inline::<T>(), "type is too large or too aligned for the arena") };
        // SAFETY: [refs, steps] `from_raw` made it for the value of an object holding a `T`, which
        // doesn't move during `'gc`.
        unsafe { Object::of_value(self.ptr.as_ptr()) }
    }

    pub fn items(self) -> &'gc [T::Item] {
        self.items_accessed(self.len());
        // SAFETY: the access hook above accounts for the exposed slice.
        unsafe { self.items_untracked() }
    }

    /// # Safety
    /// The caller must provide the bookkeeping normally done by `Inline::items_accessed`.
    pub(crate) unsafe fn items_untracked(self) -> &'gc [T::Item] {
        // SAFETY: [headers, alias] the header's length is the object's own item count, so the
        // items are inside the object, and they're borrowed shared as in `as_ref`.
        unsafe { &*self.object().items() }
    }

    pub fn len(self) -> usize {
        self.object().len()
    }

    pub fn is_empty(self) -> bool {
        self.len() == 0
    }
}

impl<T> Clone for Gc<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Gc<'_, T> {}

impl<T> Deref for Gc<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        // SAFETY: as in `as_ref`.
        unsafe { self.ptr.as_ref() }
    }
}

impl<T> fmt::Debug for Gc<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Gc").field(&self.ptr).finish()
    }
}

/// A 4-byte reference to an arena object: its offset in the arena's region.
pub struct Member<'gc, T> {
    offset: NonZeroU32,
    _marker: PhantomData<(Invariant<'gc>, fn() -> T)>,
}

impl<'gc, T> Member<'gc, T> {
    pub fn new(mc: &Mutation<'gc>, gc: Gc<'gc, T>) -> Self {
        let offset = gc.ptr.as_ptr().addr() - mc.base.as_ptr().addr() - HEADER;
        Self { offset: NonZeroU32::new(offset as u32).unwrap_or(NonZeroU32::MIN), _marker: PhantomData }
    }

    pub fn get(self, mc: &Mutation<'gc>) -> Gc<'gc, T>
    where
        T: Plain<'gc>,
    {
        let offset = (self.offset.get() & OFFSET_MASK) as usize;
        // SAFETY: [refs, memory] the offset names a live `T` in this arena's region. Masked, it
        // stays aligned and inside the reservation whatever the bits, as `from_raw` checks
        // that `T` fits.
        unsafe { Gc::from_raw(mc.base.add(offset + HEADER).cast()) }
    }

    /// # Safety
    /// `offset` must be a live `T`'s in this arena, kept where the collector traces it so it's
    /// rewritten when the object moves.
    pub(crate) unsafe fn from_offset(offset: NonZeroU32) -> Self {
        Self { offset, _marker: PhantomData }
    }

    /// # Safety
    /// Only a new offset for the same object may be written, as the tracer does when the
    /// object moves.
    pub(crate) unsafe fn offset_mut(&mut self) -> &mut NonZeroU32 {
        &mut self.offset
    }

    /// The object's offset. It only holds until the step ends: a collection can move the
    /// object, so don't use it as a lasting identity, such as an `eq?` hash.
    pub fn to_bits(self) -> NonZeroU32 {
        self.offset
    }

    /// # Safety
    /// `bits` must come from [`Member::to_bits`] on a `Member<T>` of the same arena, in the
    /// same step.
    #[cfg(test)]
    pub(crate) unsafe fn from_bits(bits: NonZeroU32) -> Self {
        Self { offset: bits, _marker: PhantomData }
    }
}

impl<T> Clone for Member<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Member<'_, T> {}

impl<T> PartialEq for Member<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        self.offset == other.offset
    }
}

impl<T> Eq for Member<'_, T> {}

impl<T> fmt::Debug for Member<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Member({:#x})", self.offset)
    }
}

// SAFETY: [plain, brand] `Option<NonZeroU32>` accepts every `u32`; a bare `Member` doesn't accept
// zero. No `T: Plain<'gc>` bound: it would make every self-referential type a trait cycle. Reading
// through the member needs `T: Plain<'gc>` anyway, which keeps the brand.
unsafe impl<'gc, T> Plain<'gc> for Option<Member<'gc, T>> {}

// SAFETY: hands its one reference to the tracer, which may rewrite it.
unsafe impl<T> Trace for Member<'_, T> {
    #[inline]
    fn trace(&mut self, t: &mut Tracer<'_>) {
        t.member(&mut self.offset);
    }
}

/// The low bits of a reference word, as a [`Value`](super::Value) holds it.
pub(crate) const OBJECT_TAG: u64 = 0b0001;

/// A reference to an arena object of any type. [`AnyRef::downcast`] checks the type.
///
/// Besides the offset it holds check bits from the object's header, the type index and an
/// allocation stamp, so a reference that outlived its object is caught when it's used.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct AnyRef<'gc> {
    word: u64,
    _brand: Invariant<'gc>,
}

impl<'gc> AnyRef<'gc> {
    pub fn new<T>(mc: &Mutation<'gc>, gc: Gc<'gc, T>) -> Self {
        Self::from_member(mc, Member::new(mc, gc))
    }

    pub fn from_member<T>(mc: &Mutation<'gc>, member: Member<'gc, T>) -> Self {
        let offset = member.offset.get();
        let check = mc.heap.check_at(offset);
        // SAFETY: [refs] the offset of a live object, with the check bits of its header.
        unsafe { Self::from_word((offset as u64) << 32 | check.to_word() | OBJECT_TAG) }
    }

    fn offset(self) -> u32 {
        (self.word >> 32) as u32
    }

    fn check(self) -> Check {
        Check::in_word(self.word)
    }

    /// # Safety
    /// The object must be a `T`, as [`AnyRef::is`] or a type tag checks.
    unsafe fn member<T>(self) -> Member<'gc, T> {
        let offset = NonZeroU32::new(self.offset()).unwrap_or(NonZeroU32::MIN);
        Member { offset, _marker: PhantomData }
    }

    /// Whether the object is a `T`. Types that differ only in lifetimes count as the same.
    pub fn is<T: Plain<'gc> + 'gc>(self, mc: &Mutation<'gc>) -> bool {
        mc.heap.has_type(self.offset(), self.check(), type_id::<T>)
    }

    pub fn downcast<T: Plain<'gc> + 'gc>(self, mc: &Mutation<'gc>) -> Option<Gc<'gc, T>> {
        self.downcast_member(mc).map(|m| m.get(mc))
    }

    pub fn downcast_member<T: Plain<'gc> + 'gc>(self, mc: &Mutation<'gc>) -> Option<Member<'gc, T>> {
        // SAFETY: [refs] `is` just found the object to be a `T`.
        self.is::<T>(mc).then(|| unsafe { self.member() })
    }

    /// Like [`AnyRef::downcast`], but compares a single number.
    #[inline]
    pub fn downcast_tag<T: Plain<'gc> + 'gc>(self, mc: &Mutation<'gc>, tag: TypeTag<'gc, T>) -> Option<Gc<'gc, T>> {
        // SAFETY: [refs] the object's header just matched `T`'s type index and the check bits.
        mc.heap.has_type_index(self.offset(), self.check(), tag.ty).then(|| unsafe { self.member() }.get(mc))
    }

    /// The reference as a word. Its offset only holds until the step ends, as with
    /// [`Member::to_bits`].
    pub fn to_bits(self) -> u64 {
        self.word
    }

    /// # Safety
    /// `bits` must come from [`AnyRef::to_bits`] in the same arena, in the same step.
    #[cfg(test)]
    pub(crate) unsafe fn from_bits(bits: u64) -> Self {
        // SAFETY: [refs] passed on to the caller.
        unsafe { Self::from_word(bits) }
    }

    /// # Safety
    /// `word` must be a live object's reference word in this arena: its offset, the check bits
    /// of its header, and the object tag.
    pub(crate) const unsafe fn from_word(word: u64) -> Self {
        Self { word, _brand: PhantomData }
    }
}

/// `T`'s type index in one arena, for downcasts that compare a single number. It can't leave
/// the step, so get it again each step with [`Mutation::type_tag`].
pub struct TypeTag<'gc, T> {
    ty: TypeIndex,
    _marker: PhantomData<(Invariant<'gc>, fn() -> T)>,
}

impl<T> Clone for TypeTag<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for TypeTag<'_, T> {}

impl<T> fmt::Debug for TypeTag<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TypeTag({})", self.ty.get())
    }
}

impl<'gc> Mutation<'gc> {
    /// The tag for a type allocated with [`Mutation::alloc`]. Fails only if the arena already
    /// has 65536 types.
    pub fn type_tag<T: Trace + Plain<'gc> + 'gc>(&self) -> Result<TypeTag<'gc, T>, OutOfMemory> {
        Ok(TypeTag { ty: self.heap.sized_type::<T>()?, _marker: PhantomData })
    }

    /// The tag for a type allocated with [`Mutation::alloc_inline`].
    pub fn inline_type_tag<T: Inline + Plain<'gc> + 'gc>(&self) -> Result<TypeTag<'gc, T>, OutOfMemory> {
        Ok(TypeTag { ty: self.heap.inline_type::<T>()?, _marker: PhantomData })
    }
}

impl fmt::Debug for AnyRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AnyRef({:#x})", self.offset())
    }
}

// SAFETY: [plain] one `u64` and a brand. Any word is valid: the check bits are compared against the
// object's header before use.
unsafe impl<'gc> Plain<'gc> for AnyRef<'gc> {}

// SAFETY: hands its one reference to the tracer, which may rewrite it.
unsafe impl Trace for AnyRef<'_> {
    #[inline]
    fn trace(&mut self, t: &mut Tracer<'_>) {
        t.value(&mut self.word);
    }
}
