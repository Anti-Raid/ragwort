use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::marker::PhantomData;
use std::num::NonZeroU32;

use super::heap::Heap;
#[cfg(any(test, feature = "gc-verify"))]
use super::heap::Verify;

/// # Safety
/// - `trace` must trace every `Member`, `HostRef` and `Ephemeron` held directly by `self`,
///   and must not otherwise change `self`. The collector may rewrite the references it visits,
///   because objects move between steps.
/// - References to arena objects must be held as `Member`, `AnyRef` or `Value` (or raw
///   offsets passed to [`Tracer::trace_raw`]), never as `Gc`, references or raw pointers.
/// - In arena objects, every field holding a reference that can change must be written
///   through [`Lock`] (or `set_unbarriered` followed by
///   [`Mutation::retrace`](super::Mutation::retrace)). Outside the arena, in the root, any
///   write is fine: the root is traced again before each collection finishes.
/// - `INLINE` must be true exactly when the type implements [`Inline`].
/// - `holds_refs` must be true whenever `trace` would visit a reference.
/// - `trace` should not panic. If it does, the arena is marked corrupted.
/// - The `'gc` lifetime may only brand arena handles (`Member`, `HostRef`, `GcVec`, ...). A
///   type must not use it, or any other lifetime, for ordinary borrows, because roots and
///   the arena root are kept past the step that created them.
///
/// Types allocated in the arena must also be [`Plain`].
///
/// [`Lock::set`]: super::Lock::set
pub unsafe trait Trace {
    const NEEDS_TRACE: bool = true;
    const INLINE: bool = false;

    fn trace(&mut self, t: &mut Tracer<'_>);

    /// Whether this value holds a reference. Storing one that doesn't skips the barrier.
    #[inline]
    fn holds_refs(&self) -> bool {
        Self::NEEDS_TRACE
    }
}

/// Types that can be stored in arena memory, branded with the arena's `'gc`. Derive it
/// rather than implementing it.
///
/// # Safety
/// - Every bit pattern must be a valid value of the type, and the type must have no padding
///   bytes. Corrupted or type-confused arena memory then always reads as some valid value.
/// - Every arena handle the type holds must carry the brand `'gc`. Otherwise a type viewed
///   with an older brand, such as `'static`, could carry references between arenas.
pub unsafe trait Plain<'gc> {
    /// Evaluated wherever arena memory is read as this type; the derive makes it fail to
    /// compile if a field isn't `Plain` or the type has padding.
    #[doc(hidden)]
    const CHECK: () = ();
}

macro_rules! plain {
    ($($t:ty),* $(,)?) => {$(unsafe impl<'gc> Plain<'gc> for $t {})*};
}

plain!((), u8, u16, u32, u64, usize, i8, i16, i32, i64, isize, f32, f64);

unsafe impl<T: ?Sized> Plain<'_> for PhantomData<T> {}

unsafe impl<'gc, T: Plain<'gc>, const N: usize> Plain<'gc> for [T; N] {
    const CHECK: () = T::CHECK;
}

/// A head type whose items are stored inline after it in the same allocation.
///
/// # Safety
/// `Trace::trace` covers the head only; the heap traces the items.
pub unsafe trait Inline: Trace {
    type Item: Trace;
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Mode {
    /// Marks what it reaches, and remembers slots that point into pages being compacted.
    Mark,
    /// Marks the value a write barrier stores.
    Barrier,
    /// Rewrites references to objects that compaction moved.
    Fixup,
    /// Clears ephemerons whose keys died.
    Clear,
    #[cfg(any(test, feature = "gc-verify"))]
    Verify,
}

/// What an ephemeron does with its value after the tracer looked at its key.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum KeyState {
    Live,
    Pending,
    Dead,
}

pub struct Tracer<'a> {
    heap: &'a Heap,
    mode: Mode,
    #[cfg(any(test, feature = "gc-verify"))]
    verify: Option<&'a mut Verify>,
}

impl<'a> Tracer<'a> {
    pub(crate) fn new(heap: &'a Heap, mode: Mode) -> Self {
        Self {
            heap,
            mode,
            #[cfg(any(test, feature = "gc-verify"))]
            verify: None,
        }
    }

    #[cfg(any(test, feature = "gc-verify"))]
    pub(crate) fn verifying(heap: &'a Heap, verify: &'a mut Verify) -> Self {
        Self { heap, mode: Mode::Verify, verify: Some(verify) }
    }

    pub(crate) fn mode(&self) -> Mode {
        self.mode
    }

    /// Traces the object whose header is at `*offset` in this arena, and updates `*offset` if
    /// the object moved. Zero is ignored, and an offset that isn't a live object marks the
    /// arena as corrupted.
    pub fn trace_raw(&mut self, offset: &mut u32) {
        if *offset != 0 {
            let slot = (offset as *mut u32).addr();
            if let Some(moved) = self.edge(*offset, slot) {
                *offset = moved;
            }
        }
    }

    /// Traces a reference word, after checking it against its object's header.
    pub(crate) fn value(&mut self, word: &mut u64) {
        let slot = (word as *mut u64).addr();
        let offset = (*word >> 32) as u32;
        if !self.heap.checks_out(offset, (*word >> 4) as u32 & ((1 << 28) - 1)) {
            return;
        }
        if let Some(moved) = self.edge(offset, slot) {
            *word = (*word & u32::MAX as u64) | (moved as u64) << 32;
        }
    }

    pub(crate) fn member(&mut self, offset: &mut NonZeroU32) {
        let slot = (offset as *mut NonZeroU32).addr();
        if let Some(moved) = self.edge(offset.get(), slot).and_then(NonZeroU32::new) {
            *offset = moved;
        }
    }

    fn edge(&mut self, offset: u32, slot: usize) -> Option<u32> {
        match self.mode {
            Mode::Mark => {
                self.heap.shade(offset);
                self.heap.note_slot(offset, slot);
                None
            }
            Mode::Barrier => {
                self.heap.shade(offset);
                None
            }
            Mode::Fixup => self.heap.forwarded(offset),
            Mode::Clear => None,
            #[cfg(any(test, feature = "gc-verify"))]
            Mode::Verify => {
                if let Some(verify) = self.verify.as_deref_mut() {
                    verify.visit(self.heap, offset);
                }
                None
            }
        }
    }

    /// Looks at an ephemeron's key, rewriting it if it moved.
    pub(crate) fn ephemeron_key(&mut self, key: &mut NonZeroU32) -> KeyState {
        let slot = (key as *mut NonZeroU32).addr();
        let offset = key.get();
        match self.mode {
            // Outside the arena, as in the arena root, an ephemeron holds its key strongly.
            Mode::Mark if !self.heap.in_region(slot) => {
                self.heap.shade(offset);
                KeyState::Live
            }
            Mode::Mark => {
                self.heap.note_slot(offset, slot);
                if self.heap.is_live(offset) {
                    KeyState::Live
                } else {
                    self.heap.pending(slot);
                    KeyState::Pending
                }
            }
            Mode::Barrier => {
                self.heap.shade(offset);
                KeyState::Live
            }
            Mode::Fixup => {
                if let Some(moved) = self.heap.forwarded(offset).and_then(NonZeroU32::new) {
                    *key = moved;
                }
                KeyState::Live
            }
            Mode::Clear if self.heap.in_region(slot) && !self.heap.is_live(offset) => KeyState::Dead,
            Mode::Clear => KeyState::Pending,
            #[cfg(any(test, feature = "gc-verify"))]
            Mode::Verify => {
                if self.heap.is_live(offset) || !self.heap.in_region(slot) {
                    self.edge(offset, slot);
                    KeyState::Live
                } else {
                    KeyState::Pending
                }
            }
        }
    }

    pub(crate) fn trace_host(&mut self, index: u32, generation: u32) {
        match self.mode {
            Mode::Mark | Mode::Barrier => {
                if !self.heap.hosts.mark(index, generation) {
                    self.heap.corrupt();
                }
            }
            Mode::Fixup | Mode::Clear => {}
            #[cfg(any(test, feature = "gc-verify"))]
            Mode::Verify => {
                if !self.heap.hosts.is_live(index, generation) {
                    return self.heap.corrupt();
                }
                assert!(self.heap.hosts.is_marked(index, generation), "gc verify: reachable host value is not marked");
            }
        }
    }
}

macro_rules! leaf {
    ($($t:ty),* $(,)?) => {$(
        unsafe impl Trace for $t {
            const NEEDS_TRACE: bool = false;

            #[inline]
            fn trace(&mut self, _: &mut Tracer<'_>) {}
        }
    )*};
}

leaf!((), bool, char, u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize, f32, f64, String);

unsafe impl Trace for str {
    const NEEDS_TRACE: bool = false;

    fn trace(&mut self, _: &mut Tracer<'_>) {}
}

unsafe impl<T: ?Sized> Trace for PhantomData<T> {
    const NEEDS_TRACE: bool = false;

    fn trace(&mut self, _: &mut Tracer<'_>) {}
}

unsafe impl<T: Trace> Trace for Option<T> {
    const NEEDS_TRACE: bool = T::NEEDS_TRACE;

    fn trace(&mut self, t: &mut Tracer<'_>) {
        if let Some(v) = self {
            v.trace(t);
        }
    }

    #[inline]
    fn holds_refs(&self) -> bool {
        T::NEEDS_TRACE && self.as_ref().is_some_and(T::holds_refs)
    }
}

unsafe impl<T: Trace, const N: usize> Trace for [T; N] {
    const NEEDS_TRACE: bool = T::NEEDS_TRACE;

    fn trace(&mut self, t: &mut Tracer<'_>) {
        if T::NEEDS_TRACE {
            for v in self {
                v.trace(t);
            }
        }
    }
}

macro_rules! tuple {
    ($($name:ident),+) => {
        unsafe impl<$($name: Trace),+> Trace for ($($name,)+) {
            const NEEDS_TRACE: bool = false $(|| $name::NEEDS_TRACE)+;

            #[allow(non_snake_case)]
            fn trace(&mut self, t: &mut Tracer<'_>) {
                let ($($name,)+) = self;
                $($name.trace(t);)+
            }
        }
    };
}

tuple!(A);
tuple!(A, B);
tuple!(A, B, C);
tuple!(A, B, C, D);

// Containers for the root and other host-side state. None of them is `Plain`, so none of
// them can end up in the arena, where writes would need a barrier.

unsafe impl<T: Trace> Trace for [T] {
    const NEEDS_TRACE: bool = T::NEEDS_TRACE;

    fn trace(&mut self, t: &mut Tracer<'_>) {
        if T::NEEDS_TRACE {
            for v in self {
                v.trace(t);
            }
        }
    }
}

unsafe impl<T: Trace + ?Sized> Trace for Box<T> {
    const NEEDS_TRACE: bool = T::NEEDS_TRACE;

    fn trace(&mut self, t: &mut Tracer<'_>) {
        (**self).trace(t);
    }
}

unsafe impl<T: Trace> Trace for Vec<T> {
    const NEEDS_TRACE: bool = T::NEEDS_TRACE;

    fn trace(&mut self, t: &mut Tracer<'_>) {
        self.as_mut_slice().trace(t);
    }
}

unsafe impl<T: Trace> Trace for VecDeque<T> {
    const NEEDS_TRACE: bool = T::NEEDS_TRACE;

    fn trace(&mut self, t: &mut Tracer<'_>) {
        if T::NEEDS_TRACE {
            for v in self {
                v.trace(t);
            }
        }
    }
}

unsafe impl<T: Trace + Copy> Trace for Cell<T> {
    const NEEDS_TRACE: bool = T::NEEDS_TRACE;

    fn trace(&mut self, t: &mut Tracer<'_>) {
        self.get_mut().trace(t);
    }
}

// Collections only run between steps, when nothing can hold a borrow.
unsafe impl<T: Trace + ?Sized> Trace for RefCell<T> {
    const NEEDS_TRACE: bool = T::NEEDS_TRACE;

    fn trace(&mut self, t: &mut Tracer<'_>) {
        self.get_mut().trace(t);
    }
}

// Keys can't hold references: rewriting a key after its object moved would break the map.
macro_rules! map {
    ($($map:ident<$($extra:ident),*>),*) => {$(
        unsafe impl<K: Trace, V: Trace $(, $extra)*> Trace for $map<K, V $(, $extra)*> {
            const NEEDS_TRACE: bool = V::NEEDS_TRACE;

            fn trace(&mut self, t: &mut Tracer<'_>) {
                const { assert!(!K::NEEDS_TRACE, "map keys can't hold arena references") };
                if V::NEEDS_TRACE {
                    for v in self.values_mut() {
                        v.trace(t);
                    }
                }
            }
        }
    )*};
}

map!(HashMap<S>, BTreeMap<>);

macro_rules! set {
    ($($set:ident<$($extra:ident),*>),*) => {$(
        unsafe impl<T: Trace $(, $extra)*> Trace for $set<T $(, $extra)*> {
            const NEEDS_TRACE: bool = false;

            fn trace(&mut self, _: &mut Tracer<'_>) {
                const { assert!(!T::NEEDS_TRACE, "set elements can't hold arena references") };
            }
        }
    )*};
}

set!(HashSet<S>, BTreeSet<>);
