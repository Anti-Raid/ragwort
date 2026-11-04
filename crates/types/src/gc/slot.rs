//! What an object's field can hold, named as `objects!` declarations name it. Each kind knows
//! which of the collector's masks its word belongs to, the Rust type it reads back as, and which
//! barrier a write takes.

use std::any::Any;
use std::marker::PhantomData;

use super::{AnyHostRef, FrozenRef, Gc, HostRef, Items, Mutation, OBJECT, Object, Raw, RegionWords, TAG};

pub use core::primitive::{bool, f64, i64, u32, u64};

/// A [`Value`](super::Value).
pub struct Value;

/// An object of type `T`, or none. Reads check the target's type.
pub struct Member<T>(PhantomData<fn() -> T>);

/// Like [`Member`], but doesn't keep the target alive: it reads as none once the target dies.
pub struct Weak<T>(PhantomData<fn() -> T>);

/// Host data of type `T`, or none.
pub struct Host<T>(PhantomData<fn() -> T>);

/// Host data of any type, or none.
pub struct AnyHost;

/// A write-once `T` outside the region, read as `&'gc T`.
pub struct Frozen<T>(PhantomData<fn() -> T>);

/// A key and a value, two words. The value is kept alive only while the key is reachable some
/// other way; once the key dies, the field reads as none.
pub struct Ephemeron;

/// What an item's word refers to, which decides its barrier.
#[doc(hidden)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Refs {
    None,
    Values,
    Members,
    Weaks,
}

impl Refs {
    pub(super) const fn of(items: Items) -> Option<Self> {
        match items {
            Items::Words => Some(Self::None),
            Items::Values => Some(Self::Values),
            Items::Members => Some(Self::Members),
            Items::Weaks => Some(Self::Weaks),
            Items::None | Items::Ephemerons => None,
        }
    }

    /// The object a word refers to.
    #[inline]
    pub(super) fn target(self, word: u64) -> Option<u32> {
        match self {
            Self::None => None,
            Self::Values => (word & TAG == OBJECT).then_some((word >> 32) as u32),
            Self::Members | Self::Weaks => Some(word as u32).filter(|&t| t != 0),
        }
    }

    #[inline]
    pub(super) fn refers(self, word: u64) -> bool {
        self.target(word).is_some()
    }
}

/// Which of the collector's masks a field is in.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Role {
    Word,
    Value,
    Member,
    Weak,
    Host,
    Frozen,
    Ephemeron,
}

mod sealed {
    pub trait Sealed {}
}

/// A kind of field. Sealed: the collector traces only these.
pub trait Slot: sealed::Sealed + 'static {
    const ROLE: Role;
    /// What a read gives.
    type Out<'gc>;
    /// What a write takes.
    type In<'gc>;

    #[doc(hidden)]
    fn get<'gc, T: Object>(gc: Gc<'gc, T>, mc: &Mutation<'gc>, field: usize) -> Self::Out<'gc>;

    #[doc(hidden)]
    fn set<'gc, T: Object>(gc: Gc<'gc, T>, mc: &Mutation<'gc>, field: usize, value: Self::In<'gc>);

    /// Writes a new object's words for the field, all the words the role takes.
    #[doc(hidden)]
    fn init(value: Self::In<'_>, words: &mut [u64]);
}

/// A kind of field that can also be an object's items: one word each.
pub trait Item: Slot {
    const ITEMS: Items;
    #[doc(hidden)]
    const REFS: Refs;

    /// Reads an item's word; `region` is for checking what an index refers to.
    #[doc(hidden)]
    fn load<'gc>(region: &'gc RegionWords, word: u64) -> Self::Out<'gc>;

    #[doc(hidden)]
    fn store(value: Self::In<'_>) -> u64;
}

macro_rules! words {
    ($($ty:ident: |$w:ident| $load:expr, |$v:ident| $store:expr;)*) => {$(
        impl sealed::Sealed for $ty {}

        impl Slot for $ty {
            const ROLE: Role = Role::Word;
            type Out<'gc> = $ty;
            type In<'gc> = $ty;

            #[inline]
            fn get<'gc, T: Object>(gc: Gc<'gc, T>, mc: &Mutation<'gc>, field: usize) -> $ty {
                Self::load(mc.heap.words, gc.word(mc, field))
            }

            #[inline]
            fn set<'gc, T: Object>(gc: Gc<'gc, T>, mc: &Mutation<'gc>, field: usize, value: $ty) {
                gc.set_word(mc, field, Self::store(value));
            }

            #[inline]
            fn init(value: $ty, words: &mut [u64]) {
                words[0] = Self::store(value);
            }
        }

        impl Item for $ty {
            const ITEMS: Items = Items::Words;
            const REFS: Refs = Refs::None;

            #[inline]
            fn load<'gc>(_: &'gc RegionWords, $w: u64) -> Self::Out<'gc> {
                $load
            }

            #[inline]
            fn store($v: $ty) -> u64 {
                $store
            }
        }
    )*};
}

words! {
    u64: |w| w, |v| v;
    i64: |w| w as i64, |v| v as u64;
    u32: |w| w as u32, |v| u64::from(v);
    f64: |w| f64::from_bits(w), |v| v.to_bits();
    bool: |w| w != 0, |v| u64::from(v);
}

impl sealed::Sealed for Value {}

impl Slot for Value {
    const ROLE: Role = Role::Value;
    type Out<'gc> = super::Value<'gc>;
    type In<'gc> = super::Value<'gc>;

    #[inline]
    fn get<'gc, T: Object>(gc: Gc<'gc, T>, mc: &Mutation<'gc>, field: usize) -> super::Value<'gc> {
        gc.value(mc, field)
    }

    #[inline]
    fn set<'gc, T: Object>(gc: Gc<'gc, T>, mc: &Mutation<'gc>, field: usize, value: super::Value<'gc>) {
        gc.set_value(mc, field, value);
    }

    #[inline]
    fn init(value: super::Value<'_>, words: &mut [u64]) {
        words[0] = value.to_bits();
    }
}

impl Item for Value {
    const ITEMS: Items = Items::Values;
    const REFS: Refs = Refs::Values;

    #[inline]
    fn load<'gc>(_: &'gc RegionWords, word: u64) -> super::Value<'gc> {
        super::Value::from_bits(word)
    }

    #[inline]
    fn store(value: super::Value<'_>) -> u64 {
        value.to_bits()
    }
}

impl<U: Object> sealed::Sealed for Member<U> {}

impl<U: Object> Slot for Member<U> {
    const ROLE: Role = Role::Member;
    type Out<'gc> = Option<Gc<'gc, U>>;
    type In<'gc> = Option<Gc<'gc, U>>;

    #[inline]
    fn get<'gc, T: Object>(gc: Gc<'gc, T>, mc: &Mutation<'gc>, field: usize) -> Option<Gc<'gc, U>> {
        super::target(mc.heap.words, gc.word(mc, field) as u32)
    }

    #[inline]
    fn set<'gc, T: Object>(gc: Gc<'gc, T>, mc: &Mutation<'gc>, field: usize, value: Option<Gc<'gc, U>>) {
        gc.set_member(mc, field, value);
    }

    #[inline]
    fn init(value: Option<Gc<'_, U>>, words: &mut [u64]) {
        words[0] = value.map_or(0, Raw::to_word);
    }
}

impl<U: Object> Item for Member<U> {
    const ITEMS: Items = Items::Members;
    const REFS: Refs = Refs::Members;

    #[inline]
    fn load<'gc>(region: &'gc RegionWords, word: u64) -> Option<Gc<'gc, U>> {
        super::target(region, word as u32)
    }

    #[inline]
    fn store(value: Option<Gc<'_, U>>) -> u64 {
        value.map_or(0, Raw::to_word)
    }
}

impl<U: Object> sealed::Sealed for Weak<U> {}

impl<U: Object> Slot for Weak<U> {
    const ROLE: Role = Role::Weak;
    type Out<'gc> = Option<Gc<'gc, U>>;
    type In<'gc> = Option<Gc<'gc, U>>;

    #[inline]
    fn get<'gc, T: Object>(gc: Gc<'gc, T>, mc: &Mutation<'gc>, field: usize) -> Option<Gc<'gc, U>> {
        super::target(mc.heap.words, gc.word(mc, field) as u32)
    }

    #[inline]
    fn set<'gc, T: Object>(gc: Gc<'gc, T>, mc: &Mutation<'gc>, field: usize, value: Option<Gc<'gc, U>>) {
        gc.set_weak(mc, field, value);
    }

    #[inline]
    fn init(value: Option<Gc<'_, U>>, words: &mut [u64]) {
        words[0] = value.map_or(0, Raw::to_word);
    }
}

impl<U: Object> Item for Weak<U> {
    const ITEMS: Items = Items::Weaks;
    const REFS: Refs = Refs::Weaks;

    /// `None` once the target has died.
    #[inline]
    fn load<'gc>(region: &'gc RegionWords, word: u64) -> Option<Gc<'gc, U>> {
        super::target(region, word as u32)
    }

    #[inline]
    fn store(value: Option<Gc<'_, U>>) -> u64 {
        value.map_or(0, Raw::to_word)
    }
}

impl<U: Any> sealed::Sealed for Host<U> {}

impl<U: Any> Slot for Host<U> {
    const ROLE: Role = Role::Host;
    type Out<'gc> = Option<HostRef<'gc, U>>;
    type In<'gc> = Option<HostRef<'gc, U>>;

    #[inline]
    fn get<'gc, T: Object>(gc: Gc<'gc, T>, mc: &Mutation<'gc>, field: usize) -> Option<HostRef<'gc, U>> {
        gc.host(mc, field).map(AnyHostRef::assume)
    }

    #[inline]
    fn set<'gc, T: Object>(gc: Gc<'gc, T>, mc: &Mutation<'gc>, field: usize, value: Option<HostRef<'gc, U>>) {
        AnyHost::set(gc, mc, field, value.map(HostRef::erase));
    }

    #[inline]
    fn init(value: Option<HostRef<'_, U>>, words: &mut [u64]) {
        words[0] = value.map_or(0, HostRef::to_word);
    }
}

impl sealed::Sealed for AnyHost {}

impl Slot for AnyHost {
    const ROLE: Role = Role::Host;
    type Out<'gc> = Option<AnyHostRef<'gc>>;
    type In<'gc> = Option<AnyHostRef<'gc>>;

    #[inline]
    fn get<'gc, T: Object>(gc: Gc<'gc, T>, mc: &Mutation<'gc>, field: usize) -> Option<AnyHostRef<'gc>> {
        gc.host(mc, field)
    }

    #[inline]
    fn set<'gc, T: Object>(gc: Gc<'gc, T>, mc: &Mutation<'gc>, field: usize, value: Option<AnyHostRef<'gc>>) {
        match value {
            Some(host) => gc.set_host(mc, field, host),
            None => gc.set_word(mc, field, 0),
        }
    }

    #[inline]
    fn init(value: Option<AnyHostRef<'_>>, words: &mut [u64]) {
        words[0] = value.map_or(0, AnyHostRef::to_word);
    }
}

impl sealed::Sealed for Ephemeron {}

impl Slot for Ephemeron {
    const ROLE: Role = Role::Ephemeron;
    type Out<'gc> = Option<(super::Value<'gc>, super::Value<'gc>)>;
    type In<'gc> = (super::Value<'gc>, super::Value<'gc>);

    #[inline]
    fn get<'gc, T: Object>(gc: Gc<'gc, T>, mc: &Mutation<'gc>, field: usize) -> Self::Out<'gc> {
        gc.ephemeron(mc, field)
    }

    #[inline]
    fn set<'gc, T: Object>(gc: Gc<'gc, T>, mc: &Mutation<'gc>, field: usize, (key, value): Self::In<'gc>) {
        gc.set_ephemeron(mc, field, key, value);
    }

    #[inline]
    fn init((key, value): Self::In<'_>, words: &mut [u64]) {
        words[0] = key.to_bits();
        words[1] = value.to_bits();
    }
}

/// A frozen value written into an object already marked, old or traced, would be missed by the
/// collections that don't trace the object again, so it's marked now.
#[inline]
fn set_frozen<'gc, T: Object>(gc: Gc<'gc, T>, mc: &Mutation<'gc>, field: usize, word: u64) {
    gc.set_word(mc, field, word);
    if mc.heap.has_bit(gc.to_word() as usize, |p| &p.marks) {
        mc.heap.m.frozen.mark(word);
    }
}

impl<U: Any> sealed::Sealed for Frozen<U> {}

impl<U: Any> Slot for Frozen<U> {
    const ROLE: Role = Role::Frozen;
    type Out<'gc> = Option<&'gc U>;
    type In<'gc> = FrozenRef<'gc, U>;

    #[inline]
    fn get<'gc, T: Object>(gc: Gc<'gc, T>, mc: &Mutation<'gc>, field: usize) -> Option<&'gc U> {
        mc.heap.m.frozen.get(gc.word(mc, field))
    }

    #[inline]
    fn set<'gc, T: Object>(gc: Gc<'gc, T>, mc: &Mutation<'gc>, field: usize, value: FrozenRef<'gc, U>) {
        set_frozen(gc, mc, field, value.to_word());
    }

    #[inline]
    fn init(value: FrozenRef<'_, U>, words: &mut [u64]) {
        words[0] = value.to_word();
    }
}
