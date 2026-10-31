//! What an object's field can hold, named as `objects!` declarations name it. Each kind knows
//! which of the collector's masks its word belongs to, the Rust type it reads back as, and which
//! barrier a write takes.

use std::any::Any;
use std::marker::PhantomData;

use super::{Gc, HostRef, Items, Mutation, Object, Raw};

pub use core::primitive::{bool, f64, i64, u32, u64};

/// A [`Value`](super::Value).
pub struct Value;

/// An object of type `T`, or none. Reads check the target's type.
pub struct Member<T>(PhantomData<fn() -> T>);

/// Like [`Member`], but doesn't keep the target alive: it reads as none once the target dies.
pub struct Weak<T>(PhantomData<fn() -> T>);

/// Host data of type `T`, or none.
pub struct Host<T>(PhantomData<fn() -> T>);

/// A key and a value, two words. The value is kept alive only while the key is reachable some
/// other way; once the key dies, the field reads as none.
pub struct Ephemeron;

/// Which of the collector's masks a field is in.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Role {
    Word,
    Value,
    Member,
    Weak,
    Host,
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
    const BARRIER: bool;

    #[doc(hidden)]
    fn load<'gc>(word: u64) -> Self::Out<'gc>;

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
                Self::load(gc.word(mc, field))
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
            const BARRIER: bool = false;

            #[inline]
            fn load<'gc>($w: u64) -> Self::Out<'gc> {
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
    const BARRIER: bool = true;

    #[inline]
    fn load<'gc>(word: u64) -> super::Value<'gc> {
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
        super::target(mc, gc.word(mc, field) as u32)
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

impl<U: Object> sealed::Sealed for Weak<U> {}

impl<U: Object> Slot for Weak<U> {
    const ROLE: Role = Role::Weak;
    type Out<'gc> = Option<Gc<'gc, U>>;
    type In<'gc> = Option<Gc<'gc, U>>;

    #[inline]
    fn get<'gc, T: Object>(gc: Gc<'gc, T>, mc: &Mutation<'gc>, field: usize) -> Option<Gc<'gc, U>> {
        super::target(mc, gc.word(mc, field) as u32)
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

impl<U: Any> sealed::Sealed for Host<U> {}

impl<U: Any> Slot for Host<U> {
    const ROLE: Role = Role::Host;
    type Out<'gc> = Option<HostRef<'gc, U>>;
    type In<'gc> = Option<HostRef<'gc, U>>;

    #[inline]
    fn get<'gc, T: Object>(gc: Gc<'gc, T>, mc: &Mutation<'gc>, field: usize) -> Option<HostRef<'gc, U>> {
        gc.host(mc, field)
    }

    #[inline]
    fn set<'gc, T: Object>(gc: Gc<'gc, T>, mc: &Mutation<'gc>, field: usize, value: Option<HostRef<'gc, U>>) {
        match value {
            Some(host) => gc.set_host(mc, field, host),
            None => gc.set_word(mc, field, 0),
        }
    }

    #[inline]
    fn init(value: Option<HostRef<'_, U>>, words: &mut [u64]) {
        words[0] = value.map_or(0, HostRef::to_word);
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
