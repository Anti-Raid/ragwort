//! The handle types: one for each kind of object.

use std::fmt;
use std::marker::PhantomData;

use ragwort_types::bytevector::AnyBytevector;
use ragwort_types::external::ExternalRef;
use ragwort_types::gc::{self, ForeignRoot, Gc, Handle, Mutation, OutOfMemory, WeakHandle};
use ragwort_types::num::Nums;
use ragwort_types::string::{Str, Strings};
use ragwort_types::table;
use ragwort_types::vector::EveryVector;
use ragwort_types::{pair, symbol};
use ragwort_vm::objects;

mod sealed {
    use ragwort_types::gc::Handle;

    /// Makes a handle type of a handle that is known to hold a value of the type's kind.
    pub trait Wrap: Sized {
        fn wrap(handle: Handle) -> Self;
    }
}

/// Defines the handle types. Each entry gives the type, the view that the arena crates have for the kind, a noun for messages, and a block that
/// returns the view of a value, or `None` if the value is of another kind.
macro_rules! handles {
    ($($(#[$doc:meta])* $name:ident: $view:ty, $noun:literal, ($mc:ident, $value:ident) $find:block)*) => {$(
        $(#[$doc])*
        ///
        /// The handle keeps the value alive and has no lifetime. It is made and read inside a step.
        #[derive(Clone, PartialEq, Eq, Debug)]
        pub struct $name(Handle);

        impl $name {
            fn view<'gc>($mc: &Mutation<'gc>, $value: gc::Value<'gc>) -> Option<$view> $find

            /// Returns a handle of `value`, or `None` if `value` is of another kind.
            pub fn of<'gc>(mc: &Mutation<'gc>, value: gc::Value<'gc>) -> Result<Option<Self>, OutOfMemory> {
                if Self::view(mc, value).is_none() {
                    return Ok(None);
                }
                Ok(Some(Self(Handle::new(mc, value)?)))
            }

            /// Returns the value as the arena's view of its kind. Fails if the handle is of an object of another arena.
            #[inline]
            pub fn get<'gc>(&self, mc: &Mutation<'gc>) -> Result<$view, ForeignRoot> {
                Ok(Self::view(mc, self.0.get(mc)?).expect(concat!("the handle holds a ", $noun)))
            }

            /// Returns the value. Fails if the handle is of an object of another arena.
            #[inline]
            pub fn value<'gc>(&self, mc: &Mutation<'gc>) -> Result<gc::Value<'gc>, ForeignRoot> {
                self.0.get(mc)
            }

            /// Returns the handle without its kind.
            pub fn handle(&self) -> &Handle {
                &self.0
            }

            /// Returns the handle without its kind.
            pub fn into_handle(self) -> Handle {
                self.0
            }

            /// Returns a weak handle of the same value. It does not keep the value alive.
            pub fn downgrade(&self) -> Weak<Self> {
                Weak { handle: self.0.downgrade(), kind: PhantomData }
            }
        }

        impl sealed::Wrap for $name {
            fn wrap(handle: Handle) -> Self {
                Self(handle)
            }
        }
    )*};
}

handles! {
    /// A handle of a string. A string of up to 7 bytes is not an object, and its handle costs the arena nothing.
    String: Str<'gc>, "string", (mc, value) { Strings::new(mc).string(value) }

    /// A handle of a symbol.
    Symbol: symbol::Symbol<'gc>, "symbol", (_mc, value) { symbol::Symbol::of(value) }

    /// A handle of a keyword, such as `#:name`.
    Keyword: symbol::Keyword<'gc>, "keyword", (_mc, value) { symbol::Keyword::of(value) }

    /// A handle of a number of any kind: an integer of any size, a ratio, a flonum or a complex number.
    Number: ragwort_types::num::Number<'gc>, "number", (mc, value) { Nums::new(mc).number(value) }

    /// A handle of a bytevector: mutable, read-only, or over bytes that the host owns.
    Bytevector: AnyBytevector<'gc>, "bytevector", (_mc, value) { AnyBytevector::of(value) }

    /// A handle of a pair.
    Pair: pair::Pair<'gc>, "pair", (_mc, value) { pair::Pair::of(value) }

    /// A handle of a vector: mutable, read-only, or over items that the host owns.
    Vector: EveryVector<'gc>, "vector", (_mc, value) { EveryVector::of(value) }

    /// A handle of a table.
    Table: table::Table<'gc>, "table", (_mc, value) { table::Table::of(value) }

    /// A handle of an instance of a struct type.
    Struct: Gc<'gc, objects::Struct>, "struct", (mc, value) { value.downcast::<objects::Struct>(mc) }

    /// A handle of a procedure: a closure, a continuation or a keyword procedure.
    Procedure: gc::Value<'gc>, "procedure", (mc, value) { if ragwort_vm::is_procedure(mc, value) { Some(value) } else { None } }

    /// A handle of a coroutine.
    Coroutine: Gc<'gc, objects::Task>, "coroutine", (mc, value) { value.downcast::<objects::Task>(mc) }

    /// A handle of a value of a host type.
    External: ExternalRef<'gc>, "external value", (_mc, value) { ExternalRef::of(value) }

    /// A handle of a value of any kind. [`Value`](crate::Value) uses it for the kinds that have no handle type of their own.
    Other: gc::Value<'gc>, "value", (_mc, value) { Some(value) }
}

/// A handle that does not keep its value alive. `T` is the handle type that it was made of.
///
/// [`Weak::upgrade`] returns a handle while the object is alive, and `None` once a collection has freed it.
pub struct Weak<T> {
    handle: WeakHandle,
    kind: PhantomData<fn() -> T>,
}

impl<T: sealed::Wrap> Weak<T> {
    /// Returns a handle that keeps the value alive, or `None` if the object has been freed. It needs no step.
    pub fn upgrade(&self) -> Option<T> {
        self.handle.upgrade().map(T::wrap)
    }
}

impl<T> Weak<T> {
    /// Returns the weak handle without its kind.
    pub fn handle(&self) -> &WeakHandle {
        &self.handle
    }
}

impl<T> Clone for Weak<T> {
    fn clone(&self) -> Self {
        Self { handle: self.handle.clone(), kind: PhantomData }
    }
}

impl<T> fmt::Debug for Weak<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.debug_tuple("Weak").field(&self.handle).finish()
    }
}
