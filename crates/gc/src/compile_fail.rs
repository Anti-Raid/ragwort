//! A `Gc` can't escape the step that produced it:
//!
//! ```compile_fail
//! use ragwort_gc::{Arena, Rootable};
//! struct R;
//! impl Rootable for R { type Root<'gc> = (); }
//! let mut arena = Arena::<R>::new(1 << 20, |_| Ok(())).unwrap();
//! let escaped = arena.mutate(|mc, _| mc.alloc(1i64).unwrap());
//! ```
//!
//! A reference from one arena can't be stored in another:
//!
//! ```compile_fail
//! use ragwort_gc::{Arena, Lock, Member, Rootable};
//! struct R;
//! impl Rootable for R { type Root<'gc> = Lock<Option<Member<'gc, i64>>>; }
//! let mut a = Arena::<R>::new(1 << 20, |_| Ok(Lock::new(None))).unwrap();
//! let mut b = Arena::<R>::new(1 << 20, |_| Ok(Lock::new(None))).unwrap();
//! a.mutate(|mca, _| {
//!     let x = mca.alloc(1i64).unwrap();
//!     b.mutate(|mcb, root| root.set(mcb, Some(Member::new(mca, x))));
//! });
//! ```
//!
//! A `Lock` in one arena can't be written with another arena's `Mutation`, which would run the
//! write barrier on the wrong heap:
//!
//! ```compile_fail
//! use ragwort_gc::{Arena, Lock, Member, Rootable};
//! struct R;
//! impl Rootable for R { type Root<'gc> = Lock<Option<Member<'gc, i64>>>; }
//! let mut a = Arena::<R>::new(1 << 20, |_| Ok(Lock::new(None))).unwrap();
//! let mut b = Arena::<R>::new(1 << 20, |_| Ok(Lock::new(None))).unwrap();
//! a.mutate(|mca, root| {
//!     let x = Some(Member::new(mca, mca.alloc(1i64).unwrap()));
//!     b.mutate(|mcb, _| root.set(mcb, x));
//! });
//! ```
//!
//! Types that aren't `Plain` can't be allocated:
//!
//! ```compile_fail,E0277
//! use ragwort_gc::{Arena, Rootable, Trace, Tracer};
//! struct Flag(bool);
//! unsafe impl Trace for Flag { const NEEDS_TRACE: bool = false; fn trace(&mut self, _: &mut Tracer) {} }
//! struct R;
//! impl Rootable for R { type Root<'gc> = (); }
//! let mut arena = Arena::<R>::new(1 << 20, |_| Ok(())).unwrap();
//! arena.mutate(|mc, _| { let _ = mc.alloc(Flag(true)); });
//! ```
//!
//! A `Member` read from corrupted memory may name a type that was never allocated, so
//! getting one requires the type to be `Plain`:
//!
//! ```compile_fail,E0277
//! use ragwort_gc::{Arena, Member, Rootable};
//! struct Flag(bool);
//! struct R;
//! impl Rootable for R { type Root<'gc> = (); }
//! let mut arena = Arena::<R>::new(1 << 20, |_| Ok(())).unwrap();
//! arena.mutate(|mc, _| {
//!     let m: Option<Member<'_, Flag>> = None;
//!     let _ = m.map(|m| m.get(mc));
//! });
//! ```
//!
//! and checks its layout too. Oversized or over-aligned types don't compile:
//!
//! ```compile_fail,E0080
//! use ragwort_gc::{Arena, Member, Rootable};
//! struct R;
//! impl Rootable for R { type Root<'gc> = (); }
//! let mut arena = Arena::<R>::new(1 << 20, |_| Ok(())).unwrap();
//! arena.mutate(|mc, _| {
//!     let m: Option<Member<'_, [u64; 1 << 24]>> = None;
//!     let _ = m.map(|m| m.get(mc));
//! });
//! ```
//!
//! ```compile_fail,E0080
//! use ragwort_gc::{Arena, Member, Rootable};
//! #[repr(C, align(16))]
//! struct Wide([u64; 2]);
//! unsafe impl<'gc> ragwort_gc::Plain<'gc> for Wide {}
//! struct R;
//! impl Rootable for R { type Root<'gc> = (); }
//! let mut arena = Arena::<R>::new(1 << 20, |_| Ok(())).unwrap();
//! arena.mutate(|mc, _| {
//!     let m: Option<Member<'_, Wide>> = None;
//!     let _ = m.map(|m| m.get(mc));
//! });
//! ```
//!
//! A derived `Plain` type can't have padding, and every field must be `Plain`:
//!
//! ```compile_fail,E0080
//! use ragwort_gc::{Arena, Plain, Rootable, Trace};
//! #[derive(Trace, Plain)]
//! struct Padded { a: u8, b: u32 }
//! struct R;
//! impl Rootable for R { type Root<'gc> = (); }
//! let mut arena = Arena::<R>::new(1 << 20, |_| Ok(())).unwrap();
//! arena.mutate(|mc, _| { let _ = mc.alloc(Padded { a: 1, b: 2 }); });
//! ```
//!
//! Without type parameters, padding is caught where the type is defined, even if it's
//! never allocated:
//!
//! ```compile_fail,E0080
//! use ragwort_gc::{Member, Plain};
//! #[derive(Plain)]
//! struct Padded<'gc> { a: u8, b: Option<Member<'gc, u8>> }
//! ```
//!
//! ```compile_fail,E0277
//! use ragwort_gc::{Plain, Trace};
//! #[derive(Trace, Plain)]
//! struct HasBool { a: bool }
//! ```
//!
//! ```compile_fail
//! use ragwort_gc::Plain;
//! #[derive(Plain)]
//! enum E { A, B }
//! ```
//!
//! `u128` needs 16-byte alignment, which the arena doesn't give, so it isn't `Plain`:
//!
//! ```compile_fail,E0277
//! use ragwort_gc::{Arena, Rootable};
//! struct R;
//! impl Rootable for R { type Root<'gc> = (); }
//! let mut arena = Arena::<R>::new(1 << 20, |_| Ok(())).unwrap();
//! arena.mutate(|mc, _| { let _ = mc.alloc(1u128); });
//! ```
//!
//! Full pointers can't be stored in the heap or the root; only `Member`s can:
//!
//! ```compile_fail,E0277
//! use ragwort_gc::{Gc, Lock, Rootable};
//! struct R;
//! impl Rootable for R { type Root<'gc> = Lock<Option<Gc<'gc, i64>>>; }
//! ```
//!
//! Arenas stay on their thread:
//!
//! ```compile_fail,E0277
//! use ragwort_gc::{Arena, Rootable};
//! struct R;
//! impl Rootable for R { type Root<'gc> = (); }
//! fn send<T: Send>() {}
//! send::<Arena<R>>();
//! ```
//!
//! ```compile_fail,E0277
//! use ragwort_gc::Gc;
//! fn send<T: Send>() {}
//! send::<Gc<'static, i64>>();
//! ```
//!
//! ```compile_fail,E0277
//! use ragwort_gc::Mutation;
//! fn send<T: Send>() {}
//! send::<Mutation<'static>>();
//! ```
//!
//! ```compile_fail,E0277
//! use ragwort_gc::{Member, Root, Rooted};
//! struct K;
//! impl Rooted for K { type Of<'gc> = Member<'gc, i64>; }
//! fn send<T: Send>() {}
//! send::<Root<K>>();
//! ```
//!
//! Inline types can't go through `alloc`:
//!
//! ```compile_fail,E0080
//! use ragwort_gc::{Arena, Inline, Rootable, Trace, Tracer};
//! struct S;
//! unsafe impl Trace for S { const INLINE: bool = true; fn trace(&mut self, _: &mut Tracer) {} }
//! unsafe impl Inline for S { type Item = u8; }
//! unsafe impl<'gc> ragwort_gc::Plain<'gc> for S {}
//! struct R;
//! impl Rootable for R { type Root<'gc> = (); }
//! let mut arena = Arena::<R>::new(1 << 20, |_| Ok(())).unwrap();
//! arena.mutate(|mc, _| { let _ = mc.alloc(S); });
//! ```
//!
//! Arena objects can't have drop glue (host data goes through `HostRef`):
//!
//! ```compile_fail,E0080
//! use ragwort_gc::{Arena, Rootable, Trace, Tracer};
//! struct D;
//! impl Drop for D { fn drop(&mut self) {} }
//! unsafe impl Trace for D { const NEEDS_TRACE: bool = false; fn trace(&mut self, _: &mut Tracer) {} }
//! unsafe impl<'gc> ragwort_gc::Plain<'gc> for D {}
//! struct R;
//! impl Rootable for R { type Root<'gc> = (); }
//! let mut arena = Arena::<R>::new(1 << 20, |_| Ok(())).unwrap();
//! arena.mutate(|mc, _| { let _ = mc.alloc(D); });
//! ```
//!
//! Map keys can't hold arena references, since the collector rewrites references to objects
//! it moves:
//!
//! ```compile_fail,E0080
//! use std::collections::HashMap;
//! use ragwort_gc::{Arena, Member, Rootable};
//! struct R;
//! impl Rootable for R { type Root<'gc> = HashMap<Member<'gc, i64>, i64>; }
//! let mut arena = Arena::<R>::new(1 << 20, |_| Ok(HashMap::new())).unwrap();
//! arena.collect();
//! ```
//!
//! Host-side containers aren't `Plain`, so they can't go in the arena, where writes through
//! `&mut` would skip the barrier:
//!
//! ```compile_fail,E0277
//! use std::cell::RefCell;
//! use ragwort_gc::{Arena, Rootable, Value};
//! struct R;
//! impl Rootable for R { type Root<'gc> = (); }
//! let mut arena = Arena::<R>::new(1 << 20, |_| Ok(())).unwrap();
//! arena.mutate(|mc, _| { let _ = mc.alloc(RefCell::new(Vec::<Value>::new())); });
//! ```
//!
//! A `Value` is branded like any other reference, so it can't leave its step:
//!
//! ```compile_fail
//! use ragwort_gc::{Arena, Rootable, Value};
//! struct R;
//! impl Rootable for R { type Root<'gc> = (); }
//! let mut arena = Arena::<R>::new(1 << 20, |_| Ok(())).unwrap();
//! let escaped = arena.mutate(|mc, _| Value::object(mc, mc.alloc(1i64).unwrap()));
//! ```
//!
//! A type tag holds an arena's type index, so it can't leave its step:
//!
//! ```compile_fail
//! use ragwort_gc::{Arena, Rootable};
//! struct R;
//! impl Rootable for R { type Root<'gc> = (); }
//! let mut arena = Arena::<R>::new(1 << 20, |_| Ok(())).unwrap();
//! let tag = arena.mutate(|mc, _| mc.type_tag::<i64>().unwrap());
//! ```
//!
//! An inline type needs an inline type tag, which would otherwise never match:
//!
//! ```compile_fail,E0080
//! use ragwort_gc::{Arena, Array, Rootable};
//! struct R;
//! impl Rootable for R { type Root<'gc> = (); }
//! let mut arena = Arena::<R>::new(1 << 20, |_| Ok(())).unwrap();
//! arena.mutate(|mc, _| { let _ = mc.type_tag::<Array<u8>>(); });
//! ```
//!
//! Arena memory can only be read with the arena's own brand. Viewed as `'static`, which
//! outlives every brand, an object's references could be carried into another arena:
//!
//! ```compile_fail
//! use ragwort_gc::{AnyRef, Arena, Lock, Plain, Rootable, Trace, Value};
//! #[derive(Trace, Plain)]
//! struct Slot<'gc> { value: Lock<Value<'gc>> }
//! struct R;
//! impl Rootable for R { type Root<'gc> = (); }
//! let mut a = Arena::<R>::new(1 << 20, |_| Ok(())).unwrap();
//! a.mutate(|mc, _| {
//!     let slot = mc.alloc(Slot { value: Lock::new(Value::NIL) }).unwrap();
//!     let _: Value<'static> = AnyRef::new(mc, slot).downcast::<Slot<'static>>(mc).unwrap().value.get();
//! });
//! ```
//!
//! ```compile_fail
//! use ragwort_gc::{Arena, Lock, Plain, Rootable, Trace, Value};
//! #[derive(Trace, Plain)]
//! struct Slot<'gc> { value: Lock<Value<'gc>> }
//! struct R;
//! impl Rootable for R { type Root<'gc> = (); }
//! let mut a = Arena::<R>::new(1 << 20, |_| Ok(())).unwrap();
//! a.mutate(|mc, _| { let _ = mc.alloc(Slot::<'static> { value: Lock::new(Value::NIL) }); });
//! ```
//!
//! ```compile_fail
//! use ragwort_gc::{Arena, Lock, Plain, Rootable, Trace, Value};
//! #[derive(Trace, Plain)]
//! struct Slot<'gc> { value: Lock<Value<'gc>> }
//! struct R;
//! impl Rootable for R { type Root<'gc> = (); }
//! let mut a = Arena::<R>::new(1 << 20, |_| Ok(())).unwrap();
//! a.mutate(|mc, _| { let _ = mc.type_tag::<Slot<'static>>(); });
//! ```
//!
//! A type without a lifetime that holds `'static`-branded references can never be allocated:
//!
//! ```compile_fail
//! use ragwort_gc::{Arena, Lock, Plain, Rootable, Trace, Value};
//! #[derive(Trace, Plain)]
//! struct Unbranded { value: Lock<Value<'static>> }
//! struct R;
//! impl Rootable for R { type Root<'gc> = (); }
//! let mut a = Arena::<R>::new(1 << 20, |_| Ok(())).unwrap();
//! a.mutate(|mc, _| { let _ = mc.alloc(Unbranded { value: Lock::new(Value::NIL) }); });
//! ```
//!
//! And a type with two lifetimes would have two brands:
//!
//! ```compile_fail
//! use ragwort_gc::{Lock, Plain, Value};
//! #[derive(Plain)]
//! struct Two<'a, 'b> { a: Lock<Value<'a>>, b: Lock<Value<'b>> }
//! ```
//!
//! A frame borrows its stack, so it can't be written after the stack captures, switches or
//! parks, when its slots stop being traced as a root:
//!
//! ```compile_fail,E0502
//! use ragwort_gc::{Arena, Rootable, Segment, Value};
//! struct R;
//! impl Rootable for R { type Root<'gc> = (); }
//! let mut a = Arena::<R>::new(1 << 20, |_| Ok(())).unwrap();
//! a.mutate(|mc, _| {
//!     let mut stack = mc.stack(Segment::new(mc, 512).unwrap()).unwrap();
//!     let frame = stack.frame(mc, 0).unwrap();
//!     stack.capture(mc, 8);
//!     frame.set(0, Value::TRUE);
//! });
//! ```
//!
//! Nor can it leave the step:
//!
//! ```compile_fail
//! use ragwort_gc::{Arena, Frame, Rootable, Segment};
//! struct R;
//! impl Rootable for R { type Root<'gc> = (); }
//! let mut a = Arena::<R>::new(1 << 20, |_| Ok(())).unwrap();
//! let stack = a.mutate(|mc, _| mc.stack(Segment::new(mc, 512).unwrap()).unwrap());
//! let _frame: Frame<'_, 'static> = a.mutate(|mc, _| stack.frame(mc, 0).unwrap());
//! ```
//!
//! Inline items carry the brand too, so a generic inline type can't be viewed with
//! `'static`-branded items:
//!
//! ```compile_fail
//! use std::marker::PhantomData;
//! use ragwort_gc::{Arena, Lock, Member, Plain, Rootable, Trace, Value};
//! #[derive(Trace, Plain)]
//! #[gc(items = Lock<T>)]
//! struct Arr<T>(PhantomData<T>);
//! struct R;
//! impl Rootable for R { type Root<'gc> = Lock<Value<'gc>>; }
//! let mut a = Arena::<R>::new(1 << 20, |_| Ok(Lock::new(Value::NIL))).unwrap();
//! let _: Option<Member<'static, u64>> = a.mutate(|mc, root| {
//!     let x = mc.alloc(7u64).unwrap();
//!     let arr = mc.alloc_inline(Arr(PhantomData), 1, |_| Lock::new(Some(Member::new(mc, x)))).unwrap();
//!     root.set(mc, Value::object(mc, arr));
//!     root.get().downcast::<Arr<Option<Member<'static, u64>>>>(mc).unwrap().items()[0].get()
//! });
//! ```
//!
//! Hashers aren't traced, so a map or set can't keep one that holds an arena reference:
//!
//! ```compile_fail,E0477
//! use std::collections::HashMap;
//! use ragwort_gc::{Member, Rootable};
//! struct R;
//! impl Rootable for R { type Root<'gc> = HashMap<u64, u64, Member<'gc, i64>>; }
//! ```
//!
//! ```compile_fail,E0477
//! use std::collections::HashSet;
//! use ragwort_gc::{Member, Rootable};
//! struct R;
//! impl Rootable for R { type Root<'gc> = HashSet<u64, Member<'gc, i64>>; }
//! ```
