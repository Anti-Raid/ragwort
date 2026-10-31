//! Fields by number, beneath the typed fields `objects!` declares, for the collector's own types
//! and for tests. A wrong field number or kind reads or writes the wrong word, which gives wrong
//! results but is never unsound. A trait in its own module, so a glob import of the crate
//! doesn't bring in names that clash with generated accessors.

use std::any::Any;
use std::marker::PhantomData;

use super::{Fields, Gc, HostRef, Item, Mutation, Object, Phase, Slots, Value, WORDS, field_slot, host_parts, items_start, mask};

pub trait Raw<'gc>: Copy {
    /// The word a field declared in `Desc::members` holds.
    fn to_word(self) -> u64;

    /// Indexes a view of the words shifted by the field, so for a constant field the masked
    /// index is the whole address computation, as a list walk's chain of loads wants.
    fn word(self, mc: &Mutation<'gc>, field: usize) -> u64;

    /// For fields that hold no reference: no barrier.
    fn set_word(self, mc: &Mutation<'gc>, field: usize, word: u64);

    fn value(self, mc: &Mutation<'gc>, field: usize) -> Value<'gc>;

    fn set_value(self, mc: &Mutation<'gc>, field: usize, value: Value<'gc>);

    /// Unchecked: the word is taken to be a `U`.
    fn member<U: Object>(self, mc: &Mutation<'gc>, field: usize) -> Option<Gc<'gc, U>>;

    fn set_member<U: Object>(self, mc: &Mutation<'gc>, field: usize, member: Option<Gc<'gc, U>>);

    /// The target of a weak field, or `None` once it has died.
    fn weak<U: Object>(self, mc: &Mutation<'gc>, field: usize) -> Option<Gc<'gc, U>>;

    /// Dirties the card, for minor collections to clear the field, but doesn't shade the target.
    fn set_weak<U: Object>(self, mc: &Mutation<'gc>, field: usize, target: Option<Gc<'gc, U>>);

    fn host<U: Any>(self, mc: &Mutation<'gc>, field: usize) -> Option<HostRef<'gc, U>>;

    fn set_host<U: Any>(self, mc: &Mutation<'gc>, field: usize, host: HostRef<'gc, U>);

    /// The object's first `N` fields. `N` past the declared fields doesn't compile.
    fn fields<const N: usize>(self, mc: &Mutation<'gc>) -> Option<Fields<'gc, N>>;

    /// The key and value of the ephemeron at `field`, one in `Desc::ephemerons`, or `None` once
    /// its key has died.
    fn ephemeron(self, mc: &Mutation<'gc>, field: usize) -> Option<(Value<'gc>, Value<'gc>)>;

    /// Neither part is shaded while marking: the value is traced once the key is found live.
    /// The cards are dirtied, so a minor collection sees both.
    fn set_ephemeron(self, mc: &Mutation<'gc>, field: usize, key: Value<'gc>, value: Value<'gc>);

    /// The items as values, whatever the type declares them as.
    fn slots(self, mc: &Mutation<'gc>) -> Slots<'gc>;

    /// The items as `S`.
    fn item_slots<S: Item>(self, mc: &Mutation<'gc>) -> Slots<'gc, S>;
}

impl<'gc, T: Object> Raw<'gc> for Gc<'gc, T> {
    fn to_word(self) -> u64 {
        u64::from(self.index)
    }

    #[inline]
    fn word(self, mc: &Mutation<'gc>, field: usize) -> u64 {
        assert!(field < T::DESC.fields as usize, "field {field} of {}", T::DESC.fields);
        let words = mc.heap.words;
        match words.get(1 + field..).and_then(<[_]>::first_chunk::<WORDS>) {
            Some(shifted) => shifted[mask(self.index as usize)].get(),
            None => words[mask(self.index as usize) + 1 + field].get(),
        }
    }

    #[inline]
    fn set_word(self, mc: &Mutation<'gc>, field: usize, word: u64) {
        mc.heap.words[field_slot(self, field)].set(word);
    }

    #[inline]
    fn value(self, mc: &Mutation<'gc>, field: usize) -> Value<'gc> {
        Value::from_bits(self.word(mc, field))
    }

    #[inline]
    fn set_value(self, mc: &Mutation<'gc>, field: usize, value: Value<'gc>) {
        let slot = field_slot(self, field);
        mc.heap.words[slot].set(value.word);
        mc.heap.barrier(slot, self.index, value.word);
    }

    #[inline]
    fn member<U: Object>(self, mc: &Mutation<'gc>, field: usize) -> Option<Gc<'gc, U>> {
        let index = self.word(mc, field) as u32;
        (index != 0).then(|| Gc::new(index))
    }

    #[inline]
    fn set_member<U: Object>(self, mc: &Mutation<'gc>, field: usize, member: Option<Gc<'gc, U>>) {
        let slot = field_slot(self, field);
        let index = member.map_or(0, |m| m.index);
        mc.heap.words[slot].set(u64::from(index));
        if index != 0 {
            mc.heap.barrier_ref(slot, self.index, index);
        }
    }

    #[inline]
    fn weak<U: Object>(self, mc: &Mutation<'gc>, field: usize) -> Option<Gc<'gc, U>> {
        self.member(mc, field)
    }

    #[inline]
    fn set_weak<U: Object>(self, mc: &Mutation<'gc>, field: usize, target: Option<Gc<'gc, U>>) {
        let slot = field_slot(self, field);
        mc.heap.words[slot].set(u64::from(target.map_or(0, |t| t.index)));
        mc.heap.dirty(slot);
    }

    #[inline]
    fn host<U: Any>(self, mc: &Mutation<'gc>, field: usize) -> Option<HostRef<'gc, U>> {
        let (id, generation) = host_parts(self.word(mc, field))?;
        Some(HostRef { id, generation, _marker: PhantomData })
    }

    fn set_host<U: Any>(self, mc: &Mutation<'gc>, field: usize, host: HostRef<'gc, U>) {
        mc.heap.words[field_slot(self, field)].set(host.to_word());
        if mc.heap.m.phase.get() == Phase::Marking && mc.heap.has_bit(self.index as usize, |p| &p.marks) {
            mc.heap.mark_host(host.to_word());
        }
    }

    #[inline]
    fn fields<const N: usize>(self, mc: &Mutation<'gc>) -> Option<Fields<'gc, N>> {
        const { assert!(N <= T::DESC.fields as usize, "more fields than the type declares") };
        let at = mask(self.index as usize) + 1;
        let heap = mc.heap;
        let words = heap.words.get(at..)?.first_chunk()?;
        Some(Fields { words, at, owner: self.index, _brand: PhantomData })
    }

    #[inline]
    fn ephemeron(self, mc: &Mutation<'gc>, field: usize) -> Option<(Value<'gc>, Value<'gc>)> {
        assert!(field + 1 < T::DESC.fields as usize, "ephemeron at field {field} of {}", T::DESC.fields);
        mc.heap.ephemeron_at(field_slot(self, field))
    }

    #[inline]
    fn set_ephemeron(self, mc: &Mutation<'gc>, field: usize, key: Value<'gc>, value: Value<'gc>) {
        assert!(field + 1 < T::DESC.fields as usize, "ephemeron at field {field} of {}", T::DESC.fields);
        mc.heap.set_ephemeron_at(field_slot(self, field), key, value);
    }

    #[inline]
    fn slots(self, mc: &Mutation<'gc>) -> Slots<'gc> {
        self.item_slots(mc)
    }

    #[inline]
    fn item_slots<S: Item>(self, mc: &Mutation<'gc>) -> Slots<'gc, S> {
        let at = items_start(self);
        let heap = mc.heap;
        let words = heap.words.get(at..at + self.len(mc)).unwrap_or(&[]);
        Slots { words, at, owner: self.index, _marker: PhantomData }
    }
}
