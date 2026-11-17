use std::marker::PhantomData;

use super::{AnyHostRef, Fields, Gc, Item, Mutation, Object, Phase, Slots, Value, WORDS, field_slot, host_parts, items_start, mask};

pub trait Raw<'gc>: Copy {
    /// Returns the word that a field declared in `Desc::members` holds for this object: the object's index.
    fn to_word(self) -> u64;

    /// Returns the word of field `field`. It indexes a view of the region that is shifted by `1 + field` words. So for a constant field, the masked
    /// index is the whole address computation. A chain of loads, as in a list walk, benefits from this.
    fn word(self, mc: &Mutation<'gc>, field: usize) -> u64;

    /// Sets the word of field `field`, with no barrier. For fields that hold no reference.
    fn set_word(self, mc: &Mutation<'gc>, field: usize, word: u64);

    fn value(self, mc: &Mutation<'gc>, field: usize) -> Value<'gc>;

    fn set_value(self, mc: &Mutation<'gc>, field: usize, value: Value<'gc>);

    /// Returns the object in member field `field`, or `None` for index 0. The type is not checked: the target is assumed to be a `U`.
    fn member<U: Object>(self, mc: &Mutation<'gc>, field: usize) -> Option<Gc<'gc, U>>;

    fn set_member<U: Object>(self, mc: &Mutation<'gc>, field: usize, member: Option<Gc<'gc, U>>);

    /// Returns the target of weak field `field`, or `None` once the target has died.
    fn weak<U: Object>(self, mc: &Mutation<'gc>, field: usize) -> Option<Gc<'gc, U>>;

    /// Sets weak field `field` to `target`. Marks the card dirty, so that a minor collection can clear the field, but does not shade the target.
    fn set_weak<U: Object>(self, mc: &Mutation<'gc>, field: usize, target: Option<Gc<'gc, U>>);

    fn host(self, mc: &Mutation<'gc>, field: usize) -> Option<AnyHostRef<'gc>>;

    fn set_host(self, mc: &Mutation<'gc>, field: usize, host: AnyHostRef<'gc>);

    /// Returns the object's first `N` fields. An `N` larger than the number of declared fields does not compile.
    fn fields<const N: usize>(self, mc: &Mutation<'gc>) -> Option<Fields<'gc, N>>;

    /// Returns the key and value of the ephemeron at `field`, which must be a field in `Desc::ephemerons`. Returns `None` once
    /// the key has died.
    fn ephemeron(self, mc: &Mutation<'gc>, field: usize) -> Option<(Value<'gc>, Value<'gc>)>;

    /// Sets the key and value of the ephemeron at `field`. Neither is shaded while marking, because the value is traced once the key is found live.
    /// Both cards are marked dirty, so a minor collection sees both words.
    fn set_ephemeron(self, mc: &Mutation<'gc>, field: usize, key: Value<'gc>, value: Value<'gc>);

    /// Returns the items as values, whatever kind the type declares for them.
    fn slots(self, mc: &Mutation<'gc>) -> Slots<'gc>;

    /// Returns the items as slots of kind `S`.
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
        let index = member.map_or(0, |member| member.index);
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
        mc.heap.words[slot].set(u64::from(target.map_or(0, |target| target.index)));
        mc.heap.dirty(slot);
    }

    #[inline]
    fn host(self, mc: &Mutation<'gc>, field: usize) -> Option<AnyHostRef<'gc>> {
        let (id, generation) = host_parts(self.word(mc, field))?;
        Some(AnyHostRef { id, generation, _brand: PhantomData })
    }

    fn set_host(self, mc: &Mutation<'gc>, field: usize, host: AnyHostRef<'gc>) {
        mc.heap.words[field_slot(self, field)].set(host.to_word());
        if mc.heap.m.phase.get() == Phase::Marking && mc.heap.has_bit(self.index as usize, |page| &page.marks) {
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
        Slots { words, region: heap.words, at, owner: self.index, _marker: PhantomData }
    }
}
