use super::*;
use crate::gc::{Arena, objects};

objects! {
    kind Kind;
    struct Num { n: i64 }
    /// About a page.
    struct Filler {} items u64
    struct Pair { car: Value, cdr: Value }
}

fn words<'gc>(mc: &Mutation<'gc>) -> GcVec<'gc, slot::u64> {
    GcVec::of(mc.root(0).downcast::<VecHead<slot::u64>>(mc).unwrap())
}

fn nums<'gc>(mc: &Mutation<'gc>) -> GcVec<'gc, slot::Member<Num>> {
    GcVec::of(mc.root(0).downcast::<VecHead<slot::Member<Num>>>(mc).unwrap())
}

fn churn(mc: &Mutation<'_>) {
    for _ in 0..100_000 {
        Pair::new(mc, Value::NIL, Value::NIL).unwrap();
    }
}

fn word_arena(limit: usize) -> Arena {
    let mut arena = Arena::new(limit, 1);
    arena.mutate(|mc| {
        let v = GcVec::<slot::u64>::new(mc).unwrap();
        mc.set_root(0, Value::object(mc, v.head()));
    });
    arena
}

#[test]
fn iterators_keep_their_range_and_storage() {
    let mut arena = word_arena(1 << 20);
    arena.mutate(|mc| {
        let v = words(mc);
        assert_eq!(v.iter(mc).len(), 0);
        for i in 0..4 {
            v.push(mc, i).unwrap();
        }
        let mut iter = v.iter(mc);
        assert_eq!(iter.next(), Some(0));
        assert_eq!(iter.next_back(), Some(3));
        assert_eq!(iter.len(), 2);
        assert!(v.set(mc, 1, 11));
        // Growing moves the vector to new slots, which the iterator doesn't see.
        v.push(mc, 4).unwrap();
        assert!(v.set(mc, 1, 99));
        v.truncate(mc, 1);
        assert_eq!(iter.collect::<Vec<_>>(), [11, 2]);
        assert_eq!(v.iter(mc).collect::<Vec<_>>(), [0]);
    });
}

#[test]
fn slots_grow_and_are_traced() {
    let n = 1000;
    let mut arena = Arena::new(8 << 20, 1);
    arena.mutate(|mc| {
        let v = GcVec::<slot::Member<Num>>::new(mc).unwrap();
        mc.set_root(0, Value::object(mc, v.head()));
        for i in 0..n {
            v.push(mc, Some(Num::new(mc, i).unwrap())).unwrap();
        }
        assert_eq!(v.len(mc), n as usize);
        assert!(v.capacity(mc) >= v.len(mc));
        assert_eq!(v.get(mc, 3).flatten().map(|x| x.n(mc)), Some(3));
        assert!(v.get(mc, n as usize).is_none());
        assert!(!v.set(mc, n as usize, None));
    });
    arena.set_evacuate_all(true);
    arena.collect();
    arena.mutate(churn);
    arena.mutate(|mc| {
        let v = nums(mc);
        assert!(v.iter(mc).enumerate().all(|(i, x)| x.map(|x| x.n(mc)) == Some(i as i64)));
        assert_eq!(v.pop(mc).flatten().map(|x| x.n(mc)), Some(n - 1));
        v.truncate(mc, 10);
        assert!(v.set(mc, 0, None));
        // The truncated slots hold the zero word, so they keep nothing alive.
        let slots = v.head().get(mc, VecHead::SLOTS).unwrap().item_slots::<slot::u64>(mc);
        assert!((10..slots.len()).all(|i| slots.get(i) == 0));
    });
    arena.collect();
    arena.mutate(churn);
    arena.mutate(|mc| {
        let v = nums(mc);
        let got: Vec<_> = v.iter(mc).map(|x| x.map(|x| x.n(mc))).collect();
        assert_eq!(got, [None].into_iter().chain((1..10).map(Some)).collect::<Vec<_>>());
    });
}

/// Stores into an old vector's slots take the barrier, so a minor collection keeps their
/// young targets.
#[test]
fn stores_into_old_slots_survive_minor_collections() {
    let mut arena = Arena::new(8 << 20, 1);
    arena.mutate(|mc| {
        let v = GcVec::<slot::Member<Num>>::with_capacity(mc, 10_000).unwrap();
        mc.set_root(0, Value::object(mc, v.head()));
    });
    arena.collect();
    arena.mutate(|mc| {
        for i in 0..10_000 {
            nums(mc).push(mc, Some(Num::new(mc, i).unwrap())).unwrap();
        }
    });
    arena.collect_minor();
    arena.mutate(churn);
    arena.mutate(|mc| assert!(nums(mc).iter(mc).enumerate().all(|(i, x)| x.map(|x| x.n(mc)) == Some(i as i64))));
}

/// A length past the slots, as damaged memory could hold, reads as the slots' length.
#[test]
fn damaged_lengths_are_bounded() {
    let mut arena = word_arena(1 << 20);
    arena.mutate(|mc| {
        let v = words(mc);
        for i in 0..8 {
            v.push(mc, i).unwrap();
        }
        let damage = || v.head().set_word(mc, 0, u64::MAX);
        damage();
        assert_eq!((v.len(mc), v.capacity(mc)), (8, 8));
        assert_eq!(v.iter(mc).count(), 8);
        assert!(v.get(mc, 1000).is_none());
        v.truncate(mc, 1000);
        assert!((0..8).all(|i| v.get(mc, i) == Some(i as u64)), "truncating above the length cleared items");
        assert_eq!(v.pop(mc), Some(7));
        v.truncate(mc, 2);
        assert_eq!(v.len(mc), 2);
        damage();
        v.truncate(mc, 0);
        assert_eq!(v.len(mc), 0);
    });
}

/// Growth a vector can do without stays out of the reserve, so it grows by what it needs.
#[test]
fn optional_growth_leaves_the_reserve_alone() {
    let mut arena = word_arena(1 << 20);
    arena.set_reserve(512 << 10);
    let capacity = arena.mutate(|mc| {
        let v = words(mc);
        while !mc.collection_due() {
            v.push(mc, 0).unwrap();
        }
        assert!(mc.used() <= mc.limit());
        v.capacity(mc)
    });
    assert_eq!(arena.mutate(|mc| words(mc).len(mc)), capacity, "the growth that drew on the reserve was exact");
}

#[test]
fn vectors_grow_by_less_when_doubling_does_not_fit() {
    let mut arena = word_arena(2 << 20);
    arena.set_reserve(0);
    arena.mutate(|mc| {
        let v = words(mc);
        for i in 0..32768 {
            v.push(mc, i).unwrap();
        }
        assert_eq!(v.capacity(mc), 32768);
        while mc.limit() - mc.used() > 400 << 10 {
            Filler::new(mc, 2000, 0).unwrap();
        }
        v.push(mc, 32768).unwrap();
        assert_eq!(v.capacity(mc), 32769);
        assert_eq!(v.get(mc, 32768), Some(32768));
        assert_eq!(v.get(mc, 100), Some(100));
    });
}

#[test]
fn failed_growth_leaves_the_vector_as_it_was() {
    let mut arena = word_arena(1 << 20);
    arena.mutate(|mc| {
        let v = words(mc);
        for i in 0..4 {
            v.push(mc, i).unwrap();
        }
        assert_eq!(v.reserve(mc, usize::MAX), Err(OutOfMemory));
    });
    arena.fail_after(Some(0));
    let result = arena.step(|mc| words(mc).reserve(mc, 1 << 16));
    assert!(matches!(result, Err(OutOfMemory) | Ok(Err(OutOfMemory))));
    arena.fail_after(None);
    arena.mutate(|mc| assert_eq!(words(mc).iter(mc).collect::<Vec<_>>(), [0, 1, 2, 3]));
}
