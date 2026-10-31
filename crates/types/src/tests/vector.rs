use ragwort_gc::{Arena, Rootable, max_items};

use super::*;
use crate::pair::Pairs;

/// A vector to write into, and a pair to check it isn't taken for one.
struct VectorRoot;
impl Rootable for VectorRoot {
    type Root<'gc> = (Lock<Value<'gc>>, Lock<Value<'gc>>);
}

fn arena() -> Arena<VectorRoot> {
    Arena::new(4 << 20, |_| Ok((Lock::new(Value::NIL), Lock::new(Value::NIL)))).unwrap()
}

fn fix<'gc>(n: i64) -> Value<'gc> {
    Value::fixnum(n).unwrap()
}

fn read<'gc>(v: Gc<'gc, Vector<'gc>>) -> Vec<Value<'gc>> {
    v.items().iter().map(Lock::get).collect()
}

#[test]
fn vectors_hold_what_they_were_made_with() {
    let mut arena = arena();
    arena.mutate(|mc, _| {
        let h = Vectors::new(mc).unwrap();
        let made = h.make(5, Value::TRUE).unwrap();
        assert_eq!(read(made), [Value::TRUE; 5]);
        let items: Vec<_> = (0..7).map(fix).collect();
        assert_eq!(read(h.from_slice(&items).unwrap()), items);
        assert!(h.make(0, Value::NIL).unwrap().items().is_empty());
        assert!(h.from_slice(&[]).unwrap().items().is_empty());
        let slots = made.items();
        slots[2].set(mc, fix(9));
        assert_eq!(slots[2].get(), fix(9));
        Lock::fill(mc, &slots[3..], Value::FALSE);
        assert_eq!(read(made), [Value::TRUE, Value::TRUE, fix(9), Value::FALSE, Value::FALSE]);
    }).unwrap();
}

#[test]
fn only_vectors_are_vectors() {
    let mut arena = arena();
    arena.mutate(|mc, _| {
        let h = Vectors::new(mc).unwrap();
        let v = Value::object(mc, h.make(2, Value::NIL).unwrap());
        assert!(h.vector(v).is_some_and(AnyVector::is_mutable) && h.mutable(v).is_some());
        let pair = Value::object(mc, Pairs::new(mc).unwrap().cons(fix(1), fix(2)).unwrap());
        assert!(h.vector(pair).is_none() && h.mutable(pair).is_none());
        assert!(h.vector(fix(1)).is_none() && h.vector(Value::NIL).is_none());
    }).unwrap();
}

#[test]
fn vectors_too_long_for_the_arena_fail() {
    let mut arena = arena();
    arena.mutate(|mc, _| {
        let h = Vectors::new(mc).unwrap();
        assert_eq!(h.make(max_items::<Vector<'_>>() + 1, Value::NIL).unwrap_err(), OutOfMemory);
        assert_eq!(h.make(usize::MAX, Value::NIL).unwrap_err(), OutOfMemory);
        assert_eq!(h.make(1 << 20, Value::NIL).unwrap_err(), OutOfMemory, "past the limit");
    }).unwrap();
}

/// Each way of storing into an old vector keeps the young objects it stores alive through
/// minor collections, and the vector follows them when compaction moves them.
#[test]
fn stores_into_old_vectors_keep_young_objects() {
    let mut arena = arena();
    arena.set_evacuate_all(true);
    arena.mutate(|mc, root| {
        let h = Vectors::new(mc).unwrap();
        root.0.set(mc, Value::object(mc, h.make(64, Value::NIL).unwrap()));
    }).unwrap();
    arena.collect();
    arena.mutate(|mc, root| {
        let v = Vectors::new(mc).unwrap().mutable(root.0.get()).unwrap();
        let p = Pairs::new(mc).unwrap();
        let slots = v.items();
        slots[0].set(mc, p.list(&[fix(0)]).unwrap());
        Lock::fill(mc, &slots[10..20], p.list(&[fix(1), fix(1)]).unwrap());
        let fresh = Vectors::new(mc).unwrap().from_slice(&[p.list(&[fix(2), fix(2), fix(2)]).unwrap(); 8]).unwrap();
        Lock::copy(mc, &slots[40..48], fresh.items());
        // Overlapping, so the copy runs backwards.
        Lock::copy(mc, &slots[41..49], &slots[40..48]);
    }).unwrap();
    let check = |arena: &mut Arena<VectorRoot>| {
        arena.mutate(|mc, root| {
            let v = Vectors::new(mc).unwrap().vector(root.0.get()).unwrap();
            let p = Pairs::new(mc).unwrap();
            let len = |i: usize| p.list_len(v.get(i).unwrap());
            assert_eq!(len(0), Some(1));
            assert!((10..20).all(|i| len(i) == Some(2)));
            assert!((40..49).all(|i| len(i) == Some(3)));
            assert_eq!(v.get(49), Some(Value::NIL));
        }).unwrap();
    };
    arena.collect_minor();
    check(&mut arena);
    arena.collect();
    check(&mut arena);
    // The vector, and the lists: one, two and three pairs.
    assert_eq!(arena.metrics().objects, 1 + 1 + 2 + 3);
}

#[test]
fn immutable_vectors_can_be_read_but_not_written() {
    let mut arena = arena();
    arena.mutate(|mc, _| {
        let h = Vectors::new(mc).unwrap();
        let items: Vec<_> = (0..4).map(fix).collect();
        let v = Value::object(mc, h.immutable_from_slice(&items).unwrap());
        let any = h.vector(v).unwrap();
        assert!(!any.is_mutable() && h.mutable(v).is_none(), "vector-set! can't reach it");
        assert_eq!((any.len(), any.get(3), any.get(4)), (4, Some(fix(3)), None));
        assert_eq!(any.value(mc), v);
        let empty = h.vector(Value::object(mc, h.immutable_from_slice(&[]).unwrap())).unwrap();
        assert!(empty.is_empty() && empty.get(0).is_none());
    }).unwrap();
}

/// Freezing copies a mutable vector, so later writes don't show, and hands back an immutable
/// one as it is.
#[test]
fn freezing_takes_a_snapshot() {
    let mut arena = arena();
    arena.mutate(|mc, _| {
        let h = Vectors::new(mc).unwrap();
        let v = h.make(3, fix(1)).unwrap();
        let frozen = h.freeze(AnyVector::Mutable(v)).unwrap();
        v.items()[0].set(mc, fix(2));
        let frozen = AnyVector::Immutable(frozen);
        assert_eq!((0..3).map(|i| frozen.get(i).unwrap()).collect::<Vec<_>>(), [fix(1); 3]);
        assert_eq!(frozen.value(mc), h.freeze(frozen).map(AnyVector::Immutable).unwrap().value(mc));
    }).unwrap();
}

#[test]
fn immutable_vectors_keep_what_they_hold() {
    let mut arena = arena();
    arena.set_evacuate_all(true);
    arena.mutate(|mc, root| {
        let p = Pairs::new(mc).unwrap();
        let items: Vec<_> = (0..20).map(|i| p.list(&vec![fix(i); i as usize + 1]).unwrap()).collect();
        let v = Vectors::new(mc).unwrap().immutable_from_slice(&items).unwrap();
        root.0.set(mc, Value::object(mc, v));
        p.list(&[fix(0); 50]).unwrap();
    }).unwrap();
    for _ in 0..2 {
        arena.collect_minor();
        arena.collect();
        assert_eq!(arena.metrics().objects, 1 + (1..=20).sum::<usize>());
        arena.mutate(|mc, root| {
            let v = Vectors::new(mc).unwrap().vector(root.0.get()).unwrap();
            let p = Pairs::new(mc).unwrap();
            assert!((0..20).all(|i| p.list_len(v.get(i).unwrap()) == Some(i as u64 + 1)));
        }).unwrap();
    }
}
