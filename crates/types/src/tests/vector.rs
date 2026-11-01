use crate::gc::Arena;

use super::*;
use crate::pair::Pairs;

fn arena() -> Arena {
    Arena::new(4 << 20, 1)
}

fn fix<'gc>(n: i64) -> Value<'gc> {
    Value::fixnum(n).unwrap()
}

fn read<'gc>(mc: &Mutation<'gc>, v: Vector<'gc>) -> Vec<Value<'gc>> {
    let items = v.items(mc);
    (0..items.len()).map(|i| items.get(i)).collect()
}

#[test]
fn vectors_hold_what_they_were_made_with() {
    arena().mutate(|mc| {
        let h = Vectors::new(mc);
        let made = h.make(5, Value::TRUE).unwrap();
        assert_eq!(read(mc, made), [Value::TRUE; 5]);
        let items: Vec<_> = (0..7).map(fix).collect();
        assert_eq!(read(mc, h.from_slice(&items).unwrap()), items);
        assert!(h.make(0, Value::NIL).unwrap().items(mc).is_empty());
        assert!(h.from_slice(&[]).unwrap().items(mc).is_empty());
        let slots = made.items(mc);
        slots.set(mc, 2, fix(9));
        assert_eq!(slots.get(2), fix(9));
        slots.slice(3..5).unwrap().fill(mc, Value::FALSE);
        assert_eq!(read(mc, made), [Value::TRUE, Value::TRUE, fix(9), Value::FALSE, Value::FALSE]);
    });
}

#[test]
fn only_vectors_are_vectors() {
    arena().mutate(|mc| {
        let h = Vectors::new(mc);
        let v = h.make(2, Value::NIL).unwrap().value(mc);
        assert!(h.vector(v).is_some_and(AnyVector::is_mutable) && h.mutable(v).is_some());
        let pair = Pairs::new(mc).cons(fix(1), fix(2)).unwrap().value(mc);
        assert!(h.vector(pair).is_none() && h.mutable(pair).is_none());
        assert!(h.vector(fix(1)).is_none() && h.vector(Value::NIL).is_none());
    });
}

#[test]
fn vectors_too_long_for_the_arena_fail() {
    arena().mutate(|mc| {
        let h = Vectors::new(mc);
        assert_eq!(h.make(usize::MAX, Value::NIL).unwrap_err(), OutOfMemory);
        assert_eq!(h.make(1 << 20, Value::NIL).unwrap_err(), OutOfMemory, "past the limit");
    });
}

/// Each way of storing into an old vector keeps the young objects it stores alive through
/// minor collections, and the vector follows them when compaction moves them.
#[test]
fn stores_into_old_vectors_keep_young_objects() {
    let mut arena = arena();
    arena.set_evacuate_all(true);
    arena.mutate(|mc| mc.set_root(0, Vectors::new(mc).make(64, Value::NIL).unwrap().value(mc)));
    arena.collect();
    arena.mutate(|mc| {
        let v = Vectors::new(mc).mutable(mc.root(0)).unwrap();
        let p = Pairs::new(mc);
        let slots = v.items(mc);
        slots.set(mc, 0, p.list(&[fix(0)]).unwrap());
        slots.slice(10..20).unwrap().fill(mc, p.list(&[fix(1), fix(1)]).unwrap());
        let fresh = Vectors::new(mc).from_slice(&[p.list(&[fix(2), fix(2), fix(2)]).unwrap(); 8]).unwrap();
        slots.slice(40..48).unwrap().copy_from(mc, fresh.items(mc));
        // Overlapping, so the copy runs backwards.
        slots.slice(41..49).unwrap().copy_from(mc, slots.slice(40..48).unwrap());
    });
    let check = |arena: &mut Arena| {
        arena.mutate(|mc| {
            let v = Vectors::new(mc).vector(mc.root(0)).unwrap();
            let p = Pairs::new(mc);
            let len = |i: usize| p.list_len(v.get(mc, i).unwrap());
            assert_eq!(len(0), Some(1));
            assert!((10..20).all(|i| len(i) == Some(2)));
            assert!((40..49).all(|i| len(i) == Some(3)));
            assert_eq!(v.get(mc, 49), Some(Value::NIL));
        });
    };
    arena.collect_minor();
    check(&mut arena);
    arena.collect();
    check(&mut arena);
    // The vector, and the lists: one, two and three pairs.
    assert_eq!(arena.objects(), 1 + 1 + 2 + 3);
}

#[test]
fn immutable_vectors_can_be_read_but_not_written() {
    arena().mutate(|mc| {
        let h = Vectors::new(mc);
        let items: Vec<_> = (0..4).map(fix).collect();
        let v = h.immutable_from_slice(&items).unwrap().value(mc);
        let any = h.vector(v).unwrap();
        assert!(!any.is_mutable() && h.mutable(v).is_none(), "vector-set! can't reach it");
        assert_eq!((any.len(mc), any.get(mc, 3), any.get(mc, 4)), (4, Some(fix(3)), None));
        assert_eq!(any.value(mc), v);
        let empty = h.vector(h.immutable_from_slice(&[]).unwrap().value(mc)).unwrap();
        assert!(empty.is_empty(mc) && empty.get(mc, 0).is_none());
    });
}

/// Freezing copies a mutable vector, so later writes don't show, and hands back an immutable
/// one as it is.
#[test]
fn freezing_takes_a_snapshot() {
    arena().mutate(|mc| {
        let h = Vectors::new(mc);
        let v = h.make(3, fix(1)).unwrap();
        let frozen = h.freeze(AnyVector::Mutable(v)).unwrap();
        v.items(mc).set(mc, 0, fix(2));
        assert_eq!((0..3).map(|i| frozen.get(mc, i).unwrap()).collect::<Vec<_>>(), [fix(1); 3]);
        assert_eq!(h.freeze(AnyVector::Immutable(frozen)).unwrap(), frozen);
    });
}

#[test]
fn immutable_vectors_keep_what_they_hold() {
    let mut arena = arena();
    arena.set_evacuate_all(true);
    arena.mutate(|mc| {
        let p = Pairs::new(mc);
        let items: Vec<_> = (0..20).map(|i| p.list(&vec![fix(i); i as usize + 1]).unwrap()).collect();
        let v = Vectors::new(mc).immutable_from_slice(&items).unwrap();
        mc.set_root(0, v.value(mc));
        p.list(&[fix(0); 50]).unwrap();
    });
    for _ in 0..2 {
        arena.collect_minor();
        arena.collect();
        assert_eq!(arena.objects(), 1 + (1..=20).sum::<usize>());
        arena.mutate(|mc| {
            let v = Vectors::new(mc).vector(mc.root(0)).unwrap();
            let p = Pairs::new(mc);
            assert!((0..20).all(|i| p.list_len(v.get(mc, i).unwrap()) == Some(i as u64 + 1)));
        });
    }
}
