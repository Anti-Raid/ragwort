use ragwort_gc::{Arena, Lock, Rootable};

use super::*;
use crate::num::{Nums, int};

struct ValueRoot;
impl Rootable for ValueRoot {
    type Root<'gc> = Lock<Value<'gc>>;
}

fn arena() -> Arena<ValueRoot> {
    sized_arena(4 << 20)
}

fn sized_arena(limit: usize) -> Arena<ValueRoot> {
    Arena::new(limit, |_| Ok(Lock::new(Value::NIL))).unwrap()
}

fn fix<'gc>(n: i64) -> Value<'gc> {
    Value::fixnum(n).unwrap()
}

fn fixnums<'gc>(p: &Pairs<'_, 'gc>, v: Value<'gc>) -> Vec<i64> {
    p.elements(v).map(|x| x.as_fixnum().unwrap()).collect()
}

#[test]
fn pairs_know_the_length_of_their_list() {
    let mut arena = arena();
    arena.mutate(|mc, _| {
        let p = Pairs::new(mc).unwrap();
        let one = p.cons(fix(1), Value::NIL).unwrap();
        assert_eq!((one.head(), one.tail(), one.list_len()), (fix(1), Value::NIL, Some(1)));
        let two = p.cons(fix(0), Value::object(mc, one)).unwrap();
        assert_eq!(two.list_len(), Some(2));
        assert_eq!(p.list_len(Value::NIL), Some(0));
        assert_eq!(p.list_len(fix(3)), None);
        assert!(p.is_list(Value::object(mc, two)) && p.is_list(Value::NIL) && !p.is_list(Value::TRUE));
    }).unwrap();
}

/// Pairs that end in something other than `()` aren't lists, nor is anything built on them.
#[test]
fn improper_chains_have_no_length() {
    let mut arena = arena();
    arena.mutate(|mc, _| {
        let p = Pairs::new(mc).unwrap();
        let dotted = p.cons(fix(1), fix(2)).unwrap();
        assert_eq!(dotted.list_len(), None);
        let longer = p.cons(fix(0), Value::object(mc, dotted)).unwrap();
        assert_eq!(longer.list_len(), None);
        assert!(!p.is_list(Value::object(mc, longer)));
        let elements = p.elements(Value::object(mc, longer));
        assert_eq!(elements.map(|x| x.as_fixnum().unwrap()).collect::<Vec<_>>(), [0, 1]);
        let mut elements = p.elements(Value::object(mc, longer));
        elements.by_ref().for_each(drop);
        assert_eq!(elements.rest(), fix(2));
        // A list as the head doesn't make the pair a list.
        let nested = p.cons(Value::object(mc, p.cons(fix(1), Value::NIL).unwrap()), fix(9)).unwrap();
        assert_eq!(nested.list_len(), None);
    }).unwrap();
}

#[test]
fn lists_round_trip() {
    let mut arena = arena();
    arena.mutate(|mc, _| {
        let p = Pairs::new(mc).unwrap();
        let items: Vec<_> = (0..10).map(fix).collect();
        let list = p.list(&items).unwrap();
        assert_eq!(p.list_len(list), Some(10));
        assert_eq!(fixnums(&p, list), (0..10).collect::<Vec<_>>());
        assert_eq!(p.list(&[]).unwrap(), Value::NIL);
        let mut elements = p.elements(list);
        elements.by_ref().for_each(drop);
        assert_eq!(elements.rest(), Value::NIL);
    }).unwrap();
}

#[test]
fn iterator_lists_preserve_tails_and_cached_lengths() {
    let mut arena = arena();
    arena.mutate(|mc, root| {
        let p = Pairs::new(mc).unwrap();
        let tail = p.list(&[fix(3), fix(4)]).unwrap();
        let list = p.list_with_tail((0..3).map(fix), tail).unwrap();
        assert_eq!(fixnums(&p, list), [0, 1, 2, 3, 4]);
        let mut rest = list;
        for len in (1..=5).rev() {
            let pair = p.pair(rest).unwrap();
            assert_eq!(pair.list_len(), Some(len));
            rest = pair.tail();
        }
        assert_eq!(rest, Value::NIL);
        assert_eq!(p.list_with_tail(std::iter::empty(), tail).unwrap(), tail);
        let dotted = p.list_with_tail((1..3).map(fix), fix(9)).unwrap();
        let dotted = p.list_with_tail(std::iter::once(fix(0)), dotted).unwrap();
        let mut elements = p.elements(dotted);
        assert_eq!(elements.by_ref().map(|v| v.as_fixnum().unwrap()).collect::<Vec<_>>(), [0, 1, 2]);
        assert_eq!(elements.rest(), fix(9));
        assert_eq!(p.list_len(dotted), None);
        root.set(mc, list);
    }).unwrap();
    arena.set_evacuate_all(true);
    arena.collect_minor();
    arena.collect();
    arena.mutate(|mc, root| {
        let p = Pairs::new(mc).unwrap();
        assert_eq!(p.list_len(root.get()), Some(5));
        assert_eq!(fixnums(&p, root.get()), [0, 1, 2, 3, 4]);
    }).unwrap();
}

/// Only pairs are pairs, though other objects are laid out the same way.
#[test]
fn other_objects_are_not_pairs() {
    let mut arena = arena();
    arena.mutate(|mc, _| {
        let p = Pairs::new(mc).unwrap();
        let h = Nums::new(mc).unwrap();
        let big = int::add(&h, int::from_i64(&h, Value::MAX_FIXNUM).unwrap(), int::from_i64(&h, 1).unwrap()).unwrap();
        assert!(p.pair(big.value()).is_none());
        let holder = p.cons(big.value(), Value::NIL).unwrap();
        assert!(p.pair(Value::object(mc, holder)).is_some());
        assert_eq!(p.list_len(big.value()), None);
        assert_eq!(p.elements(fix(1)).count(), 0);
    }).unwrap();
}

#[test]
fn long_lists_keep_their_length_through_collections() {
    let n = if cfg!(miri) { 500 } else { 200_000 };
    let mut arena = sized_arena(32 << 20);
    arena.set_evacuate_all(true);
    arena.mutate(|mc, root| {
        let p = Pairs::new(mc).unwrap();
        let mut list = Value::NIL;
        for i in (0..n).rev() {
            list = Value::object(mc, p.cons(fix(i), list).unwrap());
        }
        root.set(mc, list);
        // Garbage between the pairs, so compaction has something to close up.
        p.list(&[fix(1); 100]).unwrap();
    }).unwrap();
    arena.collect_minor();
    arena.collect();
    arena.collect();
    assert_eq!(arena.metrics().objects, n as usize);
    arena.mutate(|mc, root| {
        let p = Pairs::new(mc).unwrap();
        let list = root.get();
        assert_eq!(p.list_len(list), Some(n as u64));
        let tail = p.pair(list).unwrap().tail();
        assert_eq!(p.list_len(tail), Some(n as u64 - 1));
        assert!(p.elements(list).map(|x| x.as_fixnum().unwrap()).eq(0..n));
    }).unwrap();
}
