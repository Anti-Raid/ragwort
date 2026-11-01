use crate::gc::Arena;

use super::*;
use crate::num::{Nums, int};

fn arena() -> Arena {
    Arena::new(4 << 20, 1)
}

fn fix<'gc>(n: i64) -> Value<'gc> {
    Value::fixnum(n).unwrap()
}

fn fixnums<'gc>(p: &Pairs<'_, 'gc>, v: Value<'gc>) -> Vec<i64> {
    p.elements(v).map(|x| x.as_fixnum().unwrap()).collect()
}

#[test]
fn pairs_know_the_length_of_their_list() {
    arena().mutate(|mc| {
        let p = Pairs::new(mc);
        let one = p.cons(fix(1), Value::NIL).unwrap();
        assert_eq!((one.head(mc), one.tail(mc), one.list_len(mc)), (fix(1), Value::NIL, Some(1)));
        let two = p.cons(fix(0), one.value(mc)).unwrap();
        assert_eq!(two.list_len(mc), Some(2));
        assert_eq!(p.list_len(Value::NIL), Some(0));
        assert_eq!(p.list_len(fix(3)), None);
        assert!(p.is_list(two.value(mc)) && p.is_list(Value::NIL) && !p.is_list(Value::TRUE));
    });
}

/// Pairs that end in something other than `()` aren't lists, nor is anything built on them.
#[test]
fn improper_chains_have_no_length() {
    arena().mutate(|mc| {
        let p = Pairs::new(mc);
        let dotted = p.cons(fix(1), fix(2)).unwrap();
        assert_eq!(dotted.list_len(mc), None);
        let longer = p.cons(fix(0), dotted.value(mc)).unwrap();
        assert_eq!(longer.list_len(mc), None);
        assert!(!p.is_list(longer.value(mc)));
        assert_eq!(fixnums(&p, longer.value(mc)), [0, 1]);
        let mut elements = p.elements(longer.value(mc));
        elements.by_ref().for_each(drop);
        assert_eq!(elements.rest(), fix(2));
        // A list as the head doesn't make the pair a list.
        let nested = p.cons(p.cons(fix(1), Value::NIL).unwrap().value(mc), fix(9)).unwrap();
        assert_eq!(nested.list_len(mc), None);
    });
}

#[test]
fn lists_round_trip() {
    arena().mutate(|mc| {
        let p = Pairs::new(mc);
        let items: Vec<_> = (0..10).map(fix).collect();
        let list = p.list(&items).unwrap();
        assert_eq!(p.list_len(list), Some(10));
        assert_eq!(fixnums(&p, list), (0..10).collect::<Vec<_>>());
        assert_eq!(p.list(&[]).unwrap(), Value::NIL);
        let mut elements = p.elements(list);
        elements.by_ref().for_each(drop);
        assert_eq!(elements.rest(), Value::NIL);
    });
}

#[test]
fn iterator_lists_preserve_tails_and_cached_lengths() {
    let mut arena = arena();
    arena.mutate(|mc| {
        let p = Pairs::new(mc);
        let tail = p.list(&[fix(3), fix(4)]).unwrap();
        let list = p.list_with_tail((0..3).map(fix), tail).unwrap();
        assert_eq!(fixnums(&p, list), [0, 1, 2, 3, 4]);
        let mut rest = list;
        for len in (1..=5).rev() {
            let pair = p.pair(rest).unwrap();
            assert_eq!(pair.list_len(mc), Some(len));
            rest = pair.tail(mc);
        }
        assert_eq!(rest, Value::NIL);
        assert_eq!(p.list_with_tail(std::iter::empty(), tail).unwrap(), tail);
        let dotted = p.list_with_tail((1..3).map(fix), fix(9)).unwrap();
        let dotted = p.list_with_tail(std::iter::once(fix(0)), dotted).unwrap();
        let mut elements = p.elements(dotted);
        assert_eq!(elements.by_ref().map(|v| v.as_fixnum().unwrap()).collect::<Vec<_>>(), [0, 1, 2]);
        assert_eq!(elements.rest(), fix(9));
        assert_eq!(p.list_len(dotted), None);
        mc.set_root(0, list);
    });
    arena.set_evacuate_all(true);
    arena.collect_minor();
    arena.collect();
    arena.mutate(|mc| {
        let p = Pairs::new(mc);
        assert_eq!(p.list_len(mc.root(0)), Some(5));
        assert_eq!(fixnums(&p, mc.root(0)), [0, 1, 2, 3, 4]);
    });
}

/// Only pairs are pairs, though other objects are laid out the same way.
#[test]
fn other_objects_are_not_pairs() {
    arena().mutate(|mc| {
        let p = Pairs::new(mc);
        let h = Nums::new(mc);
        let big = int::add(&h, int::from_i64(&h, Value::MAX_FIXNUM).unwrap(), int::from_i64(&h, 1).unwrap()).unwrap();
        assert!(p.pair(big.value()).is_none());
        let holder = p.cons(big.value(), Value::NIL).unwrap();
        assert!(p.pair(holder.value(mc)).is_some());
        assert_eq!(p.list_len(big.value()), None);
        assert_eq!(p.elements(fix(1)).count(), 0);
    });
}

#[test]
fn long_lists_keep_their_length_through_collections() {
    let n = 200_000;
    let mut arena = Arena::new(32 << 20, 1);
    arena.set_evacuate_all(true);
    arena.mutate(|mc| {
        let p = Pairs::new(mc);
        let mut list = Value::NIL;
        for i in (0..n).rev() {
            list = p.cons(fix(i), list).unwrap().value(mc);
        }
        mc.set_root(0, list);
        // Garbage between the pairs, so compaction has something to close up.
        p.list(&[fix(1); 100]).unwrap();
    });
    arena.collect_minor();
    arena.collect();
    arena.collect();
    assert_eq!(arena.objects(), n as usize);
    arena.mutate(|mc| {
        let p = Pairs::new(mc);
        let list = mc.root(0);
        assert_eq!(p.list_len(list), Some(n as u64));
        let tail = p.pair(list).unwrap().tail(mc);
        assert_eq!(p.list_len(tail), Some(n as u64 - 1));
        assert!(p.elements(list).map(|x| x.as_fixnum().unwrap()).eq(0..n));
    });
}
