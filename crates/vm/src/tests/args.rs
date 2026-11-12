use ragwort_types::gc::{Arena, Mutation, Value};
use ragwort_types::pair::Pairs;
use ragwort_types::vector::Vectors;

use super::*;

fn fix<'gc>(n: i64) -> Value<'gc> {
    Value::fixnum(n).unwrap()
}

fn all<'gc>(mc: &Mutation<'gc>, args: Args<'gc>) -> Vec<Value<'gc>> {
    args.iter(mc).unwrap().collect()
}

#[test]
fn detached_arguments_are_held_inline_up_to_four() {
    let mut arena = Arena::new(1 << 20, 0);
    arena.mutate(|mc| {
        let stored: Vec<Value<'_>> = (0..6).map(fix).collect();
        let slots = Vectors::new(mc).from_slice(&stored).unwrap().items(mc);
        let rest = Pairs::new(mc).cons(fix(9), Value::NIL).unwrap().value(mc);
        for n in 0..=6 {
            let detached = Args::slots(slots.slice(0..n).unwrap(), rest).detach(mc).unwrap();
            let mut expected = stored[..n].to_vec();
            expected.push(fix(9));
            assert_eq!(all(mc, detached), expected);
            assert!(matches!(detached.held, Held::Inline(..)));
            // Up to `INLINE` arguments move inline and leave the rest list untouched; more are gathered into a new list.
            if n <= INLINE {
                assert_eq!((detached.held(), detached.rest), (n, rest));
            } else {
                assert_eq!(detached.held(), 0);
            }
        }
    });
}

#[test]
fn inline_arguments_are_sliced_and_spread() {
    let mut arena = Arena::new(1 << 20, 0);
    arena.mutate(|mc| {
        let pairs = Pairs::new(mc);
        let stored: Vec<Value<'_>> = (0..4).map(fix).collect();
        let slots = Vectors::new(mc).from_slice(&stored).unwrap().items(mc);
        let inline = Args::slots(slots, Value::NIL).detach(mc).unwrap();
        for k in 0..=4 {
            assert_eq!(all(mc, inline.tail(mc, k).unwrap()), stored[k..]);
        }
        assert_eq!(inline.tail(mc, 5).map(|_| ()), Err(Fault::Arity));

        let list = pairs.cons(fix(7), pairs.cons(fix(8), Value::NIL).unwrap().value(mc)).unwrap().value(mc);
        let last = Vectors::new(mc).from_slice(&[fix(0), fix(1), fix(2), list]).unwrap().items(mc);
        let spread = Args::slots(last, Value::NIL).detach(mc).unwrap().spread_last(mc).unwrap();
        assert_eq!(all(mc, spread), [fix(0), fix(1), fix(2), fix(7), fix(8)]);
    });
}
