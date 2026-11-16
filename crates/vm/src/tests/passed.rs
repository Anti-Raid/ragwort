use ragwort_types::gc::{Arena, Mutation, Value};
use ragwort_types::pair::Pairs;
use ragwort_types::vector::Vectors;

use super::*;

fn fix<'gc>(n: i64) -> Value<'gc> {
    Value::fixnum(n).unwrap()
}

fn all<'gc>(mc: &Mutation<'gc>, passed: Passed<'gc>) -> Vec<Value<'gc>> {
    Pairs::new(mc).elements(passed.to_list(mc).unwrap()).collect()
}

#[test]
fn passed_values_are_read_skipped_and_spread() {
    let mut arena = Arena::new(1 << 20, 0);
    arena.mutate(|mc| {
        let pairs = Pairs::new(mc);
        let stored: Vec<Value<'_>> = (0..4).map(fix).collect();
        let slots = Vectors::new(mc).from_slice(&stored).unwrap().items(mc);
        let rest = pairs.list(&[fix(7), fix(8)]).unwrap();
        // Positions run through the slots and then through the list.
        let passed = Passed::slots(slots, rest);
        let expected = [fix(0), fix(1), fix(2), fix(3), fix(7), fix(8)];
        for (index, &value) in expected.iter().enumerate() {
            assert_eq!(passed.get(mc, index), Ok(value));
            assert_eq!(all(mc, passed.skip(mc, index).unwrap()), expected[index..]);
        }
        assert_eq!(passed.get(mc, 6), Err(Fault::Arity));
        assert!(all(mc, passed.skip(mc, 6).unwrap()).is_empty());
        assert_eq!(passed.skip(mc, 7).map(|_| ()), Err(Fault::Arity));

        // The last value is spread, whether it is in a slot or at the end of the list.
        let last = Vectors::new(mc).from_slice(&[fix(0), fix(1), rest]).unwrap().items(mc);
        assert_eq!(all(mc, Passed::slots(last, Value::NULL).spread_last(mc).unwrap()), [fix(0), fix(1), fix(7), fix(8)]);
        let listed = pairs.list(&[fix(2), rest]).unwrap();
        assert_eq!(all(mc, Passed::slots(slots.slice(0..2).unwrap(), listed).spread_last(mc).unwrap()), [fix(0), fix(1), fix(2), fix(7), fix(8)]);
        assert_eq!(Passed::none().spread_last(mc).map(|_| ()), Err(Fault::Arity));

        // Exactly one value is taken as it is. Any other number is taken as a list.
        assert!(matches!(Passed::slots(slots.slice(1..2).unwrap(), Value::NULL).take(mc), Ok(Taken::One(value)) if value == fix(1)));
        assert!(matches!(Passed::none().take(mc), Ok(Taken::List(Value::NULL))));
        assert!(matches!(Passed::list(pairs.list(&[fix(9)]).unwrap()).take(mc), Ok(Taken::List(list)) if pairs.elements(list).eq([fix(9)])));
        assert!(matches!(Passed::slots(slots, fix(5)).take(mc), Err(Fault::WrongType)));
    });
}
