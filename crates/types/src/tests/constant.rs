use std::collections::HashMap;

use super::*;
use crate::gc::{Arena, GcVec, slot};
use crate::num::{int, rational};
use crate::pair::Pairs;
use crate::symbol::Symbols;

fn fix<'gc>(n: i64) -> Value<'gc> {
    Value::fixnum(n).unwrap()
}

fn pooled(c: Constant) -> Const {
    match c {
        Constant::Pooled(c) => c,
        Constant::Immediate(_) => panic!("{c:?} isn't pooled"),
    }
}

/// The `i`th of a run of constants that repeat: symbols, strings, some as ropes, bignums, ratios
/// and boxed flonums.
fn make<'gc>(mc: &Mutation<'gc>, symbols: Symbols<'gc>, i: usize) -> Result<Value<'gc>, Error> {
    let (h, n) = (Strings::new(mc), Nums::new(mc));
    let k = i / 5;
    Ok(match i % 5 {
        0 => symbols.intern_str(&h, &format!("name{}", k % 7))?.value(mc),
        1 => {
            let text = format!("message {} ", k % 9).repeat(8);
            let (a, b) = text.split_at(text.len() / 2);
            match k % 2 {
                0 => string::from_str(&h, &text)?.value(),
                _ => string::concat(&h, string::from_str(&h, a)?, string::from_str(&h, b)?)?.value(),
            }
        }
        2 => int::expt(&n, n.integer(fix(2)).unwrap(), 64 + (k % 5) as u64)?.value(),
        3 => rational::div(&n, n.rational(fix((k % 6) as i64 + 1)).unwrap(), n.rational(fix(7)).unwrap())?.value(),
        _ => Value::flonum(mc, 1e300 * (k % 3 + 1) as f64)?,
    })
}

fn describe<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> String {
    let (h, n) = (Strings::new(mc), Nums::new(mc));
    if let Some(s) = Symbol::of(v) {
        return format!("'{}", string::display(&h, s.name(mc)));
    }
    if let Some(s) = h.string(v) {
        return format!("{:?}", string::display(&h, s).to_string());
    }
    if let Some(f) = v.as_flonum(mc) {
        return format!("{f:e}");
    }
    rational::to_string(&n, n.rational(v).expect("a constant the test made"), 10).unwrap()
}

#[test]
fn immediates_need_no_slot() {
    Arena::new(1 << 20, 1).mutate(|mc| {
        let mut pool = ConstPool::new(mc).unwrap();
        let short = string::from_str(&Strings::new(mc), "!ping").unwrap().value();
        for v in [fix(3), fix(-1), Value::inline_flonum(0.5).unwrap(), Value::TRUE, Value::FALSE, Value::NIL, Value::VOID, short] {
            assert_eq!(pool.add(mc, v), Ok(Constant::Immediate(v.immediate().unwrap())));
        }
        assert!(pool.is_empty());
        assert!(pool.finish(mc).unwrap().is_empty(mc));
    });
}

#[test]
fn equal_contents_share_a_slot() {
    Arena::new(4 << 20, 1).mutate(|mc| {
        let symbols = Symbols::new(mc).unwrap();
        let mut pool = ConstPool::new(mc).unwrap();
        let mut seen = HashMap::new();
        for i in 0..400 {
            let v = make(mc, symbols, i).unwrap();
            let c = pooled(pool.add(mc, v).unwrap());
            assert_eq!(*seen.entry(describe(mc, v)).or_insert(c), c, "{}", describe(mc, v));
        }
        assert_eq!(pool.len(), seen.len());
        let mut indices: Vec<_> = seen.values().map(|c| c.index()).collect();
        indices.sort_unstable();
        assert_eq!(indices, (0..seen.len() as u32).collect::<Vec<_>>(), "distinct contents get distinct slots");
    });
}

#[test]
fn kinds_and_exactness_stay_apart() {
    Arena::new(1 << 20, 1).mutate(|mc| {
        let (h, n) = (Strings::new(mc), Nums::new(mc));
        let symbols = Symbols::new(mc).unwrap();
        let mut pool = ConstPool::new(mc).unwrap();
        let two = n.integer(fix(2)).unwrap();
        let big = int::expt(&n, two, 1000).unwrap().value();
        let values = [
            symbols.intern_str(&h, "abcdefgh").unwrap().value(mc),
            Symbols::new(mc).unwrap().intern_str(&h, "abcdefgh").unwrap().value(mc),
            string::from_str(&h, "abcdefgh").unwrap().value(),
            big,
            Value::flonum(mc, 2f64.powi(1000)).unwrap(),
            Value::flonum(mc, -2f64.powi(1000)).unwrap(),
            complex::rectangular(&n, n.real(fix(1)).unwrap(), n.real(big).unwrap()).unwrap().value(),
            complex::rectangular(&n, n.real(fix(1)).unwrap(), n.real(Value::flonum(mc, 2f64.powi(1000)).unwrap()).unwrap()).unwrap().value(),
        ];
        let consts: Vec<_> = values.iter().map(|&v| pooled(pool.add(mc, v).unwrap())).collect();
        assert_eq!(consts.iter().map(|c| c.index()).collect::<Vec<_>>(), (0..values.len() as u32).collect::<Vec<_>>());
        let again = complex::rectangular(&n, n.real(fix(1)).unwrap(), n.real(big).unwrap()).unwrap().value();
        assert_eq!(pool.add(mc, again), Ok(Constant::Pooled(consts[6])));
    });
}

#[test]
fn other_objects_get_a_slot_each_time() {
    Arena::new(1 << 20, 1).mutate(|mc| {
        let mut pool = ConstPool::new(mc).unwrap();
        let pair = Pairs::new(mc).cons(fix(1), fix(2)).unwrap().value(mc);
        let twin = Pairs::new(mc).cons(fix(1), fix(2)).unwrap().value(mc);
        let vector = Vectors::new(mc).immutable_from_slice(&[fix(1)]).unwrap().value(mc);
        let consts: Vec<_> = [pair, twin, pair, vector, vector].iter().map(|&v| pooled(pool.add(mc, v).unwrap()).index()).collect();
        assert_eq!(consts, [0, 1, 2, 3, 4]);
        assert_eq!(pool.get(mc, Const(2)), Some(pair));
        assert_eq!(pool.get(mc, Const(5)), None);
    });
}

#[test]
fn constants_keep_their_slots_as_objects_move() {
    let mut arena = Arena::new(8 << 20, 1);
    let (mut pool, seen) = arena.mutate(|mc| {
        let symbols = Symbols::new(mc).unwrap();
        mc.set_root(0, symbols.value(mc));
        let mut pool = ConstPool::new(mc).unwrap();
        let mut seen = HashMap::new();
        for i in 0..300 {
            let v = make(mc, symbols, i).unwrap();
            seen.insert(describe(mc, v), pooled(pool.add(mc, v).unwrap()));
        }
        (pool, seen)
    });
    arena.collect_minor();
    arena.set_evacuate_all(true);
    arena.collect();
    arena.collect();
    arena.mutate(|mc| {
        for (text, &c) in &seen {
            assert_eq!(&describe(mc, pool.get(mc, c).unwrap()), text);
        }
        let symbols = Symbols::of(mc.root(0)).unwrap();
        for i in 0..300 {
            let v = make(mc, symbols, i).unwrap();
            assert_eq!(pool.add(mc, v), Ok(Constant::Pooled(seen[&describe(mc, v)])), "{}", describe(mc, v));
        }
        assert_eq!(pool.len(), seen.len());
        let done = pool.finish(mc).unwrap();
        assert_eq!(done.len(mc), pool.len());
        for (text, &c) in &seen {
            assert_eq!(&describe(mc, done.get(mc, c.index() as usize).unwrap()), text);
        }
    });
}

#[test]
fn failed_steps_leave_the_pool_whole() {
    let mut arena = Arena::new(8 << 20, 1);
    let mut pool = arena.mutate(|mc| {
        mc.set_root(0, Symbols::new(mc).unwrap().value(mc));
        ConstPool::new(mc).unwrap()
    });
    let mut seen = HashMap::new();
    for fail in 0..60 {
        arena.fail_after(Some(fail));
        let _ = arena.step(|mc| {
            let symbols = Symbols::of(mc.root(0)).unwrap();
            (0..200).try_for_each(|i| pool.add(mc, make(mc, symbols, i + fail as usize)?).map(drop))
        });
        arena.fail_after(None);
        arena.mutate(|mc| {
            assert_eq!(pool.items(mc).len(mc), pool.len());
            let symbols = Symbols::of(mc.root(0)).unwrap();
            for i in 0..200 {
                let v = make(mc, symbols, i + fail as usize).unwrap();
                let c = pooled(pool.add(mc, v).unwrap());
                assert_eq!(*seen.entry(describe(mc, v)).or_insert(c), c, "{}", describe(mc, v));
                assert_eq!(describe(mc, pool.get(mc, c).unwrap()), describe(mc, v));
            }
            assert_eq!(pool.len(), seen.len());
        });
    }
}

/// The values each step adds: contents that merge, made once, and pairs, which take a slot every
/// time.
fn values<'gc>(mc: &Mutation<'gc>) -> GcVec<'gc> {
    GcVec::of(mc.root(1).downcast(mc).unwrap())
}

#[test]
fn running_out_leaves_the_pool_whole() {
    let mut arena = Arena::new(1 << 20, 2);
    let mut pool = arena.mutate(|mc| {
        let symbols = Symbols::new(mc).unwrap();
        mc.set_root(0, symbols.value(mc));
        let values = GcVec::<slot::Value>::new(mc).unwrap();
        for i in 0..50 {
            values.push(mc, make(mc, symbols, i).unwrap()).unwrap();
            values.push(mc, Pairs::new(mc).cons(fix(i as i64), Value::NIL).unwrap().value(mc)).unwrap();
        }
        mc.set_root(1, Value::object(mc, values.head()));
        ConstPool::new(mc).unwrap()
    });
    let mut steps = 0;
    while let Ok(Ok(())) = arena.step(|mc| values(mc).iter(mc).try_for_each(|v| pool.add(mc, v).map(drop))) {
        steps += 1;
        assert!(steps < 100_000, "the arena never ran out");
    }
    assert!(steps > 0);
    arena.mutate(|mc| {
        assert_eq!(pool.items(mc).len(mc), pool.len());
        let mut seen = HashMap::new();
        for v in values(mc).iter(mc).step_by(2) {
            let c = pooled(pool.add(mc, v).unwrap());
            assert_eq!(*seen.entry(describe(mc, v)).or_insert(c), c, "{}", describe(mc, v));
            assert_eq!(describe(mc, pool.get(mc, c).unwrap()), describe(mc, v));
        }
    });
}

#[test]
#[should_panic(expected = "different arena")]
fn another_arenas_pool_panics() {
    let pool = Arena::new(1 << 20, 1).mutate(|mc| ConstPool::new(mc).unwrap());
    Arena::new(1 << 20, 1).mutate(|mc| {
        pool.get(mc, Const(0));
    });
}
