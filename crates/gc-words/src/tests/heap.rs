use std::rc::Rc;

use super::*;

objects! {
    kind Kind;
    struct Pair { car: Value, cdr: Value }
    struct Node { n: u64, next: Member<Node> }
    struct Vector {} items Value
    struct Boxed { data: Host<String> }
    struct Counter { count: Host<i32> }
    /// Weakly holds a node, and links to the next holder.
    struct Holder { target: Weak<Node>, next: Member<Holder> }
    struct Table {} items Ephemeron
    struct Cached { n: Value, cache: Ephemeron }
}

/// A list of fixnums `0..n` in root 0, last first.
fn build(arena: &mut Arena, n: i64) {
    arena.mutate(|mc| {
        for i in 0..n {
            let pair = Pair::new(mc, Value::fixnum(i).unwrap(), mc.root(0)).unwrap();
            mc.set_root(0, Value::object(mc, pair));
        }
    });
}

fn sum(arena: &mut Arena) -> (i64, usize) {
    arena.mutate(|mc| {
        let (mut sum, mut len, mut cur) = (0, 0, mc.root(0));
        while let Some(pair) = cur.downcast::<Pair>(mc) {
            sum += pair.car(mc).as_fixnum().unwrap();
            len += 1;
            cur = pair.cdr(mc);
        }
        (sum, len)
    })
}

#[test]
fn lists_survive_every_kind_of_collection() {
    let mut arena = Arena::new(REGION, 1);
    build(&mut arena, 100_000);
    let expected = (100_000 * 99_999 / 2, 100_000);
    arena.collect_minor();
    assert_eq!(sum(&mut arena), expected);
    arena.collect();
    assert_eq!(sum(&mut arena), expected);
    arena.set_evacuate_all(true);
    arena.collect();
    assert_eq!(sum(&mut arena), expected);
    arena.collect();
    assert_eq!(sum(&mut arena), expected);
}

#[test]
fn garbage_is_reused() {
    let mut arena = Arena::new(4 << 20, 1);
    for _ in 0..50 {
        arena.step(|mc| {
            for i in 0..10_000 {
                Pair::new(mc, Value::fixnum(i).unwrap(), Value::NIL).unwrap();
            }
        })
        .unwrap();
    }
    build(&mut arena, 10);
    assert_eq!(sum(&mut arena), (45, 10));
}

/// An old object's young referent survives a minor collection through the card the store
/// dirtied, and nothing else.
#[test]
fn cards_keep_young_objects_alive() {
    let mut arena = Arena::new(REGION, 1);
    arena.mutate(|mc| {
        let old = Node::new(mc, 1, None).unwrap();
        mc.set_root(0, Value::object(mc, old));
    });
    arena.collect();
    arena.mutate(|mc| {
        let old = mc.root(0).downcast::<Node>(mc).unwrap();
        let young = Node::new(mc, 2, None).unwrap();
        old.set_next(mc, Some(young));
        for _ in 0..10_000 {
            Node::new(mc, 9, None).unwrap();
        }
    });
    arena.collect_minor();
    arena.mutate(|mc| {
        for _ in 0..10_000 {
            Node::new(mc, 7, None).unwrap();
        }
        let old = mc.root(0).downcast::<Node>(mc).unwrap();
        let young = old.next(mc).unwrap();
        assert_eq!(young.n(mc), 2);
    });
}

#[test]
fn stacks_and_vectors_are_traced_and_moved() {
    let mut arena = Arena::new(REGION, 1);
    let stack = arena.mutate(|mc| {
        let segment = Segment::new(mc, 1024).unwrap();
        let vector = Vector::new(mc, 300_000, Value::NIL).unwrap();
        let pair = Pair::new(mc, Value::fixnum(5).unwrap(), Value::NIL).unwrap();
        vector.items(mc).set(mc, 299_999, Value::object(mc, pair));
        mc.set_root(0, Value::object(mc, vector));
        let stack = mc.stack(segment).unwrap();
        stack.frame(mc, 512).unwrap().set(3, Value::object(mc, pair));
        stack
    });
    arena.set_evacuate_all(true);
    arena.collect();
    arena.collect_minor();
    arena.mutate(|mc| {
        let vector = mc.root(0).downcast::<Vector>(mc).unwrap();
        let from_vector = vector.items(mc).get(299_999).downcast::<Pair>(mc).unwrap();
        let from_stack = stack.frame(mc, 512).unwrap().get(3).downcast::<Pair>(mc).unwrap();
        assert!(from_vector == from_stack);
        assert_eq!(from_stack.car(mc).as_fixnum(), Some(5));
    });
}

#[test]
fn hosts_live_while_referenced() {
    let mut arena = Arena::new(1 << 20, 1);
    arena.mutate(|mc| {
        let host = mc.host(String::from("kept")).unwrap();
        let boxed = Boxed::new(mc, Some(host)).unwrap();
        mc.set_root(0, Value::object(mc, boxed));
        mc.host(String::from("dropped")).unwrap();
    });
    arena.collect();
    arena.mutate(|mc| {
        let boxed = mc.root(0).downcast::<Boxed>(mc).unwrap();
        assert_eq!(*boxed.data(mc).unwrap().get(mc).unwrap(), "kept");
    });
    assert!(arena.meta.hosts.borrow()[1].value.is_none());
}

/// A forged reference reads as some other object or none, never out of bounds.
#[test]
fn forged_references_are_only_wrong() {
    let mut arena = Arena::new(1 << 20, 1);
    arena.mutate(|mc| mc.set_root(0, Value::from_bits(u64::MAX << 4 | OBJECT)));
    arena.collect();
    arena.mutate(|mc| {
        if let Some(pair) = mc.root(0).downcast::<Pair>(mc) {
            pair.set_car(mc, pair.cdr(mc));
        }
    });
}

/// A chain of holders in root 0, each weakly holding a node; every other node is also held
/// strongly from root 1's vector.
fn holders(arena: &mut Arena, n: usize) {
    arena.mutate(|mc| {
        let kept = Vector::new(mc, n / 2, Value::NIL).unwrap();
        mc.set_root(1, Value::object(mc, kept));
        for i in 0..n {
            let node = Node::new(mc, i as u64, None).unwrap();
            if i % 2 == 0 {
                kept.items(mc).set(mc, i / 2, Value::object(mc, node));
            }
            let next = mc.root(0).downcast::<Holder>(mc);
            let holder = Holder::new(mc, Some(node), next).unwrap();
            mc.set_root(0, Value::object(mc, holder));
        }
    });
}

/// The values of the live weak targets, in chain order.
fn weak_targets(arena: &mut Arena) -> Vec<u64> {
    arena.mutate(|mc| {
        let mut out = Vec::new();
        let mut cur = mc.root(0).downcast::<Holder>(mc);
        while let Some(holder) = cur {
            if let Some(node) = holder.target(mc) {
                out.push(node.n(mc));
            }
            cur = holder.next(mc);
        }
        out
    })
}

#[test]
fn weak_references_clear_when_their_targets_die() {
    let expected: Vec<u64> = (0..1000).rev().filter(|i| i % 2 == 0).collect();
    let mut arena = Arena::new(REGION, 2);
    holders(&mut arena, 1000);
    arena.collect_minor();
    assert_eq!(weak_targets(&mut arena), expected);
    let mut arena = Arena::new(REGION, 2);
    holders(&mut arena, 1000);
    arena.collect();
    assert_eq!(weak_targets(&mut arena), expected);
    arena.set_evacuate_all(true);
    arena.collect();
    assert_eq!(weak_targets(&mut arena), expected);
}

/// The mutator rewires the list between slices of an evacuating cycle; nothing reachable is
/// lost and every moved reference is fixed.
#[test]
fn incremental_marking_keeps_what_the_mutator_moves_around() {
    let mut arena = Arena::new(REGION, 2);
    build(&mut arena, 20_000);
    arena.collect();
    arena.set_evacuate_all(true);
    arena.collect_slice(4096);
    assert_eq!(arena.phase(), Phase::Marking);
    let mut round = 0;
    while arena.phase() == Phase::Marking {
        // Move the list's tail half into root 1 and back, through a pair already marked.
        arena.mutate(|mc| {
            let mut cur = mc.root(0);
            for _ in 0..10_000 {
                cur = cur.downcast::<Pair>(mc).unwrap().cdr(mc);
            }
            let cut = cur.downcast::<Pair>(mc).unwrap();
            let tail = cut.cdr(mc);
            cut.set_cdr(mc, Value::NIL);
            let fresh = Pair::new(mc, Value::fixnum(-1).unwrap(), tail).unwrap();
            mc.set_root(1, Value::object(mc, fresh));
        });
        // A slice when idle would start another cycle.
        if arena.phase() == Phase::Marking {
            arena.collect_slice(4096);
        }
        arena.mutate(|mc| {
            let fresh = mc.root(1).downcast::<Pair>(mc).unwrap();
            let mut cur = mc.root(0);
            for _ in 0..10_000 {
                cur = cur.downcast::<Pair>(mc).unwrap().cdr(mc);
            }
            cur.downcast::<Pair>(mc).unwrap().set_cdr(mc, fresh.cdr(mc));
            mc.set_root(1, Value::NIL);
        });
        if arena.phase() == Phase::Marking {
            arena.collect_slice(4096);
        }
        round += 1;
    }
    assert!(round > 1, "the cycle should take several slices");
    assert_eq!(sum(&mut arena), (20_000 * 19_999 / 2, 20_000));
}

/// Steps pace collection on their own: minors as the nursery fills, majors as what survives
/// them grows. Root 0's list grows by one pair a step, and the rest is garbage.
#[test]
fn steps_collect_as_they_go() {
    let mut arena = Arena::new(64 << 20, 1);
    for step in 0..20_000 {
        arena.step(|mc| {
            for i in 0..100 {
                Pair::new(mc, Value::fixnum(i).unwrap(), Value::NIL).unwrap();
            }
            let kept = Pair::new(mc, Value::fixnum(step).unwrap(), mc.root(0)).unwrap();
            mc.set_root(0, Value::object(mc, kept));
        })
        .unwrap();
    }
    let (majors, minors) = arena.collections();
    assert!(majors > 0 && minors > 0, "{majors} majors, {minors} minors");
    assert_eq!(sum(&mut arena), (20_000 * 19_999 / 2, 20_000));
}

/// A heap of nothing but garbage needs no major collections.
#[test]
fn garbage_alone_needs_only_minors() {
    let mut arena = Arena::new(16 << 20, 1);
    for _ in 0..2000 {
        arena.step(|mc| {
            for i in 0..1000 {
                Pair::new(mc, Value::fixnum(i).unwrap(), Value::NIL).unwrap();
            }
        })
        .unwrap();
    }
    let (majors, minors) = arena.collections();
    assert!(majors <= 1 && minors > 10, "{majors} majors, {minors} minors");
}

/// Large objects reuse the pages of dead ones instead of taking fresh pages until the limit.
#[test]
fn large_objects_reuse_freed_pages() {
    let mut arena = Arena::new(16 << 20, 1);
    for _ in 0..200 {
        arena.step(|mc| Vector::new(mc, 128 << 10, Value::NIL).map(|_| ())).unwrap().unwrap();
    }
    assert!(arena.pages_bytes() <= 16 << 20);
}

/// Pages left mostly empty are compacted by ordinary collections, without evacuate-all.
#[test]
fn sparse_pages_are_compacted() {
    let mut arena = Arena::new(REGION, 1);
    arena.mutate(|mc| {
        for i in 0..400_000 {
            let pair = Pair::new(mc, Value::fixnum(i).unwrap(), mc.root(0)).unwrap();
            // One pair in forty is kept, so most lines stay empty but every page keeps some.
            if i % 40 == 0 {
                mc.set_root(0, Value::object(mc, pair));
            }
        }
    });
    arena.collect();
    let sparse = arena.occupied_bytes();
    arena.collect();
    let compacted = arena.occupied_bytes();
    assert!(compacted * 4 < sparse, "{sparse} -> {compacted}");
    let expected: i64 = (0..400_000).filter(|i| i % 40 == 0).sum();
    assert_eq!(sum(&mut arena), (expected, 10_000));
}

#[test]
fn host_slots_are_reused() {
    let mut arena = Arena::new(1 << 20, 1);
    for i in 0..100 {
        arena.mutate(|mc| {
            let host = mc.host(i).unwrap();
            let boxed = Counter::new(mc, Some(host)).unwrap();
            mc.set_root(0, Value::object(mc, boxed));
        });
        arena.collect();
    }
    assert!(arena.hosts() <= 2, "{} host slots", arena.hosts());
    arena.mutate(|mc| {
        let boxed = mc.root(0).downcast::<Counter>(mc).unwrap();
        assert_eq!(*boxed.count(mc).unwrap().get(mc).unwrap(), 99);
    });
}

/// Objects made while pages are still being swept lazily aren't swept away.
#[test]
fn allocation_during_lazy_sweeping_is_kept() {
    let mut arena = Arena::new(REGION, 2);
    build(&mut arena, 50_000);
    arena.mutate(|mc| {
        // Garbage, so the sweep has holes to hand out.
        for i in 0..200_000 {
            Pair::new(mc, Value::fixnum(i).unwrap(), Value::NIL).unwrap();
        }
    });
    while arena.phase() != Phase::Sweeping {
        arena.collect_slice(64 << 10);
    }
    let mut steps = 0;
    while arena.phase() == Phase::Sweeping {
        arena.mutate(|mc| {
            for i in 0..1000 {
                let pair = Pair::new(mc, Value::fixnum(i).unwrap(), mc.root(1)).unwrap();
                mc.set_root(1, Value::object(mc, pair));
            }
        });
        arena.collect_slice(16 << 10);
        steps += 1;
    }
    assert!(steps > 1, "the sweep should take several slices");
    assert_eq!(sum(&mut arena), (50_000 * 49_999 / 2, 50_000));
    let young = arena.mutate(|mc| {
        let (mut n, mut cur) = (0, mc.root(1));
        while let Some(pair) = cur.downcast::<Pair>(mc) {
            n += 1;
            cur = pair.cdr(mc);
        }
        n
    });
    assert_eq!(young, steps * 1000);
}

/// Free pages past a nursery's worth go back to the system, and come back when needed. A
/// backing that can't give memory back keeps counting them.
#[test]
fn free_pages_are_given_back() {
    let mut arena = Arena::new(64 << 20, 2);
    build(&mut arena, 10_000);
    arena.mutate(|mc| {
        // 32 MiB of vectors, dropped right after.
        for _ in 0..32 {
            let v = Vector::new(mc, 128 << 10, Value::NIL).unwrap();
            mc.set_root(1, Value::object(mc, v));
        }
        mc.set_root(1, Value::NIL);
    });
    arena.collect();
    let committed = arena.committed_bytes();
    if ragwort_gc_region::Region::releases() {
        assert!(committed < 12 << 20, "{committed} bytes still committed");
    } else {
        assert_eq!(committed, arena.pages_bytes());
    }
    assert_eq!(sum(&mut arena), (10_000 * 9_999 / 2, 10_000));
    // Allocating again reuses them, and what's written there reads back.
    arena.mutate(|mc| {
        let v = Vector::new(mc, 1 << 20, Value::fixnum(7).unwrap()).unwrap();
        mc.set_root(1, Value::object(mc, v));
    });
    arena.collect();
    arena.mutate(|mc| {
        let v = mc.root(1).downcast::<Vector>(mc).unwrap();
        assert_eq!(v.len(mc), 1 << 20);
        assert!((0..1 << 20).step_by(997).all(|i| v.items(mc).get(i) == Value::fixnum(7).unwrap()));
    });
    assert_eq!(sum(&mut arena), (10_000 * 9_999 / 2, 10_000));
}

fn fixnum<'gc>(n: usize) -> Value<'gc> {
    Value::fixnum(n as i64).unwrap()
}

fn pair<'gc>(mc: &Mutation<'gc>, car: Value<'gc>, cdr: Value<'gc>) -> Value<'gc> {
    Value::object(mc, Pair::new(mc, car, cdr).unwrap())
}

fn car<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> Value<'gc> {
    v.downcast::<Pair>(mc).unwrap().car(mc)
}

fn cdr<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> Value<'gc> {
    v.downcast::<Pair>(mc).unwrap().cdr(mc)
}

#[test]
fn flonums_round_trip_and_survive_moves() {
    let doubles = [
        0.0, -0.0, 1.0, -2.5, 0.1, 1e10, 1e-10, 1e76, -1e-76, 1e300, -1e-300, f64::MAX, f64::MIN_POSITIVE,
        5e-324, f64::INFINITY, f64::NEG_INFINITY, f64::NAN, -f64::NAN, f64::from_bits(0x7FF0_0000_0000_0001),
    ];
    let mut arena = Arena::new(REGION, 1);
    arena.mutate(|mc| {
        // A type of the test's own registered first mustn't pass for a boxed flonum.
        let other = Pair::new(mc, Value::FALSE, Value::FALSE).unwrap();
        assert!(!Value::object(mc, other).is_flonum());
        let mut list = Value::NIL;
        for &f in &doubles {
            let v = Value::flonum(mc, f).unwrap();
            assert!(v.is_flonum());
            assert_eq!(v.as_flonum(mc).unwrap().to_bits(), f.to_bits(), "{f}");
            list = pair(mc, v, list);
        }
        mc.set_root(0, list);
        assert!(Value::inline_flonum(1.5).is_some() && Value::inline_flonum(1e300).is_none());
        for v in [fixnum(3), Value::NIL, Value::FALSE, Value::BROKEN] {
            assert!(!v.is_flonum() && v.as_flonum(mc).is_none());
        }
    });
    let check = |arena: &mut Arena| {
        arena.mutate(|mc| {
            let mut cur = mc.root(0);
            for &f in doubles.iter().rev() {
                assert_eq!(car(mc, cur).as_flonum(mc).unwrap().to_bits(), f.to_bits(), "{f}");
                cur = cdr(mc, cur);
            }
        });
    };
    arena.collect_minor();
    check(&mut arena);
    arena.set_evacuate_all(true);
    arena.collect();
    check(&mut arena);
}

/// Field 0 is a value, fields 1 and 2 an ephemeron.
/// A table whose even keys are also held from root 1. Each value refers back to its key, which
/// mustn't keep the key alive.
fn half_held_table(arena: &mut Arena, n: usize) {
    arena.mutate(|mc| {
        let table = Table::new(mc, n).unwrap();
        for i in 0..n {
            let key = pair(mc, fixnum(i), Value::NIL);
            let value = pair(mc, fixnum(i), key);
            table.set_entry(mc, i, key, value);
            if i % 2 == 0 {
                mc.set_root(1, pair(mc, key, mc.root(1)));
            }
        }
        mc.set_root(0, Value::object(mc, table));
    });
}

fn check_half_held(arena: &mut Arena, n: usize) {
    arena.mutate(|mc| {
        let table = mc.root(0).downcast::<Table>(mc).unwrap();
        let mut held = mc.root(1);
        for i in (0..n).rev() {
            match table.entry(mc, i) {
                Some((key, value)) => {
                    assert_eq!(i % 2, 0, "entry {i} should have died");
                    assert_eq!(car(mc, key), fixnum(i));
                    assert_eq!((car(mc, value), cdr(mc, value)), (fixnum(i), key));
                    assert_eq!(car(mc, held), key);
                    held = cdr(mc, held);
                }
                None => assert_eq!(i % 2, 1, "entry {i} should have lived"),
            }
        }
    });
}

#[test]
fn ephemerons_hold_values_only_while_their_keys_live() {
    for kind in ["minor", "major", "evacuate"] {
        let mut arena = Arena::new(REGION, 2);
        half_held_table(&mut arena, 10_000);
        match kind {
            "minor" => arena.collect_minor(),
            "major" => arena.collect(),
            _ => {
                arena.set_evacuate_all(true);
                arena.collect();
            }
        }
        check_half_held(&mut arena, 10_000);
        arena.collect();
        check_half_held(&mut arena, 10_000);
    }
}

/// Each value is the next entry's key, and only the last entry's key is held, so marking takes
/// a pass over the table per link.
#[test]
fn ephemeron_chains_are_followed() {
    const LINKS: usize = 20;
    let mut arena = Arena::new(REGION, 2);
    arena.mutate(|mc| {
        let table = Table::new(mc, LINKS + 1).unwrap();
        let mut key = pair(mc, fixnum(LINKS), Value::NIL);
        mc.set_root(1, key);
        for i in (0..LINKS).rev() {
            let value = pair(mc, fixnum(i), Value::NIL);
            table.set_entry(mc, i, key, value);
            key = value;
        }
        table.set_entry(mc, LINKS, pair(mc, fixnum(99), Value::NIL), fixnum(1));
        mc.set_root(0, Value::object(mc, table));
    });
    arena.set_evacuate_all(true);
    arena.collect();
    arena.mutate(|mc| {
        let table = mc.root(0).downcast::<Table>(mc).unwrap();
        let mut key = mc.root(1);
        for i in (0..LINKS).rev() {
            let (k, value) = table.entry(mc, i).expect("a link died");
            assert_eq!((k, car(mc, value)), (key, fixnum(i)));
            key = value;
        }
        assert_eq!(table.entry(mc, LINKS), None);
    });
}

/// A value taken from an object not yet traced and stored in a table already traced, with
/// nothing else holding it, is found at the end of marking, and moved.
#[test]
fn ephemeron_values_stored_while_marking_are_kept() {
    let mut arena = Arena::new(REGION, 4);
    arena.mutate(|mc| {
        // Roots are traced last first: the table, the key, then the chain, deep enough that
        // its end is untraced when the value is taken from it.
        let mut chain = pair(mc, pair(mc, fixnum(777), Value::NIL), Value::NIL);
        for i in 0..10_000 {
            chain = pair(mc, fixnum(i), chain);
        }
        mc.set_root(1, chain);
        mc.set_root(2, pair(mc, fixnum(1), Value::NIL));
        mc.set_root(3, Value::object(mc, Table::new(mc, 1).unwrap()));
    });
    arena.set_evacuate_all(true);
    arena.collect_slice(1024);
    assert_eq!(arena.phase(), Phase::Marking);
    arena.mutate(|mc| {
        let mut end = mc.root(1);
        while cdr(mc, end) != Value::NIL {
            end = cdr(mc, end);
        }
        let table = mc.root(3).downcast::<Table>(mc).unwrap();
        table.set_entry(mc, 0, mc.root(2), car(mc, end));
        end.downcast::<Pair>(mc).unwrap().set_car(mc, Value::NIL);
    });
    while arena.phase() != Phase::Idle {
        arena.collect_slice(1024);
    }
    arena.mutate(|mc| {
        // Fills the freed memory, so a value wrongly freed reads back as something else.
        for i in 0..300_000 {
            pair(mc, fixnum(i), Value::NIL);
        }
        let table = mc.root(3).downcast::<Table>(mc).unwrap();
        let (key, value) = table.entry(mc, 0).unwrap();
        assert_eq!((key, car(mc, value)), (mc.root(2), fixnum(777)));
    });
}

/// An old table sees young keys and values through its dirty cards. Old keys die only in a
/// major collection.
#[test]
fn old_ephemerons_hold_young_values() {
    let mut arena = Arena::new(REGION, 2);
    arena.mutate(|mc| {
        let cached = Cached::new(mc, fixnum(5), (Value::BROKEN, Value::BROKEN)).unwrap();
        mc.set_root(0, Value::object(mc, cached));
    });
    arena.collect();
    arena.mutate(|mc| {
        let key = pair(mc, fixnum(1), Value::NIL);
        let value = pair(mc, fixnum(2), key);
        mc.set_root(1, key);
        mc.root(0).downcast::<Cached>(mc).unwrap().set_cache(mc, (key, value));
    });
    arena.collect_minor();
    let entry = |arena: &mut Arena| {
        arena.mutate(|mc| {
            let cached = mc.root(0).downcast::<Cached>(mc).unwrap();
            assert_eq!(cached.n(mc), fixnum(5));
            cached.cache(mc).map(|(key, value)| (car(mc, key).as_fixnum(), car(mc, value).as_fixnum()))
        })
    };
    assert_eq!(entry(&mut arena), Some((Some(1), Some(2))));
    arena.mutate(|mc| mc.set_root(1, Value::NIL));
    arena.collect_minor();
    assert_eq!(entry(&mut arena), Some((Some(1), Some(2))));
    arena.collect();
    assert_eq!(entry(&mut arena), None);
}

/// Keys that aren't objects never die.
#[test]
fn immediate_keys_keep_their_values() {
    let mut arena = Arena::new(REGION, 1);
    arena.mutate(|mc| {
        let table = Table::new(mc, 2).unwrap();
        table.set_entry(mc, 0, fixnum(1), pair(mc, fixnum(10), Value::NIL));
        table.set_entry(mc, 1, Value::NIL, pair(mc, fixnum(20), Value::NIL));
        mc.set_root(0, Value::object(mc, table));
    });
    arena.collect_minor();
    arena.collect();
    arena.mutate(|mc| {
        let table = mc.root(0).downcast::<Table>(mc).unwrap();
        assert_eq!(table.entry(mc, 0).map(|(k, v)| (k, car(mc, v))), Some((fixnum(1), fixnum(10))));
        assert_eq!(table.entry(mc, 1).map(|(k, v)| (k, car(mc, v))), Some((Value::NIL, fixnum(20))));
    });
}

/// Holds a host word but forgets to declare it: the wrong description the docs allow.
struct Forgetful;
impl Object for Forgetful {
    const DESC: Desc = Desc::of::<Forgetful>(1);
}

/// Host references are capabilities: a stale one must never read the value that reused its
/// slot.
#[test]
fn stale_host_refs_never_read_the_next_value() {
    let mut arena = Arena::new(1 << 20, 1);
    arena.mutate(|mc| {
        let user = mc.host(String::from("user")).unwrap();
        let forgetful = mc.alloc::<Forgetful, 1>([user.to_word()]).unwrap();
        mc.set_root(0, Value::object(mc, forgetful));
    });
    // Nothing declares the host, so it dies.
    arena.collect();
    arena.mutate(|mc| {
        let admin = mc.host(String::from("admin")).unwrap();
        let forgetful = mc.root(0).downcast::<Forgetful>(mc).unwrap();
        let stale = HostRef::<String> { id: 0, generation: 0, _marker: PhantomData };
        assert_eq!(stale.to_word(), forgetful.word(mc, 0));
        assert_eq!(admin.id, stale.id, "the slot should have been reused");
        assert!(stale.get(mc).is_none());
        assert_eq!(*admin.get(mc).unwrap(), "admin");
    });
}

/// Index 0 means none, so nothing may be allocated there, even a large first object.
#[test]
fn large_first_allocation_is_not_none() {
    let mut arena = Arena::new(REGION, 1);
    arena.mutate(|mc| {
        let big = Vector::new(mc, 3000, Value::NIL).unwrap();
        assert_ne!(big.to_word(), 0);
        let node = Node::new(mc, 0, None).unwrap();
        node.set_member(mc, 1, Some(big));
        assert!(node.member::<Vector>(mc, 1) == Some(big));
        mc.set_root(0, Value::object(mc, node));
    });
    arena.collect();
    arena.mutate(|mc| {
        let node = mc.root(0).downcast::<Node>(mc).unwrap();
        assert_eq!(node.member::<Vector>(mc, 1).unwrap().len(mc), 3000);
    });
}

#[test]
#[should_panic(expected = "field 2 of 2")]
fn fields_past_the_declared_ones_panic() {
    let mut arena = Arena::new(1 << 20, 1);
    arena.mutate(|mc| {
        let pair = mc.alloc::<Pair, 2>([0, 0]).unwrap();
        pair.set_value(mc, 2, Value::NIL);
    });
}

/// Sets a flag when dropped, and panics if asked to.
struct Flag(Rc<Cell<bool>>, bool);
impl Drop for Flag {
    fn drop(&mut self) {
        self.0.set(true);
        assert!(!self.1, "host destructor panicked");
    }
}

/// Dropped stacks are pruned, and give back their charge, once traced.
#[test]
fn dropped_stacks_are_pruned() {
    let mut arena = Arena::new(REGION, 1);
    arena.mutate(|mc| {
        let segments = Vector::new(mc, 200, Value::NIL).unwrap();
        for i in 0..200 {
            segments.items(mc).set(mc, i, Value::object(mc, Segment::new(mc, WINDOW).unwrap()));
        }
        mc.set_root(0, Value::object(mc, segments));
    });
    arena.collect();
    let used = arena.used();
    arena.mutate(|mc| {
        let segments = mc.root(0).downcast::<Vector>(mc).unwrap();
        for i in 0..200 {
            let stack = mc.stack(segments.items(mc).get(i).downcast::<Segment>(mc).unwrap()).unwrap();
            stack.frame(mc, 0).unwrap().set(0, Value::TRUE);
        }
    });
    assert_eq!(arena.used(), used + 200 * STACK_COST);
    arena.collect();
    assert!(arena.meta.stacks.borrow().is_empty());
    // The table of records keeps its capacity.
    assert!(arena.used() <= used + 256 * 8, "{} bytes more", arena.used() - used);
}

/// Many stacks, moved together.
#[test]
fn many_stacks() {
    let mut arena = Arena::new(REGION, 1);
    let stacks = arena.mutate(|mc| {
        (0..1000i64)
            .map(|i| {
                let stack = mc.stack(Segment::new(mc, WINDOW).unwrap()).unwrap();
                stack.frame(mc, 0).unwrap().set(0, Value::fixnum(i).unwrap());
                stack
            })
            .collect::<Vec<_>>()
    });
    arena.set_evacuate_all(true);
    arena.collect();
    arena.mutate(|mc| {
        for (i, stack) in stacks.iter().enumerate() {
            assert_eq!(stack.frame(mc, 0).unwrap().get(0).as_fixnum(), Some(i as i64));
        }
    });
}

/// A host destructor that panics does so after the collection is done, so the arena is
/// still usable.
#[test]
fn host_destructors_run_after_the_collector() {
    let mut arena = Arena::new(1 << 20, 1);
    let dropped = Rc::new(Cell::new(false));
    build(&mut arena, 1000);
    arena.mutate(|mc| {
        mc.host(Flag(dropped.clone(), true)).unwrap();
    });
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| arena.collect()));
    assert!(result.is_err() && dropped.get());
    assert_ne!(arena.phase(), Phase::Marking);
    arena.collect();
    assert_eq!(sum(&mut arena), (1000 * 999 / 2, 1000));
}

/// An arena's tables grow with its limit and its types, not to the most any arena could use.
#[test]
fn small_arenas_are_small() {
    let mut arena = Arena::new(1 << 20, 1);
    build(&mut arena, 100);
    assert!(arena.meta.pages.len() <= 2 * (1 << 20) / (PAGE * 8) + 2);
    assert_eq!(arena.meta.descs.chunks.iter().filter(|c| c.get().is_some()).count(), 0);
}

/// A minor collection scans only the dirty cards of an old vector, wherever in it they are,
/// and finds small objects sharing the last page of a large one, even once it has died.
#[test]
fn dirty_cards_of_large_objects() {
    const LEN: usize = 300_000;
    let mut arena = Arena::new(REGION, 2);
    arena.mutate(|mc| {
        let vector = Vector::new(mc, LEN, Value::NIL).unwrap();
        mc.set_root(0, Value::object(mc, vector));
        // Lands in the free lines after the vector's end.
        let tail = pair(mc, Value::NIL, Value::NIL);
        mc.set_root(1, tail);
    });
    arena.collect();
    let stores = [0, 1, 62, 63, 64, 2046, 2047, 150_000, LEN - 1];
    arena.mutate(|mc| {
        let vector = mc.root(0).downcast::<Vector>(mc).unwrap();
        for &i in &stores {
            // Garbage between them, so no two share a line and survive together.
            Vector::new(mc, 32, Value::NIL).unwrap();
            vector.items(mc).set(mc, i, pair(mc, fixnum(i), Value::NIL));
        }
        let tail = mc.root(1).downcast::<Pair>(mc).unwrap();
        tail.set_car(mc, pair(mc, fixnum(1_000_001), Value::NIL));
    });
    arena.collect_minor();
    arena.mutate(|mc| {
        for i in 0..300_000 {
            pair(mc, fixnum(i), Value::NIL);
        }
        let vector = mc.root(0).downcast::<Vector>(mc).unwrap();
        for &i in &stores {
            assert_eq!(car(mc, vector.items(mc).get(i)), fixnum(i));
        }
        assert_eq!(car(mc, car(mc, mc.root(1))), fixnum(1_000_001));
        // The vector dies; the tail pair, on its last page, lives on.
        mc.set_root(0, Value::NIL);
    });
    arena.collect();
    arena.mutate(|mc| {
        let tail = mc.root(1).downcast::<Pair>(mc).unwrap();
        tail.set_cdr(mc, pair(mc, fixnum(1_000_002), Value::NIL));
    });
    arena.collect_minor();
    arena.mutate(|mc| {
        for i in 0..300_000 {
            pair(mc, fixnum(i), Value::NIL);
        }
        let tail = mc.root(1).downcast::<Pair>(mc).unwrap();
        assert_eq!(car(mc, tail.cdr(mc)), fixnum(1_000_002));
    });
}

