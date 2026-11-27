use std::rc::Rc;

use super::*;

objects! {
    kind Kind;
    struct Pair { car: Value, cdr: Value }
    struct Node { n: u64, next: Member<Node> }
    struct Vector {} items Value
    struct Boxed { data: Host<String> }
    struct Counter { count: Host<i32> }
    /// Holds a weak reference to a node, and a link to the next holder.
    struct Holder { target: Weak<Node>, next: Member<Holder> }
    struct Table {} items Ephemeron
    /// Field 0 is a value. Fields 1 and 2 hold an ephemeron.
    struct Cached { n: Value, cache: Ephemeron }
}

/// Builds a list of the fixnums `0..n` in root 0, with the last number first.
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
                Pair::new(mc, Value::fixnum(i).unwrap(), Value::NULL).unwrap();
            }
        })
        .unwrap();
    }
    build(&mut arena, 10);
    assert_eq!(sum(&mut arena), (45, 10));
}

/// A young object that only an old object refers to survives a minor collection. Nothing keeps it alive except the card that the store
/// marked dirty.
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
        let vector = Vector::new(mc, 300_000, Value::NULL).unwrap();
        let pair = Pair::new(mc, Value::fixnum(5).unwrap(), Value::NULL).unwrap();
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
    assert_eq!(arena.hosts(), 1, "the dead value's slot is dropped");
}

/// A forged reference reads as some other object or as no object. It never reads out of bounds.
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

/// Builds a chain of `n` holders in root 0. Each holder has a weak reference to a node. Every second node is also held
/// strongly by the vector in root 1.
fn holders(arena: &mut Arena, n: usize) {
    arena.mutate(|mc| {
        let kept = Vector::new(mc, n / 2, Value::NULL).unwrap();
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

/// Returns the numbers of the live weak targets, in chain order.
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

/// The mutator relinks the list between the slices of an evacuating cycle. No reachable object is
/// lost, and every reference to a moved object is updated.
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
        // Move the second half of the list into root 1 and back, by way of a pair that is already marked.
        arena.mutate(|mc| {
            let mut cur = mc.root(0);
            for _ in 0..10_000 {
                cur = cur.downcast::<Pair>(mc).unwrap().cdr(mc);
            }
            let cut = cur.downcast::<Pair>(mc).unwrap();
            let tail = cut.cdr(mc);
            cut.set_cdr(mc, Value::NULL);
            let fresh = Pair::new(mc, Value::fixnum(-1).unwrap(), tail).unwrap();
            mc.set_root(1, Value::object(mc, fresh));
        });
        // A slice in the idle phase would start another cycle, so only a cycle that is still marking gets another slice.
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
            mc.set_root(1, Value::NULL);
        });
        if arena.phase() == Phase::Marking {
            arena.collect_slice(4096);
        }
        round += 1;
    }
    assert!(round > 1, "the cycle should take several slices");
    assert_eq!(sum(&mut arena), (20_000 * 19_999 / 2, 20_000));
}

/// Steps pace collection by themselves: minor collections as the nursery fills, and major cycles as the surviving
/// data grows. The list in root 0 grows by one pair per step. Everything else is garbage.
#[test]
fn steps_collect_as_they_go() {
    let mut arena = Arena::new(64 << 20, 1);
    for step in 0..20_000 {
        arena.step(|mc| {
            for i in 0..100 {
                Pair::new(mc, Value::fixnum(i).unwrap(), Value::NULL).unwrap();
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

/// A heap that holds only garbage needs no major collections.
#[test]
fn garbage_alone_needs_only_minors() {
    let mut arena = Arena::new(16 << 20, 1);
    for _ in 0..2000 {
        arena.step(|mc| {
            for i in 0..1000 {
                Pair::new(mc, Value::fixnum(i).unwrap(), Value::NULL).unwrap();
            }
        })
        .unwrap();
    }
    let (majors, minors) = arena.collections();
    assert!(majors <= 1 && minors > 10, "{majors} majors, {minors} minors");
}

/// Large objects reuse the pages of dead large objects, instead of taking fresh pages until the arena reaches its limit.
#[test]
fn large_objects_reuse_freed_pages() {
    let mut arena = Arena::new(16 << 20, 1);
    for _ in 0..200 {
        arena.step(|mc| Vector::new(mc, 128 << 10, Value::NULL).map(|_| ())).unwrap().unwrap();
    }
    assert!(arena.pages_bytes() <= 16 << 20);
}

/// Ordinary collections compact the pages that are mostly empty, without `set_evacuate_all`.
#[test]
fn sparse_pages_are_compacted() {
    let mut arena = Arena::new(REGION, 1);
    arena.mutate(|mc| {
        for i in 0..400_000 {
            let pair = Pair::new(mc, Value::fixnum(i).unwrap(), mc.root(0)).unwrap();
            // One pair in forty is kept. So most lines end up empty, but every page keeps some live pairs.
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

/// Objects allocated while the lazy sweep is still running are not freed by the sweep.
#[test]
fn allocation_during_lazy_sweeping_is_kept() {
    let mut arena = Arena::new(REGION, 2);
    build(&mut arena, 50_000);
    arena.mutate(|mc| {
        // Allocate garbage, so that the sweep frees holes for the allocator to use.
        for i in 0..200_000 {
            Pair::new(mc, Value::fixnum(i).unwrap(), Value::NULL).unwrap();
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

/// Free pages beyond one nursery's worth are released to the system, and are committed again when needed. With a
/// backing that cannot release memory, the pages stay counted as committed.
#[test]
fn free_pages_are_given_back() {
    let mut arena = Arena::new(REGION, 2);
    build(&mut arena, 10_000);
    arena.mutate(|mc| {
        // Fills half the region with 1 MiB vectors, each dropped as soon as the next one replaces it.
        for _ in 0..REGION >> 21 {
            let v = Vector::new(mc, 128 << 10, Value::NULL).unwrap();
            mc.set_root(1, Value::object(mc, v));
        }
        mc.set_root(1, Value::NULL);
    });
    arena.collect();
    let committed = arena.committed_bytes();
    if ragwort_gc_region::Region::releases() {
        assert!(committed < REGION / 16 * 3, "{committed} bytes still committed");
    } else {
        assert_eq!(committed, arena.pages_bytes());
    }
    assert_eq!(sum(&mut arena), (10_000 * 9_999 / 2, 10_000));
    // A new allocation reuses the released pages, and the data written there reads back.
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
        // The first type that the test registers must not be mistaken for a boxed flonum.
        let other = Pair::new(mc, Value::FALSE, Value::FALSE).unwrap();
        assert!(!Value::object(mc, other).is_flonum());
        let mut list = Value::NULL;
        for &f in &doubles {
            let v = Value::flonum(mc, f).unwrap();
            assert!(v.is_flonum());
            assert_eq!(v.as_flonum(mc).unwrap().to_bits(), f.to_bits(), "{f}");
            list = pair(mc, v, list);
        }
        mc.set_root(0, list);
        assert!(Value::inline_flonum(1.5).is_some() && Value::inline_flonum(1e300).is_none());
        for v in [fixnum(3), Value::NULL, Value::FALSE, Value::BROKEN] {
            assert!(!v.is_flonum() && v.as_flonum(mc).is_none());
        }
        for v in [fixnum(7), Value::inline_flonum(1.5).unwrap(), Value::NULL, Value::TRUE, Value::VOID] {
            assert_eq!(v.immediate().map(Immediate::value), Some(v));
        }
        assert_eq!(Value::flonum(mc, 1e300).unwrap().immediate(), None);
        assert_eq!(Value::object(mc, other).immediate(), None);
        // Three values are false, and the three are distinct. No other value is false: not the empty list, not void, not zero.
        let falses = [Value::FALSE, Value::NIL, Value::NONE];
        for (index, &value) in falses.iter().enumerate() {
            assert!(value.is_false() && !value.is_true() && value.immediate().map(Immediate::value) == Some(value));
            assert!(falses.iter().skip(index + 1).all(|&later| later != value));
        }
        let trues = [Value::TRUE, Value::NULL, Value::VOID, Value::UNDEFINED, Value::UNSUPPLIED, Value::VALUES, Value::BROKEN];
        for value in trues.into_iter().chain([fixnum(0), Value::char('\0'), Value::inline_flonum(0.0).unwrap(), Value::object(mc, other)]) {
            assert!(value.is_true() && !value.is_false() && !falses.contains(&value), "{value:?}");
        }
    });
    fn check(arena: &mut Arena, doubles: &[f64]) {
        arena.mutate(|mc| {
            let mut cur = mc.root(0);
            for &f in doubles.iter().rev() {
                assert_eq!(car(mc, cur).as_flonum(mc).unwrap().to_bits(), f.to_bits(), "{f}");
                cur = cdr(mc, cur);
            }
        });
    }
    arena.collect_minor();
    check(&mut arena, &doubles);
    arena.set_evacuate_all(true);
    arena.collect();
    check(&mut arena, &doubles);
}

/// Builds an ephemeron table of `n` entries in root 0. The keys of the even entries are also held from root 1. Each value refers back to its key, and
/// that reference must not keep the key alive.
fn half_held_table(arena: &mut Arena, n: usize) {
    arena.mutate(|mc| {
        let table = Table::new(mc, n).unwrap();
        for i in 0..n {
            let key = pair(mc, fixnum(i), Value::NULL);
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

/// The value of each entry is the key of the entry before it, and a root holds only the key of the last entry in the chain. So marking takes
/// one pass over the table per link.
#[test]
fn ephemeron_chains_are_followed() {
    const LINKS: usize = 20;
    let mut arena = Arena::new(REGION, 2);
    arena.mutate(|mc| {
        let table = Table::new(mc, LINKS + 1).unwrap();
        let mut key = pair(mc, fixnum(LINKS), Value::NULL);
        mc.set_root(1, key);
        for i in (0..LINKS).rev() {
            let value = pair(mc, fixnum(i), Value::NULL);
            table.set_entry(mc, i, key, value);
            key = value;
        }
        table.set_entry(mc, LINKS, pair(mc, fixnum(99), Value::NULL), fixnum(1));
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

/// A value is taken out of an object that is not yet traced, and is stored as an ephemeron value in a table that is already traced.
/// Nothing else holds the value. The end of marking must still find the value, and evacuation must move it.
#[test]
fn ephemeron_values_stored_while_marking_are_kept() {
    let mut arena = Arena::new(REGION, 4);
    arena.mutate(|mc| {
        // Roots are traced from the last to the first: the table, the key, then the chain. The chain is long enough that
        // its end is still untraced when the value is taken from it.
        let mut chain = pair(mc, pair(mc, fixnum(777), Value::NULL), Value::NULL);
        for i in 0..10_000 {
            chain = pair(mc, fixnum(i), chain);
        }
        mc.set_root(1, chain);
        mc.set_root(2, pair(mc, fixnum(1), Value::NULL));
        mc.set_root(3, Value::object(mc, Table::new(mc, 1).unwrap()));
    });
    arena.set_evacuate_all(true);
    arena.collect_slice(1024);
    assert_eq!(arena.phase(), Phase::Marking);
    arena.mutate(|mc| {
        let mut end = mc.root(1);
        while cdr(mc, end) != Value::NULL {
            end = cdr(mc, end);
        }
        let table = mc.root(3).downcast::<Table>(mc).unwrap();
        table.set_entry(mc, 0, mc.root(2), car(mc, end));
        end.downcast::<Pair>(mc).unwrap().set_car(mc, Value::NULL);
    });
    while arena.phase() != Phase::Idle {
        arena.collect_slice(1024);
    }
    arena.mutate(|mc| {
        // Fill the freed memory, so that a value that was wrongly freed reads back as something else.
        for i in 0..300_000 {
            pair(mc, fixnum(i), Value::NULL);
        }
        let table = mc.root(3).downcast::<Table>(mc).unwrap();
        let (key, value) = table.entry(mc, 0).unwrap();
        assert_eq!((key, car(mc, value)), (mc.root(2), fixnum(777)));
    });
}

/// An old object with an ephemeron finds a young key and value through its dirty cards. An old key dies only in a
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
        let key = pair(mc, fixnum(1), Value::NULL);
        let value = pair(mc, fixnum(2), key);
        mc.set_root(1, key);
        mc.root(0).downcast::<Cached>(mc).unwrap().set_cache(mc, (key, value));
    });
    arena.collect_minor();
    fn entry(arena: &mut Arena) -> Option<(Option<i64>, Option<i64>)> {
        arena.mutate(|mc| {
            let cached = mc.root(0).downcast::<Cached>(mc).unwrap();
            assert_eq!(cached.n(mc), fixnum(5));
            cached.cache(mc).map(|(key, value)| (car(mc, key).as_fixnum(), car(mc, value).as_fixnum()))
        })
    }
    assert_eq!(entry(&mut arena), Some((Some(1), Some(2))));
    arena.mutate(|mc| mc.set_root(1, Value::NULL));
    arena.collect_minor();
    assert_eq!(entry(&mut arena), Some((Some(1), Some(2))));
    arena.collect();
    assert_eq!(entry(&mut arena), None);
}

/// A key that is not an object never dies.
#[test]
fn immediate_keys_keep_their_values() {
    let mut arena = Arena::new(REGION, 1);
    arena.mutate(|mc| {
        let table = Table::new(mc, 2).unwrap();
        table.set_entry(mc, 0, fixnum(1), pair(mc, fixnum(10), Value::NULL));
        table.set_entry(mc, 1, Value::NULL, pair(mc, fixnum(20), Value::NULL));
        mc.set_root(0, Value::object(mc, table));
    });
    arena.collect_minor();
    arena.collect();
    arena.mutate(|mc| {
        let table = mc.root(0).downcast::<Table>(mc).unwrap();
        assert_eq!(table.entry(mc, 0).map(|(k, v)| (k, car(mc, v))), Some((fixnum(1), fixnum(10))));
        assert_eq!(table.entry(mc, 1).map(|(k, v)| (k, car(mc, v))), Some((Value::NULL, fixnum(20))));
    });
}

/// Holds a host word in a field that its descriptor does not declare as a host field. The module docs allow this kind of wrong descriptor.
struct Forgetful;
impl Object for Forgetful {
    const DESC: Desc = Desc::of::<Forgetful>(1);
}

/// Host references are capabilities. A stale reference must never read the value that reused its
/// slot.
#[test]
fn stale_host_refs_never_read_the_next_value() {
    let mut arena = Arena::new(1 << 20, 1);
    arena.mutate(|mc| {
        let user = mc.host(String::from("user")).unwrap();
        let forgetful = mc.alloc::<Forgetful, 1>([user.to_word()]).unwrap();
        mc.set_root(0, Value::object(mc, forgetful));
    });
    // No descriptor declares the host field, so the host value is not marked and dies.
    arena.collect();
    arena.mutate(|mc| {
        let admin = mc.host(String::from("admin")).unwrap();
        let forgetful = mc.root(0).downcast::<Forgetful>(mc).unwrap();
        let stale = HostRef::<String> { id: 0, generation: 0, _marker: PhantomData };
        assert_eq!(stale.to_word(), forgetful.word(mc, 0));
        assert_eq!(admin.id, stale.id, "the slot should have been reused");
        assert!(stale.get(mc).is_none());
        assert!(!stale.erase().is::<String>(mc) && stale.erase().downcast_ref::<String>(mc).is_none());
        assert_eq!(*admin.get(mc).unwrap(), "admin");
    });
}

/// Index 0 means no object, so no object may be allocated there, not even a large first object.
#[test]
fn large_first_allocation_is_not_none() {
    let mut arena = Arena::new(REGION, 1);
    arena.mutate(|mc| {
        let big = Vector::new(mc, 3000, Value::NULL).unwrap();
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
        pair.set_value(mc, 2, Value::NULL);
    });
}

/// Sets a flag when dropped. Its destructor also panics if the second field is true.
struct Flag(Rc<Cell<bool>>, bool);
impl Drop for Flag {
    fn drop(&mut self) {
        self.0.set(true);
        assert!(!self.1, "host destructor panicked");
    }
}

/// The record of a dropped stack is removed, and its charge is refunded, once a collection has traced it.
#[test]
fn dropped_stacks_are_pruned() {
    let mut arena = Arena::new(REGION, 1);
    arena.mutate(|mc| {
        let segments = Vector::new(mc, 200, Value::NULL).unwrap();
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
    // The vector of stack records keeps its capacity, which stays charged.
    assert!(arena.used() <= used + 256 * 8, "{} bytes more", arena.used() - used);
}

/// One collection traces many stacks and evacuates their segments.
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

/// A panic in the destructor of a host value happens after the collection has finished, so the arena is
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

/// The tables of an arena are sized by its limit and by the types it uses, not by the maximum that any arena could need.
#[test]
fn small_arenas_are_small() {
    let mut arena = Arena::new(1 << 20, 1);
    build(&mut arena, 100);
    assert!(arena.meta.page_count <= 2 * (1 << 20) / (PAGE * 8) + 2);
    assert_eq!(arena.meta.descs.chunks.iter().filter(|c| c.get().is_some()).count(), 0);
}

/// The record of a page is part of the region. It is all zero until the page is handed out, so the system has not committed it.
#[test]
fn page_records_are_written_as_pages_are_used() {
    fn written(arena: &mut Arena) -> usize {
        let heap = arena.heap();
        (0..PAGES).filter(|&page| heap.page(page).0.iter().any(|word| word.get() != 0)).count()
    }
    let mut arena = Arena::new(64 << 20, 1);
    assert_eq!(written(&mut arena), 0);
    build(&mut arena, 100);
    assert_eq!(written(&mut arena), 1);
    // 100,000 nodes need about 150 pages. No record past the pages handed out is written.
    build(&mut arena, 100_000);
    arena.collect();
    let used = arena.meta.used.get();
    assert!(used > 100 && written(&mut arena) <= used, "{} records written for {used} pages", written(&mut arena));
    assert_eq!(sum(&mut arena), (100_000 * 99_999 / 2 + 100 * 99 / 2, 100_100));
}

/// A minor collection scans only the dirty cards of an old vector, wherever the cards are in the vector.
/// It also finds small objects that share the last page of a large object, even after the large object has died.
#[test]
fn dirty_cards_of_large_objects() {
    const LEN: usize = 300_000;
    let mut arena = Arena::new(REGION, 2);
    arena.mutate(|mc| {
        let vector = Vector::new(mc, LEN, Value::NULL).unwrap();
        mc.set_root(0, Value::object(mc, vector));
        // This pair is allocated in the free lines after the end of the vector.
        let tail = pair(mc, Value::NULL, Value::NULL);
        mc.set_root(1, tail);
    });
    arena.collect();
    let stores = [0, 1, 62, 63, 64, 2046, 2047, 150_000, LEN - 1];
    arena.mutate(|mc| {
        let vector = mc.root(0).downcast::<Vector>(mc).unwrap();
        for &i in &stores {
            // Allocate garbage between the stored pairs, so that no two of them share a line and survive together.
            Vector::new(mc, 32, Value::NULL).unwrap();
            vector.items(mc).set(mc, i, pair(mc, fixnum(i), Value::NULL));
        }
        let tail = mc.root(1).downcast::<Pair>(mc).unwrap();
        tail.set_car(mc, pair(mc, fixnum(1_000_001), Value::NULL));
    });
    arena.collect_minor();
    arena.mutate(|mc| {
        for i in 0..300_000 {
            pair(mc, fixnum(i), Value::NULL);
        }
        let vector = mc.root(0).downcast::<Vector>(mc).unwrap();
        for &i in &stores {
            assert_eq!(car(mc, vector.items(mc).get(i)), fixnum(i));
        }
        assert_eq!(car(mc, car(mc, mc.root(1))), fixnum(1_000_001));
        // The vector dies. The tail pair, which is on the vector's last page, stays alive.
        mc.set_root(0, Value::NULL);
    });
    arena.collect();
    arena.mutate(|mc| {
        let tail = mc.root(1).downcast::<Pair>(mc).unwrap();
        tail.set_cdr(mc, pair(mc, fixnum(1_000_002), Value::NULL));
    });
    arena.collect_minor();
    arena.mutate(|mc| {
        for i in 0..300_000 {
            pair(mc, fixnum(i), Value::NULL);
        }
        let tail = mc.root(1).downcast::<Pair>(mc).unwrap();
        assert_eq!(car(mc, tail.cdr(mc)), fixnum(1_000_002));
    });
}


#[test]
fn characters_are_constants_apart_from_the_others() {
    for c in ['\0', 'a', 'λ', '\u{10FFFF}'] {
        let v = Value::char(c);
        assert_eq!(v.as_char(), Some(c));
        assert!(v.as_fixnum().is_none());
    }
    for v in [Value::TRUE, Value::FALSE, Value::NULL, Value::VOID, Value::fixnum(97).unwrap()] {
        assert_eq!(v.as_char(), None);
    }
    assert_ne!(Value::char('a'), Value::char('b'));
}

/// A collection keeps a nursery's worth of free pages. `trim` releases them too, and the arena works as before afterwards.
#[test]
fn trim_releases_the_free_pages_that_a_collection_keeps() {
    if !ragwort_gc_region::Region::releases() {
        return;
    }
    let mut arena = Arena::new(64 << 20, 1);
    build(&mut arena, 1000);
    // About 5 MB of garbage, in steps, so that minor collections run.
    for _ in 0..200 {
        arena
            .step(|mc| {
                for i in 0..1000 {
                    Pair::new(mc, Value::fixnum(i).unwrap(), Value::NULL).unwrap();
                }
            })
            .unwrap();
    }
    arena.collect();
    let kept = arena.committed_bytes();
    assert!(kept >= arena.nursery(), "a collection keeps a nursery's worth of free pages: {kept} bytes committed");
    arena.trim();
    // What is left holds the 1000 pairs of 24 bytes each. Pages are 16 KB.
    assert!(arena.committed_bytes() <= 4 * PAGE * 8, "{} bytes committed after the trim", arena.committed_bytes());
    assert!(arena.used() < kept / 4, "{} bytes charged after the trim", arena.used());
    assert_eq!(sum(&mut arena), (1000 * 999 / 2, 1000));
    // The arena allocates and collects as before.
    build(&mut arena, 100_000);
    arena.collect();
    arena.trim();
    assert_eq!(sum(&mut arena), (100_000 * 99_999 / 2 + 1000 * 999 / 2, 101_000));
    // A trim during a major cycle does nothing.
    arena.collect_slice(1);
    let before = arena.committed_bytes();
    arena.trim();
    assert_eq!(arena.committed_bytes(), before);
}

/// The nursery is as large as the heap that the last collection left, within its bounds. So an arena that keeps little holds little,
/// whatever its limit.
#[test]
fn the_nursery_follows_the_size_of_the_heap() {
    let mut arena = Arena::new(64 << 20, 1);
    assert_eq!(arena.nursery(), MIN_NURSERY);
    build(&mut arena, 1000);
    arena.collect();
    assert_eq!(arena.nursery(), MIN_NURSERY);
    // 50,000 pairs of 24 bytes are 1.2 MB.
    build(&mut arena, 50_000);
    arena.collect();
    assert!((1 << 20..2 << 20).contains(&arena.nursery()), "a nursery of {} bytes", arena.nursery());
    // A large heap has the largest nursery, as every arena had before.
    build(&mut arena, 500_000);
    arena.collect();
    assert_eq!(arena.nursery(), 4 << 20);
    // The heap shrinks, and the nursery with it.
    arena.mutate(|mc| mc.set_root(0, Value::NULL));
    arena.collect();
    assert_eq!(arena.nursery(), MIN_NURSERY);
    // A fixed size stays, and `None` lets the arena choose again.
    arena.set_nursery(Some(100_000));
    build(&mut arena, 50_000);
    arena.collect();
    assert_eq!(arena.nursery(), 7 * PAGE * 8);
    arena.set_nursery(None);
    assert!((1 << 20..2 << 20).contains(&arena.nursery()), "a nursery of {} bytes", arena.nursery());
    // A small limit bounds the nursery below the usual least size.
    assert_eq!(Arena::new(1 << 20, 1).nursery(), (1 << 20) / 8);
}

/// The words of the objects and the records of the pages are arrays of their own, though they are one mapping. A position past the
/// objects is past the end of the object words, and reaches no record.
#[test]
fn a_position_past_the_objects_reaches_no_record() {
    let mut arena = Arena::new(1 << 20, 2);
    build(&mut arena, 100);
    arena.collect();
    arena.collect();
    // The first record would be at this position if the two parts were one array.
    let past = WORDS + SLACK;
    let heap = arena.heap();
    assert_eq!((heap.words().len(), heap.records().len()), (WORDS + SLACK, RECORDS));
    assert!(heap.words().get(past).is_none() && heap.words().get(past..past + 4).is_none());
    assert!(heap.bit_word(past, Bits::Marks).is_none() && !heap.has_bit(past, Bits::Starts));
    let before: Vec<u64> = heap.records().iter().take(8 * PAGE_WORDS).map(Cell::get).collect();
    // A made-up reference to such a position is a reference to no object. Collections, also ones that move objects, leave the records as they were.
    arena.mutate(|mc| mc.set_root(1, Value::from_bits((past as u64 + 64) << 32 | OBJECT)));
    arena.collect();
    arena.collect_minor();
    let after: Vec<u64> = arena.heap().records().iter().take(8 * PAGE_WORDS).map(Cell::get).collect();
    assert!(before == after, "a record changed");
    arena.set_evacuate_all(true);
    arena.collect();
    assert_eq!(sum(&mut arena), (100 * 99 / 2, 100));
}

