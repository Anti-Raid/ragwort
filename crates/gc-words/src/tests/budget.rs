use super::*;

struct Pair;
impl Object for Pair {
    const DESC: Desc = Desc::of::<Pair>(2).values(0b11);
}

fn pair<'gc>(mc: &Mutation<'gc>, car: Value<'gc>, cdr: Value<'gc>) -> Result<Value<'gc>, OutOfMemory> {
    Ok(Value::object(mc, mc.alloc::<Pair, 2>([car.to_bits(), cdr.to_bits()])?))
}

/// Grows root 0's list until an allocation fails.
fn grow_until_full(arena: &mut Arena) -> Result<(), OutOfMemory> {
    arena.step(|mc| {
        while let Ok(list) = pair(mc, Value::NIL, mc.root(0)) {
            mc.set_root(0, list);
        }
    })
}

#[test]
fn the_limit_fails_the_step_and_the_arena_recovers() {
    let mut arena = Arena::new(1 << 20, 1);
    assert_eq!(grow_until_full(&mut arena), Err(OutOfMemory));
    assert!(arena.peak() <= arena.limit(), "peak {} over {}", arena.peak(), arena.limit());
    assert!(arena.committed_bytes() <= 1 << 20);
    // What the step did before failing stays done: the list is still there.
    let len = arena.mutate(|mc| {
        let mut n = 0;
        let mut v = mc.root(0);
        while let Some(p) = v.downcast::<Pair>(mc) {
            n += 1;
            v = p.value(mc, 1);
        }
        n
    });
    assert!(len > 10_000, "{len}");
    arena.mutate(|mc| mc.set_root(0, Value::NIL));
    arena.collect();
    for _ in 0..100 {
        arena.step(|mc| (0..1000).try_for_each(|_| pair(mc, Value::NIL, Value::NIL).map(drop))).unwrap().unwrap();
    }
}

/// A heap full of garbage doesn't fail a step: the reserve covers it, and the full collection
/// it calls for runs at the end of the step.
#[test]
fn the_reserve_lets_a_step_finish_and_collects() {
    let mut arena = Arena::new(1 << 20, 1);
    arena.mutate(|mc| {
        while !mc.collection_due() {
            pair(mc, Value::NIL, Value::NIL).unwrap();
        }
    });
    let (majors, _) = arena.collections();
    arena.step(|mc| {
        assert!(mc.collection_due());
        pair(mc, Value::NIL, Value::NIL).unwrap();
    })
    .unwrap();
    assert_eq!(arena.collections().0, majors + 1);
    arena.mutate(|mc| assert!(!mc.collection_due()));
}

#[test]
fn optional_allocations_neither_fail_the_step_nor_use_the_reserve() {
    let mut arena = Arena::new(1 << 20, 1);
    arena.set_reserve(1 << 20);
    arena
        .step(|mc| {
            assert_eq!(mc.optional(|| pair(mc, Value::NIL, Value::NIL)).map(drop), Err(OutOfMemory));
            assert!(!mc.collection_due());
            pair(mc, Value::NIL, Value::NIL).unwrap();
            assert!(mc.collection_due());
        })
        .unwrap();
}

#[test]
fn charges_count_until_dropped() {
    let mut arena = Arena::new(1 << 20, 1);
    let used = arena.used();
    arena.mutate(|mc| {
        let mut charge = mc.charge();
        charge.grow(1000).unwrap();
        assert_eq!(mc.used(), used + 1000);
        charge.shrink(400);
        assert_eq!(mc.used(), used + 600);
        assert_eq!(charge.grow(2 << 20), Err(OutOfMemory));
        assert_eq!(charge.bytes(), 600);
    });
    assert_eq!(arena.used(), used);
    // The failed charge fails the step, as an allocation would.
    let result = arena.step(|mc| mc.charge().grow(2 << 20));
    assert_eq!(result, Err(OutOfMemory));
}

#[test]
fn hosts_are_charged_until_freed() {
    let mut arena = Arena::new(1 << 20, 1);
    // Sizes the tables first.
    arena.mutate(|mc| {
        mc.host(0u64).unwrap();
    });
    arena.collect();
    let used = arena.used();
    arena.mutate(|mc| {
        mc.host([0u8; 1000]).unwrap();
    });
    assert_eq!(arena.used(), used + 1000 + HOST_COST);
    arena.collect();
    assert_eq!(arena.used(), used);
}

#[test]
fn injected_failures_fail_the_picked_allocation() {
    let mut arena = Arena::new(4 << 20, 1);
    arena.fail_after(Some(5));
    let made = arena.mutate(|mc| (0..10).take_while(|_| pair(mc, Value::NIL, Value::NIL).is_ok()).count());
    assert_eq!(made, 5);
    // Only once, and the next allocations go on in the same hole.
    let pages = arena.pages_bytes();
    arena.mutate(|mc| {
        for _ in 0..10 {
            pair(mc, Value::NIL, Value::NIL).unwrap();
        }
    });
    assert_eq!(arena.pages_bytes(), pages);
    // Retried over and over, a step's allocations don't waste memory.
    for _ in 0..2000 {
        arena.fail_after(Some(50));
        let result = arena.step(|mc| (0..100).try_for_each(|_| pair(mc, Value::NIL, Value::NIL).map(drop)));
        assert_eq!(result, Err(OutOfMemory));
    }
    assert!(arena.pages_bytes() <= 1 << 20, "{} bytes of pages", arena.pages_bytes());
    arena.fail_after(None);
    arena.step(|mc| (0..1000).try_for_each(|_| pair(mc, Value::NIL, Value::NIL).map(drop))).unwrap().unwrap();
}

/// Pages given back to the system are refunded, and charged again once reused.
#[test]
fn released_pages_are_refunded() {
    let mut arena = Arena::new(64 << 20, 1);
    arena.mutate(|mc| {
        for _ in 0..1_000_000 {
            pair(mc, Value::NIL, Value::NIL).unwrap();
        }
        // Keeps the last page, so the free ones before it are released rather than trimmed.
        let last = pair(mc, Value::NIL, Value::NIL).unwrap();
        mc.set_root(0, last);
    });
    let peak = arena.used();
    assert!(peak > 20 << 20, "{peak}");
    arena.collect();
    let pages = arena.committed_bytes() / (PAGE * 8);
    assert!(arena.used() < peak / 4, "{} of {peak}", arena.used());
    assert!(arena.used() >= pages * PAGE_COST);
    assert!(arena.pages_bytes() > 20 << 20, "the pages were trimmed");
    arena.mutate(|mc| {
        for _ in 0..1_000_000 {
            pair(mc, Value::NIL, Value::NIL).unwrap();
        }
    });
    assert!(arena.used() >= peak - (1 << 20), "{} of {peak}", arena.used());
    assert_eq!(arena.peak(), peak.max(arena.used()));
}
