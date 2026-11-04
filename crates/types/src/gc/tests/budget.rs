use super::*;

objects! {
    kind Kind;
    struct Pair { car: Value, cdr: Value }
    struct Owner { text: Host<String> }
    struct Bytes { data: Frozen<Box<[u8]>> }
}

fn pair<'gc>(mc: &Mutation<'gc>, car: Value<'gc>, cdr: Value<'gc>) -> Result<Value<'gc>, OutOfMemory> {
    Ok(Value::object(mc, Pair::new(mc, car, cdr)?))
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
            v = p.cdr(mc);
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

/// What a host value owns outside the arena counts until it's freed, at whatever it was last
/// set to.
#[test]
fn hosts_count_the_bytes_they_own() {
    let mut arena = Arena::new(1 << 20, 1);
    arena.mutate(|mc| {
        mc.host(0u64).unwrap();
    });
    arena.collect();
    let used = arena.used();
    let base = size_of::<String>() + HOST_COST;
    arena.mutate(|mc| {
        let text = mc.host(String::from("hi")).unwrap();
        text.set_owned_bytes(mc, 1000).unwrap();
        assert_eq!(mc.used(), used + base + 1000);
        text.erase().set_owned_bytes(mc, 300).unwrap();
        assert_eq!(mc.used(), used + base + 300);
        let held = text.get(mc).unwrap();
        assert_eq!(text.set_owned_bytes(mc, 0), Err(HostError::InUse));
        drop(held);
        assert_eq!(text.set_owned_bytes(mc, 2 << 20), Err(HostError::OutOfMemory));
        assert_eq!(mc.used(), used + base + 300, "a failed claim counts nothing");
    });
    // Nothing holds the value, so a collection frees it with all it was charged.
    assert_eq!(arena.used(), used + base + 300);
    arena.collect();
    assert_eq!(arena.used(), used);
}

#[test]
fn freed_hosts_ignore_owned_bytes() {
    let mut arena = Arena::new(1 << 20, 1);
    let stale = arena.mutate(|mc| mc.host(String::new()).unwrap().to_word());
    arena.collect();
    let used = arena.used();
    arena.mutate(|mc| {
        let fresh = mc.host(String::new()).unwrap();
        assert_eq!(fresh.to_word() & 0xffff_ffff, stale & 0xffff_ffff, "the slot should be reused");
        let used = mc.used();
        let stale = HostRef::<String> { id: fresh.id, generation: fresh.generation - 1, _marker: PhantomData };
        stale.set_owned_bytes(mc, 5000).unwrap();
        assert_eq!(mc.used(), used);
    });
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

/// Pages given back to the system are refunded, and charged again once reused. A backing that
/// can't give memory back keeps them charged.
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
    assert!(arena.used() >= pages * PAGE_COST);
    assert!(arena.pages_bytes() > 20 << 20, "the pages were trimmed");
    if !ragwort_gc_region::Region::releases() {
        assert_eq!(arena.committed_bytes(), arena.pages_bytes());
        assert!(arena.used() >= peak - (1 << 20), "{} of {peak}", arena.used());
        return;
    }
    assert!(arena.used() < peak / 4, "{} of {peak}", arena.used());
    arena.mutate(|mc| {
        for _ in 0..1_000_000 {
            pair(mc, Value::NIL, Value::NIL).unwrap();
        }
    });
    assert!(arena.used() >= peak - (1 << 20), "{} of {peak}", arena.used());
    assert_eq!(arena.peak(), peak.max(arena.used()));
}

/// An arena with about a megabyte of pairs live in root 1, so pages alone start a cycle only
/// past a couple of megabytes.
fn arena_with_live_pages(limit: usize) -> Arena {
    let mut arena = Arena::new(limit, 2);
    arena.mutate(|mc| {
        for _ in 0..40_000 {
            mc.set_root(1, pair(mc, Value::NIL, mc.root(1)).unwrap());
        }
    });
    arena.collect();
    arena
}

/// Host values and old frozen values that die count toward starting a major cycle, as pages do, so
/// they're freed long before the arena nears its limit.
#[test]
fn dead_hosts_and_frozen_values_pace_major_cycles() {
    let limit = 32 << 20;
    let mut arena = arena_with_live_pages(limit);
    for _ in 0..2000 {
        arena
            .step(|mc| {
                for _ in 0..100 {
                    let text = mc.host(String::new()).unwrap();
                    text.set_owned_bytes(mc, 200).unwrap();
                    Owner::new(mc, Some(text)).unwrap();
                }
            })
            .unwrap();
    }
    assert!(arena.collections().0 > 0);
    assert!(arena.peak() < limit / 2, "hosts: peak {} of {limit}", arena.peak());

    let mut arena = arena_with_live_pages(limit);
    for _ in 0..3000 {
        // Each value outlives a step, so a minor collection may make it old before it dies.
        arena
            .step(|mc| {
                let bytes = Bytes::new(mc, mc.frozen_owning(Box::from([0u8; 10_000]), 10_000).unwrap()).unwrap();
                mc.set_root(0, Value::object(mc, bytes));
            })
            .unwrap();
        arena.collect_minor();
    }
    assert!(arena.collections().0 > 0);
    assert!(arena.peak() < limit / 2, "frozen values: peak {} of {limit}", arena.peak());
}

/// With most of the limit live, major cycles still start early enough to finish within the
/// steps, so the reserve never forces a full collection: one pause the length of a cycle.
#[test]
fn a_nearly_full_heap_is_collected_in_slices() {
    let limit = 8 << 20;
    let mut arena = Arena::new(limit, 1);
    arena.mutate(|mc| mc.set_root(0, Value::object(mc, GcVec::<slot::Value>::new(mc).unwrap().head())));
    let live = 2500;
    for i in 0..20_000usize {
        arena
            .step(|mc| {
                let table = GcVec::<slot::Value>::of(mc.root(0).downcast(mc).unwrap());
                let entry = Value::object(mc, Bytes::new(mc, mc.frozen_owning(Box::from([0u8; 2000]), 2000).unwrap()).unwrap());
                let entry = pair(mc, entry, Value::NIL).unwrap();
                for _ in 0..4 {
                    pair(mc, entry, Value::NIL).unwrap();
                }
                if table.len(mc) < live {
                    table.push(mc, entry).unwrap();
                } else {
                    table.set(mc, i * 7919 % live, entry);
                }
            })
            .unwrap();
    }
    assert!(arena.collections().0 > 5, "{:?}", arena.collections());
    assert!(arena.peak() <= limit - limit / 16, "peak {} of {limit}: the reserve was drawn on", arena.peak());
}

/// Frozen values count toward a minor collection as objects do, so short-lived ones that small
/// objects hold are freed long before the arena nears its limit.
#[test]
fn young_frozen_values_pace_minor_collections() {
    let limit = 32 << 20;
    let mut arena = Arena::new(limit, 1);
    for _ in 0..2000 {
        arena
            .step(|mc| {
                for _ in 0..20 {
                    Bytes::new(mc, mc.frozen_owning(Box::from([0u8; 4000]), 4000).unwrap()).unwrap();
                }
            })
            .unwrap();
    }
    assert!(arena.collections().1 > 0);
    assert!(arena.peak() < limit / 4, "peak {} of {limit}", arena.peak());
}

/// Once host values die, the table drops the slots at its end and gives their room back, and
/// new values take the lowest free ids.
#[test]
fn host_tables_shrink_after_their_values_die() {
    let mut arena = Arena::new(64 << 20, 1);
    let tables = |arena: &Arena| (arena.meta.hosts.borrow().capacity(), arena.meta.free_hosts.borrow().capacity());
    arena.mutate(|mc| {
        for i in 0..100_000 {
            let owner = Owner::new(mc, Some(mc.host(String::new()).unwrap())).unwrap();
            if i == 500 {
                mc.set_root(0, Value::object(mc, owner));
            }
        }
    });
    arena.collect();
    assert_eq!(arena.hosts(), 501, "the live value at 500 keeps the slots before it");
    assert!(tables(&arena).0 < 2000 && tables(&arena).1 < 2000, "{:?}", tables(&arena));
    arena.mutate(|mc| assert_eq!(mc.host(0u8).unwrap().id, 0, "the lowest free id first"));
    arena.mutate(|mc| mc.set_root(0, Value::NIL));
    arena.collect();
    assert_eq!(arena.hosts(), 0);
    assert!(tables(&arena).0 <= 64 && tables(&arena).1 <= 64, "{:?}", tables(&arena));
}

/// A slot dropped from the table and made again starts past the generations it had, so a stale
/// reference to it reads nothing.
#[test]
fn dropped_host_slots_never_reuse_a_generation() {
    let mut arena = Arena::new(1 << 20, 1);
    let stale = arena.mutate(|mc| {
        let host = mc.host(String::from("old")).unwrap();
        (host.id, host.generation)
    });
    arena.collect();
    assert_eq!(arena.hosts(), 0);
    arena.mutate(|mc| {
        let fresh = mc.host(String::from("new")).unwrap();
        assert_eq!(fresh.id, stale.0);
        assert!(fresh.generation > stale.1);
        let stale = HostRef::<String> { id: stale.0, generation: stale.1, _marker: PhantomData };
        assert!(stale.get(mc).is_none());
    });
}

/// The host table is charged as it grows, so growing it can't take the arena past its limit.
/// Across these limits, the table's last growth lands on both sides of it.
#[test]
fn host_tables_grow_within_the_limit() {
    for limit in (512..1024).step_by(32).map(|k| k << 10) {
        let mut arena = Arena::new(limit, 1);
        let made = arena.mutate(|mc| (0..).take_while(|_| mc.host(()).is_ok()).count());
        assert!(made > 1000);
        assert!(arena.peak() <= limit, "peak {} of {limit}", arena.peak());
    }
}

#[test]
fn steps_that_end_when_due_keep_collection_incremental() {
    let limit = 4 << 20;
    let mut arena = Arena::new(limit, 1);
    // A live list to keep marking, and garbage made in steps that end once one's due.
    arena.mutate(|mc| {
        for _ in 0..10_000 {
            let list = pair(mc, Value::NIL, mc.root(0)).unwrap();
            mc.set_root(0, list);
        }
    });
    let (mut made, mut longest) = (0, 0);
    while made < 40 * limit {
        let n = arena
            .step(|mc| {
                assert!(!mc.step_due() || mc.collection_due());
                let mut n = 0;
                while !mc.step_due() {
                    pair(mc, Value::NIL, Value::NIL).unwrap();
                    n += 1;
                }
                n
            })
            .unwrap();
        made += n * 24;
        longest = longest.max(n * 24);
    }
    let (majors, minors) = arena.collections();
    assert!(majors > 0 && minors > 0, "{majors} majors, {minors} minors");
    // Never into the reserve, so never a full collection, and no step made more than a nursery.
    assert!(arena.peak() <= limit - limit / 16, "peak {} of {limit}", arena.peak());
    assert!(longest <= (limit / 8).clamp(64 << 10, 4 << 20) + 64, "{longest}");
    let len = arena.mutate(|mc| {
        let (mut n, mut v) = (0, mc.root(0));
        while let Some(p) = v.downcast::<Pair>(mc) {
            (n, v) = (n + 1, p.cdr(mc));
        }
        n
    });
    assert_eq!(len, 10_000);
}
