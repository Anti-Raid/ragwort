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
        while let Ok(list) = pair(mc, Value::NULL, mc.root(0)) {
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
    // The work that the step did before it failed is kept: the list is still there.
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
    arena.mutate(|mc| mc.set_root(0, Value::NULL));
    arena.collect();
    for _ in 0..100 {
        arena.step(|mc| (0..1000).try_for_each(|_| pair(mc, Value::NULL, Value::NULL).map(drop))).unwrap().unwrap();
    }
}

/// A heap full of garbage does not fail a step. The reserve covers the allocations, and the full collection
/// that the reserve makes due runs at the end of the step.
#[test]
fn the_reserve_lets_a_step_finish_and_collects() {
    let mut arena = Arena::new(1 << 20, 1);
    arena.mutate(|mc| {
        while !mc.collection_due() {
            pair(mc, Value::NULL, Value::NULL).unwrap();
        }
    });
    let (majors, _) = arena.collections();
    arena.step(|mc| {
        assert!(mc.collection_due());
        pair(mc, Value::NULL, Value::NULL).unwrap();
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
            assert_eq!(mc.optional(|| pair(mc, Value::NULL, Value::NULL)).map(drop), Err(OutOfMemory));
            assert!(!mc.collection_due());
            pair(mc, Value::NULL, Value::NULL).unwrap();
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
    // A failed charge fails the step, as a failed allocation does.
    let result = arena.step(|mc| mc.charge().grow(2 << 20));
    assert_eq!(result, Err(OutOfMemory));
}

#[test]
fn hosts_are_charged_until_freed() {
    let mut arena = Arena::new(1 << 20, 1);
    // Allocate one host value first, so that the tables are already sized when `used` is read.
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

/// The bytes that a host value owns outside the arena are charged until the value is freed, at the count that was last
/// set.
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
    // No object holds the value, so a collection frees it and refunds its whole charge.
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
    let made = arena.mutate(|mc| (0..10).take_while(|_| pair(mc, Value::NULL, Value::NULL).is_ok()).count());
    assert_eq!(made, 5);
    // The failure is injected only once, and the next allocations continue in the same hole.
    let pages = arena.pages_bytes();
    arena.mutate(|mc| {
        for _ in 0..10 {
            pair(mc, Value::NULL, Value::NULL).unwrap();
        }
    });
    assert_eq!(arena.pages_bytes(), pages);
    // A step that fails and is retried many times does not waste memory.
    for _ in 0..2000 {
        arena.fail_after(Some(50));
        let result = arena.step(|mc| (0..100).try_for_each(|_| pair(mc, Value::NULL, Value::NULL).map(drop)));
        assert_eq!(result, Err(OutOfMemory));
    }
    assert!(arena.pages_bytes() <= 1 << 20, "{} bytes of pages", arena.pages_bytes());
    arena.fail_after(None);
    arena.step(|mc| (0..1000).try_for_each(|_| pair(mc, Value::NULL, Value::NULL).map(drop))).unwrap().unwrap();
}

/// A minor collection sweeps only the pages allocated into since the last collection, even with an old heap that is many
/// times bigger. The allocator reuses the memory that the minor collection frees. A new object that an old page refers to
/// stays alive through the old page's dirty cards.
#[test]
fn minor_collections_sweep_only_young_pages() {
    let mut arena = Arena::new(64 << 20, 1);
    arena.mutate(|mc| {
        for _ in 0..300_000 {
            let list = pair(mc, Value::NULL, mc.root(0)).unwrap();
            mc.set_root(0, list);
        }
    });
    arena.collect();
    let (old, pages) = (arena.meta.used.get(), arena.pages_bytes());
    for round in 0..50 {
        arena.mutate(|mc| {
            for _ in 0..20_000 {
                pair(mc, Value::NULL, Value::NULL).unwrap();
            }
            // Store a new object in the head of the old list.
            let head = mc.root(0).downcast::<Pair>(mc).unwrap();
            head.set_car(mc, pair(mc, Value::fixnum(round).unwrap(), Value::NULL).unwrap());
        });
        let young = arena.meta.young_pages.iter(false).count();
        assert!(young * 10 < old, "{young} young pages of {old}");
        arena.collect_minor();
        assert_eq!(arena.meta.young_pages.iter(false).count(), 0);
    }
    assert!(arena.pages_bytes() <= pages + (1 << 20), "{} bytes of pages, from {pages}", arena.pages_bytes());
    let (len, last) = arena.mutate(|mc| {
        let head = mc.root(0).downcast::<Pair>(mc).unwrap();
        let last = head.car(mc).downcast::<Pair>(mc).unwrap().car(mc).as_fixnum();
        let (mut n, mut v) = (0, mc.root(0));
        while let Some(p) = v.downcast::<Pair>(mc) {
            n += 1;
            v = p.cdr(mc);
        }
        (n, last)
    });
    assert_eq!((len, last), (300_000, Some(49)));
}

/// A minor collection releases the pages that a burst of garbage left free, except for one nursery's worth.
#[test]
fn a_minor_collection_gives_back_what_a_burst_freed() {
    let mut arena = Arena::new(64 << 20, 1);
    arena.mutate(|mc| {
        for _ in 0..1_000_000 {
            pair(mc, Value::NULL, Value::NULL).unwrap();
        }
        // Keep an object on the last page. The free pages before it are then released to the system, not trimmed from the count of pages handed out.
        let last = pair(mc, Value::NULL, Value::NULL).unwrap();
        mc.set_root(0, last);
    });
    assert!(arena.committed_bytes() > 20 << 20, "{}", arena.committed_bytes());
    arena.collect_minor();
    assert_eq!(arena.collections(), (0, 1));
    if ragwort_gc_region::Region::releases() {
        assert!(arena.committed_bytes() <= arena.meta.nursery + (1 << 20), "{} bytes committed", arena.committed_bytes());
    }
}

/// Pages released to the system are refunded, and are charged again once they are reused. With a backing that
/// cannot release memory, the pages stay charged.
#[test]
fn released_pages_are_refunded() {
    let mut arena = Arena::new(64 << 20, 1);
    arena.mutate(|mc| {
        for _ in 0..1_000_000 {
            pair(mc, Value::NULL, Value::NULL).unwrap();
        }
        // Keep an object on the last page. The free pages before it are then released to the system, not trimmed from the count of pages handed out.
        let last = pair(mc, Value::NULL, Value::NULL).unwrap();
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
            pair(mc, Value::NULL, Value::NULL).unwrap();
        }
    });
    assert!(arena.used() >= peak - (1 << 20), "{} of {peak}", arena.used());
    assert_eq!(arena.peak(), peak.max(arena.used()));
}

/// Returns an arena with about a megabyte of live pairs in root 1. So the occupied pages alone start a major cycle only
/// beyond a couple of megabytes.
fn arena_with_live_pages(limit: usize) -> Arena {
    let mut arena = Arena::new(limit, 2);
    arena.mutate(|mc| {
        for _ in 0..40_000 {
            mc.set_root(1, pair(mc, Value::NULL, mc.root(1)).unwrap());
        }
    });
    arena.collect();
    arena
}

/// Host values and old frozen values count toward the start of a major cycle, as pages do. So the dead ones
/// are freed long before the arena nears its limit.
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
        // Each value stays alive past the end of its step, so a minor collection can make it old before it dies.
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

/// With most of the limit live, major cycles still start early enough to finish in slices between the
/// steps. So the reserve never forces a full collection, which would be one pause as long as a whole cycle.
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
                let entry = pair(mc, entry, Value::NULL).unwrap();
                for _ in 0..4 {
                    pair(mc, entry, Value::NULL).unwrap();
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

/// Frozen values count toward the start of a minor collection, as objects do. So short-lived frozen values held by small
/// objects are freed long before the arena nears its limit.
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

/// Once host values die, the host table removes the free slots at its end and shrinks its capacity.
/// New values take the lowest free ids.
#[test]
fn host_tables_shrink_after_their_values_die() {
    let mut arena = Arena::new(64 << 20, 1);
    fn tables(arena: &Arena) -> (usize, usize) {
        (arena.meta.hosts.borrow().capacity(), arena.meta.free_hosts.borrow().capacity())
    }
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
    arena.mutate(|mc| mc.set_root(0, Value::NULL));
    arena.collect();
    assert_eq!(arena.hosts(), 0);
    assert!(tables(&arena).0 <= 64 && tables(&arena).1 <= 64, "{:?}", tables(&arena));
}

/// A slot that is removed from the table and later created again starts at a generation past the ones it had. So a stale
/// reference to the slot reads nothing.
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

/// The host table is charged as it grows, so growing it cannot take the arena past its limit.
/// The limits tried here cover both cases: the table's last growth fits under the limit, and it does not fit.
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
    // Build a live list, so that cycles have something to mark. The loop below allocates garbage in steps that end as soon as `step_due` is true.
    arena.mutate(|mc| {
        for _ in 0..10_000 {
            let list = pair(mc, Value::NULL, mc.root(0)).unwrap();
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
                    pair(mc, Value::NULL, Value::NULL).unwrap();
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
    // The peak never reaches the reserve, so no full collection ran. No step allocated more than one nursery.
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
