use super::raw::Raw;
use super::*;

objects! {
    kind Kind;
    struct Node { n: i64 }
    struct Nodes {} items Member<Node>
    struct Weaks {} items Weak<Node>
    struct Pair { car: Value, cdr: Value }
}

const BIG: usize = 100_000;

/// Fills the space dead objects left, so a reference to one reads something else.
fn churn(mc: &Mutation<'_>) {
    for _ in 0..300_000 {
        Pair::new(mc, Value::NIL, Value::NIL).unwrap();
    }
}

fn nodes<'gc>(mc: &Mutation<'gc>, root: usize) -> Gc<'gc, Nodes> {
    mc.root(root).downcast::<Nodes>(mc).unwrap()
}

fn weaks<'gc>(mc: &Mutation<'gc>, root: usize) -> Gc<'gc, Weaks> {
    mc.root(root).downcast::<Weaks>(mc).unwrap()
}

/// What each item refers to, by its node's number.
fn numbers<'gc, S: Item<Out<'gc> = Option<Gc<'gc, Node>>>>(mc: &Mutation<'gc>, items: Slots<'gc, S>) -> Vec<Option<i64>> {
    (0..items.len()).map(|i| items.get(i).map(|n| n.n(mc))).collect()
}

#[test]
fn member_items_keep_their_targets_and_follow_moves() {
    let mut arena = Arena::new(16 << 20, 1);
    arena.mutate(|mc| {
        let array = Nodes::new(mc, 1000, None).unwrap();
        for i in 0..1000 {
            churn_a_little(mc);
            if i % 3 != 0 {
                array.items(mc).set(mc, i, Some(Node::new(mc, i as i64).unwrap()));
            }
        }
        mc.set_root(0, Value::object(mc, array));
    });
    let expected: Vec<_> = (0..1000).map(|i| (i % 3 != 0).then_some(i as i64)).collect();
    arena.collect();
    assert_eq!(arena.mutate(|mc| numbers(mc, nodes(mc, 0).items(mc))), expected);
    arena.set_evacuate_all(true);
    arena.collect();
    arena.mutate(churn);
    assert_eq!(arena.mutate(|mc| numbers(mc, nodes(mc, 0).items(mc))), expected);
}

fn churn_a_little(mc: &Mutation<'_>) {
    for _ in 0..10 {
        Pair::new(mc, Value::NIL, Value::NIL).unwrap();
    }
}

/// Stores into an old array: a minor collection must find the young targets through the
/// dirty cards, though it doesn't trace the rest of the array.
#[test]
fn member_items_on_dirty_cards_survive_minor_collections() {
    let mut arena = Arena::new(32 << 20, 1);
    arena.mutate(|mc| {
        let array = Nodes::new(mc, BIG, None).unwrap();
        mc.set_root(0, Value::object(mc, array));
    });
    arena.collect();
    let stores = [0, 1, 63, 64, 2047, 2048, 50_000, BIG - 1];
    arena.mutate(|mc| {
        for &i in &stores {
            churn_a_little(mc);
            nodes(mc, 0).items(mc).set(mc, i, Some(Node::new(mc, i as i64).unwrap()));
        }
    });
    arena.collect_minor();
    arena.mutate(|mc| {
        churn(mc);
        let items = nodes(mc, 0).items(mc);
        for &i in &stores {
            assert_eq!(items.get(i).map(|n| n.n(mc)), Some(i as i64));
        }
    });
}

#[test]
fn weak_items_clear_once_their_targets_die() {
    let mut arena = Arena::new(16 << 20, 2);
    arena.mutate(|mc| {
        let weak = Weaks::new(mc, 1000, None).unwrap();
        let strong = Nodes::new(mc, 500, None).unwrap();
        for i in 0..1000 {
            let node = Node::new(mc, i as i64).unwrap();
            weak.items(mc).set(mc, i, Some(node));
            if i % 2 == 0 {
                strong.items(mc).set(mc, i / 2, Some(node));
            }
        }
        mc.set_root(0, Value::object(mc, weak));
        mc.set_root(1, Value::object(mc, strong));
    });
    let expected: Vec<_> = (0..1000).map(|i| (i % 2 == 0).then_some(i as i64)).collect();
    arena.collect();
    arena.mutate(churn);
    assert_eq!(arena.mutate(|mc| numbers(mc, weaks(mc, 0).items(mc))), expected);
    arena.set_evacuate_all(true);
    arena.collect();
    arena.mutate(churn);
    assert_eq!(arena.mutate(|mc| numbers(mc, weaks(mc, 0).items(mc))), expected);
    // Dropping the strong array kills the rest.
    arena.set_evacuate_all(false);
    arena.mutate(|mc| mc.set_root(1, Value::NIL));
    arena.collect();
    assert!(arena.mutate(|mc| numbers(mc, weaks(mc, 0).items(mc))).iter().all(Option::is_none));
}

/// A minor collection clears weak items on dirty cards whose young targets died, and leaves
/// the rest of the array alone.
#[test]
fn weak_items_on_dirty_cards_clear_in_minor_collections() {
    let mut arena = Arena::new(32 << 20, 2);
    arena.mutate(|mc| {
        let weak = Weaks::new(mc, BIG, None).unwrap();
        let old = Node::new(mc, -1).unwrap();
        weak.items(mc).set(mc, 1, Some(old));
        mc.set_root(0, Value::object(mc, weak));
        let strong = Nodes::new(mc, 16, None).unwrap();
        strong.items(mc).set(mc, 15, Some(old));
        mc.set_root(1, Value::object(mc, strong));
    });
    arena.collect();
    let stores = [0, 63, 64, 2048, 50_000, BIG - 1];
    arena.mutate(|mc| {
        for (k, &i) in stores.iter().enumerate() {
            churn_a_little(mc);
            let node = Node::new(mc, i as i64).unwrap();
            weaks(mc, 0).items(mc).set(mc, i, Some(node));
            if k % 2 == 0 {
                nodes(mc, 1).items(mc).set(mc, k, Some(node));
            }
        }
    });
    arena.collect_minor();
    arena.mutate(|mc| {
        churn(mc);
        let items = weaks(mc, 0).items(mc);
        for (k, &i) in stores.iter().enumerate() {
            assert_eq!(items.get(i).map(|n| n.n(mc)), (k % 2 == 0).then_some(i as i64), "item {i}");
        }
        assert_eq!(items.get(1).map(|n| n.n(mc)), Some(-1));
    });
}

/// Nodes move back and forth between an array of members and a list of values while a cycle
/// runs in small slices, so most moves store into an object already traced.
#[test]
fn member_item_stores_while_marking_keep_their_targets() {
    const N: usize = 2000;
    let mut arena = Arena::new(16 << 20, 2);
    arena.mutate(|mc| {
        let array = Nodes::new(mc, N, None).unwrap();
        let mut list = Value::NIL;
        for i in 0..N {
            list = Value::object(mc, Pair::new(mc, Value::object(mc, Node::new(mc, i as i64).unwrap()), list).unwrap());
        }
        // Roots are traced last first, so the array is traced before the list.
        mc.set_root(1, Value::object(mc, array));
        mc.set_root(0, list);
    });
    arena.collect();
    // Slices big enough that cycles end while nodes are in the array. Everything live moves,
    // so a node the barrier missed leaves its page to be reused: kept in place, a line shared
    // with a live pair would keep it readable.
    arena.set_evacuate_all(true);
    arena.set_stress(Some(16 << 10));
    for round in 0..61 {
        arena
            .step(|mc| {
                let array = nodes(mc, 1).items(mc);
                let mut cur = mc.root(0);
                let mut i = round % 2;
                while let Some(pair) = cur.downcast::<Pair>(mc) {
                    if i < N {
                        // Swap the pair's node and the array's.
                        let held = array.get(i);
                        array.set(mc, i, pair.car(mc).downcast::<Node>(mc));
                        pair.set_car(mc, held.map_or(Value::NIL, |n| Value::object(mc, n)));
                    }
                    i += 2;
                    cur = pair.cdr(mc);
                }
                churn_a_little(mc);
            })
            .unwrap();
    }
    arena.set_stress(None);
    arena.collect();
    arena.mutate(churn);
    arena.mutate(|mc| {
        let mut seen: Vec<i64> = numbers(mc, nodes(mc, 1).items(mc)).into_iter().flatten().collect();
        let mut cur = mc.root(0);
        while let Some(pair) = cur.downcast::<Pair>(mc) {
            seen.extend(pair.car(mc).downcast::<Node>(mc).map(|n| n.n(mc)));
            cur = pair.cdr(mc);
        }
        seen.sort();
        assert_eq!(seen, (0..N as i64).collect::<Vec<_>>());
    });
}

/// Nodes move between two arrays by bulk copies and fills while a cycle runs in small slices,
/// so a copy often lands in an array already traced, from one that isn't yet.
#[test]
fn bulk_member_copies_while_marking_keep_their_targets() {
    const N: usize = 4096;
    let mut arena = Arena::new(16 << 20, 2);
    arena.mutate(|mc| {
        let full = Nodes::new(mc, N, None).unwrap();
        for i in 0..N {
            full.items(mc).set(mc, i, Some(Node::new(mc, i as i64).unwrap()));
        }
        mc.set_root(0, Value::object(mc, Nodes::new(mc, N, None).unwrap()));
        mc.set_root(1, Value::object(mc, full));
    });
    arena.collect();
    arena.set_evacuate_all(true);
    arena.set_stress(Some(256));
    for round in 0..64 {
        arena
            .step(|mc| {
                let (to, from) = if round % 2 == 0 { (0, 1) } else { (1, 0) };
                for chunk in 0..N / 256 {
                    let range = chunk * 256..(chunk + 1) * 256;
                    nodes(mc, to).items(mc).slice(range.clone()).unwrap().copy_from(mc, nodes(mc, from).items(mc).slice(range.clone()).unwrap());
                    nodes(mc, from).items(mc).slice(range).unwrap().fill(mc, None);
                    churn_a_little(mc);
                }
            })
            .unwrap();
    }
    arena.set_stress(None);
    arena.collect();
    arena.mutate(churn);
    arena.mutate(|mc| {
        let mut all: Vec<i64> = (0..2).flat_map(|r| numbers(mc, nodes(mc, r).items(mc))).flatten().collect();
        all.sort();
        assert_eq!(all, (0..N as i64).collect::<Vec<_>>());
    });
}

/// Bulk copies and fills into an old array dirty the cards they cover, so minor collections
/// see them.
#[test]
fn bulk_stores_into_old_items_are_seen_by_minor_collections() {
    let mut arena = Arena::new(32 << 20, 3);
    arena.mutate(|mc| {
        mc.set_root(0, Value::object(mc, Nodes::new(mc, BIG, None).unwrap()));
        mc.set_root(1, Value::object(mc, Weaks::new(mc, BIG, None).unwrap()));
    });
    arena.collect();
    arena.mutate(|mc| {
        let kept = Node::new(mc, 7).unwrap();
        nodes(mc, 0).items(mc).slice(1000..3000).unwrap().fill(mc, Some(kept));
        let young = Nodes::new(mc, 100, Some(kept)).unwrap();
        let dies = Weaks::new(mc, 100, Some(Node::new(mc, 8).unwrap())).unwrap();
        weaks(mc, 1).items(mc).slice(0..100).unwrap().copy_from(mc, dies.items(mc));
        nodes(mc, 0).items(mc).slice(BIG - 100..BIG).unwrap().copy_from(mc, young.items(mc));
        let lives = Weaks::new(mc, 100, Some(kept)).unwrap();
        weaks(mc, 1).items(mc).slice(BIG - 100..BIG).unwrap().copy_from(mc, lives.items(mc));
    });
    arena.collect_minor();
    arena.mutate(|mc| {
        churn(mc);
        let strong = numbers(mc, nodes(mc, 0).items(mc));
        assert!(strong[1000..3000].iter().chain(&strong[BIG - 100..]).all(|&n| n == Some(7)));
        assert!(strong[..1000].iter().chain(&strong[3000..BIG - 100]).all(Option::is_none));
        let weak = numbers(mc, weaks(mc, 1).items(mc));
        assert!(weak[..100].iter().all(Option::is_none), "the copied weak items' target died");
        assert!(weak[BIG - 100..].iter().all(|&n| n == Some(7)));
    });
}

#[test]
#[should_panic(expected = "isn't of type")]
fn member_item_reads_check_the_target_type() {
    let mut arena = Arena::new(1 << 20, 1);
    arena.mutate(|mc| {
        let array = Nodes::new(mc, 4, None).unwrap();
        let pair = Pair::new(mc, Value::NIL, Value::NIL).unwrap();
        array.item_slots::<slot::u64>(mc).set(mc, 2, pair.to_word());
        array.items(mc).get(2);
    });
}

#[test]
#[should_panic(expected = "isn't of type")]
fn weak_item_reads_check_the_target_type() {
    let mut arena = Arena::new(1 << 20, 1);
    arena.mutate(|mc| {
        let array = Weaks::new(mc, 4, None).unwrap();
        let pair = Pair::new(mc, Value::NIL, Value::NIL).unwrap();
        array.item_slots::<slot::u64>(mc).set(mc, 0, pair.to_word());
        array.items(mc).get(0);
    });
}
