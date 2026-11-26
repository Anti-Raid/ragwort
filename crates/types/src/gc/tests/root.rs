use super::*;

objects! {
    kind Kind;
    struct Node { n: i64, next: Member<Node> }
    struct Watch { target: Weak<Node> }
}

#[test]
fn roots_keep_objects_across_collections_and_moves() {
    let mut arena = Arena::new(1 << 20, 1);
    let root = arena.mutate(|mc| {
        let tail = Node::new(mc, 2, None).unwrap();
        Root::new(mc, Node::new(mc, 1, Some(tail)).unwrap()).unwrap()
    });
    arena.collect_minor();
    arena.set_evacuate_all(true);
    arena.collect();
    arena.collect();
    assert_eq!(arena.objects(), 2);
    arena.mutate(|mc| {
        let head = root.get(mc).unwrap();
        assert_eq!((head.n(mc), head.next(mc).map(|n| n.n(mc))), (1, Some(2)));
    });
}

#[test]
fn dropping_every_clone_frees_the_object() {
    let mut arena = Arena::new(1 << 20, 1);
    let root = arena.mutate(|mc| {
        let node = Node::new(mc, 1, None).unwrap();
        let watch = Watch::new(mc, Some(node)).unwrap();
        mc.set_root(0, Value::object(mc, watch));
        Root::new(mc, node).unwrap()
    });
    let clone = root.clone();
    drop(root);
    arena.collect();
    fn alive(arena: &mut Arena) -> bool {
        arena.mutate(|mc| mc.root(0).downcast::<Watch>(mc).unwrap().target(mc).is_some())
    }
    assert!(alive(&mut arena), "a clone still holds it");
    drop(clone);
    arena.collect();
    assert!(!alive(&mut arena));
}

#[test]
fn another_arenas_root_is_refused() {
    let mut a = Arena::new(1 << 20, 1);
    let mut b = Arena::new(1 << 20, 1);
    let root = a.mutate(|mc| Root::new(mc, Node::new(mc, 1, None).unwrap()).unwrap());
    assert_eq!(b.mutate(|mc| root.get(mc).err()), Some(ForeignRoot));
}

#[test]
fn value_roots_keep_objects_and_hold_the_rest() {
    let mut arena = Arena::new(1 << 20, 1);
    let (node, five, nil) = arena.mutate(|mc| {
        let node = ValueRoot::new(mc, Value::object(mc, Node::new(mc, 7, None).unwrap())).unwrap();
        (node, ValueRoot::new(mc, Value::fixnum(5).unwrap()).unwrap(), ValueRoot::new(mc, Value::NULL).unwrap())
    });
    arena.set_evacuate_all(true);
    arena.collect();
    assert_eq!(arena.objects(), 1);
    arena.mutate(|mc| {
        assert_eq!(node.get(mc).unwrap().downcast::<Node>(mc).unwrap().n(mc), 7);
        assert_eq!((five.get(mc).unwrap().as_fixnum(), nil.get(mc).unwrap()), (Some(5), Value::NULL));
    });
    drop(node);
    arena.collect();
    assert_eq!(arena.objects(), 0);
    let mut other = Arena::new(1 << 20, 1);
    assert_eq!(other.mutate(|mc| five.get(mc).err()), Some(ForeignRoot));
}

#[test]
fn handles_keep_objects_across_collections_and_moves() {
    let mut arena = Arena::new(1 << 20, 1);
    let handle = arena.mutate(|mc| {
        let tail = Node::new(mc, 2, None).unwrap();
        Handle::new(mc, Value::object(mc, Node::new(mc, 1, Some(tail)).unwrap())).unwrap()
    });
    assert!(handle.is_object());
    arena.collect_minor();
    arena.set_evacuate_all(true);
    arena.collect();
    arena.collect();
    assert_eq!((arena.objects(), arena.handles()), (2, 1));
    arena.mutate(|mc| {
        let head = handle.get(mc).unwrap().downcast::<Node>(mc).unwrap();
        assert_eq!((head.n(mc), head.next(mc).map(|n| n.n(mc))), (1, Some(2)));
    });
}

/// A clone has a slot of its own, so the object lives until every handle of it is dropped. A dropped handle's slot is used again, so the table does not grow.
#[test]
fn a_handle_and_its_clones_are_dropped_one_by_one() {
    let mut arena = Arena::new(1 << 20, 1);
    let handle = arena.mutate(|mc| {
        let node = Node::new(mc, 1, None).unwrap();
        let watch = Watch::new(mc, Some(node)).unwrap();
        mc.set_root(0, Value::object(mc, watch));
        Handle::new(mc, Value::object(mc, node)).unwrap()
    });
    fn alive(arena: &mut Arena) -> bool {
        arena.mutate(|mc| mc.root(0).downcast::<Watch>(mc).unwrap().target(mc).is_some())
    }
    let clone = handle.clone();
    assert_eq!(arena.handles(), 2);
    drop(handle);
    arena.collect();
    assert!(alive(&mut arena) && arena.handles() == 1, "a clone still holds it");
    drop(clone);
    assert_eq!(arena.handles(), 0);
    arena.collect();
    assert!(!alive(&mut arena));
    // The two slots are free. Handles that come and go take them again and again.
    let before = arena.root_table_bytes();
    for round in 0..10_000 {
        let (first, second) = arena.mutate(|mc| {
            let first = Handle::new(mc, Value::object(mc, Node::new(mc, round, None).unwrap())).unwrap();
            (first.clone(), first)
        });
        assert_eq!(arena.handles(), 2);
        arena.mutate(|mc| assert_eq!(first.get(mc).unwrap().downcast::<Node>(mc).unwrap().n(mc), round));
        drop((first, second));
    }
    arena.collect();
    assert_eq!((arena.handles(), arena.objects()), (0, 1));
    assert_eq!(arena.root_table_bytes(), before, "the table kept its two slots");
}

/// A value that is not an object is kept in the handle, and takes no slot. Handles are equal if they keep the same value.
#[test]
fn handles_hold_values_that_are_no_objects_themselves() {
    let mut arena = Arena::new(1 << 20, 1);
    let (node, same, other, five, nil) = arena.mutate(|mc| {
        let node = Value::object(mc, Node::new(mc, 7, None).unwrap());
        let other = Value::object(mc, Node::new(mc, 7, None).unwrap());
        (Handle::new(mc, node).unwrap(), Handle::new(mc, node).unwrap(), Handle::new(mc, other).unwrap(), Handle::new(mc, Value::fixnum(5).unwrap()).unwrap(), Handle::new(mc, Value::NULL).unwrap())
    });
    assert_eq!(arena.handles(), 3);
    assert!(!five.is_object() && !nil.is_object());
    // The comparison is by identity, and holds after the objects have moved.
    arena.set_evacuate_all(true);
    arena.collect();
    assert!(node == same && node != other && node == node.clone() && five == five.clone() && five != nil && five != node);
    arena.mutate(|mc| {
        assert_eq!((five.get(mc).unwrap().as_fixnum(), nil.get(mc).unwrap()), (Some(5), Value::NULL));
        assert_eq!(node.get(mc).unwrap(), same.get(mc).unwrap());
    });
    // A handle of an object belongs to its arena. A value that is no object is the same in every arena.
    let mut second = Arena::new(1 << 20, 1);
    let foreign = second.mutate(|mc| Handle::new(mc, Value::object(mc, Node::new(mc, 7, None).unwrap())).unwrap());
    assert!(foreign != node);
    second.mutate(|mc| {
        assert_eq!((node.get(mc).err(), five.get(mc).map(|value| value.as_fixnum())), (Some(ForeignRoot), Ok(Some(5))));
    });
    arena.mutate(|mc| assert_eq!(foreign.get(mc).err(), Some(ForeignRoot)));
}

/// Handles are made, cloned and dropped while the arena collects in steps and moves its objects. Every handle that is alive reads the object it was made for.
#[test]
fn handles_survive_collections_in_steps() {
    let mut arena = Arena::new(1 << 18, 1);
    arena.set_evacuate_all(true);
    let mut held: Vec<(Handle, i64)> = Vec::new();
    let mut seed = 0x9E37_79B9_7F4A_7C15u64;
    for round in 0..20_000i64 {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let choice = (seed >> 33) % 8;
        arena
            .step(|mc| {
                // Garbage, so that collections run all the time.
                for filler in 0..8 {
                    Node::new(mc, filler, None).unwrap();
                }
                if choice < 4 {
                    held.push((Handle::new(mc, Value::object(mc, Node::new(mc, round, None).unwrap())).unwrap(), round));
                }
                for (handle, number) in &held {
                    assert_eq!(handle.get(mc).unwrap().downcast::<Node>(mc).unwrap().n(mc), *number, "round {round}");
                }
            })
            .unwrap();
        // Outside a step: a clone of a handle, and the drop of one.
        if choice == 4 && !held.is_empty() {
            let index = (seed >> 40) as usize % held.len();
            let copy = (held[index].0.clone(), held[index].1);
            held.push(copy);
        }
        if choice >= 5 && !held.is_empty() {
            let index = (seed >> 40) as usize % held.len();
            held.swap_remove(index);
        }
        if held.len() > 200 {
            held.truncate(100);
        }
        assert_eq!(arena.handles(), held.len());
    }
    let (major, minor) = arena.collections();
    assert!(major + minor > 10, "{major} major and {minor} minor collections");
    held.clear();
    arena.collect();
    assert_eq!((arena.handles(), arena.objects()), (0, 0));
}

/// A weak handle does not keep its object alive. It gives a handle while the object lives, follows the object when it moves, and holds nothing once the object is freed.
#[test]
fn weak_handles_do_not_keep_objects() {
    let mut arena = Arena::new(1 << 20, 1);
    let (handle, weak, five) = arena.mutate(|mc| {
        let handle = Handle::new(mc, Value::object(mc, Node::new(mc, 9, None).unwrap())).unwrap();
        let weak = handle.downgrade();
        (handle, weak, Handle::new(mc, Value::fixnum(5).unwrap()).unwrap().downgrade())
    });
    let second = weak.clone();
    arena.collect_minor();
    arena.set_evacuate_all(true);
    arena.collect();
    assert_eq!((arena.objects(), arena.handles()), (1, 1));
    arena.mutate(|mc| {
        assert_eq!(weak.get(mc).unwrap().and_then(|value| value.downcast::<Node>(mc)).map(|node| node.n(mc)), Some(9));
        assert_eq!(weak.get(mc).unwrap(), Some(handle.get(mc).unwrap()));
    });
    // A handle made from the weak one keeps the object when the first handle is dropped.
    let again = weak.upgrade().unwrap();
    assert!(again == handle && arena.handles() == 2);
    drop(handle);
    arena.collect();
    assert_eq!(arena.objects(), 1);
    drop(again);
    assert_eq!(arena.handles(), 0);
    // Only weak handles are left: a minor collection frees a young object, and a major one an old object.
    arena.collect();
    assert_eq!(arena.objects(), 0);
    assert!(weak.upgrade().is_none() && second.upgrade().is_none());
    arena.mutate(|mc| assert_eq!((weak.get(mc), second.get(mc)), (Ok(None), Ok(None))));
    let young = arena.mutate(|mc| Handle::new(mc, Value::object(mc, Node::new(mc, 3, None).unwrap())).unwrap().downgrade());
    arena.collect_minor();
    assert!(young.upgrade().is_none());
    // A value that is no object never dies.
    assert_eq!(arena.mutate(|mc| five.upgrade().unwrap().get(mc).unwrap().as_fixnum()), Some(5));
    let mut other = Arena::new(1 << 20, 1);
    let foreign = other.mutate(|mc| Handle::new(mc, Value::object(mc, Node::new(mc, 1, None).unwrap())).unwrap());
    assert_eq!(arena.mutate(|mc| foreign.downgrade().get(mc).err()), Some(ForeignRoot));
}

/// The case that a weak handle is for: an object that owns the handle of something that holds the object. With a handle the two are never freed. With a weak handle they are.
#[test]
fn a_weak_handle_breaks_a_cycle_through_the_roots() {
    let mut arena = Arena::new(1 << 20, 1);
    // `owner` stands for a table. `owned` stands for a host function that the table holds, whose Rust code keeps a handle of the table.
    let (strong, weak) = arena.mutate(|mc| {
        let owner = Node::new(mc, 1, None).unwrap();
        let other = Node::new(mc, 2, None).unwrap();
        (Handle::new(mc, Value::object(mc, owner)).unwrap(), Handle::new(mc, Value::object(mc, other)).unwrap().downgrade())
    });
    arena.collect();
    arena.collect();
    // The handle keeps its object, though nothing in the arena refers to it. The weak handle's object is gone.
    assert_eq!((arena.objects(), weak.upgrade().is_none()), (1, true));
    drop(strong);
    arena.collect();
    assert_eq!(arena.objects(), 0);
}

