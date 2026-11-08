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
    let alive = |arena: &mut Arena| arena.mutate(|mc| mc.root(0).downcast::<Watch>(mc).unwrap().target(mc).is_some());
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
        (node, ValueRoot::new(mc, Value::fixnum(5).unwrap()).unwrap(), ValueRoot::new(mc, Value::NIL).unwrap())
    });
    arena.set_evacuate_all(true);
    arena.collect();
    assert_eq!(arena.objects(), 1);
    arena.mutate(|mc| {
        assert_eq!(node.get(mc).unwrap().downcast::<Node>(mc).unwrap().n(mc), 7);
        assert_eq!((five.get(mc).unwrap().as_fixnum(), nil.get(mc).unwrap()), (Some(5), Value::NIL));
    });
    drop(node);
    arena.collect();
    assert_eq!(arena.objects(), 0);
    let mut other = Arena::new(1 << 20, 1);
    assert_eq!(other.mutate(|mc| five.get(mc).err()), Some(ForeignRoot));
}
