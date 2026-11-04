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
