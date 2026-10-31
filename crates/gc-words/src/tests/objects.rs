use super::raw::Raw;
use super::*;

objects! {
    /// The types these tests use.
    kind Kind;

    struct Pair { car: Value, cdr: Value }
    /// A list cell with a typed link.
    struct Node { n: i64, next: Member<Node> }
    struct Words { a: u64, b: u32, c: f64, d: bool, e: i64 }
    struct Holder { target: Weak<Node>, keep: Member<Node> }
    struct Labelled { label: Host<String> }
    struct Cached { n: Value, cache: Ephemeron, after: u64 }
    struct Vector {} items Value
    struct Bytes { tag: u64 } items u64
    struct Table {} items Ephemeron
}

objects! {
    kind Later after Kind;
    struct Box1 { v: Value }
}

fn fixnum<'gc>(n: i64) -> Value<'gc> {
    Value::fixnum(n).unwrap()
}

#[test]
fn layouts_match_hand_written_descriptions() {
    let same = |a: &Desc, b: &Desc| {
        (a.fields, a.values, a.members, a.hosts, a.weaks, a.ephemerons, a.items)
            == (b.fields, b.values, b.members, b.hosts, b.weaks, b.ephemerons, b.items)
    };
    assert!(same(&Pair::DESC, &Desc::of::<Pair>(2).values(0b11)));
    assert!(same(&Node::DESC, &Desc::of::<Node>(2).members(0b10)));
    assert!(same(&Words::DESC, &Desc::of::<Words>(5)));
    assert!(same(&Holder::DESC, &Desc::of::<Holder>(2).weaks(0b01).members(0b10)));
    assert!(same(&Labelled::DESC, &Desc::of::<Labelled>(1).hosts(1)));
    assert!(same(&Cached::DESC, &Desc::of::<Cached>(4).values(1).ephemerons(0b10)));
    assert!(same(&Vector::DESC, &Desc::of::<Vector>(0).items(Items::Values)));
    assert!(same(&Bytes::DESC, &Desc::of::<Bytes>(1).items(Items::Words)));
    assert!(same(&Table::DESC, &Desc::of::<Table>(0).items(Items::Ephemerons)));
    assert_eq!(Cached::AFTER.index(), 3);
    assert_eq!(Cached::DESC.role(2), None, "an ephemeron's value has no field of its own");
}

#[test]
fn fields_read_back_what_was_written() {
    let mut arena = Arena::new(1 << 20, 4);
    arena.mutate(|mc| {
        let w = Words::new(mc, u64::MAX, 7, -0.5, true, -3).unwrap();
        assert_eq!((w.a(mc), w.b(mc), w.c(mc), w.d(mc), w.e(mc)), (u64::MAX, 7, -0.5, true, -3));
        w.set_b(mc, u32::MAX);
        w.set_d(mc, false);
        assert_eq!((w.b(mc), w.d(mc), w.a(mc)), (u32::MAX, false, u64::MAX));
        assert_eq!(w.get(mc, Words::E), -3);
        w.set(mc, Words::E, 9);
        assert_eq!(w.e(mc), 9);

        let tail = Node::new(mc, 2, None).unwrap();
        let head = Node::new(mc, 1, Some(tail)).unwrap();
        assert_eq!(head.next(mc), Some(tail));
        assert_eq!(tail.next(mc), None);
        head.set_next(mc, None);
        assert_eq!(head.next(mc), None);

        let label = mc.host(String::from("hi")).unwrap();
        let l = Labelled::new(mc, Some(label)).unwrap();
        assert_eq!(l.label(mc).unwrap().get(mc).as_deref().map(String::as_str), Some("hi"));
        l.set_label(mc, None);
        assert!(l.label(mc).is_none());

        let c = Cached::new(mc, fixnum(1), (Value::NIL, fixnum(2)), 3).unwrap();
        assert_eq!(c.cache(mc), Some((Value::NIL, fixnum(2))));
        assert_eq!((c.n(mc), c.after(mc)), (fixnum(1), 3));
    });
}

#[test]
fn objects_survive_collections_and_evacuation() {
    let mut arena = Arena::new(16 << 20, 4);
    arena.mutate(|mc| {
        let mut list = None;
        for i in 0..10_000 {
            list = Some(Node::new(mc, i, list).unwrap());
            Pair::new(mc, fixnum(i), Value::NIL).unwrap();
        }
        mc.set_root(0, Value::object(mc, list.unwrap()));
        let v = Vector::new(mc, 100, Value::NIL).unwrap();
        mc.set_root(1, Value::object(mc, v));
    });
    arena.collect_minor();
    arena.set_evacuate_all(true);
    arena.collect();
    arena.mutate(|mc| {
        let v = mc.root(1).downcast::<Vector>(mc).unwrap();
        for i in 0..100 {
            v.items(mc).set(mc, i, Value::object(mc, Pair::new(mc, fixnum(i as i64), Value::NIL).unwrap()));
        }
    });
    arena.collect();
    arena.mutate(|mc| {
        let (mut sum, mut cur) = (0, mc.root(0).downcast::<Node>(mc));
        while let Some(n) = cur {
            sum += n.n(mc);
            cur = n.next(mc);
        }
        assert_eq!(sum, 10_000 * 9_999 / 2);
        let v = mc.root(1).downcast::<Vector>(mc).unwrap();
        let cars: i64 = (0..100).map(|i| v.items(mc).get(i).downcast::<Pair>(mc).unwrap().car(mc).as_fixnum().unwrap()).sum();
        assert_eq!(cars, 99 * 100 / 2);
    });
}

#[test]
fn typed_stores_while_marking_take_the_barrier() {
    let mut arena = Arena::new(16 << 20, 2);
    arena.mutate(|mc| {
        let holder = Holder::new(mc, None, None).unwrap();
        mc.set_root(0, Value::object(mc, holder));
        let mut list = None;
        for i in 0..50_000 {
            list = Some(Node::new(mc, i, list).unwrap());
        }
        mc.set_root(1, Value::object(mc, list.unwrap()));
    });
    arena.collect();
    arena.collect_slice(4096);
    assert_eq!(arena.phase(), Phase::Marking);
    arena.mutate(|mc| {
        let holder = mc.root(0).downcast::<Holder>(mc).unwrap();
        holder.set_keep(mc, Some(Node::new(mc, 42, None).unwrap()));
    });
    arena.collect();
    arena.collect();
    arena.mutate(|mc| {
        let holder = mc.root(0).downcast::<Holder>(mc).unwrap();
        assert_eq!(holder.keep(mc).map(|n| n.n(mc)), Some(42));
    });
}

#[test]
fn weak_fields_clear_when_their_target_dies() {
    let mut arena = Arena::new(1 << 20, 2);
    arena.mutate(|mc| {
        let kept = Node::new(mc, 1, None).unwrap();
        let dies = Node::new(mc, 2, None).unwrap();
        let a = Holder::new(mc, Some(kept), Some(kept)).unwrap();
        let b = Holder::new(mc, Some(dies), None).unwrap();
        mc.set_root(0, Value::object(mc, a));
        mc.set_root(1, Value::object(mc, b));
    });
    arena.collect();
    arena.mutate(|mc| {
        let a = mc.root(0).downcast::<Holder>(mc).unwrap();
        let b = mc.root(1).downcast::<Holder>(mc).unwrap();
        assert_eq!(a.target(mc).map(|n| n.n(mc)), Some(1));
        assert_eq!(b.target(mc), None);
    });
}

#[test]
fn word_and_ephemeron_items() {
    let mut arena = Arena::new(1 << 20, 2);
    arena.mutate(|mc| {
        let bytes = Bytes::new(mc, 5, 4, u64::MAX).unwrap();
        bytes.items(mc).set(mc, 1, 17);
        assert_eq!((0..4).map(|i| bytes.items(mc).get(i)).collect::<Vec<_>>(), [u64::MAX, 17, u64::MAX, u64::MAX]);
        assert_eq!(bytes.tag(mc), 5);
        mc.set_root(0, Value::object(mc, bytes));

        let table = Table::new(mc, 3).unwrap();
        assert_eq!(table.len(mc), 6);
        assert_eq!(table.entry(mc, 2), None);
        let key = Value::object(mc, Pair::new(mc, Value::NIL, Value::NIL).unwrap());
        table.set_entry(mc, 0, key, fixnum(10));
        table.set_entry(mc, 1, Value::object(mc, Pair::new(mc, Value::NIL, Value::NIL).unwrap()), fixnum(20));
        mc.set_root(1, Value::object(mc, table));
        let keeper = Pair::new(mc, key, Value::NIL).unwrap();
        mc.root(0).downcast::<Bytes>(mc).unwrap().set_tag(mc, 6);
        let v = Vector::new(mc, 1, Value::object(mc, keeper)).unwrap();
        let held = Pair::new(mc, Value::object(mc, v), mc.root(0)).unwrap();
        mc.set_root(0, Value::object(mc, held));
    });
    arena.collect();
    arena.mutate(|mc| {
        let table = mc.root(1).downcast::<Table>(mc).unwrap();
        assert_eq!(table.entry(mc, 0).map(|(_, v)| v), Some(fixnum(10)));
        assert_eq!(table.entry(mc, 1), None);
        let bytes = mc.root(0).downcast::<Pair>(mc).unwrap().cdr(mc).downcast::<Bytes>(mc).unwrap();
        assert_eq!((bytes.tag(mc), bytes.items(mc).get(1)), (6, 17));
    });
}

#[test]
fn kinds_tell_the_group_types_apart() {
    let mut arena = Arena::new(1 << 20, 1);
    arena.mutate(|mc| {
        let p = Pair::new(mc, Value::NIL, Value::NIL).unwrap();
        let n = Node::new(mc, 1, None).unwrap();
        let t = Table::new(mc, 1).unwrap();
        let b = Box1::new(mc, Value::NIL).unwrap();
        let s = Segment::new(mc, 4).unwrap();
        assert_eq!(Kind::of(Value::object(mc, p)), Some(Kind::Pair(p)));
        assert_eq!(Kind::of(Value::object(mc, n)), Some(Kind::Node(n)));
        assert_eq!(Kind::of(Value::object(mc, t)), Some(Kind::Table(t)));
        assert_eq!(Kind::of(Value::object(mc, b)), None);
        assert_eq!(Later::of(Value::object(mc, b)), Some(Later::Box1(b)));
        assert_eq!(Later::of(Value::object(mc, p)), None);
        assert_eq!(Kind::of(Value::object(mc, s)), None);
        assert_eq!(Kind::of(Value::flonum(mc, 1e300).unwrap()), None);
        for v in [Value::NIL, Value::TRUE, fixnum(3), Value::inline_flonum(1.5).unwrap()] {
            assert_eq!(Kind::of(v), None);
        }
        let v = Kind::Node(n).value(mc);
        assert_eq!(v.downcast::<Node>(mc), Some(n));
    });
    assert_eq!((Kind::BASE, Kind::END, Later::BASE, Later::END), (FIRST_TYPE, FIRST_TYPE + 9, FIRST_TYPE + 9, FIRST_TYPE + 10));
}

/// Types numbered by the arena come down from the top, so they never take a group's numbers.
#[test]
fn unnumbered_types_stay_clear_of_groups() {
    struct Loose;
    impl Object for Loose {
        const DESC: Desc = Desc::of::<Loose>(1).values(1);
    }
    let mut arena = Arena::new(1 << 20, 2);
    arena.mutate(|mc| {
        let loose = mc.alloc::<Loose, 1>([Value::NIL.to_bits()]).unwrap();
        let p = Pair::new(mc, Value::object(mc, loose), Value::NIL).unwrap();
        mc.set_root(0, Value::object(mc, p));
        assert_eq!(Kind::of(Value::object(mc, loose)), None);
        assert!(Value::object(mc, loose).downcast::<Loose>(mc).is_some());
    });
    arena.collect();
    arena.mutate(|mc| {
        let p = mc.root(0).downcast::<Pair>(mc).unwrap();
        assert!(p.car(mc).downcast::<Loose>(mc).is_some());
    });
}

mod overlapping {
    use super::super::*;

    objects! {
        kind Clash;
        pub struct Clashing { v: Value }
    }
}

#[test]
#[should_panic(expected = "two types have type number")]
fn groups_that_overlap_panic() {
    let mut arena = Arena::new(1 << 20, 1);
    arena.mutate(|mc| {
        Pair::new(mc, Value::NIL, Value::NIL).unwrap();
        overlapping::Clashing::new(mc, Value::NIL).unwrap();
    });
}

#[test]
#[should_panic(expected = "isn't of type")]
fn member_reads_check_the_target_type() {
    let mut arena = Arena::new(1 << 20, 1);
    arena.mutate(|mc| {
        let pair = Pair::new(mc, Value::NIL, Value::NIL).unwrap();
        let node = Node::new(mc, 1, None).unwrap();
        // Raw words can point a member at the wrong type; the typed read catches it.
        node.set_word(mc, 1, pair.to_word());
        node.next(mc);
    });
}
