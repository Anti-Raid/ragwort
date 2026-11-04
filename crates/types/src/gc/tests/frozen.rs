use std::cell::Cell;
use std::rc::Rc;

use super::*;

objects! {
    kind Kind;
    struct Text { chars: Frozen<Box<[u8]>> }
    struct Wide { units: Frozen<Box<[u32]>>, tag: u64 }
    struct Named { name: Frozen<String> }
    struct Dropper { counted: Frozen<Counted> }
    struct Pair { car: Value, cdr: Value }
}

/// Counts its drops.
struct Counted(Rc<Cell<usize>>);

impl Drop for Counted {
    fn drop(&mut self) {
        self.0.set(self.0.get() + 1);
    }
}

/// `s`'s bytes, charged as they'd be charged in the region.
fn bytes<'gc>(mc: &Mutation<'gc>, s: &str) -> FrozenRef<'gc, Box<[u8]>> {
    mc.frozen_owning(Box::from(s.as_bytes()), s.len()).unwrap()
}

fn text<'gc>(mc: &Mutation<'gc>, s: &str) -> Gc<'gc, Text> {
    Text::new(mc, bytes(mc, s)).unwrap()
}

fn chars<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> &'gc [u8] {
    v.downcast::<Text>(mc).unwrap().chars(mc).unwrap()
}

fn churn(mc: &Mutation<'_>) {
    for _ in 0..200_000 {
        Pair::new(mc, Value::NIL, Value::NIL).unwrap();
    }
}

fn list<'gc>(mc: &Mutation<'gc>, items: impl IntoIterator<Item = Value<'gc>>) -> Value<'gc> {
    let items: Vec<_> = items.into_iter().collect();
    items.into_iter().rev().fold(Value::NIL, |tail, v| Value::object(mc, Pair::new(mc, v, tail).unwrap()))
}

fn each<'gc>(mc: &Mutation<'gc>, mut list: Value<'gc>) -> Vec<Value<'gc>> {
    let mut out = Vec::new();
    while let Some(p) = list.downcast::<Pair>(mc) {
        out.push(p.car(mc));
        list = p.cdr(mc);
    }
    out
}

/// Frozen values read back the same through collections that move their objects.
#[test]
fn frozen_values_read_back_through_collections() {
    let mut arena = Arena::new(16 << 20, 1);
    arena.mutate(|mc| {
        let wide = Wide::new(mc, mc.frozen(Box::from([0x1F600, 7, 0x10FFFF])).unwrap(), 9).unwrap();
        let named = Named::new(mc, mc.frozen(String::from("frozen")).unwrap()).unwrap();
        let items = [text(mc, "hello"), text(mc, ""), text(mc, &"long ".repeat(1000))].map(|t| Value::object(mc, t));
        let all: Vec<_> = items.into_iter().chain([Value::object(mc, wide), Value::object(mc, named)]).collect();
        mc.set_root(0, list(mc, all));
    });
    let check = |arena: &mut Arena| {
        arena.mutate(|mc| {
            let items = each(mc, mc.root(0));
            let texts: Vec<_> = items[..3].iter().map(|&v| chars(mc, v).to_vec()).collect();
            assert_eq!(texts, [b"hello".to_vec(), vec![], "long ".repeat(1000).into_bytes()]);
            let wide = items[3].downcast::<Wide>(mc).unwrap();
            assert_eq!((wide.units(mc).map(|u| &u[..]), wide.tag(mc)), (Some(&[0x1F600, 7, 0x10FFFF][..]), 9));
            assert_eq!(items[4].downcast::<Named>(mc).unwrap().name(mc).map(String::as_str), Some("frozen"));
        });
    };
    check(&mut arena);
    arena.collect_minor();
    arena.mutate(churn);
    check(&mut arena);
    arena.set_evacuate_all(true);
    arena.collect();
    arena.mutate(churn);
    check(&mut arena);
    assert_eq!(arena.frozen_values(), 5);
}

/// A minor collection frees the young frozen values whose objects died, and those never stored,
/// and a major one the old ones, refunding what they were charged.
#[test]
fn dead_frozen_values_are_freed_and_refunded() {
    let mut arena = Arena::new(16 << 20, 1);
    arena.mutate(|mc| {
        let kept: Vec<_> = (0..100).map(|i| Value::object(mc, text(mc, &format!("kept {i}")))).collect();
        mc.set_root(0, list(mc, kept));
        for i in 0..1000 {
            text(mc, &format!("garbage {i} {}", "x".repeat(i)));
            bytes(mc, &"y".repeat(64));
        }
    });
    assert_eq!(arena.frozen_values(), 2100);
    let (peak, charged) = (arena.used(), arena.meta.frozen.charged());
    assert!(charged > 1000 * 1000 / 2, "{charged}");
    arena.collect_minor();
    assert_eq!(arena.frozen_values(), 100);
    arena.mutate(|mc| mc.set_root(0, list(mc, each(mc, mc.root(0)).into_iter().step_by(2))));
    arena.collect_minor();
    assert_eq!(arena.frozen_values(), 100, "old values outlive minor collections");
    arena.collect();
    assert_eq!(arena.frozen_values(), 50);
    arena.mutate(|mc| mc.set_root(0, Value::NIL));
    arena.collect();
    arena.collect();
    assert_eq!((arena.frozen_values(), arena.meta.frozen.charged()), (0, 0));
    // The table of frozen values is charged once a collection ends, so it's left out of the peak.
    let table = arena.meta.frozen.table_bytes();
    assert!(arena.used() + charged <= peak + table + (16 << 10), "{} charged after freeing, {peak} at the peak", arena.used());
}

/// A young frozen value stored into an old object survives a minor collection, which doesn't
/// trace the object again, and one stored into an object already traced survives the cycle.
#[test]
fn frozen_values_stored_into_marked_objects_survive() {
    let mut arena = Arena::new(16 << 20, 1);
    arena.mutate(|mc| mc.set_root(0, list(mc, (0..1000).map(|_| Value::object(mc, text(mc, "old"))))));
    arena.collect();
    arena.mutate(|mc| {
        for (i, t) in each(mc, mc.root(0)).into_iter().enumerate() {
            t.downcast::<Text>(mc).unwrap().set_chars(mc, bytes(mc, &format!("young {i}")));
        }
    });
    arena.collect_minor();
    arena.mutate(churn);
    arena.mutate(|mc| {
        for (i, t) in each(mc, mc.root(0)).into_iter().enumerate() {
            assert_eq!(chars(mc, t), format!("young {i}").as_bytes());
        }
    });
    // While marking, in slices: values move between texts, many of them already traced.
    arena.set_stress(Some(4 << 10));
    for round in 0..40 {
        arena
            .step(|mc| {
                let texts: Vec<_> = each(mc, mc.root(0)).into_iter().map(|t| t.downcast::<Text>(mc).unwrap()).collect();
                for (i, t) in texts.iter().enumerate().skip(round % 7).step_by(7) {
                    t.set_chars(mc, bytes(mc, &format!("round {round} {i}")));
                }
            })
            .unwrap();
    }
    arena.set_stress(None);
    arena.collect();
    arena.collect();
    arena.mutate(churn);
    arena.mutate(|mc| {
        for t in each(mc, mc.root(0)) {
            let chars = chars(mc, t);
            assert!(chars.starts_with(b"round") || chars.starts_with(b"young"), "{:?}", String::from_utf8_lossy(chars));
        }
    });
    assert_eq!(arena.frozen_values(), 1000);
}

#[test]
fn frozen_values_drop_once_freed() {
    let drops = Rc::new(Cell::new(0));
    let mut arena = Arena::new(4 << 20, 1);
    arena.mutate(|mc| {
        let kept = Dropper::new(mc, mc.frozen(Counted(drops.clone())).unwrap()).unwrap();
        mc.set_root(0, Value::object(mc, kept));
        for _ in 0..10 {
            Dropper::new(mc, mc.frozen(Counted(drops.clone())).unwrap()).unwrap();
        }
        assert!(mc.root(0).downcast::<Dropper>(mc).unwrap().counted(mc).is_some());
    });
    assert_eq!(drops.get(), 0);
    arena.collect_minor();
    assert_eq!(drops.get(), 10);
    arena.mutate(|mc| mc.set_root(0, Value::NIL));
    arena.collect();
    assert_eq!(drops.get(), 11);
}

#[test]
fn frozen_values_fail_as_allocations_do() {
    let mut arena = Arena::new(1 << 20, 1);
    arena.mutate(|mc| {
        assert_eq!(mc.frozen_owning((), 2 << 20).err(), Some(OutOfMemory));
        assert_eq!(mc.frozen_owning((), usize::MAX).err(), Some(OutOfMemory));
    });
    arena.fail_after(Some(0));
    assert!(arena.step(|mc| mc.frozen(8u64).map(drop)).is_err());
    arena.fail_after(None);
    assert_eq!(arena.frozen_values(), 0);
}
