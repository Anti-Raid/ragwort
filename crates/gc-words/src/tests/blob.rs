use std::cell::Cell;
use std::rc::Rc;

use super::*;

objects! {
    kind Kind;
    struct Text { chars: Blob<u8> }
    struct Wide { units: Blob<u32>, tag: u64 }
    struct Digits { digits: Blob<u64> }
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

fn text<'gc>(mc: &Mutation<'gc>, s: &str) -> Gc<'gc, Text> {
    let chars = mc.blob(s.len(), |u| {
        u.copy_from_slice(s.as_bytes());
        s.len()
    });
    Text::new(mc, chars.unwrap()).unwrap()
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

/// Blobs of each unit, and frozen values, read back the same through collections that move
/// their objects.
#[test]
fn blobs_read_back_through_collections() {
    let mut arena = Arena::new(16 << 20, 1);
    arena.mutate(|mc| {
        let wide = Wide::new(mc, mc.blob(3, |u: &mut [u32]| {
            u.copy_from_slice(&[0x1F600, 7, 0x10FFFF]);
            3
        }).unwrap(), 9).unwrap();
        let digits = Digits::new(mc, mc.blob(10, |d: &mut [u64]| {
            d[..4].copy_from_slice(&[1, 2, 3, u64::MAX]);
            4
        }).unwrap()).unwrap();
        let named = Named::new(mc, mc.frozen(String::from("frozen")).unwrap()).unwrap();
        let items = [text(mc, "hello"), text(mc, ""), text(mc, &"long ".repeat(1000))].map(|t| Value::object(mc, t));
        let all: Vec<_> = items.into_iter().chain([Value::object(mc, wide), Value::object(mc, digits), Value::object(mc, named)]).collect();
        mc.set_root(0, list(mc, all));
    });
    let check = |arena: &mut Arena| {
        arena.mutate(|mc| {
            let items = each(mc, mc.root(0));
            let texts: Vec<_> = items[..3].iter().map(|v| v.downcast::<Text>(mc).unwrap().chars(mc).to_vec()).collect();
            assert_eq!(texts, [b"hello".to_vec(), vec![], "long ".repeat(1000).into_bytes()]);
            let wide = items[3].downcast::<Wide>(mc).unwrap();
            assert_eq!((wide.units(mc), wide.tag(mc)), (&[0x1F600, 7, 0x10FFFF][..], 9));
            assert_eq!(items[4].downcast::<Digits>(mc).unwrap().digits(mc), [1, 2, 3, u64::MAX]);
            assert_eq!(items[5].downcast::<Named>(mc).unwrap().name(mc).map(String::as_str), Some("frozen"));
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
    assert_eq!(arena.blobs(), 6);
}

/// A minor collection frees the young blobs whose objects died, and those never stored, and a
/// major one the old ones, refunding what they were charged.
#[test]
fn dead_blobs_are_freed_and_refunded() {
    let mut arena = Arena::new(16 << 20, 1);
    arena.mutate(|mc| {
        let kept: Vec<_> = (0..100).map(|i| Value::object(mc, text(mc, &format!("kept {i}")))).collect();
        mc.set_root(0, list(mc, kept));
        for i in 0..1000 {
            text(mc, &format!("garbage {i} {}", "x".repeat(i)));
            mc.blob(64, |_: &mut [u8]| 64).unwrap();
        }
    });
    assert_eq!(arena.blobs(), 2100);
    let (peak, charged) = (arena.used(), arena.meta.blobs.charged());
    assert!(charged > 1000 * 1000 / 2, "{charged}");
    arena.collect_minor();
    assert_eq!(arena.blobs(), 100);
    arena.mutate(|mc| mc.set_root(0, list(mc, each(mc, mc.root(0)).into_iter().step_by(2))));
    arena.collect_minor();
    assert_eq!(arena.blobs(), 100, "old blobs outlive minor collections");
    arena.collect();
    assert_eq!(arena.blobs(), 50);
    arena.mutate(|mc| mc.set_root(0, Value::NIL));
    arena.collect();
    arena.collect();
    assert_eq!((arena.blobs(), arena.meta.blobs.charged()), (0, 0));
    // The table of blobs is charged once a collection ends, so it's left out of the peak.
    let table = arena.meta.blobs.table_bytes();
    assert!(arena.used() + charged <= peak + table + (16 << 10), "{} charged after freeing, {peak} at the peak", arena.used());
}

/// A young blob stored into an old object survives a minor collection, which doesn't trace the
/// object again, and one stored into an object already traced survives the cycle.
#[test]
fn blobs_stored_into_marked_objects_survive() {
    let mut arena = Arena::new(16 << 20, 1);
    arena.mutate(|mc| mc.set_root(0, list(mc, (0..1000).map(|_| Value::object(mc, text(mc, "old"))))));
    arena.collect();
    arena.mutate(|mc| {
        for (i, t) in each(mc, mc.root(0)).into_iter().enumerate() {
            let s = format!("young {i}");
            let chars = mc.blob(s.len(), |u| {
                u.copy_from_slice(s.as_bytes());
                s.len()
            });
            t.downcast::<Text>(mc).unwrap().set_chars(mc, chars.unwrap());
        }
    });
    arena.collect_minor();
    arena.mutate(churn);
    arena.mutate(|mc| {
        for (i, t) in each(mc, mc.root(0)).into_iter().enumerate() {
            assert_eq!(t.downcast::<Text>(mc).unwrap().chars(mc), format!("young {i}").as_bytes());
        }
    });
    // While marking, in slices: blobs move between texts, many of them already traced.
    arena.set_stress(Some(4 << 10));
    for round in 0..40 {
        arena
            .step(|mc| {
                let texts: Vec<_> = each(mc, mc.root(0)).into_iter().map(|t| t.downcast::<Text>(mc).unwrap()).collect();
                for (i, t) in texts.iter().enumerate().skip(round % 7).step_by(7) {
                    let s = format!("round {round} {i}");
                    let chars = mc.blob(s.len(), |u| {
                        u.copy_from_slice(s.as_bytes());
                        s.len()
                    });
                    t.set_chars(mc, chars.unwrap());
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
            let chars = t.downcast::<Text>(mc).unwrap().chars(mc);
            assert!(chars.starts_with(b"round") || chars.starts_with(b"young"), "{:?}", String::from_utf8_lossy(chars));
        }
    });
    assert_eq!(arena.blobs(), 1000);
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
fn blobs_fail_as_allocations_do() {
    let mut arena = Arena::new(1 << 20, 1);
    arena.mutate(|mc| {
        assert_eq!(mc.blob(2 << 20, |_: &mut [u8]| 0).err(), Some(OutOfMemory));
        assert_eq!(mc.blob(usize::MAX, |_: &mut [u64]| 0).err(), Some(OutOfMemory));
    });
    arena.fail_after(Some(0));
    assert!(arena.step(|mc| mc.blob(8, |_: &mut [u8]| 8).map(drop)).is_err());
    arena.fail_after(None);
    assert_eq!(arena.blobs(), 0);
}
