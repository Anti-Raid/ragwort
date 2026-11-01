use std::collections::HashSet;

use super::*;
use crate::{Arena, objects};

objects! {
    kind Types;
    /// A symbol, named by a number, with its name's hash.
    struct Sym { n: i64, hash: u64 }
    struct Pair { car: Value, cdr: Value }
}

fn churn(mc: &Mutation<'_>) {
    for _ in 0..200_000 {
        Pair::new(mc, Value::NIL, Value::NIL).unwrap();
    }
}

fn fix<'gc>(n: i64) -> Value<'gc> {
    Value::fixnum(n).unwrap()
}

/// A hash of a number, made weak by `bits` to force collisions.
fn hash(n: i64, bits: u64) -> u64 {
    (n as u64).wrapping_mul(0x2545_F491_4F6C_DD1D).rotate_left(17) & bits
}

fn table<'gc, K: Kind>(mc: &Mutation<'gc>, root: usize) -> Table<'gc, K> {
    Table::of(mc.root(root).downcast::<TableHead>(mc).unwrap())
}

type Map<'gc> = Table<'gc, Strong>;

fn get<'gc>(mc: &Mutation<'gc>, t: Map<'gc>, n: i64, bits: u64) -> Option<i64> {
    t.get(mc, hash(n, bits), |k| Ok::<_, OutOfMemory>(k == fix(n))).unwrap().map(|v| v.as_fixnum().unwrap())
}

fn insert<'gc>(mc: &Mutation<'gc>, t: Map<'gc>, n: i64, v: i64, bits: u64) -> Option<i64> {
    t.insert(mc, hash(n, bits), |k| Ok::<_, OutOfMemory>(k == fix(n)), fix(n), fix(v)).unwrap().map(|v| v.as_fixnum().unwrap())
}

fn remove<'gc>(mc: &Mutation<'gc>, t: Map<'gc>, n: i64, bits: u64) -> Option<i64> {
    let gone = t.remove(mc, hash(n, bits), |(k, _)| Ok::<_, OutOfMemory>(k == fix(n))).unwrap();
    gone.map(|(_, v)| v.as_fixnum().unwrap())
}

/// Inserting, replacing and removing, with hashes that collide more and more, and every entry
/// found where a probe reaches it after each rebuild.
#[test]
fn maps_find_what_they_hold() {
    for bits in [u64::MAX, 0xFF, 0b110, 0] {
        let mut arena = Arena::new(8 << 20, 1);
        arena.mutate(|mc| {
            let t = Map::new(mc).unwrap();
            mc.set_root(0, Value::object(mc, t.head()));
            for n in 0..2000 {
                assert_eq!(insert(mc, t, n, n * 10, bits), None);
            }
            for n in (0..2000).step_by(3) {
                assert_eq!(insert(mc, t, n, -n, bits), Some(n * 10));
            }
            for n in (0..2000).step_by(2) {
                assert_eq!(remove(mc, t, n, bits), Some(if n % 3 == 0 { -n } else { n * 10 }));
            }
            assert_eq!(remove(mc, t, 0, bits), None);
            assert_eq!(t.count(mc), 1000);
            assert!(t.capacity(mc).is_power_of_two() && t.head().used(mc) as usize * 4 <= t.capacity(mc) * 3);
        });
        arena.set_evacuate_all(true);
        arena.collect();
        arena.mutate(churn);
        arena.mutate(|mc| {
            let t = table::<Strong>(mc, 0);
            for n in 0..2000 {
                let want = (n % 2 == 1).then(|| if n % 3 == 0 { -n } else { n * 10 });
                assert_eq!(get(mc, t, n, bits), want, "{bits:#x}: {n}");
            }
            let keys: HashSet<_> = t.entries(mc).map(|(k, _)| k.as_fixnum().unwrap()).collect();
            assert_eq!(keys, (1..2000).step_by(2).collect());
        });
    }
}

/// Entries made and removed over and over don't grow the table past what the live ones need,
/// and a key that comes and goes takes its old slot back without rebuilding.
#[test]
fn churn_leaves_the_table_small() {
    let mut arena = Arena::new(8 << 20, 1);
    arena.mutate(|mc| {
        let t = Map::new(mc).unwrap();
        for n in 0..100 {
            insert(mc, t, n, n, u64::MAX);
        }
        for round in 0..30 {
            for i in 0..500 {
                let n = 1000 + round * 500 + i;
                insert(mc, t, n, n, u64::MAX);
                remove(mc, t, n, u64::MAX);
            }
            assert!(t.capacity(mc) <= 1024, "{} slots", t.capacity(mc));
        }
        let (used, keys) = (t.head().used(mc), t.head().keys(mc));
        for _ in 0..1000 {
            insert(mc, t, -1, 0, u64::MAX);
            remove(mc, t, -1, u64::MAX);
        }
        assert_eq!(t.head().used(mc), used + 1);
        assert_eq!(t.head().keys(mc), keys, "rebuilt");
        assert!((0..100).all(|n| get(mc, t, n, u64::MAX) == Some(n)));
    });
}

/// An identity table's object keys move in an evacuating collection, and it finds them again.
#[test]
fn identity_tables_rehash_after_objects_move() {
    let mut arena = Arena::new(16 << 20, 2);
    arena.mutate(|mc| {
        let t = Table::<Strong>::new_eq(mc).unwrap();
        let keys = crate::GcVec::<slot::Value>::new(mc).unwrap();
        for n in 0..3000 {
            churn_a_little(mc);
            let key = Value::object(mc, Pair::new(mc, fix(n), Value::NIL).unwrap());
            keys.push(mc, key).unwrap();
            t.insert_eq(mc, key, fix(n)).unwrap();
        }
        assert_eq!(t.insert_eq(mc, fix(7), fix(-7)).unwrap(), None);
        mc.set_root(0, Value::object(mc, t.head()));
        mc.set_root(1, Value::object(mc, keys.head()));
    });
    for round in 0..3 {
        arena.set_evacuate_all(true);
        arena.collect();
        arena.mutate(churn);
        arena.mutate(|mc| {
            let t = table::<Strong>(mc, 0);
            let keys = crate::GcVec::<slot::Value>::of(mc.root(1).downcast(mc).unwrap());
            for (n, key) in keys.iter(mc).enumerate() {
                let want = (round < 2 || n % 2 == 1).then(|| fix(n as i64));
                assert_eq!(t.get_eq(mc, key).unwrap(), want, "round {round}: key {n}");
            }
            assert_eq!(t.get_eq(mc, fix(7)).unwrap(), Some(fix(-7)));
            let fresh = Value::object(mc, Pair::new(mc, Value::NIL, Value::NIL).unwrap());
            assert_eq!(t.get_eq(mc, fresh).unwrap(), None);
            if round == 1 {
                for key in keys.iter(mc).step_by(2) {
                    assert!(t.remove_eq(mc, key).unwrap().is_some());
                }
            }
        });
    }
    arena.mutate(|mc| assert_eq!(table::<Strong>(mc, 0).count(mc), 1501));
}

fn churn_a_little(mc: &Mutation<'_>) {
    for _ in 0..7 {
        Pair::new(mc, Value::NIL, Value::NIL).unwrap();
    }
}

/// An ephemeron table's entry lasts while its key is held elsewhere, even when its value refers
/// to the key.
#[test]
fn ephemeron_entries_die_with_their_keys() {
    let mut arena = Arena::new(16 << 20, 2);
    arena.mutate(|mc| {
        let t = Table::<Ephemerons>::new_eq(mc).unwrap();
        let held = crate::GcVec::<slot::Value>::new(mc).unwrap();
        for n in 0..2000 {
            let key = Value::object(mc, Pair::new(mc, fix(n), Value::NIL).unwrap());
            let value = Value::object(mc, Pair::new(mc, key, fix(n)).unwrap());
            t.insert_eq(mc, key, value).unwrap();
            if n % 4 == 0 {
                held.push(mc, key).unwrap();
            }
        }
        mc.set_root(0, Value::object(mc, t.head()));
        mc.set_root(1, Value::object(mc, held.head()));
    });
    arena.set_evacuate_all(true);
    arena.collect();
    arena.mutate(churn);
    arena.mutate(|mc| {
        let t = table::<Ephemerons>(mc, 0);
        assert_eq!(t.count(mc), 500);
        let held = crate::GcVec::<slot::Value>::of(mc.root(1).downcast(mc).unwrap());
        for key in held.iter(mc) {
            let value = t.get_eq(mc, key).unwrap().and_then(|v| v.downcast::<Pair>(mc)).unwrap();
            assert_eq!(value.car(mc), key);
        }
        for n in 0..1000 {
            let key = Value::object(mc, Pair::new(mc, fix(n), Value::NIL).unwrap());
            t.insert_eq(mc, key, Value::NIL).unwrap();
        }
        assert_eq!(t.count(mc), 1500);
        assert!(held.iter(mc).all(|key| t.get_eq(mc, key).unwrap().is_some()));
    });
}

fn intern<'gc>(mc: &Mutation<'gc>, t: Table<'gc, WeakObjects<Sym>>, n: i64, bits: u64) -> Gc<'gc, Sym> {
    let h = hash(n, bits);
    t.find_or_insert(mc, h, |s| Ok::<_, OutOfMemory>(s.n(mc) == n), || Sym::new(mc, n, h)).unwrap()
}

/// A weak table of symbols, as interning keeps them: one per name while it's held, gone once
/// nothing else holds it, and a dead one's name gets a new symbol.
#[test]
fn weak_objects_go_once_unreachable() {
    for bits in [u64::MAX, 0b110] {
        let mut arena = Arena::new(16 << 20, 2);
        arena.mutate(|mc| {
            let t = Table::<WeakObjects<Sym>>::new(mc).unwrap();
            let held = crate::GcVec::<slot::Member<Sym>>::new(mc).unwrap();
            for n in 0..1500 {
                let s = intern(mc, t, n, bits);
                assert_eq!(intern(mc, t, n, bits), s);
                if n % 3 == 2 {
                    held.push(mc, Some(s)).unwrap();
                }
            }
            mc.set_root(0, Value::object(mc, t.head()));
            mc.set_root(1, Value::object(mc, held.head()));
        });
        arena.set_evacuate_all(true);
        arena.collect();
        arena.mutate(churn);
        arena.mutate(|mc| {
            let t = table::<WeakObjects<Sym>>(mc, 0);
            assert_eq!(t.count(mc), 500);
            let held = crate::GcVec::<slot::Member<Sym>>::of(mc.root(1).downcast(mc).unwrap());
            for (i, s) in held.iter(mc).enumerate() {
                let s = s.unwrap();
                assert_eq!(s.n(mc), 3 * i as i64 + 2);
                assert_eq!(intern(mc, t, s.n(mc), bits), s, "{bits:#x}");
                assert!(t.contains_eq(mc, s).is_ok());
            }
            let fresh = intern(mc, t, 0, bits);
            assert!(!held.iter(mc).any(|s| s == Some(fresh)));
            assert_eq!(t.count(mc), 501);
        });
    }
}

/// A failed `make` or a failed rebuild adds nothing, and the table works after.
#[test]
fn failures_leave_the_table_as_it_was() {
    let mut arena = Arena::new(8 << 20, 1);
    arena.mutate(|mc| {
        let t = Map::new(mc).unwrap();
        mc.set_root(0, Value::object(mc, t.head()));
        for n in 0..6 {
            insert(mc, t, n, n, u64::MAX);
        }
        let made = t.find_or_insert(mc, hash(99, u64::MAX), |_| Ok(false), || Err(OutOfMemory));
        assert_eq!(made, Err(OutOfMemory));
        assert_eq!(get(mc, t, 99, u64::MAX), None);
    });
    // The seventh entry needs a rebuild, and its allocations are failed one at a time.
    for fail in 0..2 {
        arena.fail_after(Some(fail));
        let result = arena.step(|mc| {
            let t = table::<Strong>(mc, 0);
            t.insert(mc, hash(6, u64::MAX), |k| Ok::<_, OutOfMemory>(k == fix(6)), fix(6), fix(6)).map(drop)
        });
        assert!(matches!(result, Err(OutOfMemory) | Ok(Err(OutOfMemory))), "{fail}: {result:?}");
        arena.fail_after(None);
        arena.mutate(|mc| {
            let t = table::<Strong>(mc, 0);
            assert_eq!(t.count(mc), 6);
            assert!((0..6).all(|n| get(mc, t, n, u64::MAX) == Some(n)));
        });
    }
    arena.mutate(|mc| {
        let t = table::<Strong>(mc, 0);
        assert_eq!(insert(mc, t, 6, 6, u64::MAX), None);
        assert!((0..7).all(|n| get(mc, t, n, u64::MAX) == Some(n)));
    });
}

/// Probe keys damaged so no slot is unused: probes stop after a lap instead of looping, and an
/// insertion rebuilds.
#[test]
fn damaged_keys_end_probes() {
    let mut arena = Arena::new(4 << 20, 1);
    arena.mutate(|mc| {
        let t = Map::new(mc).unwrap();
        insert(mc, t, 1, 1, u64::MAX);
        t.head().keys(mc).unwrap().items(mc).fill(mc, 3);
        assert_eq!(get(mc, t, 2, u64::MAX), None);
        assert_eq!(insert(mc, t, 2, 2, u64::MAX), None);
        assert_eq!(get(mc, t, 2, u64::MAX), Some(2));
    });
}

/// A table read as the wrong kind holds nothing.
#[test]
fn the_wrong_kind_is_empty() {
    let mut arena = Arena::new(4 << 20, 1);
    arena.mutate(|mc| {
        let t = Map::new(mc).unwrap();
        insert(mc, t, 1, 1, u64::MAX);
        let wrong = Table::<Ephemerons>::of(t.head());
        assert_eq!(wrong.count(mc), 0);
        assert_eq!(wrong.get(mc, hash(1, u64::MAX), |_| Ok::<_, OutOfMemory>(true)), Ok(None));
    });
}
