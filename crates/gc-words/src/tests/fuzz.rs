use std::collections::{HashMap, HashSet};

use super::*;
use crate::raw::Raw;
use crate::strings::{ExternalText, Str, Strings, concat, display, equal, equal_str, flatten, from_str, hash, len, substring};
use crate::table::{Ephemerons, Strong, TableHead, WeakObjects};

objects! {
    kind Kind;

    /// Items hold `id + i`, and the blob `5 * id + i`, so a moved or overwritten payload shows.
    struct Obj { id: i64, next: Member<Obj>, owned: Host<u64>, cache: Weak<Obj>, data: Blob<u64>, text: Value } items u64
    struct Holder {} items Member<Obj>
}

const SLOTS: usize = 16;
/// Root 0 holds the slots, 1 to 3 the ephemeron, weak-object and strong tables, and 4 the
/// segments the stack retired.
const ROOTS: usize = 5;
const SEGMENT: usize = WINDOW + 128;
const RETIRED: usize = 3;
const MAX_TEXT: usize = 1500;
const MAX_STRONG: usize = 24;
const SEED: u64 = 0x5eed;

struct Rng(u64);

impl Rng {
    fn below(&mut self, n: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 % n as u64) as usize
    }

    fn chance(&mut self, n: usize) -> bool {
        self.below(n) == 0
    }
}

#[derive(Clone)]
struct Model {
    next: Option<i64>,
    len: usize,
    blob: usize,
    host: bool,
    weak: Option<i64>,
    text: Option<String>,
}

/// What the arena should hold.
#[derive(Default)]
struct World {
    objs: HashMap<i64, Model>,
    slots: [Option<i64>; SLOTS],
    roots: Vec<(Root<Obj>, i64)>,
    eph: HashMap<i64, i64>,
    weak: HashSet<i64>,
    /// Keyed by the key string's characters.
    strong: HashMap<String, i64>,
    /// The stack's segment, slot by slot, and the segments it retired, as root 4 lists them.
    stack: Vec<Option<i64>>,
    retired: Vec<Vec<Option<i64>>>,
}

impl World {
    /// What the arena must keep: what the slots, roots, strong table and stack reach, and the
    /// values of ephemerons whose keys are kept.
    fn live(&self) -> HashSet<i64> {
        let stack = self.stack.iter().chain(self.retired.iter().flatten()).flatten();
        let roots = self.roots.iter().map(|r| &r.1);
        let mut pending: Vec<i64> = self.slots.iter().flatten().chain(roots).chain(self.strong.values()).chain(stack).copied().collect();
        let mut live = HashSet::new();
        while !pending.is_empty() {
            while let Some(x) = pending.pop() {
                if live.insert(x) {
                    pending.extend(self.objs[&x].next);
                }
            }
            pending.extend(self.eph.iter().filter(|&(k, v)| live.contains(k) && !live.contains(v)).map(|(_, &v)| v));
        }
        live
    }

    fn text(&self, slot: usize) -> Option<&String> {
        self.slots[slot].and_then(|x| self.objs[&x].text.as_ref())
    }
}

/// What a step found, for the model to check or follow.
enum Got {
    Done,
    Root(Root<Obj>),
    Id(Option<i64>),
    Flag(bool),
    Writes(Vec<(usize, Option<i64>)>),
    Retired(usize),
    Top(usize),
}

/// A weak reference may only ever read as its own target, and must while the target is reachable.
fn check_weak(got: Option<i64>, want: Option<i64>, live: &HashSet<i64>) {
    assert!(got.is_none() || got == want, "weak read {got:?}, expected {want:?}");
    if want.is_some_and(|w| live.contains(&w)) {
        assert_eq!(got, want, "weak ref to a reachable object was cleared");
    }
}

fn verify_obj<'gc>(
    mc: &Mutation<'gc>,
    objs: &HashMap<i64, Model>,
    live: &HashSet<i64>,
    mut cur: Option<Gc<'gc, Obj>>,
    mut want: Option<i64>,
    depth: usize,
) {
    for _ in 0..depth {
        assert_eq!(cur.map(|o| o.id(mc)), want);
        let (Some(o), Some(id)) = (cur, want) else { return };
        let m = &objs[&id];
        let items = o.items(mc);
        assert_eq!(items.len(), m.len, "obj {id}");
        let stride = (m.len / 7).max(1);
        assert!((0..m.len).step_by(stride).all(|i| items.get(i) == id as u64 + i as u64), "obj {id} payload");
        assert!(o.data(mc).iter().copied().eq((0..m.blob as u64).map(|i| 5 * id as u64 + i)), "obj {id} blob");
        let host = o.owned(mc).map(|h| *h.get(mc).unwrap());
        assert_eq!(host, m.host.then_some(id as u64 * 3), "obj {id} host");
        check_weak(o.cache(mc).map(|w| w.id(mc)), m.weak, live);
        cur = o.next(mc);
        want = m.next;
    }
}

fn verify_text<'gc>(h: &Strings<'_, 'gc>, o: Gc<'gc, Obj>, want: Option<&str>) {
    match (h.string(o.text(h.mutation())), want) {
        (None, None) => {}
        (Some(s), Some(w)) => {
            let ok = len(h, s) == w.chars().count() && equal_str(h, s, w) == Ok(true);
            assert!(ok, "obj {} text {:?}, expected {w:?}", o.id(h.mutation()), display(h, s).to_string());
        }
        (got, _) => panic!("obj {} has text: {}, expected {want:?}", o.id(h.mutation()), got.is_some()),
    }
}

/// Entries the tables hold are ones the model has, and every one with a live key is there.
/// When `exact`, after a full collection, those are all.
fn verify_tables(mc: &Mutation<'_>, world: &World, live: &HashSet<i64>, exact: bool) {
    let eph: HashMap<i64, i64> =
        table::<Ephemerons>(mc, 1).entries(mc).map(|(k, v)| (id_of(mc, k).unwrap(), id_of(mc, v).unwrap())).collect();
    for (k, v) in &eph {
        assert_eq!(world.eph.get(k), Some(v), "ephemeron {k}");
    }
    let kept = world.eph.iter().filter(|(k, _)| live.contains(k));
    for (k, v) in kept.clone() {
        assert_eq!(eph.get(k), Some(v), "ephemeron with a live key {k}");
    }
    let weak: HashSet<i64> = table::<WeakObjects<Obj>>(mc, 2).entries(mc).map(|o| o.id(mc)).collect();
    assert!(weak.is_subset(&world.weak), "weak table {weak:?}, expected {:?}", world.weak);
    assert!(world.weak.iter().filter(|x| live.contains(x)).all(|x| weak.contains(x)), "weak table lost a live object");
    if exact {
        assert_eq!(eph.len(), kept.count());
        assert_eq!(weak.len(), world.weak.iter().filter(|x| live.contains(x)).count());
    }
    let h = Strings::new(mc);
    let strong: HashMap<String, i64> = table::<Strong>(mc, 3)
        .entries(mc)
        .map(|(k, v)| (display(&h, h.string(k).unwrap()).to_string(), id_of(mc, v).unwrap()))
        .collect();
    assert_eq!(strong, world.strong);
}

/// A number from the environment variable `name`, if it's set.
fn fuzz_knob(name: &str) -> Option<u64> {
    let value = std::env::var(name).ok()?;
    Some(value.parse().unwrap_or_else(|_| panic!("{name} must be a number, not {value:?}")))
}

/// Reports which seed was running if it panics.
struct FuzzSeed(u64);

impl Drop for FuzzSeed {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!("model_fuzz failed on seed {0}; rerun it alone with RAGWORT_FUZZ_SEED={0}", self.0);
        }
    }
}

fn slots<'gc>(mc: &Mutation<'gc>) -> Slots<'gc, slot::Member<Obj>> {
    mc.root(0).downcast::<Holder>(mc).unwrap().items(mc)
}

fn table<'gc, K: crate::table::Kind>(mc: &Mutation<'gc>, root: usize) -> Table<'gc, K> {
    Table::of(mc.root(root).downcast::<TableHead>(mc).unwrap())
}

fn retired<'gc>(mc: &Mutation<'gc>) -> GcVec<'gc> {
    GcVec::of(mc.root(4).downcast(mc).unwrap())
}

fn id_of<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> Option<i64> {
    v.downcast::<Obj>(mc).map(|o| o.id(mc))
}

fn text_of<'gc>(h: &Strings<'_, 'gc>, o: Option<Gc<'gc, Obj>>) -> Option<Str<'gc>> {
    o.and_then(|o| h.string(o.text(h.mutation())))
}

/// Up to `max` characters from one of four sets, so flat strings of every width turn up.
fn random_text(rng: &mut Rng, max: usize) -> String {
    const SETS: [&str; 4] = ["abc xyz!", "aéßÿ", "aé日本ā", "a😀é日"];
    let set: Vec<char> = SETS[rng.below(SETS.len())].chars().collect();
    (0..rng.below(max + 1)).map(|_| set[rng.below(set.len())]).collect()
}

/// Random steps and collections, checked against a model: objects with payloads, blobs, host
/// values, weak references and strings; ephemeron, weak-object and strong tables; and a VM
/// stack written without a barrier. Longer runs on demand: `RAGWORT_FUZZ_SEEDS` seeds from
/// `RAGWORT_FUZZ_FIRST`, of `RAGWORT_FUZZ_OPS` operations each, or only seed
/// `RAGWORT_FUZZ_SEED`. Seeds cycle through a roomy limit and two tight ones.
#[test]
fn model_fuzz() {
    const LIMITS: [usize; 3] = [3 << 20, 192 << 10, 96 << 10];
    let default_ops = 3000;
    let ops = fuzz_knob("RAGWORT_FUZZ_OPS").unwrap_or(default_ops);
    let seeds = match fuzz_knob("RAGWORT_FUZZ_SEED") {
        Some(seed) => seed..=seed,
        None => {
            let first = fuzz_knob("RAGWORT_FUZZ_FIRST").unwrap_or(1);
            first..=first.saturating_add(fuzz_knob("RAGWORT_FUZZ_SEEDS").unwrap_or(3)).saturating_sub(1)
        }
    };
    let mut total_ooms = 0;
    let mut tight = false;
    for seed in seeds {
        let _report = FuzzSeed(seed);
        let limit = LIMITS[(seed as usize + LIMITS.len() - 1) % LIMITS.len()];
        tight |= limit < LIMITS[0];
        let mut arena = Arena::new(limit, ROOTS);
        let mut stack = arena.mutate(|mc| {
            mc.set_root(0, Value::object(mc, Holder::new(mc, SLOTS, None).unwrap()));
            mc.set_root(1, Value::object(mc, Table::<Ephemerons>::new_eq(mc).unwrap().head()));
            mc.set_root(2, Value::object(mc, Table::<WeakObjects<Obj>>::new_eq(mc).unwrap().head()));
            mc.set_root(3, Value::object(mc, Table::<Strong>::new(mc).unwrap().head()));
            mc.set_root(4, Value::object(mc, GcVec::<slot::Value>::new(mc).unwrap().head()));
            mc.stack(Segment::new(mc, SEGMENT).unwrap()).unwrap()
        });
        let mut rng = Rng(0x9e3779b97f4a7c15 ^ seed.wrapping_mul(0xbf58476d1ce4e5b9));
        let mut world = World { stack: vec![None; SEGMENT], ..World::default() };
        let (mut ooms, mut next_id) = (0, 0i64);
        for _ in 0..ops {
            let (a, b, c) = (rng.below(SLOTS), rng.below(SLOTS), rng.below(SLOTS));
            let op = rng.below(28);
            let id = next_id;
            // In words: a few objects larger than a page, some of several lines, most small.
            let len = match rng.below(20) {
                0 => 1100 + rng.below(3800),
                1..=5 => 8 + rng.below(1000),
                _ => rng.below(8),
            };
            let host = rng.chance(3);
            let blob = if rng.chance(4) { rng.below(600) } else { rng.below(4) };
            let r = if world.roots.is_empty() { 0 } else { rng.below(world.roots.len()) };
            let live = world.live();
            // Text operations, worked out from the model: the slot whose object gets new text,
            // and what that text should read.
            let external = rng.chance(2);
            let mut cut = None;
            let text_plan = match op {
                16 => {
                    let max = if rng.chance(8) { 600 } else { 40 };
                    let fresh = random_text(&mut rng, max);
                    world.slots[a].map(|_| (a, fresh))
                }
                17 => match (world.text(b), world.text(c)) {
                    (Some(x), Some(y)) if world.slots[a].is_some() && x.chars().count() + y.chars().count() <= MAX_TEXT => {
                        Some((a, format!("{x}{y}")))
                    }
                    _ => None,
                },
                18 => world.text(b).filter(|_| world.slots[a].is_some()).map(|t| {
                    let chars: Vec<char> = t.chars().collect();
                    let start = rng.below(chars.len() + 1);
                    let end = start + rng.below(chars.len() - start + 1);
                    cut = Some((start, end));
                    (a, chars[start..end].iter().collect())
                }),
                19 => world.text(a).filter(|_| world.slots[b].is_some()).map(|t| (b, t.clone())),
                _ => None,
            };
            let remove = rng.chance(3) || world.strong.len() >= MAX_STRONG && op == 23;
            let ready = match op {
                20 => world.slots[a].is_some() && (remove || world.slots[b].is_some()),
                21 | 22 => world.slots[a].is_some(),
                23 => world.text(a).is_some() && (remove || world.slots[b].is_some()),
                24 => world.text(a).is_some(),
                _ => false,
            };
            match op {
                10 => arena.collect_slice(1 + rng.below(20_000)),
                11 if rng.chance(4) => arena.collect(),
                11 => arena.collect_minor(),
                12 => arena.set_stress(if rng.chance(2) { None } else { Some(1 + rng.below(500)) }),
                13 => arena.set_evacuate_all(rng.chance(3)),
                8 if !world.roots.is_empty() => drop(world.roots.swap_remove(r)),
                _ => {
                    let (world_ref, plan) = (&world, &text_plan);
                    let (rng, stack) = (&mut rng, &mut stack);
                    let result = arena.step(|mc| -> Result<Got, Error> {
                        let items = slots(mc);
                        let h = Strings::new(mc);
                        let obj = |i: usize| items.get(i).unwrap();
                        Ok(match op {
                            0..=3 => {
                                let data = mc.blob(blob, |d: &mut [u64]| {
                                    d.iter_mut().zip(5 * id as u64..).for_each(|(d, v)| *d = v);
                                    blob
                                })?;
                                let o = Obj::new(mc, id, items.get(b), None, None, data, Value::FALSE, len, 0)?;
                                let payload = o.items(mc);
                                for i in 0..len {
                                    payload.set(mc, i, id as u64 + i as u64);
                                }
                                if host {
                                    let h = mc.host(id as u64 * 3).map_err(|_| mc.out_of_memory())?;
                                    o.set_owned(mc, Some(h));
                                }
                                items.set(mc, a, Some(o));
                                Got::Done
                            }
                            4 => {
                                if let Some(o) = items.get(a) {
                                    o.set_next(mc, items.get(b));
                                }
                                Got::Done
                            }
                            5 => {
                                items.set(mc, a, items.get(b).and_then(|o| o.next(mc)));
                                Got::Done
                            }
                            6 => {
                                if let Some(o) = items.get(a) {
                                    o.set_cache(mc, items.get(b));
                                }
                                Got::Done
                            }
                            7 => match items.get(a) {
                                Some(o) => Got::Root(Root::new(mc, o)?),
                                None => Got::Done,
                            },
                            9 if !world_ref.roots.is_empty() => {
                                items.set(mc, a, Some(world_ref.roots[r].0.get(mc).unwrap()));
                                Got::Done
                            }
                            14 => {
                                let target = items.get(b).and_then(|o| o.cache(mc));
                                items.set(mc, a, target);
                                Got::Id(target.map(|t| t.id(mc)))
                            }
                            16 if plan.is_some() => {
                                let fresh = plan.as_ref().unwrap().1.clone();
                                let s = if external { h.external(ExternalText::new(fresh))? } else { from_str(&h, &fresh)? };
                                obj(a).set_text(mc, s.value());
                                Got::Done
                            }
                            17 if plan.is_some() => {
                                let s = concat(&h, text_of(&h, items.get(b)).unwrap(), text_of(&h, items.get(c)).unwrap())?;
                                obj(a).set_text(mc, s.value());
                                Got::Done
                            }
                            18 if plan.is_some() => {
                                let (start, end) = cut.unwrap();
                                let s = substring(&h, text_of(&h, items.get(b)).unwrap(), start, end)?;
                                obj(a).set_text(mc, s.value());
                                Got::Done
                            }
                            19 if plan.is_some() => {
                                let s = flatten(&h, text_of(&h, items.get(a)).unwrap())?;
                                obj(b).set_text(mc, s.value());
                                Got::Done
                            }
                            20 if ready => {
                                let (t, key) = (table::<Ephemerons>(mc, 1), Value::object(mc, obj(a)));
                                let old = if remove { t.remove_eq(mc, key)? } else { t.insert_eq(mc, key, Value::object(mc, obj(b)))? };
                                Got::Id(old.and_then(|v| id_of(mc, v)))
                            }
                            21 if ready => {
                                let found = table::<Ephemerons>(mc, 1).get_eq(mc, Value::object(mc, obj(a)))?;
                                let found = found.map(|v| v.downcast::<Obj>(mc).unwrap());
                                items.set(mc, c, found);
                                Got::Id(found.map(|o| o.id(mc)))
                            }
                            22 if ready => {
                                let t = table::<WeakObjects<Obj>>(mc, 2);
                                if remove {
                                    Got::Flag(t.contains_eq(mc, obj(a))?)
                                } else {
                                    t.insert_eq(mc, obj(a))?;
                                    Got::Done
                                }
                            }
                            23 | 24 if ready => {
                                let key = text_of(&h, items.get(a)).unwrap();
                                let hash = hash(&h, key, SEED)?;
                                let t = table::<Strong>(mc, 3);
                                let old = if op == 24 {
                                    t.get(mc, hash, |k| equal(&h, h.string(k).unwrap(), key))?
                                } else if remove {
                                    t.remove(mc, hash, |(k, _)| equal(&h, h.string(k).unwrap(), key))?.map(|(_, v)| v)
                                } else {
                                    let value = Value::object(mc, obj(b));
                                    t.insert(mc, hash, |k| equal(&h, h.string(k).unwrap(), key), key.value(), value)?
                                };
                                let old = old.map(|v| v.downcast::<Obj>(mc).unwrap());
                                if op == 24 {
                                    items.set(mc, c, old);
                                }
                                Got::Id(old.map(|o| o.id(mc)))
                            }
                            25 | 26 => {
                                let (base, top) = (stack.base(), stack.top().min(SEGMENT));
                                let Some(room) = (SEGMENT - WINDOW + 1).checked_sub(base).filter(|&n| n > 0) else { return Ok(Got::Writes(Vec::new())) };
                                let fp = base + rng.below(room);
                                let frame = stack.frame(mc, fp).unwrap();
                                let mut writes = Vec::new();
                                for _ in 0..1 + rng.below(6) {
                                    let r = rng.below(WINDOW);
                                    let o = items.get(rng.below(SLOTS));
                                    frame.set(r as u8, o.map_or(Value::VOID, |o| Value::object(mc, o)));
                                    // Slots from `top` up are dead, so collections void them.
                                    if fp + r < top {
                                        writes.push((fp + r, o.map(|o| o.id(mc))));
                                    }
                                }
                                Got::Writes(writes)
                            }
                            27 => {
                                let (base, top) = (stack.base(), stack.top().min(SEGMENT));
                                match rng.below(5) {
                                    0 if base < top => {
                                        stack.capture(mc, base + 1 + rng.below(top - base)).unwrap();
                                        Got::Done
                                    }
                                    1 => {
                                        let new = Segment::new(mc, SEGMENT)?;
                                        let (list, old) = (retired(mc), Value::object(mc, stack.segment(mc)));
                                        let at = if list.len(mc) < RETIRED {
                                            list.push(mc, old)?;
                                            list.len(mc) - 1
                                        } else {
                                            let at = rng.below(RETIRED);
                                            list.set(mc, at, old);
                                            at
                                        };
                                        stack.switch(mc, new);
                                        Got::Retired(at)
                                    }
                                    2 => {
                                        stack.park(mc);
                                        Got::Done
                                    }
                                    3 => {
                                        let top = base + rng.below(top - base + 1);
                                        stack.set_top(top);
                                        Got::Top(top)
                                    }
                                    _ => {
                                        let raised = top + rng.below(SEGMENT - top + 1);
                                        stack.set_top(raised);
                                        for i in top..raised {
                                            stack.set(mc, i, Value::VOID);
                                        }
                                        Got::Done
                                    }
                                }
                            }
                            16..=24 => Got::Done,
                            _ => {
                                items.set(mc, a, None);
                                Got::Done
                            }
                        })
                    });
                    let got = match result {
                        Ok(Ok(got)) => got,
                        Ok(Err(Error::OutOfMemory)) | Err(OutOfMemory) => {
                            ooms += 1;
                            continue;
                        }
                        Ok(Err(e)) => panic!("op {op} failed: {e:?}"),
                    };
                    let w = &mut world;
                    match (op, got) {
                        (0..=3, _) => {
                            w.objs.insert(id, Model { next: w.slots[b], len, blob, host, weak: None, text: None });
                            w.slots[a] = Some(id);
                            next_id += 1;
                        }
                        (4, _) => {
                            if let Some(x) = w.slots[a] {
                                w.objs.get_mut(&x).unwrap().next = w.slots[b];
                            }
                        }
                        (5, _) => w.slots[a] = w.slots[b].and_then(|x| w.objs[&x].next),
                        (6, _) => {
                            if let Some(x) = w.slots[a] {
                                w.objs.get_mut(&x).unwrap().weak = w.slots[b];
                            }
                        }
                        (7, Got::Root(root)) => w.roots.push((root, w.slots[a].unwrap())),
                        (7, _) => {}
                        (9, _) if !w.roots.is_empty() => w.slots[a] = Some(w.roots[r].1),
                        (14, Got::Id(loaded)) => {
                            check_weak(loaded, w.slots[b].and_then(|x| w.objs[&x].weak), &live);
                            w.slots[a] = loaded;
                        }
                        (16..=19, _) => {
                            if let Some((slot, text)) = text_plan {
                                w.objs.get_mut(&w.slots[slot].unwrap()).unwrap().text = Some(text);
                            }
                        }
                        (20, Got::Id(old)) => {
                            let key = w.slots[a].unwrap();
                            assert_eq!(old, w.eph.get(&key).copied(), "ephemeron {key}");
                            if remove {
                                w.eph.remove(&key);
                            } else {
                                w.eph.insert(key, w.slots[b].unwrap());
                            }
                        }
                        (21, Got::Id(found)) => {
                            let key = w.slots[a].unwrap();
                            assert_eq!(found, w.eph.get(&key).copied(), "ephemeron {key}");
                            w.slots[c] = found;
                        }
                        (22, Got::Flag(found)) => assert_eq!(found, w.weak.contains(&w.slots[a].unwrap())),
                        (22, _) if ready => {
                            w.weak.insert(w.slots[a].unwrap());
                        }
                        (23 | 24, Got::Id(old)) => {
                            let key = w.text(a).unwrap().clone();
                            assert_eq!(old, w.strong.get(&key).copied(), "strong entry {key:?}");
                            match op {
                                24 => w.slots[c] = old,
                                _ if remove => drop(w.strong.remove(&key)),
                                _ => drop(w.strong.insert(key, w.slots[b].unwrap())),
                            }
                        }
                        (25 | 26, Got::Writes(writes)) => {
                            for (i, x) in writes {
                                w.stack[i] = x;
                            }
                        }
                        (27, Got::Retired(at)) => {
                            let old = std::mem::replace(&mut w.stack, vec![None; SEGMENT]);
                            if at == w.retired.len() {
                                w.retired.push(old);
                            } else {
                                w.retired[at] = old;
                            }
                        }
                        (27, Got::Top(top)) => w.stack[top..].fill(None),
                        (20..=27, _) => {}
                        _ => w.slots[a] = None,
                    }
                }
            }
            let live = world.live();
            arena.mutate(|mc| {
                let h = Strings::new(mc);
                let items = slots(mc);
                for (i, want) in world.slots.iter().enumerate() {
                    verify_obj(mc, &world.objs, &live, items.get(i), *want, 3);
                    if let Some(x) = want {
                        verify_text(&h, items.get(i).unwrap(), world.objs[x].text.as_deref());
                    }
                }
                for (root, id) in &world.roots {
                    verify_obj(mc, &world.objs, &live, Some(root.get(mc).unwrap()), Some(*id), 2);
                }
                for (i, want) in world.stack.iter().enumerate().filter(|(_, x)| x.is_some()) {
                    assert_eq!(stack.get(mc, i).and_then(|v| id_of(mc, v)), *want, "stack slot {i}");
                }
                let list = retired(mc);
                for (n, model) in world.retired.iter().enumerate() {
                    let segment = list.get(mc, n).unwrap().downcast::<Segment>(mc).unwrap().slots(mc);
                    for (i, want) in model.iter().enumerate().filter(|(_, x)| x.is_some()) {
                        assert_eq!(id_of(mc, segment.get(i)), *want, "retired segment {n} slot {i}");
                    }
                }
                verify_tables(mc, &world, &live, false);
            });
        }
        arena.set_stress(None);
        arena.collect();
        let live = world.live();
        world.eph.retain(|k, _| live.contains(k));
        world.weak.retain(|x| live.contains(x));
        arena.mutate(|mc| verify_tables(mc, &world, &live, true));
        // Down to the objects the slots and roots reach, without their strings, so whatever
        // else the arena still holds after collecting is a leak. A dropped stack is traced once more.
        drop(stack);
        arena.mutate(|mc| {
            for root in 1..ROOTS {
                mc.set_root(root, Value::FALSE);
            }
            let items = slots(mc);
            let roots = world.roots.iter().map(|r| r.0.get(mc).unwrap());
            let mut pending: Vec<_> = (0..SLOTS).filter_map(|i| items.get(i)).chain(roots).collect();
            let mut seen = HashSet::new();
            while let Some(o) = pending.pop() {
                if seen.insert(o.id(mc)) {
                    o.set_text(mc, Value::FALSE);
                    pending.extend(o.next(mc));
                }
            }
        });
        world.eph.clear();
        world.weak.clear();
        world.strong.clear();
        world.stack.clear();
        world.retired.clear();
        arena.collect();
        arena.collect();
        let live = world.live();
        let hosts = live.iter().filter(|x| world.objs[x].host).count();
        let live_hosts = arena.meta.hosts.borrow().iter().filter(|s| s.value.is_some()).count();
        assert_eq!((arena.objects(), live_hosts, arena.blobs()), (1 + live.len(), hosts, live.len()));
        let (majors, minors) = arena.collections();
        assert!(majors > 0 && minors > 0);
        eprintln!("seed {seed}: {ooms} ooms, {majors} + {minors} minor collections, {} objects", arena.objects());
        total_ooms += ooms;
    }
    if tight && ops >= default_ops {
        assert!(total_ooms > 0, "the tight limits should hit out of memory");
    }
}
