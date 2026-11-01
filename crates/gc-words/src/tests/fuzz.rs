use std::collections::{HashMap, HashSet};

use super::*;

objects! {
    kind Kind;

    /// Items hold `id + i`, so a moved or overwritten payload shows.
    struct Obj { id: i64, next: Member<Obj>, owned: Host<u64>, cache: Weak<Obj> } items u64
    struct Holder {} items Member<Obj>
}

struct Rng(u64);

impl Rng {
    fn below(&mut self, n: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 % n as u64) as usize
    }
}

#[derive(Clone, Copy)]
struct Model {
    next: Option<i64>,
    len: usize,
    host: bool,
    weak: Option<i64>,
}

fn reachable(objs: &HashMap<i64, Model>, from: impl IntoIterator<Item = i64>) -> HashSet<i64> {
    let mut reachable = HashSet::new();
    let mut pending: Vec<i64> = from.into_iter().collect();
    while let Some(x) = pending.pop() {
        if reachable.insert(x) {
            pending.extend(objs[&x].next);
        }
    }
    reachable
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
        let m = objs[&id];
        let items = o.items(mc);
        assert_eq!(items.len(), m.len, "obj {id}");
        let stride = (m.len / 7).max(1);
        assert!((0..m.len).step_by(stride).all(|i| items.get(i) == id as u64 + i as u64), "obj {id} payload");
        let host = o.owned(mc).map(|h| *h.get(mc).unwrap());
        assert_eq!(host, m.host.then_some(id as u64 * 3), "obj {id} host");
        check_weak(o.cache(mc).map(|w| w.id(mc)), m.weak, live);
        cur = o.next(mc);
        want = m.next;
    }
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

/// Random steps and collections, checked against a model. Longer runs on demand:
/// `RAGWORT_FUZZ_SEEDS` seeds from `RAGWORT_FUZZ_FIRST`, of `RAGWORT_FUZZ_OPS` operations each,
/// or only seed `RAGWORT_FUZZ_SEED`. Seeds cycle through a roomy limit and two tight ones.
#[test]
fn model_fuzz() {
    const SLOTS: usize = 16;
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
        let mut arena = Arena::new(limit, 1);
        arena.mutate(|mc| mc.set_root(0, Value::object(mc, Holder::new(mc, SLOTS, None).unwrap())));
        let mut rng = Rng(0x9e3779b97f4a7c15 ^ seed.wrapping_mul(0xbf58476d1ce4e5b9));
        let mut objs: HashMap<i64, Model> = HashMap::new();
        let mut slots_model: [Option<i64>; SLOTS] = [None; SLOTS];
        let mut roots: Vec<(Root<Obj>, i64)> = Vec::new();
        let (mut ooms, mut next_id) = (0, 0i64);
        for _ in 0..ops {
            let (a, b) = (rng.below(SLOTS), rng.below(SLOTS));
            let op = rng.below(16);
            let id = next_id;
            // In words: a few objects larger than a page, some of several lines, most small.
            let len = match rng.below(20) {
                0 => 1100 + rng.below(3800),
                1..=5 => 8 + rng.below(1000),
                _ => rng.below(8),
            };
            let host = rng.below(3) == 0;
            let r = if roots.is_empty() { 0 } else { rng.below(roots.len()) };
            let live = reachable(&objs, slots_model.iter().flatten().copied().chain(roots.iter().map(|r| r.1)));
            match op {
                10 => arena.collect_slice(1 + rng.below(20_000)),
                11 if rng.below(4) == 0 => arena.collect(),
                11 => arena.collect_minor(),
                12 => arena.set_stress(if rng.below(2) == 0 { None } else { Some(1 + rng.below(500)) }),
                13 => arena.set_evacuate_all(rng.below(3) == 0),
                8 if !roots.is_empty() => drop(roots.swap_remove(r)),
                _ => {
                    let roots_ref = &roots;
                    let result = arena.step(|mc| -> Result<_, OutOfMemory> {
                        let items = slots(mc);
                        match op {
                            0..=3 => {
                                let obj = Obj::new(mc, id, items.get(b), None, None, len, 0)?;
                                let payload = obj.items(mc);
                                for i in 0..len {
                                    payload.set(mc, i, id as u64 + i as u64);
                                }
                                if host {
                                    let h = mc.host(id as u64 * 3).map_err(|_| mc.out_of_memory())?;
                                    obj.set_owned(mc, Some(h));
                                }
                                items.set(mc, a, Some(obj));
                                Ok((None, None))
                            }
                            4 => {
                                if let Some(o) = items.get(a) {
                                    o.set_next(mc, items.get(b));
                                }
                                Ok((None, None))
                            }
                            5 => {
                                items.set(mc, a, items.get(b).and_then(|o| o.next(mc)));
                                Ok((None, None))
                            }
                            6 => {
                                if let Some(o) = items.get(a) {
                                    o.set_cache(mc, items.get(b));
                                }
                                Ok((None, None))
                            }
                            7 => match items.get(a) {
                                Some(o) => Root::new(mc, o).map(|r| (Some(r), None)),
                                None => Ok((None, None)),
                            },
                            9 if !roots_ref.is_empty() => {
                                items.set(mc, a, Some(roots_ref[r].0.get(mc).unwrap()));
                                Ok((None, None))
                            }
                            14 => {
                                let target = items.get(b).and_then(|o| o.cache(mc));
                                items.set(mc, a, target);
                                Ok((None, target.map(|t| t.id(mc))))
                            }
                            _ => {
                                items.set(mc, a, None);
                                Ok((None, None))
                            }
                        }
                    });
                    match result {
                        Ok(Ok((new_root, loaded))) => match op {
                            0..=3 => {
                                objs.insert(id, Model { next: slots_model[b], len, host, weak: None });
                                slots_model[a] = Some(id);
                                next_id += 1;
                            }
                            4 => {
                                if let Some(x) = slots_model[a] {
                                    objs.get_mut(&x).unwrap().next = slots_model[b];
                                }
                            }
                            5 => slots_model[a] = slots_model[b].and_then(|x| objs[&x].next),
                            6 => {
                                if let Some(x) = slots_model[a] {
                                    objs.get_mut(&x).unwrap().weak = slots_model[b];
                                }
                            }
                            14 => {
                                check_weak(loaded, slots_model[b].and_then(|x| objs[&x].weak), &live);
                                slots_model[a] = loaded;
                            }
                            7 => {
                                if let Some(root) = new_root {
                                    roots.push((root, slots_model[a].unwrap()));
                                }
                            }
                            9 if !roots.is_empty() => slots_model[a] = Some(roots[r].1),
                            _ => slots_model[a] = None,
                        },
                        Ok(Err(OutOfMemory)) | Err(OutOfMemory) => ooms += 1,
                    }
                }
            }
            let live = reachable(&objs, slots_model.iter().flatten().copied().chain(roots.iter().map(|r| r.1)));
            arena.mutate(|mc| {
                let items = slots(mc);
                for (i, want) in slots_model.iter().enumerate() {
                    verify_obj(mc, &objs, &live, items.get(i), *want, 3);
                }
                for (root, id) in &roots {
                    verify_obj(mc, &objs, &live, Some(root.get(mc).unwrap()), Some(*id), 2);
                }
            });
        }
        arena.set_stress(None);
        arena.collect();
        let live = reachable(&objs, slots_model.iter().flatten().copied().chain(roots.iter().map(|r| r.1)));
        let hosts = live.iter().filter(|x| objs[x].host).count();
        let live_hosts = arena.meta.hosts.borrow().iter().filter(|s| s.value.is_some()).count();
        assert_eq!((arena.objects(), live_hosts), (1 + live.len(), hosts));
        let (majors, minors) = arena.collections();
        assert!(majors > 0 && minors > 0);
        eprintln!("seed {seed}: {ooms} ooms, {majors} + {minors} minor collections, {} objects", arena.objects());
        total_ooms += ooms;
    }
    if tight && ops >= default_ops {
        assert!(total_ooms > 0, "the tight limits should hit out of memory");
    }
}
