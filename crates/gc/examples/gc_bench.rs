use std::hint::black_box;
use std::time::{Duration, Instant};

use ragwort_gc::*;

#[derive(Trace, Plain)]
struct Node<'gc> {
    value: i64,
    next: Lock<Option<Member<'gc, Node<'gc>>>>,
    _pad: u32,
}

#[derive(Trace, Plain)]
struct Host<'gc> {
    host: HostRef<'gc, u64>,
}

struct List;
impl Rootable for List {
    type Root<'gc> = Lock<Option<Member<'gc, Node<'gc>>>>;
}

#[derive(Trace, Plain)]
struct Pair<'gc> {
    car: Lock<Value<'gc>>,
    cdr: Lock<Value<'gc>>,
}

#[derive(Trace, Plain)]
#[gc(items = Lock<Value<'gc>>)]
struct Vector<'gc>(std::marker::PhantomData<&'gc ()>);

struct Values;
impl Rootable for Values {
    type Root<'gc> = (Lock<Value<'gc>>, Lock<Value<'gc>>);
}

fn value_arena() -> Arena<Values> {
    Arena::new(REGION, |_| Ok((Lock::new(Value::NIL), Lock::new(Value::NIL)))).unwrap()
}

#[derive(Trace, Plain)]
struct Holder<'gc> {
    weak: Weak<'gc, Node<'gc>>,
    next: Lock<Option<Member<'gc, Holder<'gc>>>>,
}

struct Holders;
impl Rootable for Holders {
    type Root<'gc> = Lock<Option<Member<'gc, Holder<'gc>>>>;
}

/// Keeps a key alive.
#[derive(Trace, Plain)]
struct Keep<'gc> {
    key: Lock<Option<Member<'gc, Node<'gc>>>>,
    next: Lock<Option<Member<'gc, Keep<'gc>>>>,
}

type Entry<'gc> = Ephemeron<'gc, Node<'gc>, Option<Member<'gc, Node<'gc>>>>;

#[derive(Trace, Plain)]
#[gc(items = Entry<'gc>)]
struct Entries<'gc>(std::marker::PhantomData<&'gc ()>);

struct EntriesRoot;
impl Rootable for EntriesRoot {
    type Root<'gc> = (Lock<Option<Member<'gc, Entries<'gc>>>>, Lock<Option<Member<'gc, Keep<'gc>>>>);
}

struct Hosts;
impl Rootable for Hosts {
    type Root<'gc> = Lock<Option<Member<'gc, Host<'gc>>>>;
}

fn list_arena() -> Arena<List> {
    Arena::new(REGION, |_| Ok(Lock::new(None))).unwrap()
}

fn build(arena: &mut Arena<List>, n: i64) {
    arena.mutate(|mc, root| {
        for i in 0..n {
            let node = mc.alloc(Node { value: i, next: Lock::new(root.get()), _pad: 0 }).unwrap();
            root.store(mc, Some(node));
        }
    }).unwrap();
}

fn time(name: &str, runs: usize, mut f: impl FnMut() -> Duration) {
    let mut times: Vec<Duration> = (0..runs).map(|_| f()).collect();
    times.sort();
    println!("{name:<28} {:>9.2} ms", times[runs / 2].as_secs_f64() * 1e3);
}

fn main() {
    time("alloc 4M young (steps)", 7, || {
        let mut arena = list_arena();
        let start = Instant::now();
        for _ in 0..4000 {
            arena
                .step(|mc, _| {
                    for i in 0..1000 {
                        black_box(mc.alloc(Node { value: i, next: Lock::new(None), _pad: 0 })?);
                    }
                    Ok::<_, OutOfMemory>(())
                })
                .unwrap();
        }
        start.elapsed()
    });

    time("barrier 50M sets", 7, || {
        let mut arena = list_arena();
        build(&mut arena, 2);
        arena.collect();
        let start = Instant::now();
        arena.mutate(|mc, root| {
            let head = root.load(mc).unwrap();
            let next = head.next.get();
            for _ in 0..50_000_000 {
                head.next.set(mc, black_box(next));
            }
        }).unwrap();
        start.elapsed()
    });

    time("batch 50M sets", 7, || {
        let mut arena = list_arena();
        build(&mut arena, 2);
        arena.collect();
        let start = Instant::now();
        arena.mutate(|mc, root| {
            let head = root.load(mc).unwrap();
            let next = head.next.get();
            mc.batch(head, |b| {
                for _ in 0..50_000_000 {
                    b.set(&head.next, black_box(next));
                }
            });
        }).unwrap();
        start.elapsed()
    });

    time("major collect 1M list", 7, || {
        let mut arena = list_arena();
        build(&mut arena, 1_000_000);
        arena.collect();
        let start = Instant::now();
        arena.collect();
        start.elapsed()
    });

    time("minor collect, 1M old", 7, || {
        let mut arena = list_arena();
        build(&mut arena, 1_000_000);
        arena.collect();
        build(&mut arena, 200_000);
        let start = Instant::now();
        arena.collect_minor();
        start.elapsed()
    });

    time("minor, 1M vector, 1K stores x 100", 7, || {
        let mut arena = value_arena();
        arena.mutate(|mc, root| {
            let v = mc.alloc_inline(Vector(Default::default()), 1_000_000, |_| Lock::new(Value::NIL)).unwrap();
            root.0.set(mc, Value::object(mc, v));
        }).unwrap();
        arena.collect();
        let start = Instant::now();
        for round in 0..100 {
            arena.mutate(|mc, root| {
                let items = root.0.get().downcast::<Vector>(mc).unwrap().items();
                for i in 0..1000 {
                    let at = (round * 1000 + i) * 7919 % 1_000_000;
                    let pair = mc.alloc(Pair { car: Lock::new(Value::NIL), cdr: Lock::new(Value::NIL) }).unwrap();
                    items[at].set(mc, Value::object(mc, pair));
                }
            }).unwrap();
            arena.collect_minor();
        }
        start.elapsed()
    });

    time("evacuate-all collect 500K", 7, || {
        let mut arena = list_arena();
        build(&mut arena, 500_000);
        arena.collect();
        arena.set_evacuate_all(true);
        let start = Instant::now();
        arena.collect();
        start.elapsed()
    });

    time("host get 50M", 7, || {
        let mut arena = Arena::<Hosts>::new(1 << 20, |mc| {
            let host = mc.host(7u64)?;
            Ok(Lock::new(Some(Member::new(mc, mc.alloc(Host { host })?))))
        })
        .unwrap();
        let start = Instant::now();
        arena.mutate(|mc, root| {
            let host = root.load(mc).unwrap().host;
            let mut sum = 0;
            for _ in 0..50_000_000 {
                sum += *black_box(host).get(mc).unwrap();
            }
            black_box(sum);
        }).unwrap();
        start.elapsed()
    });

    time("value list sum 1M x 20", 7, || {
        let mut arena = value_arena();
        arena.mutate(|mc, root| {
            for i in 0..1_000_000 {
                let pair = Pair { car: Lock::new(Value::fixnum(i).unwrap()), cdr: Lock::new(root.0.get()) };
                root.0.set(mc, Value::object(mc, mc.alloc(pair).unwrap()));
            }
        }).unwrap();
        arena.collect();
        let start = Instant::now();
        arena.mutate(|mc, root| {
            for _ in 0..20 {
                let (mut sum, mut cur) = (Value::fixnum(0).unwrap(), root.0.get());
                while let Some(pair) = cur.downcast::<Pair>(mc) {
                    sum = sum.fixnum_add(pair.car.get()).unwrap();
                    cur = pair.cdr.get();
                }
                black_box(sum);
            }
        }).unwrap();
        start.elapsed()
    });

    time("value list sum (tag) 1M x 20", 7, || {
        let mut arena = value_arena();
        arena.mutate(|mc, root| {
            for i in 0..1_000_000 {
                let pair = Pair { car: Lock::new(Value::fixnum(i).unwrap()), cdr: Lock::new(root.0.get()) };
                root.0.set(mc, Value::object(mc, mc.alloc(pair).unwrap()));
            }
        }).unwrap();
        arena.collect();
        let start = Instant::now();
        arena.mutate(|mc, root| {
            let pair_tag = mc.type_tag::<Pair>().unwrap();
            for _ in 0..20 {
                let (mut sum, mut cur) = (Value::fixnum(0).unwrap(), root.0.get());
                while let Some(pair) = cur.downcast_tag(mc, pair_tag) {
                    sum = sum.fixnum_add(pair.car.get()).unwrap();
                    cur = pair.cdr.get();
                }
                black_box(sum);
            }
        }).unwrap();
        start.elapsed()
    });

    time("fixnum store 50M", 7, || {
        let mut arena = value_arena();
        arena.mutate(|mc, root| {
            let pair = Pair { car: Lock::new(Value::NIL), cdr: Lock::new(Value::NIL) };
            root.0.set(mc, Value::object(mc, mc.alloc(pair).unwrap()));
        }).unwrap();
        arena.collect();
        let start = Instant::now();
        arena.mutate(|mc, root| {
            let pair = root.0.get().downcast::<Pair>(mc).unwrap();
            for i in 0..50_000_000 {
                pair.car.set(mc, black_box(Value::fixnum(i).unwrap()));
            }
        }).unwrap();
        start.elapsed()
    });

    time("member list sum 1M x 20", 7, || {
        let mut arena = list_arena();
        build(&mut arena, 1_000_000);
        arena.collect();
        let start = Instant::now();
        arena.mutate(|mc, root| {
            for _ in 0..20 {
                let (mut sum, mut cur) = (0i64, root.load(mc));
                while let Some(node) = cur {
                    sum += node.value;
                    cur = node.next.load(mc);
                }
                black_box(sum);
            }
        }).unwrap();
        start.elapsed()
    });

    for (name, bulk) in [("vector-copy! 1M x 50, bulk", true), ("vector-copy! 1M x 50, sets", false)] {
        time(name, 7, || {
            let mut arena = value_arena();
            arena.mutate(|mc, root| {
                let pair = Value::object(mc, mc.alloc(Pair { car: Lock::new(Value::NIL), cdr: Lock::new(Value::NIL) }).unwrap());
                for slot in [&root.0, &root.1] {
                    let v = mc.alloc_inline(Vector(Default::default()), 1_000_000, |_| Lock::new(pair)).unwrap();
                    slot.set(mc, Value::object(mc, v));
                }
            }).unwrap();
            arena.collect();
            let start = Instant::now();
            arena.mutate(|mc, root| {
                let a = root.0.get().downcast::<Vector>(mc).unwrap().items();
                let b = root.1.get().downcast::<Vector>(mc).unwrap().items();
                for _ in 0..50 {
                    if bulk {
                        Lock::copy(mc, black_box(a), b);
                    } else {
                        for (d, s) in black_box(a).iter().zip(b) {
                            d.set(mc, s.get());
                        }
                    }
                }
            }).unwrap();
            start.elapsed()
        });
    }

    for (name, on_stack) in [("register moves 50M, frame", true), ("register moves 50M, locks", false)] {
        time(name, 7, || {
            let mut arena = value_arena();
            let stack = arena.mutate(|mc, root| {
                let pair = Value::object(mc, mc.alloc(Pair { car: Lock::new(Value::NIL), cdr: Lock::new(Value::NIL) }).unwrap());
                let v = mc.alloc_inline(Vector(Default::default()), 2048, |_| Lock::new(pair)).unwrap();
                root.0.set(mc, Value::object(mc, v));
                let segment = Segment::new(mc, 2048).unwrap();
                Lock::fill(mc, segment.items(), pair);
                mc.stack(segment).unwrap()
            }).unwrap();
            arena.collect();
            let start = Instant::now();
            arena.mutate(|mc, root| {
                if on_stack {
                    let f = black_box(stack.frame(mc, 0).unwrap());
                    for i in 0..50_000_000u32 {
                        f.set((i.wrapping_mul(7)) as u8, f.get((i.wrapping_mul(13)) as u8));
                    }
                } else {
                    let items = root.0.get().downcast::<Vector>(mc).unwrap().items();
                    let r: &[Lock<Value>; 256] = black_box(items.first_chunk().unwrap());
                    for i in 0..50_000_000u32 {
                        r[(i.wrapping_mul(7)) as u8 as usize].set(mc, r[(i.wrapping_mul(13)) as u8 as usize].get());
                    }
                }
            }).unwrap();
            start.elapsed()
        });
    }

    time("frame per call 20M", 7, || {
        let mut arena = value_arena();
        let stack = arena.mutate(|mc, _| mc.stack(Segment::new(mc, 4096).unwrap()).unwrap()).unwrap();
        arena.collect();
        let start = Instant::now();
        arena.mutate(|mc, _| {
            let (mut fp, mut acc) = (0, Value::fixnum(0).unwrap());
            for _ in 0..20_000_000u32 {
                let f = black_box(&stack).frame(mc, fp).unwrap();
                f.set(0, acc);
                acc = f.get(1);
                fp = if fp + 16 > 4096 - WINDOW { 0 } else { fp + 16 };
            }
            black_box(acc);
        }).unwrap();
        start.elapsed()
    });

    // How many 64K slices a major cycle over a 1M list takes, counted outside the timing,
    // since reading the phase walks every page.
    let slices = {
        let mut arena = list_arena();
        build(&mut arena, 1_000_000);
        arena.collect();
        let mut n = 1;
        arena.collect_slice(64 * 1024);
        while arena.metrics().phase != Phase::Idle {
            arena.collect_slice(64 * 1024);
            n += 1;
        }
        n
    };
    time("incremental major 1M, 64K", 7, || {
        let mut arena = list_arena();
        build(&mut arena, 1_000_000);
        arena.collect();
        let start = Instant::now();
        for _ in 0..slices {
            arena.collect_slice(64 * 1024);
        }
        start.elapsed()
    });

    time("barrier 50M sets, marking", 7, || {
        let mut arena = list_arena();
        build(&mut arena, 2);
        arena.collect();
        arena.collect_slice(0);
        let start = Instant::now();
        arena.mutate(|mc, root| {
            let head = root.load(mc).unwrap();
            let next = head.next.get();
            for _ in 0..50_000_000 {
                head.next.set(mc, black_box(next));
            }
        }).unwrap();
        start.elapsed()
    });

    time("weak 1M, targets die, major", 7, || {
        let mut arena = Arena::<Holders>::new(REGION, |_| Ok(Lock::new(None))).unwrap();
        arena.mutate(|mc, root| {
            for i in 0..1_000_000 {
                let node = mc.alloc(Node { value: i, next: Lock::new(None), _pad: 0 }).unwrap();
                let holder = mc.alloc(Holder { weak: Weak::new(mc, node), next: Lock::new(root.get()) }).unwrap();
                root.store(mc, Some(holder));
            }
        }).unwrap();
        let start = Instant::now();
        arena.collect();
        start.elapsed()
    });

    time("flonum store 50M", 7, || {
        let mut arena = value_arena();
        arena.mutate(|mc, root| {
            let pair = Pair { car: Lock::new(Value::NIL), cdr: Lock::new(Value::NIL) };
            root.0.set(mc, Value::object(mc, mc.alloc(pair).unwrap()));
        }).unwrap();
        arena.collect();
        let start = Instant::now();
        arena.mutate(|mc, root| {
            let pair = root.0.get().downcast::<Pair>(mc).unwrap();
            for i in 0..50_000_000 {
                pair.car.set(mc, Value::inline_flonum(black_box(i as f64 + 0.5)).unwrap());
            }
        }).unwrap();
        start.elapsed()
    });

    time("flonum list sum 1M x 20", 7, || {
        let mut arena = value_arena();
        arena.mutate(|mc, root| {
            for i in 0..1_000_000 {
                let car = Value::inline_flonum(i as f64 + 0.5).unwrap();
                let pair = Pair { car: Lock::new(car), cdr: Lock::new(root.0.get()) };
                root.0.set(mc, Value::object(mc, mc.alloc(pair).unwrap()));
            }
        }).unwrap();
        arena.collect();
        let start = Instant::now();
        arena.mutate(|mc, root| {
            for _ in 0..20 {
                let (mut sum, mut cur) = (0.0, root.0.get());
                while let Some(pair) = cur.downcast::<Pair>(mc) {
                    sum += pair.car.get().as_flonum(mc).unwrap();
                    cur = pair.cdr.get();
                }
                black_box(sum);
            }
        }).unwrap();
        start.elapsed()
    });

    time("boxed flonum 4M (steps)", 7, || {
        let mut arena = value_arena();
        let start = Instant::now();
        for _ in 0..4000 {
            arena
                .step(|mc, _| {
                    for i in 0..1000 {
                        black_box(Value::flonum(mc, 1e300 * (i as f64 + 1.0))?);
                    }
                    Ok::<_, OutOfMemory>(())
                })
                .unwrap();
        }
        start.elapsed()
    });

    time("ephemeron 500K, half die", 7, || {
        let mut arena = Arena::<EntriesRoot>::new(REGION, |_| Ok((Lock::new(None), Lock::new(None)))).unwrap();
        arena.mutate(|mc, root| {
            let table = mc.alloc_inline(Entries(std::marker::PhantomData), 500_000, |_| Entry::empty()).unwrap();
            let entries = table.items();
            for i in 0..500_000 {
                let key = mc.alloc(Node { value: i, next: Lock::new(None), _pad: 0 }).unwrap();
                let value = mc.alloc(Node { value: i, next: Lock::new(Some(Member::new(mc, key))), _pad: 0 }).unwrap();
                entries[i as usize].set(mc, key, Some(Member::new(mc, value)));
                if i % 2 == 0 {
                    let keep = Keep { key: Lock::new(Some(Member::new(mc, key))), next: Lock::new(root.1.get()) };
                    root.1.store(mc, Some(mc.alloc(keep).unwrap()));
                }
            }
            root.0.store(mc, Some(table));
        }).unwrap();
        let start = Instant::now();
        arena.collect();
        start.elapsed()
    });
}
