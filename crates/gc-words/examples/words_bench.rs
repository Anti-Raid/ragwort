//! `ragwort-gc`'s `gc_bench`, row for row, on the word heap. Objects are the same sizes: a
//! header word and two fields. Run with `--release` and compare with
//! `cargo run --release -p ragwort-gc --example gc_bench`.

use std::hint::black_box;
use std::time::{Duration, Instant};

use ragwort_gc_words::*;

objects! {
    kind Kind;
    struct Node { n: u64, next: Member<Node> }
    struct Pair { car: Value, cdr: Value }
    struct Vector {} items Value
    struct Holder { target: Weak<Node>, next: Member<Holder> }
    struct Table {} items Ephemeron
    struct HostBox { data: Host<u64> }
}

fn fixnum<'gc>(n: i64) -> Value<'gc> {
    Value::fixnum(n).expect("fixnum")
}

fn pair<'gc>(mc: &Mutation<'gc>, car: Value<'gc>, cdr: Value<'gc>) -> Value<'gc> {
    Value::object(mc, Pair::new(mc, car, cdr).expect("alloc"))
}

fn head<'gc>(mc: &Mutation<'gc>) -> Option<Gc<'gc, Node>> {
    mc.root(0).downcast::<Node>(mc)
}

/// A list of `n` nodes in root 0.
fn build(arena: &mut Arena, n: i64) {
    arena.mutate(|mc| {
        for i in 0..n {
            let node = Node::new(mc, i as u64, head(mc)).expect("alloc");
            mc.set_root(0, Value::object(mc, node));
        }
    });
}

fn time(name: &str, runs: usize, mut f: impl FnMut() -> Duration) {
    let mut times: Vec<Duration> = (0..runs).map(|_| f()).collect();
    times.sort();
    println!("{name:<28} {:>9.2} ms", times[runs / 2].as_secs_f64() * 1e3);
}

fn main() {
    time("alloc 4M young (steps)", 7, || {
        let mut arena = Arena::new(REGION, 1);
        let start = Instant::now();
        for _ in 0..4000 {
            arena.step(|mc| {
                for i in 0..1000 {
                    black_box(Node::new(mc, i, None).expect("alloc"));
                }
            })
            .expect("step");
        }
        start.elapsed()
    });

    time("barrier 50M sets", 7, || {
        let mut arena = Arena::new(REGION, 1);
        build(&mut arena, 2);
        arena.collect();
        let start = Instant::now();
        arena.mutate(|mc| {
            let head = head(mc).expect("head");
            let next = head.next(mc);
            for _ in 0..50_000_000 {
                head.set_next(mc, black_box(next));
            }
        });
        start.elapsed()
    });

    time("major collect 1M list", 7, || {
        let mut arena = Arena::new(REGION, 1);
        build(&mut arena, 1_000_000);
        arena.collect();
        let start = Instant::now();
        arena.collect();
        start.elapsed()
    });

    time("minor collect, 1M old", 7, || {
        let mut arena = Arena::new(REGION, 1);
        build(&mut arena, 1_000_000);
        arena.collect();
        build(&mut arena, 200_000);
        let start = Instant::now();
        arena.collect_minor();
        start.elapsed()
    });

    time("minor, 1M vector, 1K stores x 100", 7, || {
        let mut arena = Arena::new(REGION, 1);
        arena.mutate(|mc| {
            let vector = Vector::new(mc, 1_000_000, Value::NIL).expect("alloc");
            mc.set_root(0, Value::object(mc, vector));
        });
        arena.collect();
        let start = Instant::now();
        for round in 0..100 {
            arena.mutate(|mc| {
                let vector = mc.root(0).downcast::<Vector>(mc).expect("vector");
                for i in 0..1000 {
                    let at = (round * 1000 + i) * 7919 % 1_000_000;
                    vector.items(mc).set(mc, at as usize, pair(mc, fixnum(i), Value::NIL));
                }
            });
            arena.collect_minor();
        }
        start.elapsed()
    });

    time("evacuate-all collect 500K", 7, || {
        let mut arena = Arena::new(REGION, 1);
        build(&mut arena, 500_000);
        arena.collect();
        arena.set_evacuate_all(true);
        let start = Instant::now();
        arena.collect();
        start.elapsed()
    });

    time("host get 50M", 7, || {
        let mut arena = Arena::new(1 << 20, 1);
        arena.mutate(|mc| {
            let host = mc.host(7u64).expect("host");
            let object = HostBox::new(mc, Some(host)).expect("alloc");
            mc.set_root(0, Value::object(mc, object));
        });
        let start = Instant::now();
        arena.mutate(|mc| {
            let host = mc.root(0).downcast::<HostBox>(mc).and_then(|h| h.data(mc)).expect("host");
            let mut sum = 0;
            for _ in 0..50_000_000 {
                sum += *black_box(host).get(mc).expect("host");
            }
            black_box(sum);
        });
        start.elapsed()
    });

    for tagged in [false, true] {
        let name = if tagged { "value list sum (tag) 1M x 20" } else { "value list sum 1M x 20" };
        time(name, 7, || {
            let mut arena = Arena::new(REGION, 1);
            arena.mutate(|mc| {
                for i in 0..1_000_000 {
                    let list = pair(mc, fixnum(i), mc.root(0));
                    mc.set_root(0, list);
                }
            });
            arena.collect();
            let start = Instant::now();
            arena.mutate(|mc| {
                let tag = mc.type_tag::<Pair>().expect("tag");
                for _ in 0..20 {
                    let (mut sum, mut cur) = (fixnum(0), mc.root(0));
                    loop {
                        let pair = if tagged { cur.downcast_tag(tag) } else { cur.downcast::<Pair>(mc) };
                        let Some(pair) = pair else { break };
                        sum = sum.fixnum_add(pair.car(mc)).expect("sum");
                        cur = pair.cdr(mc);
                    }
                    black_box(sum);
                }
            });
            start.elapsed()
        });
    }

    time("fixnum store 50M", 7, || {
        let mut arena = Arena::new(REGION, 1);
        arena.mutate(|mc| {
            let p = pair(mc, Value::NIL, Value::NIL);
            mc.set_root(0, p);
        });
        arena.collect();
        let start = Instant::now();
        arena.mutate(|mc| {
            let pair = mc.root(0).downcast::<Pair>(mc).expect("pair");
            for i in 0..50_000_000 {
                pair.set_car(mc, black_box(fixnum(i)));
            }
        });
        start.elapsed()
    });

    time("member list sum 1M x 20", 7, || {
        let mut arena = Arena::new(REGION, 1);
        build(&mut arena, 1_000_000);
        arena.collect();
        let start = Instant::now();
        arena.mutate(|mc| {
            for _ in 0..20 {
                let (mut sum, mut cur) = (0i64, head(mc));
                while let Some(node) = cur {
                    sum += node.n(mc) as i64;
                    cur = node.next(mc);
                }
                black_box(sum);
            }
        });
        start.elapsed()
    });

    for (name, bulk) in [("vector-copy! 1M x 50, bulk", true), ("vector-copy! 1M x 50, sets", false)] {
        time(name, 7, || {
            let mut arena = Arena::new(REGION, 2);
            arena.mutate(|mc| {
                let p = pair(mc, Value::NIL, Value::NIL);
                for root in 0..2 {
                    let v = Vector::new(mc, 1_000_000, p).expect("alloc");
                    mc.set_root(root, Value::object(mc, v));
                }
            });
            arena.collect();
            let start = Instant::now();
            arena.mutate(|mc| {
                let a = mc.root(0).downcast::<Vector>(mc).expect("vector").items(mc);
                let b = mc.root(1).downcast::<Vector>(mc).expect("vector").items(mc);
                for _ in 0..50 {
                    if bulk {
                        black_box(a).copy_from(mc, b);
                    } else {
                        let a = black_box(a);
                        for i in 0..a.len() {
                            a.set(mc, i, b.get(i));
                        }
                    }
                }
            });
            start.elapsed()
        });
    }

    for (name, on_stack) in [("register moves 50M, frame", true), ("register moves 50M, locks", false)] {
        time(name, 7, || {
            let mut arena = Arena::new(REGION, 1);
            let stack = arena.mutate(|mc| {
                let p = pair(mc, Value::NIL, Value::NIL);
                let v = Vector::new(mc, 2048, p).expect("alloc");
                mc.set_root(0, Value::object(mc, v));
                let segment = mc.alloc_items::<Segment, 1>([0], 2048, p).expect("alloc");
                mc.stack(segment).expect("stack")
            });
            arena.collect();
            let start = Instant::now();
            arena.mutate(|mc| {
                if on_stack {
                    let f = black_box(stack.frame(mc, 0).expect("frame"));
                    for i in 0..50_000_000u32 {
                        f.set((i.wrapping_mul(7)) as u8, f.get((i.wrapping_mul(13)) as u8));
                    }
                } else {
                    let slots = mc.root(0).downcast::<Vector>(mc).expect("vector").items(mc);
                    let r = black_box(slots.window().expect("window"));
                    for i in 0..50_000_000u32 {
                        r.set(mc, (i.wrapping_mul(7)) as u8, r.get((i.wrapping_mul(13)) as u8));
                    }
                }
            });
            start.elapsed()
        });
    }

    time("frame per call 20M", 7, || {
        let mut arena = Arena::new(REGION, 1);
        let stack = arena.mutate(|mc| {
            let segment = Segment::new(mc, 4096).expect("alloc");
            mc.stack(segment).expect("stack")
        });
        arena.collect();
        let start = Instant::now();
        arena.mutate(|mc| {
            let (mut fp, mut acc) = (0, fixnum(0));
            for _ in 0..20_000_000u32 {
                let f = black_box(&stack).frame(mc, fp).expect("frame");
                f.set(0, acc);
                acc = f.get(1);
                fp = if fp + 16 > 4096 - WINDOW { 0 } else { fp + 16 };
            }
            black_box(acc);
        });
        start.elapsed()
    });

    let slices = {
        let mut arena = Arena::new(REGION, 1);
        build(&mut arena, 1_000_000);
        arena.collect();
        let mut n = 1;
        arena.collect_slice(64 * 1024);
        while arena.phase() != Phase::Idle {
            arena.collect_slice(64 * 1024);
            n += 1;
        }
        n
    };
    time("incremental major 1M, 64K", 7, || {
        let mut arena = Arena::new(REGION, 1);
        build(&mut arena, 1_000_000);
        arena.collect();
        let start = Instant::now();
        for _ in 0..slices {
            arena.collect_slice(64 * 1024);
        }
        start.elapsed()
    });

    time("barrier 50M sets, marking", 7, || {
        let mut arena = Arena::new(REGION, 1);
        build(&mut arena, 2);
        arena.collect();
        arena.collect_slice(0);
        let start = Instant::now();
        arena.mutate(|mc| {
            let head = head(mc).expect("head");
            let next = head.next(mc);
            for _ in 0..50_000_000 {
                head.set_next(mc, black_box(next));
            }
        });
        start.elapsed()
    });

    time("weak 1M, targets die, major", 7, || {
        let mut arena = Arena::new(REGION, 1);
        arena.mutate(|mc| {
            for i in 0..1_000_000 {
                let node = Node::new(mc, i, None).expect("alloc");
                let next = mc.root(0).downcast::<Holder>(mc);
                let holder = Holder::new(mc, Some(node), next).expect("alloc");
                mc.set_root(0, Value::object(mc, holder));
            }
        });
        let start = Instant::now();
        arena.collect();
        start.elapsed()
    });

    time("flonum store 50M", 7, || {
        let mut arena = Arena::new(REGION, 1);
        arena.mutate(|mc| {
            let p = pair(mc, Value::NIL, Value::NIL);
            mc.set_root(0, p);
        });
        arena.collect();
        let start = Instant::now();
        arena.mutate(|mc| {
            let pair = mc.root(0).downcast::<Pair>(mc).expect("pair");
            for i in 0..50_000_000 {
                pair.set_car(mc, Value::inline_flonum(black_box(i as f64 + 0.5)).expect("inline"));
            }
        });
        start.elapsed()
    });

    time("flonum list sum 1M x 20", 7, || {
        let mut arena = Arena::new(REGION, 1);
        arena.mutate(|mc| {
            for i in 0..1_000_000 {
                let p = pair(mc, Value::inline_flonum(i as f64 + 0.5).expect("inline"), mc.root(0));
                mc.set_root(0, p);
            }
        });
        arena.collect();
        let start = Instant::now();
        arena.mutate(|mc| {
            for _ in 0..20 {
                let (mut sum, mut cur) = (0.0, mc.root(0));
                while let Some(pair) = cur.downcast::<Pair>(mc) {
                    sum += pair.car(mc).as_flonum(mc).expect("flonum");
                    cur = pair.cdr(mc);
                }
                black_box(sum);
            }
        });
        start.elapsed()
    });

    time("boxed flonum 4M (steps)", 7, || {
        let mut arena = Arena::new(REGION, 1);
        let start = Instant::now();
        for _ in 0..4000 {
            arena.step(|mc| {
                for i in 0..1000 {
                    black_box(Value::flonum(mc, 1e300 * (i as f64 + 1.0)).expect("alloc"));
                }
            })
            .expect("step");
        }
        start.elapsed()
    });

    time("ephemeron 500K, half die", 7, || {
        let mut arena = Arena::new(REGION, 2);
        arena.mutate(|mc| {
            let table = Table::new(mc, 500_000).expect("alloc");
            for i in 0..500_000 {
                let key = pair(mc, fixnum(i), Value::NIL);
                table.set_entry(mc, i as usize, key, pair(mc, fixnum(i), key));
                if i % 2 == 0 {
                    let held = pair(mc, key, mc.root(1));
                    mc.set_root(1, held);
                }
            }
            mc.set_root(0, Value::object(mc, table));
        });
        let start = Instant::now();
        arena.collect();
        start.elapsed()
    });
}
