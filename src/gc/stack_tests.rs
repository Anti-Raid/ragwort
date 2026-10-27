use super::*;

#[derive(Trace, Plain)]
struct Num(i64);

#[derive(Trace, Plain)]
struct Pair<'gc> {
    car: Lock<Value<'gc>>,
    cdr: Lock<Value<'gc>>,
}

struct ValueRoot;
impl Rootable for ValueRoot {
    type Root<'gc> = Lock<Value<'gc>>;
}

fn arena() -> Arena<ValueRoot> {
    Arena::new(4 << 20, |_| Ok(Lock::new(Value::NIL))).unwrap()
}

fn num<'gc>(mc: &Mutation<'gc>, n: i64) -> Value<'gc> {
    Value::object(mc, mc.alloc(Num(n)).unwrap())
}

fn read<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> Option<i64> {
    match v.as_object() {
        Some(r) => Some(r.downcast::<Num>(mc)?.0),
        None => None,
    }
}

fn new_stack(arena: &mut Arena<ValueRoot>, len: usize) -> Stack {
    arena.mutate(|mc, root| {
        let segment = Segment::new(mc, len).unwrap();
        root.set(mc, Value::object(mc, segment));
        mc.stack(segment).unwrap()
    })
}

/// Fills registers `0..n` of the frame at `fp` with new numbers `first..`.
fn fill(arena: &mut Arena<ValueRoot>, stack: &Stack, fp: usize, n: u8, first: i64) {
    arena.mutate(|mc, _| {
        let frame = stack.frame(mc, fp).unwrap();
        for r in 0..n {
            frame.set(r, num(mc, first + r as i64));
        }
    });
}

fn frame_values(arena: &mut Arena<ValueRoot>, stack: &Stack, fp: usize, n: u8) -> Vec<Option<i64>> {
    arena.mutate(|mc, _| (0..n).map(|r| read(mc, stack.frame(mc, fp).unwrap().get(r))).collect())
}

fn expected(n: u8, first: i64) -> Vec<Option<i64>> {
    (0..n as i64).map(|i| Some(first + i)).collect()
}

/// The values in `range` of the segment the root holds.
fn rooted_segment(arena: &mut Arena<ValueRoot>, range: std::ops::Range<usize>) -> Vec<Option<i64>> {
    arena.mutate(|mc, root| {
        let segment = root.get().downcast::<Segment>(mc).unwrap();
        segment.items()[range].iter().map(|s| read(mc, s.get())).collect()
    })
}

fn segment_offset(arena: &mut Arena<ValueRoot>, stack: &Stack) -> u32 {
    arena.mutate(|mc, _| Member::new(mc, stack.segment(mc)).to_bits().get())
}

#[test]
fn frame_writes_skip_the_barrier_and_minor_collections_see_them() {
    let mut arena = arena();
    let stack = new_stack(&mut arena, 512);
    arena.collect();
    let segment = segment_offset(&mut arena, &stack);
    assert!(arena.heap().is_old(segment));
    fill(&mut arena, &stack, 0, 16, 100);
    assert_eq!(arena.heap().dirty_cards(), 0, "frame writes dirtied cards");
    arena.collect_minor();
    assert_eq!(frame_values(&mut arena, &stack, 0, 16), expected(16, 100));
    arena.collect();
    assert_eq!(frame_values(&mut arena, &stack, 0, 16), expected(16, 100));
    assert!(!arena.metrics().corrupted);
    arena.heap().check();
}

#[test]
fn frame_writes_while_marking_are_traced_before_the_cycle_ends() {
    let mut arena = arena();
    let stack = new_stack(&mut arena, 512);
    let (pair, x) = arena.mutate(|mc, root| {
        let x = num(mc, 7);
        let pair = Value::object(mc, mc.alloc(Pair { car: Lock::new(x), cdr: Lock::new(root.get()) }).unwrap());
        root.set(mc, pair);
        (pair.as_object().unwrap().to_bits() >> 32, x.to_bits() >> 32)
    });
    arena.collect();
    // The root pair is shaded first and the segment last, so the segment is traced first.
    arena.collect_slice(1);
    let segment = segment_offset(&mut arena, &stack);
    assert!(arena.heap().is_old(segment), "the segment wasn't traced first");
    assert!(!arena.heap().is_old(x as u32) && arena.heap().is_old(pair as u32));
    arena.mutate(|mc, root| {
        let pair = root.get().downcast::<Pair>(mc).unwrap();
        stack.frame(mc, 0).unwrap().set(0, pair.car.get());
        pair.car.set(mc, Value::VOID);
    });
    arena.collect_slice(usize::MAX);
    assert_eq!(arena.metrics().phase, Phase::Idle);
    assert_eq!(frame_values(&mut arena, &stack, 0, 1), [Some(7)]);
    assert!(!arena.metrics().corrupted);
}

#[test]
fn slots_above_top_are_voided_by_collections() {
    let mut arena = arena();
    let stack = new_stack(&mut arena, 512);
    fill(&mut arena, &stack, 0, 20, 0);
    stack.set_top(10);
    let objects = arena.metrics().objects;
    arena.collect_minor();
    assert_eq!(arena.metrics().objects, objects - 10);
    let values = frame_values(&mut arena, &stack, 0, 20);
    assert_eq!(values[..10], expected(10, 0)[..]);
    assert!(values[10..].iter().all(Option::is_none));
    arena.mutate(|mc, _| assert_eq!(stack.get(mc, 15), Some(Value::VOID)));
}

#[test]
fn captured_frames_become_ordinary_memory() {
    let mut arena = arena();
    let mut stack = new_stack(&mut arena, 512);
    arena.collect();
    fill(&mut arena, &stack, 0, 8, 50);
    let captured = arena.mutate(|mc, _| stack.capture(mc, 8));
    assert_eq!(captured, Some(0..8));
    assert_eq!(stack.base(), 8);
    arena.collect_minor();
    assert_eq!(rooted_segment(&mut arena, 0..8), expected(8, 50));
    arena.mutate(|mc, _| {
        assert!(stack.frame(mc, 7).is_none() && stack.frame(mc, 8).is_some());
        assert!(!stack.set(mc, 7, Value::TRUE) && stack.set(mc, 8, Value::TRUE));
        let segment = stack.segment(mc);
        assert!(!stack.write(mc, 7, &segment.items()[..2]));
        assert!(stack.capture(mc, 7).is_none() && stack.capture(mc, 513).is_none());
    });
    // A continuation copies its frames back above `base`.
    arena.mutate(|mc, _| {
        let segment = stack.segment(mc);
        assert!(stack.write(mc, 8, &segment.items()[..8]));
    });
    arena.collect_minor();
    assert_eq!(frame_values(&mut arena, &stack, 8, 8), expected(8, 50));
    assert!(!arena.metrics().corrupted);
}

#[test]
fn switching_segments_retires_the_old_one() {
    let mut arena = arena();
    let mut stack = new_stack(&mut arena, 512);
    arena.collect();
    fill(&mut arena, &stack, 0, 8, 10);
    arena.mutate(|mc, _| assert!(stack.set(mc, 100, num(mc, 99))));
    stack.set_top(8);
    arena.mutate(|mc, _| stack.switch(mc, Segment::new(mc, 300).unwrap()));
    assert_eq!((stack.base(), stack.top()), (0, 300));
    arena.collect_minor();
    assert_eq!(rooted_segment(&mut arena, 0..8), expected(8, 10));
    assert_eq!(rooted_segment(&mut arena, 100..101), [None]);
    fill(&mut arena, &stack, 0, 4, 20);
    arena.collect();
    assert_eq!(frame_values(&mut arena, &stack, 0, 4), expected(4, 20));
    assert!(!arena.metrics().corrupted);
    arena.heap().check();
}

#[test]
fn parked_stacks_keep_their_frames() {
    let mut arena = arena();
    let mut stack = new_stack(&mut arena, 512);
    arena.collect();
    fill(&mut arena, &stack, 0, 8, 30);
    stack.set_top(8);
    arena.mutate(|mc, _| stack.park(mc));
    arena.collect_minor();
    arena.collect();
    assert_eq!(frame_values(&mut arena, &stack, 0, 8), expected(8, 30));
    // Getting a frame unparks the stack, so new writes are traced again.
    fill(&mut arena, &stack, 0, 8, 40);
    arena.collect_minor();
    assert_eq!(frame_values(&mut arena, &stack, 0, 8), expected(8, 40));
    assert!(!arena.metrics().corrupted);
}

#[test]
fn dropped_stacks_are_traced_once_more() {
    let mut arena = arena();
    let stack = new_stack(&mut arena, 512);
    arena.collect();
    fill(&mut arena, &stack, 0, 8, 60);
    stack.set_top(8);
    drop(stack);
    arena.collect_minor();
    assert_eq!(rooted_segment(&mut arena, 0..8), expected(8, 60));
    assert!(arena.heap().stacks.borrow().is_empty());
    arena.collect();
    assert_eq!(rooted_segment(&mut arena, 0..8), expected(8, 60));
    assert!(!arena.metrics().corrupted);
    arena.heap().check();
}

#[test]
fn moved_segments_keep_working() {
    let mut arena = arena();
    let stack = new_stack(&mut arena, 300);
    fill(&mut arena, &stack, 0, 16, 70);
    arena.collect();
    let before = segment_offset(&mut arena, &stack);
    arena.set_evacuate_all(true);
    arena.collect();
    assert_ne!(segment_offset(&mut arena, &stack), before, "the segment didn't move");
    assert_eq!(frame_values(&mut arena, &stack, 0, 16), expected(16, 70));
    fill(&mut arena, &stack, 0, 16, 80);
    arena.collect_minor();
    assert_eq!(frame_values(&mut arena, &stack, 0, 16), expected(16, 80));
    assert!(!arena.metrics().corrupted);
}

#[test]
fn frames_check_their_bounds() {
    let mut arena = arena();
    let stack = new_stack(&mut arena, 300);
    arena.mutate(|mc, _| {
        assert!(stack.frame(mc, 0).is_some() && stack.frame(mc, 300 - WINDOW).is_some());
        assert!(stack.frame(mc, 301 - WINDOW).is_none() && stack.frame(mc, usize::MAX).is_none());
        assert!(stack.get(mc, 299).is_some() && stack.get(mc, 300).is_none());
        assert!(!stack.set(mc, 300, Value::TRUE));
        let segment = stack.segment(mc);
        assert!(!stack.write(mc, 299, &segment.items()[..2]) && !stack.write(mc, usize::MAX, &segment.items()[..2]));
    });
}

#[test]
#[should_panic(expected = "different arena")]
fn stacks_belong_to_one_arena() {
    let mut a = arena();
    let mut b = arena();
    let stack = new_stack(&mut a, 300);
    b.mutate(|mc, _| {
        stack.frame(mc, 0);
    });
}

#[test]
#[should_panic(expected = "already in use")]
fn a_segment_belongs_to_one_stack() {
    let mut arena = arena();
    let _stack = new_stack(&mut arena, 300);
    arena.mutate(|mc, root| {
        let _ = mc.stack(root.get().downcast::<Segment>(mc).unwrap());
    });
}

#[test]
#[should_panic(expected = "already in use")]
fn switching_to_a_used_segment_panics() {
    let mut arena = arena();
    let _first = new_stack(&mut arena, 300);
    let mut second = arena.mutate(|mc, _| mc.stack(Segment::new(mc, 300).unwrap()).unwrap());
    arena.mutate(|mc, root| second.switch(mc, root.get().downcast::<Segment>(mc).unwrap()));
}

#[test]
fn segments_can_be_reused_once_free() {
    let mut arena = arena();
    let mut first = new_stack(&mut arena, 300);
    assert_eq!(first.top(), 300);
    // Switching to the segment it already uses is fine.
    arena.mutate(|mc, _| first.switch(mc, first.segment(mc)));
    arena.mutate(|mc, _| first.switch(mc, Segment::new(mc, 300).unwrap()));
    let second = arena.mutate(|mc, root| mc.stack(root.get().downcast::<Segment>(mc).unwrap()).unwrap());
    // Dropped stacks free their segment at once, and their last trace doesn't void what the
    // segment's next stack wrote.
    second.set_top(0);
    drop(second);
    let third = arena.mutate(|mc, root| mc.stack(root.get().downcast::<Segment>(mc).unwrap()).unwrap());
    fill(&mut arena, &third, 0, 8, 90);
    third.set_top(8);
    arena.collect();
    assert_eq!(frame_values(&mut arena, &third, 0, 8), expected(8, 90));
    assert_eq!(arena.heap().stacks.borrow().len(), 2);
    assert!(!arena.metrics().corrupted);
}

#[test]
fn lowering_top_while_parked_voids_the_rest() {
    let mut arena = arena();
    let mut stack = new_stack(&mut arena, 512);
    fill(&mut arena, &stack, 0, 20, 0);
    stack.set_top(20);
    arena.mutate(|mc, _| stack.park(mc));
    stack.set_top(10);
    arena.collect();
    let values = frame_values(&mut arena, &stack, 0, 20);
    assert_eq!(values[..10], expected(10, 0)[..]);
    assert!(values[10..].iter().all(Option::is_none));
}

#[test]
fn dropped_stacks_void_what_is_above_top() {
    let mut arena = arena();
    let stack = new_stack(&mut arena, 512);
    fill(&mut arena, &stack, 0, 8, 10);
    arena.mutate(|mc, _| assert!(stack.set(mc, 20, num(mc, 99))));
    stack.set_top(8);
    drop(stack);
    arena.collect();
    assert_eq!(rooted_segment(&mut arena, 0..8), expected(8, 10));
    assert_eq!(rooted_segment(&mut arena, 20..21), [None]);
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

/// Random frame writes, captures, switches and parks, with a collector slice after every
/// step, checked against a model of what each slot should hold.
#[test]
fn random_stack_traffic_under_stress() {
    const LEN: usize = 600;
    let mut arena = arena();
    let mut stack = new_stack(&mut arena, LEN);
    arena.set_stress(Some(2048));
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    // The live slots of the current segment, and the captured ranges of every segment, which
    // the root keeps as a list in order.
    let mut live = vec![None; LEN];
    let mut captured: Vec<Vec<Option<i64>>> = vec![Vec::new()];
    let mut next = 0;
    for _ in 0..400 {
        let op = rng.below(20);
        let top = stack.top().min(LEN);
        arena
            .step(|mc, root| {
                match op {
                    0 if stack.base() + 1 < top => {
                        let at = stack.base() + 1 + rng.below(top - stack.base() - 1);
                        let range = stack.capture(mc, at).unwrap();
                        captured.last_mut().unwrap().extend_from_slice(&live[range]);
                    }
                    1 => {
                        let segment = Segment::new(mc, LEN).unwrap();
                        stack.switch(mc, segment);
                        let list = mc.alloc(Pair { car: Lock::new(Value::object(mc, segment)), cdr: Lock::new(root.get()) });
                        root.set(mc, Value::object(mc, list.unwrap()));
                        live = vec![None; LEN];
                        captured.push(Vec::new());
                    }
                    2 => stack.park(mc),
                    _ => {
                        let fp = stack.base() + rng.below(LEN - WINDOW - stack.base().min(LEN - WINDOW) + 1);
                        if let Some(frame) = stack.frame(mc, fp) {
                            for _ in 0..rng.below(8) {
                                let r = rng.below(WINDOW) as u8;
                                // Slots from `top` up are dead, so collections void them.
                                if fp + r as usize >= top {
                                    continue;
                                }
                                frame.set(r, num(mc, next));
                                live[fp + r as usize] = Some(next);
                                next += 1;
                            }
                        }
                    }
                }
                Ok::<_, ()>(())
            })
            .unwrap();
        if rng.below(4) == 0 {
            let top = stack.base() + rng.below(LEN - stack.base() + 1);
            stack.set_top(top);
            live[top..].fill(None);
        }
        arena.mutate(|mc, root| {
            let base = stack.base();
            for (i, want) in live.iter().enumerate().skip(base) {
                if want.is_some() {
                    assert_eq!(read(mc, stack.get(mc, i).unwrap()), *want, "slot {i}");
                }
            }
            let mut list = root.get();
            for want in captured.iter().rev() {
                let (segment, rest) = match list.downcast::<Pair>(mc) {
                    Some(pair) => (pair.car.get(), pair.cdr.get()),
                    None => (list, Value::NIL),
                };
                let items = segment.downcast::<Segment>(mc).unwrap().items();
                for (i, w) in want.iter().enumerate() {
                    if w.is_some() {
                        assert_eq!(read(mc, items[i].get()), *w, "captured slot {i}");
                    }
                }
                list = rest;
            }
        });
        assert!(!arena.metrics().corrupted);
    }
    arena.set_stress(None);
    arena.collect();
    arena.heap().check();
}
