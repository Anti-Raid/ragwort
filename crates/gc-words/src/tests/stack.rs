use super::*;

/// A boxed number, so whether it's alive can be seen.
struct Num;
impl Object for Num {
    const DESC: Desc = Desc::of::<Num>(1);
}

struct Pair;
impl Object for Pair {
    const DESC: Desc = Desc::of::<Pair>(2).values(0b11);
}

fn arena() -> Arena {
    Arena::new(4 << 20, 1)
}

fn num<'gc>(mc: &Mutation<'gc>, n: i64) -> Value<'gc> {
    Value::object(mc, mc.alloc::<Num, 1>([n as u64]).unwrap())
}

fn read<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> Option<i64> {
    Some(v.downcast::<Num>(mc)?.word(mc, 0) as i64)
}

/// Objects alive after the last sweep.
fn objects(arena: &Arena) -> usize {
    let m = &arena.meta;
    m.pages[..m.used.get()].iter().flat_map(|p| &p.starts).map(|w| w.get().count_ones() as usize).sum()
}

fn dirty_cards(arena: &Arena) -> u32 {
    arena.meta.pages.iter().map(|p| p.cards.get().count_ones()).sum()
}

fn is_marked(arena: &mut Arena, index: u32) -> bool {
    arena.heap().has_bit(index as usize, |p| &p.marks)
}

fn new_stack(arena: &mut Arena, len: usize) -> Stack {
    arena.mutate(|mc| {
        let segment = Segment::new(mc, len).unwrap();
        mc.set_root(0, Value::object(mc, segment));
        mc.stack(segment).unwrap()
    })
}

/// Fills registers `0..n` of the frame at `fp` with new numbers `first..`.
fn fill(arena: &mut Arena, stack: &Stack, fp: usize, n: u8, first: i64) {
    arena.mutate(|mc| {
        let frame = stack.frame(mc, fp).unwrap();
        for r in 0..n {
            frame.set(r, num(mc, first + r as i64));
        }
    });
}

fn frame_values(arena: &mut Arena, stack: &Stack, fp: usize, n: u8) -> Vec<Option<i64>> {
    arena.mutate(|mc| (0..n).map(|r| read(mc, stack.frame(mc, fp).unwrap().get(r))).collect())
}

fn expected(n: u8, first: i64) -> Vec<Option<i64>> {
    (0..n as i64).map(|i| Some(first + i)).collect()
}

/// The values in `range` of the segment root 0 holds.
fn rooted_segment(arena: &mut Arena, range: Range<usize>) -> Vec<Option<i64>> {
    arena.mutate(|mc| {
        let slots = mc.root(0).downcast::<Segment>(mc).unwrap().slots(mc);
        range.map(|i| read(mc, slots.get(i))).collect()
    })
}

fn segment_index(arena: &mut Arena, stack: &Stack) -> u32 {
    arena.mutate(|mc| stack.segment(mc).index)
}

/// Overwrites freed memory, so a value wrongly freed reads back as something else.
fn churn(arena: &mut Arena) {
    arena.mutate(|mc| {
        for _ in 0..100_000 {
            num(mc, -1);
        }
    });
}

#[test]
fn frame_writes_skip_the_barrier_and_minor_collections_see_them() {
    let mut arena = arena();
    let stack = new_stack(&mut arena, 512);
    arena.collect();
    let segment = segment_index(&mut arena, &stack);
    assert!(is_marked(&mut arena, segment));
    fill(&mut arena, &stack, 0, 16, 100);
    assert_eq!(dirty_cards(&arena), 0, "frame writes dirtied cards");
    arena.collect_minor();
    churn(&mut arena);
    assert_eq!(frame_values(&mut arena, &stack, 0, 16), expected(16, 100));
    arena.collect();
    churn(&mut arena);
    assert_eq!(frame_values(&mut arena, &stack, 0, 16), expected(16, 100));
}

#[test]
fn frame_writes_while_marking_are_traced_before_the_cycle_ends() {
    let mut arena = arena();
    let stack = new_stack(&mut arena, 512);
    let segment = segment_index(&mut arena, &stack);
    arena.mutate(|mc| {
        let pair = mc.alloc::<Pair, 2>([num(mc, 7).to_bits(), Value::object(mc, stack.segment(mc)).to_bits()]).unwrap();
        mc.set_root(0, Value::object(mc, pair));
    });
    arena.collect();
    // The root is marked first and the segment last, so the segment is traced first.
    arena.collect_slice(1);
    assert_eq!(arena.phase(), Phase::Marking);
    let pair = arena.mutate(|mc| mc.root(0).downcast::<Pair>(mc).unwrap().index);
    assert!(arena.heap().has_bit(segment as usize, |p| &p.marks));
    assert!(arena.meta.work.borrow().gray.contains(&pair), "the pair was traced first");
    arena.mutate(|mc| {
        let pair = mc.root(0).downcast::<Pair>(mc).unwrap();
        stack.frame(mc, 0).unwrap().set(0, pair.value(mc, 0));
        pair.set_value(mc, 0, Value::VOID);
    });
    arena.collect_slice(usize::MAX);
    assert_eq!(arena.phase(), Phase::Idle);
    churn(&mut arena);
    assert_eq!(frame_values(&mut arena, &stack, 0, 1), [Some(7)]);
}

#[test]
fn slots_above_top_are_voided_by_collections() {
    let mut arena = arena();
    let stack = new_stack(&mut arena, 512);
    arena.collect();
    fill(&mut arena, &stack, 0, 20, 0);
    stack.set_top(10);
    let before = objects(&arena);
    arena.collect_minor();
    assert_eq!(objects(&arena), before - 10);
    let values = frame_values(&mut arena, &stack, 0, 20);
    assert_eq!(values[..10], expected(10, 0)[..]);
    assert!(values[10..].iter().all(Option::is_none));
    arena.mutate(|mc| assert!(stack.get(mc, 15) == Some(Value::VOID)));
}

#[test]
fn captured_frames_become_ordinary_memory() {
    let mut arena = arena();
    let mut stack = new_stack(&mut arena, 512);
    arena.collect();
    fill(&mut arena, &stack, 0, 8, 50);
    let captured = arena.mutate(|mc| stack.capture(mc, 8));
    assert_eq!(captured, Some(0..8));
    assert_eq!(stack.base(), 8);
    arena.collect_minor();
    churn(&mut arena);
    assert_eq!(rooted_segment(&mut arena, 0..8), expected(8, 50));
    arena.mutate(|mc| {
        assert!(stack.frame(mc, 7).is_none() && stack.frame(mc, 8).is_some());
        assert!(!stack.set(mc, 7, Value::TRUE) && stack.set(mc, 8, Value::TRUE));
        let slots = stack.segment(mc).slots(mc);
        assert!(!stack.write(mc, 7, slots.slice(0..2).unwrap()));
        assert!(stack.capture(mc, 7).is_none() && stack.capture(mc, 513).is_none());
    });
    // A continuation copies its frames back above `base`.
    arena.mutate(|mc| {
        let slots = stack.segment(mc).slots(mc);
        assert!(stack.write(mc, 8, slots.slice(0..8).unwrap()));
    });
    arena.collect_minor();
    churn(&mut arena);
    assert_eq!(frame_values(&mut arena, &stack, 8, 8), expected(8, 50));
}

#[test]
fn switching_segments_retires_the_old_one() {
    let mut arena = arena();
    let mut stack = new_stack(&mut arena, 512);
    arena.collect();
    fill(&mut arena, &stack, 0, 8, 10);
    arena.mutate(|mc| assert!(stack.set(mc, 100, num(mc, 99))));
    stack.set_top(8);
    arena.mutate(|mc| stack.switch(mc, Segment::new(mc, 300).unwrap()));
    assert_eq!((stack.base(), stack.top()), (0, 300));
    assert!(dirty_cards(&arena) > 0, "retiring didn't take the barrier");
    arena.collect_minor();
    churn(&mut arena);
    assert_eq!(rooted_segment(&mut arena, 0..8), expected(8, 10));
    assert_eq!(rooted_segment(&mut arena, 100..101), [None]);
    fill(&mut arena, &stack, 0, 4, 20);
    arena.collect();
    churn(&mut arena);
    assert_eq!(frame_values(&mut arena, &stack, 0, 4), expected(4, 20));
}

#[test]
fn parked_stacks_keep_their_frames() {
    let mut arena = arena();
    let mut stack = new_stack(&mut arena, 512);
    arena.collect();
    fill(&mut arena, &stack, 0, 8, 30);
    stack.set_top(8);
    arena.mutate(|mc| stack.park(mc));
    arena.collect_minor();
    arena.collect();
    churn(&mut arena);
    assert_eq!(frame_values(&mut arena, &stack, 0, 8), expected(8, 30));
    // Getting a frame unparks the stack, so new writes are traced again.
    fill(&mut arena, &stack, 0, 8, 40);
    arena.collect_minor();
    churn(&mut arena);
    assert_eq!(frame_values(&mut arena, &stack, 0, 8), expected(8, 40));
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
    churn(&mut arena);
    assert_eq!(rooted_segment(&mut arena, 0..8), expected(8, 60));
    assert!(arena.meta.stacks.borrow().is_empty());
    arena.collect();
    churn(&mut arena);
    assert_eq!(rooted_segment(&mut arena, 0..8), expected(8, 60));
}

#[test]
fn moved_segments_keep_working() {
    let mut arena = arena();
    let stack = new_stack(&mut arena, 300);
    fill(&mut arena, &stack, 0, 16, 70);
    arena.collect();
    let before = segment_index(&mut arena, &stack);
    arena.set_evacuate_all(true);
    arena.collect();
    arena.set_evacuate_all(false);
    assert_ne!(segment_index(&mut arena, &stack), before, "the segment didn't move");
    churn(&mut arena);
    assert_eq!(frame_values(&mut arena, &stack, 0, 16), expected(16, 70));
    fill(&mut arena, &stack, 0, 16, 80);
    arena.collect_minor();
    churn(&mut arena);
    assert_eq!(frame_values(&mut arena, &stack, 0, 16), expected(16, 80));
}

/// Frames written while marking, to objects being evacuated, are fixed when they move.
#[test]
fn frame_writes_while_marking_are_fixed_by_evacuation() {
    let mut arena = arena();
    let stack = new_stack(&mut arena, 512);
    arena.mutate(|mc| {
        let pair = mc.alloc::<Pair, 2>([num(mc, 5).to_bits(), Value::object(mc, stack.segment(mc)).to_bits()]).unwrap();
        mc.set_root(0, Value::object(mc, pair));
    });
    arena.collect();
    arena.set_evacuate_all(true);
    arena.collect_slice(1);
    arena.mutate(|mc| {
        let pair = mc.root(0).downcast::<Pair>(mc).unwrap();
        stack.frame(mc, 0).unwrap().set(3, pair.value(mc, 0));
    });
    arena.collect_slice(usize::MAX);
    arena.set_evacuate_all(false);
    churn(&mut arena);
    assert_eq!(frame_values(&mut arena, &stack, 0, 4)[3], Some(5));
    arena.mutate(|mc| {
        let pair = mc.root(0).downcast::<Pair>(mc).unwrap();
        assert!(stack.frame(mc, 0).unwrap().get(3) == pair.value(mc, 0));
    });
}

#[test]
fn frames_check_their_bounds() {
    let mut arena = arena();
    let stack = new_stack(&mut arena, 300);
    arena.mutate(|mc| {
        assert!(stack.frame(mc, 0).is_some() && stack.frame(mc, 300 - WINDOW).is_some());
        assert!(stack.frame(mc, 301 - WINDOW).is_none() && stack.frame(mc, usize::MAX).is_none());
        assert!(stack.get(mc, 299).is_some() && stack.get(mc, 300).is_none());
        assert!(!stack.set(mc, 300, Value::TRUE));
        let two = stack.segment(mc).slots(mc).slice(0..2).unwrap();
        assert!(!stack.write(mc, 299, two) && !stack.write(mc, usize::MAX, two));
    });
}

/// Copies between overlapping slots of the stack's own segment move them as `copy_within`
/// does, in either direction.
#[test]
fn writes_from_overlapping_slots_move_them() {
    for shift in [-3isize, -1, 1, 3] {
        let mut arena = arena();
        let stack = new_stack(&mut arena, 512);
        fill(&mut arena, &stack, 0, 20, 100);
        let mut want = expected(20, 100);
        want.resize(30, Some(-1));
        let (from, to) = (5, (5 + shift) as usize);
        want.copy_within(from..from + 10, to);
        arena.mutate(|mc| {
            for i in 20..30 {
                stack.set(mc, i, num(mc, -1));
            }
            let slots = stack.segment(mc).slots(mc);
            assert!(stack.write(mc, to, slots.slice(from..from + 10).unwrap()));
        });
        arena.collect();
        assert_eq!(frame_values(&mut arena, &stack, 0, 30), want, "shifted by {shift}");
    }
}

#[test]
#[should_panic(expected = "different arena")]
fn stacks_belong_to_one_arena() {
    let mut a = arena();
    let mut b = arena();
    let stack = new_stack(&mut a, 300);
    new_stack(&mut b, 300);
    b.mutate(|mc| {
        stack.frame(mc, 0);
    });
}

#[test]
#[should_panic(expected = "already in use")]
fn a_segment_belongs_to_one_stack() {
    let mut arena = arena();
    let _stack = new_stack(&mut arena, 300);
    arena.mutate(|mc| {
        let _ = mc.stack(mc.root(0).downcast::<Segment>(mc).unwrap());
    });
}

#[test]
#[should_panic(expected = "already in use")]
fn switching_to_a_used_segment_panics() {
    let mut arena = arena();
    let _first = new_stack(&mut arena, 300);
    let mut second = arena.mutate(|mc| mc.stack(Segment::new(mc, 300).unwrap()).unwrap());
    arena.mutate(|mc| second.switch(mc, mc.root(0).downcast::<Segment>(mc).unwrap()));
}

#[test]
fn segments_can_be_reused_once_free() {
    let mut arena = arena();
    let mut first = new_stack(&mut arena, 300);
    assert_eq!(first.top(), 300);
    // Switching to the segment it already uses is fine.
    arena.mutate(|mc| first.switch(mc, first.segment(mc)));
    arena.mutate(|mc| first.switch(mc, Segment::new(mc, 300).unwrap()));
    let second = arena.mutate(|mc| mc.stack(mc.root(0).downcast::<Segment>(mc).unwrap()).unwrap());
    // Dropped stacks free their segment at once, and their last trace doesn't void what the
    // segment's next stack wrote.
    fill(&mut arena, &second, 0, 8, 1);
    second.set_top(0);
    drop(second);
    let third = arena.mutate(|mc| mc.stack(mc.root(0).downcast::<Segment>(mc).unwrap()).unwrap());
    fill(&mut arena, &third, 0, 8, 90);
    third.set_top(8);
    arena.collect();
    churn(&mut arena);
    assert_eq!(frame_values(&mut arena, &third, 0, 8), expected(8, 90));
    assert_eq!(arena.meta.stacks.borrow().len(), 2);
}

#[test]
fn lowering_top_while_parked_voids_the_rest() {
    let mut arena = arena();
    let mut stack = new_stack(&mut arena, 512);
    fill(&mut arena, &stack, 0, 20, 0);
    stack.set_top(20);
    arena.mutate(|mc| stack.park(mc));
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
    arena.mutate(|mc| assert!(stack.set(mc, 20, num(mc, 99))));
    stack.set_top(8);
    drop(stack);
    arena.collect();
    churn(&mut arena);
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

/// Random frame writes, captures, switches and parks, with a collection slice after every
/// step, checked against a model of what each slot should hold.
#[test]
fn random_stack_traffic_under_stress() {
    const LEN: usize = 600;
    for (seed, evacuate) in [(0x9e37_79b9_7f4a_7c15, false), (0x2545_f491_4f6c_dd1d, true)] {
        let mut arena = arena();
        let mut stack = new_stack(&mut arena, LEN);
        arena.set_stress(Some(2048));
        arena.set_evacuate_all(evacuate);
        let mut rng = Rng(seed);
        // The live slots of the current segment, and the captured ranges of every segment,
        // which the root keeps as a list, newest first.
        let mut live = vec![None; LEN];
        let mut captured: Vec<Vec<Option<i64>>> = vec![Vec::new()];
        let mut next = 0;
        for _ in 0..400 {
            let op = rng.below(20);
            let top = stack.top().min(LEN);
            arena
                .step(|mc| match op {
                    0 if stack.base() + 1 < top => {
                        let at = stack.base() + 1 + rng.below(top - stack.base() - 1);
                        let range = stack.capture(mc, at).unwrap();
                        captured.last_mut().unwrap().extend_from_slice(&live[range]);
                    }
                    1 => {
                        let segment = Segment::new(mc, LEN).unwrap();
                        stack.switch(mc, segment);
                        let list = [Value::object(mc, segment).to_bits(), mc.root(0).to_bits()];
                        mc.set_root(0, Value::object(mc, mc.alloc::<Pair, 2>(list).unwrap()));
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
                })
                .unwrap();
            if rng.below(4) == 0 {
                let top = stack.base() + rng.below(LEN - stack.base() + 1);
                stack.set_top(top);
                live[top..].fill(None);
            }
            arena.mutate(|mc| {
                for (i, want) in live.iter().enumerate().skip(stack.base()) {
                    if want.is_some() {
                        assert_eq!(read(mc, stack.get(mc, i).unwrap()), *want, "slot {i}");
                    }
                }
                let mut list = mc.root(0);
                for want in captured.iter().rev() {
                    let (segment, rest) = match list.downcast::<Pair>(mc) {
                        Some(pair) => (pair.value(mc, 0), pair.value(mc, 1)),
                        None => (list, Value::NIL),
                    };
                    let slots = segment.downcast::<Segment>(mc).unwrap().slots(mc);
                    for (i, w) in want.iter().enumerate() {
                        if w.is_some() {
                            assert_eq!(read(mc, slots.get(i)), *w, "captured slot {i}");
                        }
                    }
                    list = rest;
                }
            });
        }
    }
}

#[test]
fn stack_allocation_obeys_failure_injection_without_attaching() {
    let mut arena = arena();
    arena.mutate(|mc| mc.set_root(0, Value::object(mc, Segment::new(mc, 512).unwrap())));
    let used = arena.used();
    arena.fail_after(Some(0));
    arena.mutate(|mc| assert!(matches!(mc.stack(mc.root(0).downcast::<Segment>(mc).unwrap()), Err(OutOfMemory))));
    assert_eq!(arena.used(), used);
    assert!(arena.meta.stacks.borrow().is_empty());
    let stack = arena.mutate(|mc| mc.stack(mc.root(0).downcast::<Segment>(mc).unwrap()).unwrap());
    fill(&mut arena, &stack, 0, 1, 7);
    arena.collect();
    assert_eq!(frame_values(&mut arena, &stack, 0, 1), [Some(7)]);
}
