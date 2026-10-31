use ragwort_gc::{Arena, Rootable};

use super::*;

struct Unit;
impl Rootable for Unit {
    type Root<'gc> = ();
}

#[test]
fn scratch_vecs_count_against_the_budget_while_they_live() {
    let mut arena = Arena::<Unit>::new(4 << 20, |_| Ok(())).unwrap();
    let before = arena.metrics().used;
    arena
        .mutate(|mc, _| {
            let mut scratch = ScratchVec::new(mc);
            for i in 0..1000u64 {
                scratch.push(i).unwrap();
            }
            assert!(mc.used() >= before + 1000 * 8);
            assert_eq!(scratch.iter().sum::<u64>(), 999 * 1000 / 2);
            scratch.truncate(10);
            assert_eq!(scratch.pop(), Some(9));
            let mut huge = ScratchVec::<u64>::new(mc);
            assert_eq!(huge.reserve(mc.limit()), Err(OutOfMemory));
            assert_eq!(huge.reserve(usize::MAX), Err(OutOfMemory));
            assert!(huge.is_empty());
        })
        .unwrap();
    assert_eq!(arena.metrics().used, before);
}
