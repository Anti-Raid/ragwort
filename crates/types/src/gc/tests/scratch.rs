use super::*;
use crate::gc::Arena;

#[test]
fn scratch_vecs_count_against_the_budget_while_they_live() {
    let mut arena = Arena::new(4 << 20, 1);
    let before = arena.used();
    arena.mutate(|mc| {
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
    });
    assert_eq!(arena.used(), before);
}
