use crate::{Arena, Box, CollectIn, Vec, vec_in};

#[test]
fn boxes_and_vectors_hold_what_they_were_given() {
    let arena = Arena::new();
    let b = Box::new_in((1, "one"), &arena);
    assert_eq!(*b, (1, "one"));
    assert_eq!(Box::into_inner(b), (1, "one"));

    let mut v = vec_in![&arena; 1, 2, 3];
    v.push(4);
    v.insert(0, 0);
    assert_eq!(v.as_slice(), [0, 1, 2, 3, 4]);
    assert_eq!(v.remove(1), 1);
    v.retain(|&x| x != 3);
    assert_eq!(v.split_off(2).as_slice(), [4]);
    assert_eq!(v.drain(..).rev().collect::<std::vec::Vec<_>>(), [2, 0]);
    assert!(v.is_empty());

    let mut sevens = arena.vec_of(7, 3);
    assert_eq!(sevens.as_slice(), [7, 7, 7]);
    sevens.resize(4, 8);
    assert_eq!(sevens.as_slice(), [7, 7, 7, 8]);
    let w = (0..5).map(|x| x * x).collect_in(&arena);
    assert_eq!(w.clone(), w);
    assert_eq!(w.into_iter().rev().collect::<std::vec::Vec<_>>(), [16, 9, 4, 1, 0]);
    let all: Result<Vec<'_, i32>, &str> = [Ok(1), Err("two"), Ok(3)].into_iter().try_collect_in(&arena);
    assert_eq!(all, Err("two"));
}

#[test]
fn what_a_box_holds_is_dropped_with_it() {
    use std::cell::Cell;
    struct Counted<'c>(&'c Cell<u32>);
    impl Drop for Counted<'_> {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }
    let drops = Cell::new(0);
    let arena = Arena::new();
    drop(Box::new_in(Counted(&drops), &arena));
    drop(vec_in![&arena; Counted(&drops), Counted(&drops)]);
    assert_eq!(drops.get(), 3);
}
