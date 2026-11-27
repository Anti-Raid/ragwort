use super::*;
use crate::gc::{Arena, Value, objects};

objects! {
    kind Kind;
    struct Text { chars: Frozen<Box<[u8]>>, next: Member<Text> }
}

/// The chunks follow each other without a gap: every slot number has one place, and the places of a chunk are its slots in order.
#[test]
fn every_slot_number_has_one_place() {
    let mut expected = (0, 0);
    for number in 0..SMALL + 5 * LARGEST {
        assert_eq!(place(number), expected, "slot {number}");
        assert_eq!(first(expected.0) + expected.1, number);
        expected = if expected.1 + 1 == size(expected.0) { (expected.0 + 1, 0) } else { (expected.0, expected.1 + 1) };
    }
    assert_eq!((size(0), size(DOUBLING - 1), size(DOUBLING), size(DOUBLING + 9)), (FIRST, LARGEST / 2, LARGEST, LARGEST));
}

/// A table with few values is small, whatever the arena's limit. It grows as values are added, every value stays where it is, and the
/// slots of freed values are used again.
#[test]
fn the_table_grows_with_its_values() {
    let mut arena = Arena::new(64 << 20, 1);
    let empty = arena.meta.frozen.table_bytes();
    assert!(empty < 8 << 10, "{empty} bytes for a table with no values");
    let mut made = 0u32;
    for (count, most) in [(10, FIRST), (1000, 2048), (30_000, 4 * LARGEST + SMALL)] {
        arena.mutate(|mc| {
            let mut list = mc.root(0).downcast::<Text>(mc);
            while made < count {
                let chars: Box<[u8]> = made.to_le_bytes().into();
                list = Some(Text::new(mc, mc.frozen(chars).unwrap(), list).unwrap());
                made += 1;
            }
            mc.set_root(0, Value::object(mc, list.unwrap()));
        });
        arena.collect();
        assert_eq!(arena.frozen_values(), count as usize);
        let slots = arena.meta.frozen.made.get();
        assert!(slots >= count as usize && slots <= most, "{slots} slots for {count} values");
        // Every value is read back, the newest first.
        arena.mutate(|mc| {
            let (mut text, mut number) = (mc.root(0).downcast::<Text>(mc), count);
            while let Some(held) = text {
                number -= 1;
                assert_eq!(held.chars(mc).map(|chars| &chars[..]), Some(&number.to_le_bytes()[..]));
                text = held.next(mc);
            }
            assert_eq!(number, 0);
        });
    }
    // The values die. New values take their slots, so the table does not grow.
    let before = arena.meta.frozen.made.get();
    arena.mutate(|mc| mc.set_root(0, Value::NULL));
    arena.collect();
    assert_eq!(arena.frozen_values(), 0);
    for _ in 0..3 {
        arena.mutate(|mc| {
            for number in 0..20_000u32 {
                let chars: Box<[u8]> = number.to_le_bytes().into();
                mc.frozen(chars).unwrap();
            }
        });
        arena.collect();
    }
    assert_eq!((arena.frozen_values(), arena.meta.frozen.made.get()), (0, before));
}
