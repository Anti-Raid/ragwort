use crate::gc::Arena;

use super::*;

#[test]
fn bytes_pack_and_read_back() {
    Arena::new(4 << 20, 1).mutate(|mc| {
        let h = Bytevectors::new(mc);
        let bytes: Vec<u8> = (0..19).map(|i| i * 13).collect();
        let v = AnyBytevector::Mutable(h.from_slice(&bytes).unwrap());
        assert_eq!(v.to_vec(mc), bytes);
        assert_eq!((v.len(mc), v.get(mc, 18), v.get(mc, 19)), (19, Some(234), None));
        let made = h.make(11, 7).unwrap();
        assert!(made.set(mc, 9, 200));
        assert!(!made.set(mc, 11, 1));
        let made = AnyBytevector::Mutable(made);
        assert_eq!(made.to_vec(mc), [7, 7, 7, 7, 7, 7, 7, 7, 7, 200, 7]);
        let literal = h.immutable_from_slice(&[7, 7, 7, 7, 7, 7, 7, 7, 7, 200, 7]).unwrap();
        assert!(made.same_bytes(mc, literal) && !literal.is_mutable());
        assert!(h.mutable(literal.value(mc)).is_none());
        assert!(!literal.same_bytes(mc, h.immutable_from_slice(&[7; 11]).unwrap()));
        assert!(h.make(0, 1).unwrap().value(mc) != h.make(0, 1).unwrap().value(mc));
        assert_eq!(h.bytevector(Value::NIL), None);
    });
}

#[test]
fn integers_of_up_to_8_bytes_read_and_write_at_any_offset() {
    Arena::new(4 << 20, 1).mutate(|mc| {
        let h = Bytevectors::new(mc);
        let model: Vec<u8> = (0..20u32).map(|i| (i * 37 + 5) as u8).collect();
        let v = h.from_slice(&model).unwrap();
        for size in 1..=8 {
            for at in 0..=model.len() {
                let mut want = [0; 8];
                let fits = at + size <= model.len();
                if fits {
                    want[..size].copy_from_slice(&model[at..at + size]);
                }
                let got = AnyBytevector::Mutable(v).get_uint(mc, at, size);
                assert_eq!(got, fits.then(|| u64::from_le_bytes(want)), "{size} at {at}");
                let mut wrote = model.clone();
                let value = 0x0123_4567_89ab_cdef_u64.rotate_left(at as u32);
                if fits {
                    wrote[at..at + size].copy_from_slice(&value.to_le_bytes()[..size]);
                }
                assert_eq!(v.set_uint(mc, at, size, value), fits);
                assert_eq!(AnyBytevector::Mutable(v).to_vec(mc), wrote, "{size} at {at}");
                for (i, &b) in model.iter().enumerate() {
                    assert!(v.set(mc, i, b));
                }
            }
        }
        assert!(!v.set_uint(mc, usize::MAX, 2, 0));
        assert_eq!(AnyBytevector::Mutable(v).get_uint(mc, usize::MAX, 2), None);
    });
}
