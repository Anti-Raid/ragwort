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
