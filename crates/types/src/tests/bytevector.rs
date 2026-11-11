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

/// Bytes that say when they're dropped.
struct Watched(Vec<u8>, std::rc::Rc<std::cell::Cell<bool>>);

impl AsRef<[u8]> for Watched {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl Drop for Watched {
    fn drop(&mut self) {
        self.1.set(true);
    }
}

/// External bytes read like any others, stay outside the arena while the bytevector is
/// reachable, through moving collections, and their owner is dropped once it isn't.
#[test]
fn external_bytevectors_keep_their_owner_while_reachable() {
    let dropped = std::rc::Rc::new(std::cell::Cell::new(false));
    let bytes: Vec<u8> = (0..203u32).map(|i| (i * 7) as u8).collect();
    let mut arena = Arena::new(4 << 20, 1);
    arena.set_evacuate_all(true);
    arena.mutate(|mc| {
        let h = Bytevectors::new(mc);
        let v = h.external(Watched(bytes.clone(), dropped.clone())).unwrap();
        assert!(v.is_external() && !v.is_mutable() && h.mutable(v.value(mc)).is_none());
        assert_eq!(AnyBytevector::of(v.value(mc)), Some(v));
        mc.set_root(0, v.value(mc));
        let short = h.external(vec![1, 2, 3]).unwrap();
        assert!(!short.is_external(), "short externals are copied");
        assert_eq!(short.to_vec(mc), [1, 2, 3]);
    });
    arena.collect();
    arena.collect();
    assert!(!dropped.get());
    arena.mutate(|mc| {
        let h = Bytevectors::new(mc);
        let v = AnyBytevector::of(mc.root(0)).unwrap();
        assert_eq!((v.len(mc), v.get(mc, 202), v.get(mc, 203)), (203, Some(bytes[202]), None));
        assert_eq!(v.to_vec(mc), bytes);
        let copy = AnyBytevector::Mutable(h.from_slice(&bytes).unwrap());
        assert!(v.same_bytes(mc, copy) && copy.same_bytes(mc, v));
        for (start, end) in [(0, 0), (0, 203), (3, 9), (8, 16), (13, 203), (200, 203)] {
            assert_eq!(*v.bytes(mc, start, end), bytes[start..end]);
            assert_eq!(*copy.bytes(mc, start, end), bytes[start..end], "{start}..{end}");
        }
        for (at, size) in [(0, 8), (5, 8), (199, 4), (200, 3), (202, 1)] {
            assert_eq!(v.get_uint(mc, at, size), copy.get_uint(mc, at, size), "{size} at {at}");
        }
        assert_eq!(v.get_uint(mc, 200, 4), None);
        mc.set_root(0, crate::gc::Value::FALSE);
    });
    arena.collect();
    arena.collect();
    assert!(dropped.get(), "the owner went with its bytevector");
}

impl AsMut<[u8]> for Watched {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.0
    }
}

/// A buffer the host gives the arena is written through a bytevector like any other's bytes,
/// stays outside the arena however short it is, and is dropped once nothing reaches it.
#[test]
fn external_mutable_bytevectors_write_their_buffer() {
    let dropped = std::rc::Rc::new(std::cell::Cell::new(false));
    let bytes: Vec<u8> = (0..19u8).map(|i| i * 13).collect();
    let mut arena = Arena::new(4 << 20, 1);
    arena.set_evacuate_all(true);
    arena.mutate(|mc| {
        let h = Bytevectors::new(mc);
        let v = h.external_mutable(Watched(bytes.clone(), dropped.clone())).unwrap();
        let any = AnyBytevector::Mutable(v);
        assert!(any.is_external() && any.is_mutable());
        assert_eq!((AnyBytevector::of(v.value(mc)), h.mutable(v.value(mc))), (Some(any), Some(v)));
        let copy = h.from_slice(&bytes).unwrap();
        assert!(any.same_bytes(mc, AnyBytevector::Mutable(copy)));
        assert_eq!((any.len(mc), any.get(mc, 18), any.get(mc, 19), any.to_vec(mc)), (19, Some(234), None, bytes.clone()));
        for (at, size, value) in [(0, 1, 0xAB), (3, 8, 0x0102_0304_0506_0708), (6, 4, 0xDEAD_BEEF), (15, 4, 0xFFFF_FFFF_FFFF), (18, 1, 7)] {
            assert!(v.set_uint(mc, at, size, value) && copy.set_uint(mc, at, size, value));
            assert_eq!(any.get_uint(mc, at, size), AnyBytevector::Mutable(copy).get_uint(mc, at, size), "{size} at {at}");
            assert_eq!(any.to_vec(mc), AnyBytevector::Mutable(copy).to_vec(mc), "{size} at {at}");
        }
        assert!(v.set(mc, 1, 99) && !v.set(mc, 19, 1) && !v.set_uint(mc, 16, 4, 0) && !v.set_uint(mc, usize::MAX, 2, 0));
        assert_eq!(*any.bytes(mc, 1, 4), [99, 26, 8]);
        mc.set_root(0, v.value(mc));
        assert!(AnyBytevector::Mutable(h.external_mutable(vec![1, 2]).unwrap()).is_external(), "short ones stay outside");
    });
    arena.collect();
    arena.collect();
    assert!(!dropped.get());
    arena.mutate(|mc| {
        let v = AnyBytevector::of(mc.root(0)).unwrap();
        assert_eq!((v.len(mc), v.get(mc, 0), v.get(mc, 1), v.get(mc, 18)), (19, Some(0xAB), Some(99), Some(7)));
        mc.set_root(0, crate::gc::Value::FALSE);
    });
    arena.collect();
    arena.collect();
    assert!(dropped.get(), "the buffer went with its bytevector");
}
