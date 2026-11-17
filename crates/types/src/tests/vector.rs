use std::cell::Cell;
use std::rc::Rc;

use crate::gc::Arena;

use super::*;
use crate::pair::Pairs;

fn arena() -> Arena {
    Arena::new(4 << 20, 1)
}

fn fix<'gc>(n: i64) -> Value<'gc> {
    Value::fixnum(n).unwrap()
}

fn read<'gc>(mc: &Mutation<'gc>, v: Vector<'gc>) -> Vec<Value<'gc>> {
    let items = v.items(mc);
    (0..items.len()).map(|i| items.get(i)).collect()
}

#[test]
fn vectors_hold_what_they_were_made_with() {
    arena().mutate(|mc| {
        let h = Vectors::new(mc);
        let made = h.make(5, Value::TRUE).unwrap();
        assert_eq!(read(mc, made), [Value::TRUE; 5]);
        let items: Vec<_> = (0..7).map(fix).collect();
        assert_eq!(read(mc, h.from_slice(&items).unwrap()), items);
        assert!(h.make(0, Value::NULL).unwrap().items(mc).is_empty());
        assert!(h.from_slice(&[]).unwrap().items(mc).is_empty());
        let slots = made.items(mc);
        slots.set(mc, 2, fix(9));
        assert_eq!(slots.get(2), fix(9));
        slots.slice(3..5).unwrap().fill(mc, Value::FALSE);
        assert_eq!(read(mc, made), [Value::TRUE, Value::TRUE, fix(9), Value::FALSE, Value::FALSE]);
    });
}

#[test]
fn only_vectors_are_vectors() {
    arena().mutate(|mc| {
        let h = Vectors::new(mc);
        let v = h.make(2, Value::NULL).unwrap().value(mc);
        assert!(h.vector(v).is_some_and(AnyVector::is_mutable) && h.mutable(v).is_some());
        let pair = Pairs::new(mc).cons(fix(1), fix(2)).unwrap().value(mc);
        assert!(h.vector(pair).is_none() && h.mutable(pair).is_none());
        assert!(h.vector(fix(1)).is_none() && h.vector(Value::NULL).is_none());
    });
}

#[test]
fn vectors_too_long_for_the_arena_fail() {
    arena().mutate(|mc| {
        let h = Vectors::new(mc);
        assert_eq!(h.make(usize::MAX, Value::NULL).unwrap_err(), OutOfMemory);
        assert_eq!(h.make(1 << 20, Value::NULL).unwrap_err(), OutOfMemory, "past the limit");
    });
}

/// Each way of storing into an old vector keeps the stored young objects alive through minor
/// collections. The vector's slots are updated when compaction moves those objects.
#[test]
fn stores_into_old_vectors_keep_young_objects() {
    let mut arena = arena();
    arena.set_evacuate_all(true);
    arena.mutate(|mc| mc.set_root(0, Vectors::new(mc).make(64, Value::NULL).unwrap().value(mc)));
    arena.collect();
    arena.mutate(|mc| {
        let v = Vectors::new(mc).mutable(mc.root(0)).unwrap();
        let p = Pairs::new(mc);
        let slots = v.items(mc);
        slots.set(mc, 0, p.list(&[fix(0)]).unwrap());
        slots.slice(10..20).unwrap().fill(mc, p.list(&[fix(1), fix(1)]).unwrap());
        let fresh = Vectors::new(mc).from_slice(&[p.list(&[fix(2), fix(2), fix(2)]).unwrap(); 8]).unwrap();
        slots.slice(40..48).unwrap().copy_from(mc, fresh.items(mc));
        // The two ranges overlap, so the copy runs backwards.
        slots.slice(41..49).unwrap().copy_from(mc, slots.slice(40..48).unwrap());
    });
    fn check(arena: &mut Arena) {
        arena.mutate(|mc| {
            let v = Vectors::new(mc).vector(mc.root(0)).unwrap();
            let p = Pairs::new(mc);
            assert_eq!(p.list_len(v.get(mc, 0).unwrap()), Some(1));
            assert!((10..20).all(|i| p.list_len(v.get(mc, i).unwrap()) == Some(2)));
            assert!((40..49).all(|i| p.list_len(v.get(mc, i).unwrap()) == Some(3)));
            assert_eq!(v.get(mc, 49), Some(Value::NULL));
        });
    }
    arena.collect_minor();
    check(&mut arena);
    arena.collect();
    check(&mut arena);
    // The live objects are the vector and three lists, of one, two and three pairs.
    assert_eq!(arena.objects(), 1 + 1 + 2 + 3);
}

#[test]
fn immutable_vectors_can_be_read_but_not_written() {
    arena().mutate(|mc| {
        let h = Vectors::new(mc);
        let items: Vec<_> = (0..4).map(fix).collect();
        let v = h.immutable_from_slice(&items).unwrap().value(mc);
        let any = h.vector(v).unwrap();
        assert!(!any.is_mutable() && h.mutable(v).is_none(), "vector-set! can't reach it");
        assert_eq!((any.len(mc), any.get(mc, 3), any.get(mc, 4)), (4, Some(fix(3)), None));
        assert_eq!(any.value(mc), v);
        let empty = h.vector(h.immutable_from_slice(&[]).unwrap().value(mc)).unwrap();
        assert!(empty.is_empty(mc) && empty.get(mc, 0).is_none());
    });
}

/// Freezing a mutable vector copies it, so later writes to the vector do not show in the copy.
/// Freezing an immutable vector returns the same vector.
#[test]
fn freezing_takes_a_snapshot() {
    arena().mutate(|mc| {
        let h = Vectors::new(mc);
        let v = h.make(3, fix(1)).unwrap();
        let frozen = h.freeze(AnyVector::Mutable(v)).unwrap();
        v.items(mc).set(mc, 0, fix(2));
        assert_eq!((0..3).map(|i| frozen.get(mc, i).unwrap()).collect::<Vec<_>>(), [fix(1); 3]);
        assert_eq!(h.freeze(AnyVector::Immutable(frozen)).unwrap(), frozen);
    });
}

#[test]
fn immutable_vectors_keep_what_they_hold() {
    let mut arena = arena();
    arena.set_evacuate_all(true);
    arena.mutate(|mc| {
        let p = Pairs::new(mc);
        let items: Vec<_> = (0..20).map(|i| p.list(&vec![fix(i); i as usize + 1]).unwrap()).collect();
        let v = Vectors::new(mc).immutable_from_slice(&items).unwrap();
        mc.set_root(0, v.value(mc));
        p.list(&[fix(0); 50]).unwrap();
    });
    for _ in 0..2 {
        arena.collect_minor();
        arena.collect();
        assert_eq!(arena.objects(), 1 + (1..=20).sum::<usize>());
        arena.mutate(|mc| {
            let v = Vectors::new(mc).vector(mc.root(0)).unwrap();
            let p = Pairs::new(mc);
            assert!((0..20).all(|i| p.list_len(v.get(mc, i).unwrap()) == Some(i as u64 + 1)));
        });
    }
}

/// The names that an event mentions, owned by the host. `reads` counts the calls of `get`. `dropped` is set when the arena drops the host's value.
struct Names {
    names: Vec<&'static str>,
    reads: Rc<Cell<usize>>,
    dropped: Rc<Cell<bool>>,
}

impl Drop for Names {
    fn drop(&mut self) {
        self.dropped.set(true);
    }
}

impl ExternalVector for Names {
    fn len(&self) -> usize {
        self.names.len()
    }

    fn get<'gc>(&self, mc: &Mutation<'gc>, index: usize) -> Result<Value<'gc>, Error> {
        self.reads.set(self.reads.get() + 1);
        Ok(crate::string::from_str(&crate::string::Strings::new(mc), self.names[index])?.value())
    }
}

/// Numbers that the host owns and programs can modify. The host accepts only fixnums.
struct Numbers(Vec<i64>);

impl ExternalVector for Numbers {
    const WRITABLE: bool = true;

    fn len(&self) -> usize {
        self.0.len()
    }

    fn get<'gc>(&self, _: &Mutation<'gc>, index: usize) -> Result<Value<'gc>, Error> {
        Ok(fix(self.0[index]))
    }

    fn set<'gc>(&mut self, _: &Mutation<'gc>, index: usize, value: Value<'gc>) -> Result<(), Refused> {
        self.0[index] = value.as_fixnum().ok_or(Refused)?;
        Ok(())
    }
}

/// A program reads an external vector like any other. Each element is read from the host once. The vector returns that cached value from then on.
#[test]
fn an_external_vector_is_read_from_its_host_once() {
    let (reads, dropped) = (Rc::new(Cell::new(0)), Rc::new(Cell::new(false)));
    let mut arena = arena();
    arena.mutate(|mc| {
        let names = vec!["a name that is too long to fit in a word", "bo", "cy"];
        let vector = Vectors::new(mc).external(Names { names, reads: reads.clone(), dropped: dropped.clone() }, 64).unwrap();
        let every = EveryVector::of(vector.value(mc)).unwrap();
        assert_eq!((every, every.len(mc), every.is_writable(mc), reads.get()), (EveryVector::External(vector), 3, false, 0));
        // An external vector is not an `AnyVector`, which is the kind of vector that the arena's own data is built from.
        assert!(AnyVector::of(vector.value(mc)).is_none() && Vector::of(vector.value(mc)).is_none() && ExternVector::of(fix(1)).is_none());
        let first = every.get(mc, 0).unwrap().unwrap();
        assert_eq!((every.get(mc, 0), every.get(mc, 0), reads.get()), (Ok(Some(first)), Ok(Some(first)), 1));
        assert_eq!((every.get(mc, 2).map(|name| name.is_some()), every.get(mc, 3), every.get(mc, usize::MAX), reads.get()), (Ok(true), Ok(None), Ok(None), 2));
        assert_eq!((vector.set(mc, 0, fix(1)), vector.set(mc, 9, fix(1)), reads.get()), (Err(VectorError::Immutable), Err(VectorError::Immutable), 2));
        assert_eq!(vector.host::<Names>(mc).map(|host| host.names.len()), Some(3));
        assert!(vector.host::<Numbers>(mc).is_none());
        mc.set_root(0, Pairs::new(mc).list(&[vector.value(mc), first]).unwrap());
    });
    // The cached values survive a collection that moves objects, and are still not read from the host again.
    arena.set_evacuate_all(true);
    arena.collect();
    arena.mutate(|mc| {
        let kept: Vec<_> = Pairs::new(mc).elements(mc.root(0)).collect();
        let every = EveryVector::of(kept[0]).unwrap();
        assert_eq!((every.get(mc, 0), reads.get()), (Ok(Some(kept[1])), 2));
        assert_eq!((every.get(mc, 1).map(|name| name.is_some()), reads.get()), (Ok(true), 3));
        mc.set_root(0, Value::NULL);
    });
    assert!(!dropped.get());
    arena.collect();
    arena.collect();
    assert!(dropped.get());
}

/// A write to a writable external vector changes the host's elements. A later read returns the value that was written, as it does for a vector in the arena.
#[test]
fn a_writable_external_vector_changes_its_hosts_elements() {
    arena().mutate(|mc| {
        let vector = Vectors::new(mc).external(Numbers(vec![1, 2, 3]), 24).unwrap();
        let every = EveryVector::of(vector.value(mc)).unwrap();
        assert!(every.is_writable(mc) && vector.is_writable(mc) && !vector.is_empty(mc));
        assert_eq!(every.get(mc, 1), Ok(Some(fix(2))));
        vector.set(mc, 1, fix(20)).unwrap();
        vector.set(mc, 2, fix(30)).unwrap();
        assert_eq!((every.get(mc, 0), every.get(mc, 1), every.get(mc, 2)), (Ok(Some(fix(1))), Ok(Some(fix(20))), Ok(Some(fix(30)))));
        assert_eq!(vector.host::<Numbers>(mc).map(|host| host.0.clone()), Some(vec![1, 20, 30]));
        // The host rejects a value that it cannot hold. An index at or past the length is rejected before the host is called.
        assert_eq!((vector.set(mc, 0, Value::TRUE), vector.set(mc, 3, fix(4))), (Err(VectorError::Refused), Err(VectorError::OutOfRange)));
        assert_eq!((every.get(mc, 0), vector.host::<Numbers>(mc).map(|host| host.0.clone())), (Ok(Some(fix(1))), Some(vec![1, 20, 30])));
        let empty = Vectors::new(mc).external(Numbers(Vec::new()), 0).unwrap();
        assert_eq!((empty.len(mc), empty.is_empty(mc), empty.get(mc, 0), empty.set(mc, 0, fix(1))), (0, true, Ok(None), Err(VectorError::OutOfRange)));
    });
}

/// `EveryVector::set` writes to whichever kind of vector it is given, and fails with the error of that kind.
#[test]
fn any_vector_is_set_through_one_method() {
    arena().mutate(|mc| {
        let vectors = Vectors::new(mc);
        let mutable = EveryVector::of(vectors.make(2, fix(0)).unwrap().value(mc)).unwrap();
        assert_eq!((mutable.set(mc, 1, fix(5)), mutable.get(mc, 1), mutable.set(mc, 2, fix(6))), (Ok(()), Ok(Some(fix(5))), Err(VectorError::OutOfRange)));
        let frozen = EveryVector::of(vectors.immutable_from_slice(&[fix(1)]).unwrap().value(mc)).unwrap();
        assert_eq!((frozen.set(mc, 0, fix(5)), frozen.get(mc, 0)), (Err(VectorError::Immutable), Ok(Some(fix(1)))));
        let numbers = EveryVector::of(vectors.external(Numbers(vec![1, 2]), 0).unwrap().value(mc)).unwrap();
        assert_eq!((numbers.set(mc, 0, fix(9)), numbers.get(mc, 0), numbers.set(mc, 2, fix(9)), numbers.set(mc, 1, Value::TRUE)), (Ok(()), Ok(Some(fix(9))), Err(VectorError::OutOfRange), Err(VectorError::Refused)));
    });
}

/// The squares of the indices below a length. The host computes each square when it is requested. `reads` counts the calls of `get`.
struct Squares {
    len: usize,
    reads: Rc<Cell<usize>>,
}

impl ExternalVector for Squares {
    const WRITABLE: bool = true;

    fn len(&self) -> usize {
        self.len
    }

    fn get<'gc>(&self, _: &Mutation<'gc>, index: usize) -> Result<Value<'gc>, Error> {
        self.reads.set(self.reads.get() + 1);
        Ok(fix((index * index) as i64))
    }

    fn set<'gc>(&mut self, _: &Mutation<'gc>, _: usize, _: Value<'gc>) -> Result<(), Refused> {
        Ok(())
    }
}

/// Reading a few elements of a long external vector allocates cache chunks for those elements and their neighbors, not a slot for every element. Each element is still read from the host once, wherever it is in the vector.
#[test]
fn a_long_external_vector_remembers_what_is_read_in_chunks() {
    let reads = Rc::new(Cell::new(0));
    let mut arena = Arena::new(4 << 20, 1);
    arena.mutate(|mc| mc.set_root(0, Vectors::new(mc).external(Squares { len: 10_000, reads: reads.clone() }, 0).unwrap().value(mc)));
    let before = arena.used();
    arena.mutate(|mc| {
        let vector = ExternVector::of(mc.root(0)).unwrap();
        assert_eq!((vector.get(mc, 5000), vector.get(mc, 5000), reads.get()), (Ok(Some(fix(25_000_000))), Ok(Some(fix(25_000_000))), 1));
    });
    // After one read, the cache is the vector of chunks and one chunk. That is a small fraction of a slot for each of the 10,000 elements.
    let one = arena.used() - before;
    assert!(one < 4096, "{one} bytes after one read");
    arena.mutate(|mc| {
        let vector = ExternVector::of(mc.root(0)).unwrap();
        // Read the first and the last element of a chunk, and the first and the last element of the vector, whose last chunk is short. Then read the index past the end.
        for index in [0, 63, 64, 127, 128, 9983, 9984, 9999] {
            assert_eq!(vector.get(mc, index), Ok(Some(fix((index * index) as i64))), "{index}");
        }
        assert_eq!((vector.get(mc, 10_000), reads.get()), (Ok(None), 9));
        // A write is cached like a read, both in a chunk that is not allocated yet and in a chunk that is.
        vector.set(mc, 300, fix(-1)).unwrap();
        vector.set(mc, 5000, fix(-2)).unwrap();
        assert_eq!((vector.get(mc, 300), vector.get(mc, 5000), vector.get(mc, 301), reads.get()), (Ok(Some(fix(-1))), Ok(Some(fix(-2))), Ok(Some(fix(301 * 301))), 10));
    });
    arena.mutate(|mc| {
        let vector = ExternVector::of(mc.root(0)).unwrap();
        for index in 0..10_000 {
            let expected = match index {
                300 => -1,
                5000 => -2,
                _ => (index * index) as i64,
            };
            assert_eq!(vector.get(mc, index), Ok(Some(fix(expected))));
        }
        // Every element was read from the host exactly once, except element 300, which was written before it was ever read. The second pass reads nothing from the host.
        assert_eq!(reads.get(), 10_000 - 1);
        for index in (0..10_000).step_by(7) {
            assert!(vector.get(mc, index).unwrap().is_some());
        }
        assert_eq!(reads.get(), 10_000 - 1);
    });
    // After every element is read, the cache takes little more than one slot for each element.
    let all = arena.used() - before;
    assert!(all < 10_000 * 8 * 5 / 4, "{all} bytes after reading everything");
    // Check vectors of one element, of exactly one chunk, and of one element more than a chunk.
    arena.mutate(|mc| {
        for len in [1, 64, 65] {
            let vector = Vectors::new(mc).external(Squares { len, reads: reads.clone() }, 0).unwrap();
            for index in 0..len {
                assert_eq!(vector.get(mc, index), Ok(Some(fix((index * index) as i64))), "{index} of {len}");
            }
            assert_eq!(vector.get(mc, len), Ok(None));
        }
    });
}
