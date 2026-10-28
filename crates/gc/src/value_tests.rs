use std::cell::{Cell, RefCell};
use std::collections::{HashMap, VecDeque};
use std::hint::black_box;
use std::marker::PhantomData;
use std::rc::Rc;

use super::*;

#[derive(Trace, Plain)]
struct Pair<'gc> {
    car: Lock<Value<'gc>>,
    cdr: Lock<Value<'gc>>,
}

#[derive(Trace, Plain)]
struct Num(i64);

#[derive(Trace, Plain)]
#[gc(items = Lock<Value<'gc>>)]
struct Vector<'gc>(PhantomData<&'gc ()>);

fn cons<'gc>(mc: &Mutation<'gc>, car: Value<'gc>, cdr: Value<'gc>) -> Value<'gc> {
    Value::object(mc, mc.alloc(Pair { car: Lock::new(car), cdr: Lock::new(cdr) }).unwrap())
}

fn fix<'gc>(n: i64) -> Value<'gc> {
    Value::fixnum(n).unwrap()
}

fn vector<'gc>(mc: &Mutation<'gc>, len: usize, fill: impl Fn(usize) -> Value<'gc>) -> Value<'gc> {
    Value::object(mc, mc.alloc_inline(Vector(PhantomData), len, |i| Lock::new(fill(i))).unwrap())
}

fn items<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> &'gc [Lock<Value<'gc>>] {
    v.downcast::<Vector>(mc).unwrap().items()
}

/// A list of `0..n`, with each element boxed in a pair: `((0) (1) ...)`.
fn list<'gc>(mc: &Mutation<'gc>, n: i64) -> Value<'gc> {
    (0..n).rev().fold(Value::NIL, |tail, i| cons(mc, cons(mc, fix(i), Value::NIL), tail))
}

fn read_list<'gc>(mc: &Mutation<'gc>, mut v: Value<'gc>) -> Vec<i64> {
    let mut out = Vec::new();
    while let Some(pair) = v.downcast::<Pair>(mc) {
        out.push(pair.car.get().downcast::<Pair>(mc).unwrap().car.get().as_fixnum().unwrap());
        v = pair.cdr.get();
    }
    assert_eq!(v, Value::NIL);
    out
}

struct ValueRoot;
impl Rootable for ValueRoot {
    type Root<'gc> = Lock<Value<'gc>>;
}

fn value_arena(limit: usize) -> Arena<ValueRoot> {
    Arena::new(limit, |_| Ok(Lock::new(Value::NIL))).unwrap()
}

struct TwoRoot;
impl Rootable for TwoRoot {
    type Root<'gc> = (Lock<Value<'gc>>, Lock<Value<'gc>>);
}

#[derive(Trace)]
struct Vm<'gc> {
    stack: RefCell<Vec<Value<'gc>>>,
    frames: RefCell<VecDeque<Value<'gc>>>,
    globals: RefCell<HashMap<u32, Value<'gc>>>,
    constants: Box<[Value<'gc>]>,
    acc: Cell<Value<'gc>>,
    scratch: RefLock<Option<Value<'gc>>>,
}

struct VmRoot;
impl Rootable for VmRoot {
    type Root<'gc> = Vm<'gc>;
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

fn check_flonum<'gc>(mc: &Mutation<'gc>, v: Value<'gc>, f: f64) {
    assert_eq!(v.as_flonum(mc).map(f64::to_bits), Some(f.to_bits()), "{f:e}");
    assert!(v.is_flonum() && !v.is_fixnum() && v.as_object().is_none() && v.as_char().is_none());
    assert!(matches!(v.unpack(mc), Unpacked::Flonum(g) if g.to_bits() == f.to_bits()));
}

const SPECIALS: [u64; 6] = [0, 1 << 63, 0x7FF0 << 48, 0xFFF0 << 48, 0x7FF8 << 48, 0xFFF8 << 48];
/// The inline doubles whose words the specials took.
const DISPLACED: [u64; 6] = [0x3000 << 48, 0xB000 << 48, (0x3000 << 48) + 1, (0xB000 << 48) + 1, (0x3000 << 48) + 2, (0xB000 << 48) + 2];

fn fits_inline(bits: u64) -> bool {
    SPECIALS.contains(&bits) || (matches!(bits >> 60 & 7, 3 | 4) && !DISPLACED.contains(&bits))
}

#[test]
fn flonums_round_trip() {
    let mut doubles = vec![
        0.0,
        -0.0,
        1.0,
        -1.0,
        0.1,
        1.5,
        -2.5e10,
        1e77,
        1e-77,
        1e78,
        1e-78,
        f64::MAX,
        f64::MIN,
        f64::MIN_POSITIVE,
        f64::EPSILON,
        5e-324,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::NAN,
        -f64::NAN,
    ];
    doubles.extend(DISPLACED.map(f64::from_bits));
    // NaNs with other payloads.
    doubles.extend([0x7FF8_0000_0000_0001u64, 0xFFF0_0000_0000_0001, 0x7FF4_0000_0000_0000].map(f64::from_bits));
    for bits in [0x3000_0000_0000_0003u64, 0x2FFF_FFFF_FFFF_FFFF, 0x4FFF_FFFF_FFFF_FFFF, 0x5000_0000_0000_0000] {
        doubles.push(f64::from_bits(bits));
        doubles.push(f64::from_bits(bits | 1 << 63));
    }
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    for _ in 0..if cfg!(miri) { 300 } else { 20_000 } {
        doubles.push(f64::from_bits(rng.next()));
        // Mostly ordinary magnitudes, which are what has to fit inline.
        doubles.push(f64::from_bits(rng.next() >> 2 | 0x3000_0000_0000_0000));
    }
    let mut arena = Arena::<VmRoot>::new(16 << 20, |_| {
        Ok(Vm {
            stack: RefCell::new(Vec::new()),
            frames: RefCell::default(),
            globals: RefCell::default(),
            constants: Box::new([]),
            acc: Cell::new(Value::VOID),
            scratch: RefLock::new(None),
        })
    })
    .unwrap();
    arena.set_evacuate_all(true);
    let boxed = arena.mutate(|mc, vm| {
        let mut boxed = 0;
        for &f in &doubles {
            let v = Value::flonum(mc, f).unwrap();
            assert_eq!(Value::inline_flonum(f).is_some(), fits_inline(f.to_bits()), "{f:e}");
            check_flonum(mc, v, f);
            boxed += usize::from(!fits_inline(f.to_bits()));
            vm.stack.borrow_mut().push(v);
        }
        assert!(Value::inline_flonum(0.0).is_some() && Value::inline_flonum(0.1).is_some());
        for f in [-0.0, f64::INFINITY, f64::NEG_INFINITY, f64::NAN, -f64::NAN, 0.0 / black_box(0.0)] {
            assert!(Value::inline_flonum(f).is_some(), "{f}");
        }
        assert!(Value::inline_flonum(1e100).is_none() && Value::inline_flonum(f64::from_bits(DISPLACED[0])).is_none());
        boxed
    });
    arena.collect();
    arena.collect();
    arena.heap().check();
    assert_eq!(arena.metrics().objects, boxed);
    arena.mutate(|mc, vm| {
        for (&v, &f) in vm.stack.borrow().iter().zip(&doubles) {
            check_flonum(mc, v, f);
        }
    });
}

#[test]
fn fixnums_cover_63_bits() {
    let snowflake = 1_300_000_000_000_000_000;
    for n in [0, 1, -1, snowflake, -snowflake, Value::MIN_FIXNUM, Value::MAX_FIXNUM] {
        let v = Value::fixnum(n).unwrap();
        assert_eq!(v.as_fixnum(), Some(n));
        assert!(v.is_fixnum() && !v.is_flonum() && v.as_object().is_none());
    }
    assert_eq!(Value::fixnum(Value::MAX_FIXNUM + 1), None);
    assert_eq!(Value::fixnum(Value::MIN_FIXNUM - 1), None);
    assert_eq!(Value::MAX_FIXNUM, (1 << 62) - 1);

    let (max, min) = (fix(Value::MAX_FIXNUM), fix(Value::MIN_FIXNUM));
    assert_eq!(max.fixnum_add(fix(1)), None);
    assert_eq!(min.fixnum_sub(fix(1)), None);
    assert_eq!(max.fixnum_mul(fix(2)), None);
    assert_eq!(min.fixnum_mul(fix(-1)), None);
    assert_eq!(max.fixnum_add(min), Some(fix(-1)));
    assert_eq!(fix(1 << 31).fixnum_mul(fix(1 << 30)), Some(fix(1 << 61)));
    assert_eq!(fix(1 << 31).fixnum_mul(fix(1 << 31)), None);
    assert_eq!(fix(1).fixnum_add(Value::TRUE), None);
    assert_eq!(Value::char('a').fixnum_sub(fix(1)), None);
    assert_eq!(fix(3).fixnum_mul(Value::NIL), None);

    let mut rng = Rng(12345);
    for _ in 0..10_000 {
        let (a, b) = ((rng.next() as i64) >> 1, (rng.next() as i64) >> (1 + rng.next() % 62));
        let wide = |r: i128| i64::try_from(r).ok().and_then(Value::fixnum);
        assert_eq!(fix(a).fixnum_add(fix(b)), wide(a as i128 + b as i128));
        assert_eq!(fix(a).fixnum_sub(fix(b)), wide(a as i128 - b as i128));
        assert_eq!(fix(a).fixnum_mul(fix(b)), wide(a as i128 * b as i128));
    }
}

#[test]
fn immediates_unpack() {
    let mut arena = value_arena(1 << 20);
    arena.mutate(|mc, _| {
        for c in ['\0', 'a', 'λ', '🦀', char::MAX] {
            let v = Value::char(c);
            assert_eq!((v.as_char(), v.unpack(mc)), (Some(c), Unpacked::Char(c)));
            assert!(!v.is_fixnum() && !v.is_flonum() && v.as_object().is_none());
        }
        let constants = [
            (Value::FALSE, Unpacked::Bool(false), "#f"),
            (Value::TRUE, Unpacked::Bool(true), "#t"),
            (Value::NIL, Unpacked::Nil, "()"),
            (Value::EOF, Unpacked::Eof, "#<eof>"),
            (Value::VOID, Unpacked::Void, "#<void>"),
            (Value::UNBOUND, Unpacked::Unbound, "#<unbound>"),
        ];
        for (v, unpacked, shown) in constants {
            assert_eq!(v.unpack(mc), unpacked);
            assert_eq!(format!("{v:?}"), shown);
            assert_eq!(v.is_true(), v != Value::FALSE);
            assert!(!v.is_fixnum() && !v.is_flonum() && v.as_object().is_none() && v.as_char().is_none());
        }
        assert_eq!((Value::bool(true), Value::from(false)), (Value::TRUE, Value::FALSE));
        assert_eq!(Value::TRUE.as_bool(), Some(true));
        assert_eq!(fix(0).as_bool(), None);
        assert!(fix(0).is_true());
        assert_eq!(Value::default(), Value::VOID);
        assert_eq!(format!("{:?} {:?} {:?}", fix(-7), Value::char('x'), Value::inline_flonum(1.5).unwrap()), "-7 'x' 1.5");

        // SAFETY: neither holds a reference, and any other bits are a valid value.
        assert_eq!(unsafe { Value::from_bits(0xD800 << 32 | 0b0101) }.as_char(), Some(char::REPLACEMENT_CHARACTER));
        // SAFETY: as above.
        assert_eq!(unsafe { Value::from_bits(99 << 32 | 0b1101) }.unpack(mc), Unpacked::Void);
    });
    assert!(!arena.metrics().corrupted);
}

#[test]
fn downcasts_check_the_type() {
    let mut arena = value_arena(1 << 20);
    arena.mutate(|mc, root| {
        let pair = cons(mc, fix(1), fix(2));
        let num = Value::object(mc, mc.alloc(Num(5)).unwrap());
        let vec = vector(mc, 3, |i| fix(i as i64));
        root.set(mc, vec);

        assert_eq!(pair.downcast::<Pair>(mc).unwrap().cdr.get(), fix(2));
        assert!(pair.downcast::<Num>(mc).is_none() && pair.downcast::<Vector>(mc).is_none());
        assert!(num.is::<Num>(mc) && !num.is::<Pair>(mc));
        assert_eq!(num.downcast::<Num>(mc).unwrap().0, 5);
        assert_eq!(items(mc, vec).iter().map(|v| v.get()).collect::<Vec<_>>(), [fix(0), fix(1), fix(2)]);
        assert!(fix(1).downcast::<Pair>(mc).is_none() && Value::NIL.downcast::<Pair>(mc).is_none());

        let r = pair.as_object().unwrap();
        assert_eq!(Value::from(r), pair);
        assert_eq!(r.downcast_member::<Pair>(mc).map(|m| Value::from_member(mc, m)), Some(pair));
        // SAFETY: the bits come from `to_bits` in this arena and step.
        assert!(unsafe { AnyRef::from_bits(r.to_bits()) }.is::<Pair>(mc));
        assert!(matches!(pair.unpack(mc), Unpacked::Object(o) if o == r));
    });
    assert!(!arena.metrics().corrupted);
}

#[test]
fn forged_references_are_caught_by_the_collector() {
    // Unaligned, outside any page, null, and inside an object rather than at its start.
    for bits in [12345 << 32 | 0b0001, 8 << 32 | 0b0001, 0b0001, 16392 << 32 | 0b1001] {
        let mut arena = value_arena(1 << 20);
        arena.mutate(|mc, root| {
            cons(mc, fix(1), fix(2));
            // SAFETY: not upheld on purpose: made-up references, which the collector must reject.
            root.set(mc, unsafe { Value::from_bits(bits) });
        });
        arena.collect();
        assert!(arena.metrics().corrupted, "{bits:#x}");
    }
}

#[test]
fn values_keep_objects_alive_and_follow_moves() {
    let mut arena = value_arena(4 << 20);
    arena.set_evacuate_all(true);
    let before = arena.mutate(|mc, root| {
        let l = list(mc, 200);
        let boxed = Value::flonum(mc, 1e300).unwrap();
        root.set(mc, cons(mc, boxed, l));
        for _ in 0..100 {
            list(mc, 3);
        }
        root.get().to_bits()
    });
    for round in 0..3 {
        arena.collect_minor();
        arena.collect();
        arena.heap().check();
        assert!(!arena.metrics().corrupted);
        assert_eq!(arena.metrics().objects, 1 + 1 + 400);
        arena.mutate(|mc, root| {
            if round == 0 {
                assert_ne!(root.get().to_bits(), before, "nothing moved");
            }
            let top = root.get().downcast::<Pair>(mc).unwrap();
            assert_eq!(top.car.get().as_flonum(mc), Some(1e300));
            assert_eq!(read_list(mc, top.cdr.get()), (0..200).collect::<Vec<_>>());
        });
    }
    arena.mutate(|mc, root| root.set(mc, Value::NIL));
    arena.collect();
    assert_eq!(arena.metrics().objects, 0);
}

#[test]
fn young_objects_stored_in_old_values_survive_minor_collections() {
    for len in [4, 5000] {
        let mut arena = value_arena(4 << 20);
        arena.mutate(|mc, root| root.set(mc, vector(mc, len, |_| Value::NIL)));
        arena.collect();
        arena.mutate(|mc, root| {
            let slots = items(mc, root.get());
            slots[0].set(mc, cons(mc, fix(1), Value::NIL));
            slots[len - 1].set(mc, Value::flonum(mc, 1e100).unwrap());
            cons(mc, fix(3), Value::NIL);
        });
        arena.collect_minor();
        arena.heap().check();
        assert_eq!(arena.metrics().objects, 3, "{len} slots");
        arena.mutate(|mc, root| {
            let slots = items(mc, root.get());
            assert_eq!(slots[0].get().downcast::<Pair>(mc).unwrap().car.get(), fix(1));
            assert_eq!(slots[len - 1].get().as_flonum(mc), Some(1e100));
        });
    }
}

#[test]
fn root_containers_are_traced() {
    let mut arena = Arena::<VmRoot>::new(4 << 20, |mc| {
        Ok(Vm {
            stack: RefCell::new(Vec::new()),
            frames: RefCell::default(),
            globals: RefCell::default(),
            constants: vec![list(mc, 5), Value::flonum(mc, 1e100)?].into_boxed_slice(),
            acc: Cell::new(Value::NIL),
            scratch: RefLock::new(None),
        })
    })
    .unwrap();
    arena.set_evacuate_all(true);
    arena.mutate(|mc, vm| {
        vm.stack.borrow_mut().extend((0..10).map(|i| list(mc, i)));
        vm.frames.borrow_mut().push_front(list(mc, 7));
        vm.globals.borrow_mut().insert(1, list(mc, 8));
        vm.acc.set(list(mc, 9));
        *vm.scratch.borrow_mut(mc).unwrap() = Some(list(mc, 4));
        list(mc, 50);
    });
    let objects = 2 * (45 + 5 + 7 + 8 + 9 + 4) + 1;
    for _ in 0..2 {
        arena.collect_minor();
        assert_eq!(arena.metrics().objects, objects);
        arena.collect();
        arena.heap().check();
        assert_eq!(arena.metrics().objects, objects);
        arena.mutate(|mc, vm| {
            for (i, &v) in vm.stack.borrow().iter().enumerate() {
                assert_eq!(read_list(mc, v), (0..i as i64).collect::<Vec<_>>());
            }
            assert_eq!(read_list(mc, vm.frames.borrow()[0]).len(), 7);
            assert_eq!(read_list(mc, vm.globals.borrow()[&1]).len(), 8);
            assert_eq!(read_list(mc, vm.constants[0]).len(), 5);
            assert_eq!(vm.constants[1].as_flonum(mc), Some(1e100));
            assert_eq!(read_list(mc, vm.acc.get()).len(), 9);
            assert_eq!(read_list(mc, vm.scratch.borrow().unwrap().unwrap()).len(), 4);
        });
    }
    arena.mutate(|_, vm| {
        vm.stack.borrow_mut().clear();
        vm.globals.borrow_mut().clear();
    });
    arena.collect();
    assert_eq!(arena.metrics().objects, objects - 2 * (45 + 8));
}

#[test]
fn bulk_copies_handle_overlap() {
    let mut arena = value_arena(1 << 20);
    arena.mutate(|mc, root| {
        root.set(mc, vector(mc, 10, |i| fix(i as i64)));
        let slots = items(mc, root.get());
        let read = || slots.iter().map(|s| s.get().as_fixnum().unwrap()).collect::<Vec<_>>();
        Lock::copy(mc, &slots[2..8], &slots[0..6]);
        assert_eq!(read(), [0, 1, 0, 1, 2, 3, 4, 5, 8, 9]);
        Lock::copy(mc, &slots[0..6], &slots[2..8]);
        assert_eq!(read(), [0, 1, 2, 3, 4, 5, 4, 5, 8, 9]);
        Lock::copy(mc, &slots[3..3], &slots[0..0]);
        Lock::fill(mc, &slots[8..], fix(7));
        Lock::write(mc, &slots[..2], &[fix(-1), fix(-2)]);
        assert_eq!(read(), [-1, -2, 2, 3, 4, 5, 4, 5, 7, 7]);
    });
}

#[test]
#[should_panic(expected = "different lengths")]
fn bulk_copies_check_lengths() {
    let mut arena = value_arena(1 << 20);
    arena.mutate(|mc, _| {
        let slots = items(mc, vector(mc, 4, |_| Value::NIL));
        Lock::copy(mc, &slots[..2], &slots[..3]);
    });
}

#[test]
fn bulk_copies_are_seen_by_minor_collections() {
    for len in [8, 2500] {
        let n = 2 * len;
        let mut arena = value_arena(8 << 20);
        arena.mutate(|mc, root| root.set(mc, vector(mc, n, |_| Value::NIL)));
        arena.collect();
        arena.mutate(|mc, root| {
            let old = items(mc, root.get());
            let young = items(mc, vector(mc, 3, |i| cons(mc, fix(i as i64), Value::NIL)));
            Lock::copy(mc, &old[n - 3..], young);
            Lock::write(mc, &old[..2], &[cons(mc, fix(10), Value::NIL), cons(mc, fix(11), Value::NIL)]);
            Lock::fill(mc, &old[2..4], cons(mc, fix(12), Value::NIL));
            // Long enough to cover many cards, and a page boundary for the page run.
            let long = items(mc, vector(mc, len / 2, |i| cons(mc, fix(i as i64), Value::NIL)));
            Lock::copy(mc, &old[4..4 + len / 2], long);
        });
        arena.collect_minor();
        arena.heap().check();
        assert_eq!(arena.metrics().objects, 1 + 3 + 2 + 1 + len / 2, "{len} slots");
        arena.mutate(|mc, root| {
            fn car<'gc>(mc: &Mutation<'gc>, v: &Lock<Value<'gc>>) -> i64 {
                v.get().downcast::<Pair>(mc).unwrap().car.get().as_fixnum().unwrap()
            }
            let car = |v| car(mc, v);
            let old = items(mc, root.get());
            assert_eq!(old[n - 3..].iter().map(car).collect::<Vec<_>>(), [0, 1, 2]);
            assert_eq!(old[..4].iter().map(car).collect::<Vec<_>>(), [10, 11, 12, 12]);
            assert!(old[4..4 + len / 2].iter().map(car).eq(0..len as i64 / 2));
        });
    }
}

#[test]
fn bulk_copies_into_black_objects_are_traced() {
    let mut arena = Arena::<TwoRoot>::new(1 << 20, |_| Ok((Lock::new(Value::NIL), Lock::new(Value::NIL)))).unwrap();
    arena.mutate(|mc, root| {
        // `.0` is a chain of 50 pairs ending in the pair that will move; `.1` gets traced first.
        let tail = cons(mc, fix(7), Value::NIL);
        root.0.set(mc, (0..50).fold(tail, |next, i| cons(mc, fix(i), next)));
        root.1.set(mc, vector(mc, 4, |_| Value::NIL));
    });
    arena.collect_slice(64);
    assert_eq!(arena.metrics().phase, Phase::Marking);
    let tail = arena.mutate(|mc, root| {
        let mut before = root.0.get().downcast::<Pair>(mc).unwrap();
        loop {
            let next = before.cdr.get().downcast::<Pair>(mc).unwrap();
            if next.cdr.get() == Value::NIL {
                break;
            }
            before = next;
        }
        let tail = before.cdr.get();
        before.cdr.set(mc, Value::NIL);
        Lock::write(mc, &items(mc, root.1.get())[1..3], &[tail, tail]);
        tail.to_bits() >> 32
    });
    assert!(arena.heap().is_old(tail as u32), "the copy didn't shade what it stored");
    arena.collect();
    arena.heap().check();
    assert!(!arena.metrics().corrupted);
    assert_eq!(arena.metrics().objects, 52);
    arena.mutate(|mc, root| {
        let tail = items(mc, root.1.get())[2].get().downcast::<Pair>(mc).unwrap();
        assert_eq!(tail.car.get(), fix(7));
    });
}

#[derive(Trace, Plain)]
struct Foreign<'gc> {
    host: AnyHostRef<'gc>,
}

struct Dropped(Rc<Cell<bool>>);

impl Drop for Dropped {
    fn drop(&mut self) {
        self.0.set(true);
    }
}

#[test]
fn any_host_refs_check_the_type() {
    let dropped = Rc::new(Cell::new(false));
    let mut arena = value_arena(1 << 20);
    arena.mutate(|mc, root| {
        let host = AnyHostRef::from(mc.host(Dropped(dropped.clone())).unwrap());
        root.set(mc, Value::object(mc, mc.alloc(Foreign { host }).unwrap()));
        assert!(host.is::<Dropped>(mc) && !host.is::<String>(mc));
        assert!(host.downcast::<String>(mc).is_none());
        assert!(host.downcast::<Dropped>(mc).unwrap().get(mc).is_some());
    });
    arena.collect();
    arena.mutate(|mc, root| {
        let host = root.get().downcast::<Foreign>(mc).unwrap().host;
        assert!(Rc::ptr_eq(&host.downcast_ref::<Dropped>(mc).unwrap().0, &dropped));
    });
    assert!(!dropped.get());
    arena.mutate(|mc, root| root.set(mc, Value::NIL));
    arena.collect();
    assert!(dropped.get());
}

#[test]
fn stores_without_references_skip_the_barrier() {
    let mut arena = value_arena(1 << 20);
    arena.mutate(|mc, root| root.set(mc, vector(mc, 8, |_| Value::NIL)));
    arena.collect();
    let dirty = |arena: &mut Arena<ValueRoot>, f: &dyn for<'gc> Fn(&Mutation<'gc>, &'gc [Lock<Value<'gc>>])| {
        arena.collect_minor();
        assert_eq!(arena.heap().dirty_cards(), 0);
        arena.mutate(|mc, root| f(mc, items(mc, root.get())));
        arena.heap().dirty_cards()
    };
    fn plain<'gc>() -> [Value<'gc>; 5] {
        [fix(1), Value::char('x'), Value::TRUE, Value::NIL, Value::inline_flonum(2.5).unwrap()]
    }
    for i in 0..5 {
        assert_eq!(dirty(&mut arena, &|mc, slots| slots[0].set(mc, plain()[i])), 0, "{:?}", plain()[i]);
    }
    assert_eq!(dirty(&mut arena, &|mc, slots| Lock::fill(mc, slots, fix(3))), 0);
    assert_eq!(dirty(&mut arena, &|mc, slots| Lock::write(mc, &slots[..3], &plain()[..3])), 0);
    assert_eq!(dirty(&mut arena, &|mc, slots| Lock::copy(mc, &slots[4..], &slots[..4])), 0);

    assert_eq!(dirty(&mut arena, &|mc, slots| slots[0].set(mc, cons(mc, fix(1), Value::NIL))), 1);
    assert_eq!(dirty(&mut arena, &|mc, slots| slots[1].set(mc, Value::flonum(mc, 1e100).unwrap())), 1);
    assert_eq!(dirty(&mut arena, &|mc, slots| Lock::write(mc, &slots[2..4], &[fix(1), slots[0].get()])), 1);
    assert_eq!(dirty(&mut arena, &|mc, slots| Lock::copy(mc, &slots[4..], &slots[..4])), 1);
    arena.collect();
    arena.heap().check();
}

#[derive(Clone, Copy)]
struct Liar<'gc>(Option<Member<'gc, Num>>);

// SAFETY: not upheld on purpose: `holds_refs` lies, which the verifier must catch.
unsafe impl Trace for Liar<'_> {
    fn trace(&mut self, t: &mut Tracer<'_>) {
        self.0.trace(t);
    }

    fn holds_refs(&self) -> bool {
        false
    }
}

// SAFETY: an `Option<Member>`, which is `Plain`.
unsafe impl<'gc> Plain<'gc> for Liar<'gc> {}

#[derive(Trace, Plain)]
struct Holder<'gc> {
    liar: Lock<Liar<'gc>>,
}

#[test]
#[should_panic(expected = "gc verify")]
fn verifier_catches_a_wrong_holds_refs() {
    let mut arena = value_arena(1 << 20);
    arena.mutate(|mc, root| root.set(mc, Value::object(mc, mc.alloc(Holder { liar: Lock::new(Liar(None)) }).unwrap())));
    arena.collect();
    arena.mutate(|mc, root| {
        let young = Member::new(mc, mc.alloc(Num(1)).unwrap());
        root.get().downcast::<Holder>(mc).unwrap().liar.set(mc, Liar(Some(young)));
    });
    arena.collect_minor();
}

#[test]
fn type_tags_downcast_like_type_ids() {
    let mut arena = value_arena(1 << 20);
    arena.mutate(|mc, root| {
        // Taken before any pair exists, so the tag registers the type.
        let pair_tag = mc.type_tag::<Pair>().unwrap();
        let num_tag = mc.type_tag::<Num>().unwrap();
        let vec_tag = mc.inline_type_tag::<Vector>().unwrap();
        let pair = cons(mc, fix(1), fix(2));
        let num = Value::object(mc, mc.alloc(Num(5)).unwrap());
        let vec = vector(mc, 2, |_| fix(9));
        root.set(mc, cons(mc, pair, cons(mc, num, vec)));
        assert_eq!(pair.downcast_tag(mc, pair_tag).unwrap().cdr.get(), fix(2));
        assert_eq!(num.downcast_tag(mc, num_tag).unwrap().0, 5);
        assert_eq!(vec.downcast_tag(mc, vec_tag).unwrap().items().len(), 2);
        assert!(pair.downcast_tag(mc, num_tag).is_none() && num.downcast_tag(mc, vec_tag).is_none());
        assert!(fix(1).downcast_tag(mc, pair_tag).is_none() && Value::NIL.downcast_tag(mc, pair_tag).is_none());
    });
    arena.set_evacuate_all(true);
    arena.collect();
    arena.mutate(|mc, root| {
        let (pair_tag, vec_tag) = (mc.type_tag::<Pair>().unwrap(), mc.inline_type_tag::<Vector>().unwrap());
        let outer = root.get().downcast_tag(mc, pair_tag).unwrap();
        assert_eq!(outer.car.get().downcast_tag(mc, pair_tag).unwrap().car.get(), fix(1));
        let rest = outer.cdr.get().downcast_tag(mc, pair_tag).unwrap();
        assert_eq!(rest.cdr.get().downcast_tag(mc, vec_tag).unwrap().items()[1].get(), fix(9));
    });
    assert!(!arena.metrics().corrupted);
}

fn new_pair<'gc>(mc: &Mutation<'gc>) -> Value<'gc> {
    cons(mc, fix(3), fix(4))
}

fn new_num<'gc>(mc: &Mutation<'gc>) -> Value<'gc> {
    Value::object(mc, mc.alloc(Num(5)).unwrap())
}

/// A value whose object was freed, and whose memory now holds a new object made by `reuse`.
fn stale_value(arena: &mut Arena<ValueRoot>, reuse: impl for<'gc> Fn(&Mutation<'gc>) -> Value<'gc>) -> u64 {
    let bits = arena.mutate(|mc, _| cons(mc, fix(1), fix(2)).to_bits());
    arena.collect();
    let new = arena.mutate(|mc, root| {
        let v = reuse(mc);
        root.set(mc, v);
        v.to_bits()
    });
    assert_eq!(new >> 32, bits >> 32, "the memory wasn't reused");
    bits
}

#[test]
fn stale_references_are_caught_when_used() {
    let reuses: [for<'gc> fn(&Mutation<'gc>) -> Value<'gc>; 2] = [new_pair, new_num];
    for reuse in reuses {
        let mut arena = value_arena(1 << 20);
        let bits = stale_value(&mut arena, reuse);
        arena.mutate(|mc, _| {
            // SAFETY: not upheld on purpose: the bits are from an earlier step, and the downcast
            // must tell.
            let stale = unsafe { Value::from_bits(bits) };
            assert!(stale.downcast::<Pair>(mc).is_none());
        });
        assert!(arena.metrics().corrupted);
    }
}

#[test]
fn stale_references_are_caught_by_the_collector() {
    // A new pair at the same offset is a valid object of the right type, so only the stamp
    // tells the stale reference apart.
    let mut arena = value_arena(1 << 20);
    let bits = stale_value(&mut arena, new_pair);
    arena.mutate(|mc, root| {
        // SAFETY: as above.
        let holder = cons(mc, root.get(), unsafe { Value::from_bits(bits) });
        root.set(mc, holder);
    });
    arena.collect();
    assert!(arena.metrics().corrupted);
}

#[test]
fn damaged_references_are_caught_when_used() {
    for flip in [4, 19, 20, 31] {
        let mut arena = value_arena(1 << 20);
        arena.mutate(|mc, root| {
            let pair = cons(mc, fix(1), fix(2));
            root.set(mc, pair);
            // SAFETY: not upheld on purpose: one bit is flipped, which the checks must catch.
            let damaged = unsafe { Value::from_bits(pair.to_bits() ^ 1 << flip) };
            let tag = mc.type_tag::<Pair>().unwrap();
            assert!(damaged.downcast::<Pair>(mc).is_none() && damaged.downcast_tag(mc, tag).is_none());
        });
        assert_eq!(arena.metrics().corrupted, flip >= 20, "bit {flip}");
    }
}

#[test]
fn type_mismatches_are_decided_without_the_header() {
    let mut arena = value_arena(1 << 20);
    arena.mutate(|mc, root| {
        let pair = cons(mc, fix(1), fix(2));
        root.set(mc, pair);
        assert!(pair.downcast::<Num>(mc).is_none() && !pair.is::<Vector>(mc));
        assert!(pair.downcast_tag(mc, mc.type_tag::<Num>().unwrap()).is_none());
    });
    assert!(!arena.metrics().corrupted, "an ordinary type mismatch isn't corruption");
}

#[test]
fn zeroed_references_never_check_out() {
    let mut arena = value_arena(1 << 20);
    arena.mutate(|mc, root| {
        root.set(mc, Value::object(mc, mc.alloc(Num(1)).unwrap()));
        let tag = mc.type_tag::<Num>().unwrap();
        assert_eq!(format!("{tag:?}"), "TypeTag(0)", "Num isn't the first type, so this tests nothing");
        // SAFETY: not upheld on purpose: zero never comes from `to_bits`, and downcasts must
        // refuse it.
        let zero = unsafe { AnyRef::from_bits(0) };
        assert!(zero.downcast::<Num>(mc).is_none() && zero.downcast_tag(mc, tag).is_none());
        // SAFETY: as above.
        assert!(unsafe { Value::from_bits(0b0001) }.downcast::<Num>(mc).is_none());
    });
    assert!(arena.metrics().corrupted);
}

#[test]
fn references_to_the_old_copy_of_a_moved_object_are_stale() {
    let mut arena = value_arena(1 << 20);
    let old = arena.mutate(|mc, root| {
        let v = vector(mc, 3, |i| fix(i as i64));
        root.set(mc, v);
        v.to_bits()
    });
    arena.set_evacuate_all(true);
    arena.collect();
    arena.mutate(|mc, root| {
        assert_ne!(root.get().to_bits(), old, "nothing moved");
        assert_eq!(items(mc, root.get()).len(), 3);
        // SAFETY: not upheld on purpose: the bits are from before the object moved.
        assert!(unsafe { Value::from_bits(old) }.downcast::<Vector>(mc).is_none());
    });
    assert!(arena.metrics().corrupted);
}

#[test]
fn references_to_swept_objects_are_stale_before_the_memory_is_reused() {
    let mut arena = value_arena(1 << 20);
    let dead = arena.mutate(|mc, root| {
        let dead = cons(mc, fix(1), fix(2));
        root.set(mc, cons(mc, fix(3), fix(4)));
        dead.to_bits()
    });
    arena.collect();
    // SAFETY: not upheld on purpose: the object is dead.
    arena.mutate(|mc, _| assert!(unsafe { Value::from_bits(dead) }.downcast::<Pair>(mc).is_none()));
    assert!(arena.metrics().corrupted);
}
