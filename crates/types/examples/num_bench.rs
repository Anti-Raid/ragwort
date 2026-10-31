//! The generic integer layer against the same work written for the arena by hand.

use std::hint::black_box;
use std::time::Instant;

use ragwort_gc_prims::GcVec;
use ragwort_types::gc::{Arena, Gc, Mutation, Rootable, TypeTag, Value};
use ragwort_types::num::bigint::{self, Digits, RWDigits};
use ragwort_types::num::{Big, Host, Integer, IntView, Nums, int};

struct Ints;
impl Rootable for Ints {
    type Root<'gc> = GcVec<'gc, Value<'gc>>;
}

/// Keeps each benchmark's best time, since runs interleave and noise only adds.
#[derive(Default)]
struct Best(Vec<(&'static str, f64)>);

impl Best {
    fn time(&mut self, name: &'static str, f: impl FnOnce()) {
        let start = Instant::now();
        f();
        let ms = start.elapsed().as_secs_f64() * 1e3;
        match self.0.iter_mut().find(|(n, _)| *n == name) {
            Some((_, best)) => *best = best.min(ms),
            None => self.0.push((name, ms)),
        }
    }
}

#[inline(never)]
fn generic_adds<'gc>(h: &Nums<'_, 'gc>, n: i64) -> Integer<'gc> {
    let (mut x, one) = (int::from_i64(h, 0).expect("alloc"), int::from_i64(h, 1).expect("alloc"));
    for _ in 0..n {
        x = int::add(h, black_box(x), black_box(one)).expect("add");
    }
    x
}

/// The JavaScript benchmark's loop: operands read from an array, the sum in a register.
#[inline(never)]
fn array_adds<'gc>(h: &Nums<'_, 'gc>, n: i64) -> Integer<'gc> {
    let ops = black_box([int::from_i64(h, 0).expect("alloc"), int::from_i64(h, 1).expect("alloc")]);
    let mut x = ops[0];
    for i in 0..n as usize {
        x = int::add(h, x, ops[(i & 1) | 1]).expect("add");
    }
    x
}

/// Only the digit work of a 4x4 multiply, into a buffer on the stack.
#[inline(never)]
fn digit_muls(x: &[u64], n: usize) {
    let mut z = [0u64; 8];
    for _ in 0..n {
        bigint::multiply(RWDigits::new(black_box(&mut z)), Digits::new(black_box(x)), Digits::new(black_box(x)));
    }
}

#[inline(never)]
fn by_hand_adds<'gc>(h: &Nums<'_, 'gc>, n: i64) -> Value<'gc> {
    let (mut x, one) = (Value::fixnum(0).expect("fixnum"), Value::fixnum(1).expect("fixnum"));
    for _ in 0..n {
        x = by_hand_add(h, black_box(x), black_box(one));
    }
    x
}

/// What a VM would write: the fixnum case inline, anything else out of line.
fn by_hand_add<'gc>(h: &Nums<'_, 'gc>, x: Value<'gc>, y: Value<'gc>) -> Value<'gc> {
    match x.fixnum_add(y) {
        Some(z) => z,
        None => by_hand_add_slow(h, x, y),
    }
}

#[inline(never)]
fn by_hand_add_slow<'gc>(h: &Nums<'_, 'gc>, x: Value<'gc>, y: Value<'gc>) -> Value<'gc> {
    let (x, y) = (h.integer(x).expect("integer"), h.integer(y).expect("integer"));
    int::add(h, x, y).expect("add").value()
}

#[inline(never)]
fn generic_mul<'gc>(h: &Nums<'_, 'gc>, x: Integer<'gc>, y: Integer<'gc>) -> Integer<'gc> {
    int::mul(h, x, y).expect("mul")
}

/// What a VM would write for multiplying bignums: try fixnums, check both operands' types,
/// multiply, and keep the result a fixnum if it fits.
#[inline(never)]
fn by_hand_mul<'gc>(mc: &Mutation<'gc>, tag: TypeTag<'gc, Big>, x: Value<'gc>, y: Value<'gc>) -> Value<'gc> {
    if let Some(z) = x.fixnum_mul(y) {
        return z;
    }
    let (x, y) = (x.downcast_tag(mc, tag).expect("bignum"), y.downcast_tag(mc, tag).expect("bignum"));
    let negative = x.is_negative() != y.is_negative();
    let (xd, yd) = (Digits::new(Gc::items(x)), Digits::new(Gc::items(y)));
    let len = xd.len() + yd.len();
    let mut small = None;
    let z = mc
        .alloc_inline_with(Big::new(negative), len, 0, |digits| {
            bigint::multiply(RWDigits::new(digits), xd, yd);
            let len = Digits::new(digits).normalize().len();
            if len <= 1 {
                small = Value::fixnum(if negative { (digits[0] as i64).wrapping_neg() } else { digits[0] as i64 });
            }
            len
        })
        .expect("alloc");
    small.unwrap_or_else(|| Value::object(mc, z))
}

/// Four digits.
fn operands<'gc>(h: &Nums<'_, 'gc>) -> Integer<'gc> {
    let x = int::parse(h, b"123456789012345678901234567890123456789012345678901234567890123456789012", 10, false);
    x.expect("alloc").expect("parse")
}

const ADDS: i64 = 50_000_000;
const MULS: usize = 4_000_000;
const BATCH: usize = 50_000;

fn main() {
    let mut arena = Arena::<Ints>::new(256 << 20, |_| Ok(GcVec::new())).expect("arena");
    let mut best = Best::default();
    for _ in 0..9 {
        arena.mutate(|mc, _| {
            let h = Nums::new(mc).expect("nums");
            best.time("fixnum add, generic", || assert_eq!(int::to_i64(&h, generic_adds(&h, ADDS)), Some(ADDS)));
            best.time("fixnum add, by hand", || assert_eq!(by_hand_adds(&h, ADDS).as_fixnum(), Some(ADDS)));
            best.time("fixnum add, generic, array operands", || assert_eq!(int::to_i64(&h, array_adds(&h, ADDS)), Some(ADDS)));
            let x = operands(&h).value().downcast::<Big>(mc).expect("bignum");
            best.time("4x4 digit mul, digits only", || digit_muls(Gc::items(x), MULS));
        }).expect("corrupted");
        best.time("4x4 digit bignum mul, generic", || {
            for _ in 0..MULS / BATCH {
                arena.mutate(|mc, _| {
                    let h = Nums::new(mc).expect("nums");
                    let x = operands(&h);
                    for _ in 0..BATCH {
                        black_box(generic_mul(&h, black_box(x), black_box(x)));
                    }
                }).expect("corrupted");
                arena.collect_minor();
            }
        });
        best.time("4x4 digit bignum mul, by hand", || {
            for _ in 0..MULS / BATCH {
                arena.mutate(|mc, _| {
                    let h = Nums::new(mc).expect("nums");
                    let x = operands(&h);
                    assert!(matches!(h.view(x), IntView::Big { .. }));
                    let (x, tag) = (x.value(), mc.inline_type_tag::<Big>().expect("tag"));
                    for _ in 0..BATCH {
                        black_box(by_hand_mul(mc, tag, black_box(x), black_box(x)));
                    }
                }).expect("corrupted");
                arena.collect_minor();
            }
        });
    }
    for (name, ms) in best.0 {
        println!("{name:40} {ms:>8.1} ms");
    }
}
