//! The generic integer layer against the same work written for the arena by hand.

use std::cell::Cell;
use std::hint::black_box;
use std::time::Instant;

use ragwort_types::gc::{Arena, Gc, Mutation, Value};
use ragwort_types::num::bigint::{self, Digits, RWDigits};
use ragwort_types::num::{Big, BigFields, Host, Integer, IntView, Numbers, Nums, int};

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
fn digit_muls(x: &[Cell<u64>], n: usize) {
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
fn by_hand_mul<'gc>(mc: &Mutation<'gc>, x: Value<'gc>, y: Value<'gc>) -> Value<'gc> {
    if let Some(z) = x.fixnum_mul(y) {
        return z;
    }
    let (Some(Numbers::Big(x)), Some(Numbers::Big(y))) = (Numbers::of(x), Numbers::of(y)) else { panic!("bignums") };
    let negative = x.negative(mc) != y.negative(mc);
    let digits = |x: Gc<'gc, Big>| Digits::new(&x.items(mc).words()[..x.digits(mc) as usize]);
    let (xd, yd) = (digits(x), digits(y));
    let len = xd.len() + yd.len();
    let z = mc.alloc_zeroed::<Big, 2>([u64::from(negative), 0], len).expect("alloc");
    bigint::multiply(RWDigits::of_cells(z.items(mc).words()), xd, yd);
    let kept = digits(z).normalize().len();
    let low = z.items(mc).words()[0].get();
    if kept <= 1
        && let Some(small) = Value::fixnum(if negative { (low as i64).wrapping_neg() } else { low as i64 })
    {
        return small;
    }
    z.set_digits(mc, kept as u64);
    Value::object(mc, z)
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
    let mut arena = Arena::new(256 << 20, 0);
    let mut best = Best::default();
    for _ in 0..9 {
        arena.mutate(|mc| {
            let h = Nums::new(mc);
            best.time("fixnum add, generic", || assert_eq!(int::to_i64(&h, generic_adds(&h, ADDS)), Some(ADDS)));
            best.time("fixnum add, by hand", || assert_eq!(by_hand_adds(&h, ADDS).as_fixnum(), Some(ADDS)));
            best.time("fixnum add, generic, array operands", || assert_eq!(int::to_i64(&h, array_adds(&h, ADDS)), Some(ADDS)));
            let Some(Numbers::Big(x)) = Numbers::of(operands(&h).value()) else { panic!("a bignum") };
            best.time("4x4 digit mul, digits only", || digit_muls(&x.items(mc).words()[..x.digits(mc) as usize], MULS));
        });
        best.time("4x4 digit bignum mul, generic", || {
            for _ in 0..MULS / BATCH {
                arena.mutate(|mc| {
                    let h = Nums::new(mc);
                    let x = operands(&h);
                    for _ in 0..BATCH {
                        black_box(generic_mul(&h, black_box(x), black_box(x)));
                    }
                });
                arena.collect_minor();
            }
        });
        best.time("4x4 digit bignum mul, by hand", || {
            for _ in 0..MULS / BATCH {
                arena.mutate(|mc| {
                    let h = Nums::new(mc);
                    let x = operands(&h);
                    assert!(matches!(h.view(x), IntView::Big { .. }));
                    let x = x.value();
                    for _ in 0..BATCH {
                        black_box(by_hand_mul(mc, black_box(x), black_box(x)));
                    }
                });
                arena.collect_minor();
            }
        });
    }
    for (name, ms) in best.0 {
        println!("{name:40} {ms:>8.1} ms");
    }
}
