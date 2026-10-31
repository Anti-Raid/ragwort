use std::cmp::Ordering;

use crate::int::{self, NumError};
use crate::rational::{self, Round};
use crate::real::*;
use crate::testing::{Oracle, ROUNDS, Rng, TestError, TestHost, TestRational, TestReal, WIDTHS, error_token};

type Op = fn(&TestHost, TestReal, TestReal) -> Result<TestReal, TestError>;

fn show(h: &TestHost, x: Result<TestReal, TestError>) -> String {
    x.map_or_else(error_token, |x| h.show_real(x))
}

fn binary(seed: u64, ops: &[(&str, Op)]) {
    let (mut rng, mut oracle) = (Rng(seed), Oracle::default());
    for bits in WIDTHS {
        let h = TestHost::new(bits);
        for _ in 0..ROUNDS / WIDTHS.len() {
            let (x, y) = (h.random_real(&mut rng, 2), h.random_real(&mut rng, 2));
            for (name, op) in ops {
                oracle.case(name, &[h.show_real(x), h.show_real(y)], show(&h, op(&h, x, y)));
            }
        }
    }
    oracle.check();
}

#[test]
fn arithmetic() {
    binary(41, &[("xadd", add), ("xsub", sub), ("xmul", mul), ("xdiv", div)]);
}

#[test]
fn extremes() {
    binary(42, &[("xmax", max), ("xmin", min)]);
}

#[test]
fn comparisons_are_exact() {
    let (mut rng, mut oracle) = (Rng(43), Oracle::default());
    for bits in WIDTHS {
        let h = TestHost::new(bits);
        for _ in 0..ROUNDS / WIDTHS.len() {
            let (x, y) = (h.random_real(&mut rng, 2), h.random_real(&mut rng, 2));
            let ours = compare(&h, x, y).unwrap().map_or("nan".to_string(), |o| (o as i8).to_string());
            oracle.case("xcmp", &[h.show_real(x), h.show_real(y)], ours);
        }
        // Integers just past 2^53, against the doubles they round to.
        for k in 53..63 {
            for n in [(1i64 << k) + 1, -(1i64 << k) - 1, (1i64 << k) - 1] {
                let (x, y) = (from_i64(&h, n).unwrap(), flo(n as f64));
                let ours = compare(&h, x, y).unwrap().map_or("nan".to_string(), |o| (o as i8).to_string());
                oracle.case("xcmp", &[h.show_real(x), h.show_real(y)], ours);
            }
        }
    }
    oracle.check();
}

#[test]
fn rounding_parts_and_exactness() {
    let (mut rng, mut oracle) = (Rng(44), Oracle::default());
    for bits in WIDTHS {
        let h = TestHost::new(bits);
        for _ in 0..ROUNDS / WIDTHS.len() {
            let x = h.random_real(&mut rng, 2);
            let xs = std::slice::from_ref(&h.show_real(x)).to_vec();
            for (name, mode) in [("xfloor", Round::Floor), ("xceiling", Round::Ceiling), ("xtruncate", Round::Truncate), ("xround", Round::Nearest)] {
                oracle.case(name, &xs, show(&h, round(&h, x, mode)));
            }
            oracle.case("xnumerator", &xs, show(&h, numerator(&h, x)));
            oracle.case("xdenominator", &xs, show(&h, denominator(&h, x)));
            oracle.case("xinexact", &xs, show(&h, inexact(&h, x)));
            oracle.case("xexact", &xs, show(&h, exact(&h, x)));
        }
    }
    oracle.check();
}

/// Mostly integers, exact and not, with a few that aren't.
fn random_integer(h: &TestHost, rng: &mut Rng) -> TestReal {
    match rng.below(5) {
        0 => TestReal::Exact(TestRational::Int(h.random(rng, 2))),
        1 => TestReal::Flonum((rng.below(41) as f64 - 20.0).copysign(if rng.bool() { 1.0 } else { -1.0 })),
        2 => TestReal::Flonum([1e300, -2f64.powi(63), 2f64.powi(53) + 2.0, 4503599627370497.0][rng.below(4) as usize]),
        3 => TestReal::Flonum(h.random_flonum(rng)),
        _ => h.random_real(rng, 2),
    }
}

#[test]
fn integer_division_of_inexact_integers() {
    let (mut rng, mut oracle) = (Rng(45), Oracle::default());
    for bits in WIDTHS {
        let h = TestHost::new(bits);
        for _ in 0..ROUNDS / WIDTHS.len() {
            let (x, y) = (random_integer(&h, &mut rng), random_integer(&h, &mut rng));
            let args = [h.show_real(x), h.show_real(y)];
            oracle.case("xquotient", &args, show(&h, quotient(&h, x, y)));
            oracle.case("xremainder", &args, show(&h, remainder(&h, x, y)));
            oracle.case("xmodulo", &args, show(&h, modulo(&h, x, y)));
        }
    }
    oracle.check();
}

fn ratio(h: &TestHost, n: i64, d: i64) -> TestReal {
    let r = rational::from_parts(h, int::from_i64(h, n).unwrap(), int::from_i64(h, d).unwrap()).unwrap();
    TestReal::Exact(r)
}

fn flo(f: f64) -> TestReal {
    TestReal::Flonum(f)
}

/// The cases Racket's reference spells out.
#[test]
fn exact_zero_stays_exact_where_racket_says() {
    let h = TestHost::new(64);
    let zero = ratio(&h, 0, 1);
    let is_exact_zero = |x: Result<TestReal, TestError>| crate::real::is_exact_zero(&h, x.unwrap());
    assert!(is_exact_zero(mul(&h, zero, flo(f64::INFINITY))));
    assert!(is_exact_zero(mul(&h, flo(f64::NAN), zero)));
    assert!(is_exact_zero(div(&h, zero, flo(0.0))));
    assert_eq!(div(&h, flo(1.0), zero).unwrap_err(), TestError::Num(NumError::DivideByZero));
    assert_eq!(h.show_real(div(&h, flo(1.0), flo(0.0)).unwrap()), h.show_real(flo(f64::INFINITY)));
    assert_eq!(h.show_real(add(&h, zero, flo(1.5)).unwrap()), h.show_real(flo(1.5)));
    let three = max(&h, max(&h, ratio(&h, 1, 1), ratio(&h, 3, 1)).unwrap(), flo(2.0)).unwrap();
    assert_eq!(h.show_real(three), h.show_real(flo(3.0)));
    assert_eq!(h.show_real(quotient(&h, flo(-10.0), ratio(&h, 3, 1)).unwrap()), h.show_real(flo(-3.0)));
    assert_eq!(quotient(&h, flo(1.5), ratio(&h, 1, 1)).unwrap_err(), TestError::Num(NumError::NotInteger));
    assert_eq!(h.show_real(numerator(&h, flo(2.3)).unwrap()), h.show_real(flo(2589569785738035.0)));
    assert_eq!(h.show_real(denominator(&h, flo(2.3)).unwrap()), h.show_real(flo(1125899906842624.0)));
    assert_eq!(h.show_real(round(&h, flo(2.5), Round::Nearest).unwrap()), h.show_real(flo(2.0)));
    assert_eq!(compare(&h, ratio(&h, 1, 3), flo(1.0 / 3.0)).unwrap(), Some(Ordering::Greater));
    assert_eq!(compare(&h, flo(f64::NAN), flo(f64::NAN)).unwrap(), None);
    assert_eq!(compare(&h, flo(0.0), flo(-0.0)).unwrap(), Some(Ordering::Equal));
}

#[test]
fn eqv_tells_exactness_and_zero_signs_apart() {
    let h = TestHost::new(64);
    let hash_of = |x| hash_of_in(&h, x);
    let other_nan = flo(f64::from_bits(f64::NAN.to_bits() ^ 1));
    assert!(eqv(&h, flo(f64::NAN), other_nan) && hash_of(flo(f64::NAN)) == hash_of(other_nan));
    assert!(eqv(&h, flo(f64::NAN), flo(-f64::NAN)));
    assert!(!eqv(&h, flo(0.0), flo(-0.0)));
    assert!(!eqv(&h, ratio(&h, 1, 1), flo(1.0)));
    assert!(eqv(&h, ratio(&h, 6, 4), ratio(&h, 3, 2)));
    assert!(!eqv(&h, ratio(&h, 1, 2), ratio(&h, 1, 3)));
    let mut rng = Rng(46);
    let hosts = WIDTHS.map(TestHost::new);
    for _ in 0..ROUNDS / 4 {
        let x = hosts[0].random_real(&mut rng, 3);
        assert!(eqv(&hosts[0], x, x));
        // Rebuilt in a narrower host, an exact number takes other paths but hashes the same.
        let text = hosts[0].show_real(x);
        for other in &hosts[1..] {
            let y = match x {
                TestReal::Flonum(f) => flo(f),
                TestReal::Exact(r) => {
                    let (n, d) = (rational::numerator(&hosts[0], r), rational::denominator(&hosts[0], r).unwrap());
                    let rebuild = |n| {
                        let s = int::to_string(&hosts[0], n, 16).unwrap();
                        let (neg, digits) = s.strip_prefix('-').map_or((false, s.as_str()), |rest| (true, rest));
                        int::parse(other, digits.as_bytes(), 16, neg).unwrap().unwrap()
                    };
                    TestReal::Exact(rational::from_parts(other, rebuild(n), rebuild(d)).unwrap())
                }
            };
            assert_eq!(hash_of_in(other, y), hash_of_in(&hosts[0], x), "{text}");
        }
    }
}

fn hash_of_in(h: &TestHost, x: TestReal) -> u64 {
    let mut state = std::hash::DefaultHasher::new();
    hash(h, x, &mut state);
    std::hash::Hasher::finish(&state)
}
