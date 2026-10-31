use std::cmp::Ordering;

use crate::int::{self, NumError};
use crate::rational::*;
use crate::testing::{Oracle, ROUNDS, Rng, TestError, TestHost, TestRational, WIDTHS, hex_i64};

type Op = fn(&TestHost, TestRational, TestRational) -> Result<TestRational, TestError>;

fn binary(oracle_op: &str, seed: u64, op: Op) {
    let (mut rng, mut oracle) = (Rng(seed), Oracle::default());
    for bits in WIDTHS {
        let h = TestHost::new(bits);
        for _ in 0..ROUNDS / WIDTHS.len() {
            let (x, y) = (h.random_rational(&mut rng, 3), h.random_rational(&mut rng, 3));
            match op(&h, x, y) {
                Ok(z) => oracle.case(oracle_op, &[h.show_rational(x), h.show_rational(y)], h.show_rational(z)),
                Err(TestError::Num(NumError::DivideByZero)) => assert_eq!(sign(&h, y), Ordering::Equal),
                Err(e) => panic!("{e:?}"),
            }
        }
    }
    oracle.check();
}

#[test]
fn addition() {
    binary("radd", 31, add);
}

#[test]
fn subtraction() {
    binary("rsub", 32, sub);
}

#[test]
fn multiplication() {
    binary("rmul", 33, mul);
}

#[test]
fn division() {
    binary("rdiv", 34, div);
}

#[test]
fn parts_are_reduced_with_a_positive_denominator() {
    let (mut rng, mut oracle) = (Rng(35), Oracle::default());
    for bits in WIDTHS {
        let h = TestHost::new(bits);
        for _ in 0..ROUNDS / WIDTHS.len() {
            let (n, d) = (h.random(&mut rng, 3), h.random(&mut rng, 3));
            match from_parts(&h, n, d) {
                Ok(x) => oracle.case("parts", &[h.show(n), h.show(d)], h.show_rational(x)),
                Err(e) => {
                    assert_eq!(e, TestError::Num(NumError::DivideByZero));
                    assert_eq!(int::sign(&h, d), Ordering::Equal);
                }
            }
        }
    }
    oracle.check();
}

#[test]
fn comparisons_rounding_and_powers() {
    let (mut rng, mut oracle) = (Rng(36), Oracle::default());
    for bits in WIDTHS {
        let h = TestHost::new(bits);
        for _ in 0..ROUNDS / WIDTHS.len() {
            let (x, y) = (h.random_rational(&mut rng, 3), h.random_rational(&mut rng, 3));
            let (xs, ys) = (h.show_rational(x), h.show_rational(y));
            oracle.case("rcmp", &[xs.clone(), ys], (compare(&h, x, y).unwrap() as i8).to_string());
            for (name, mode) in [("floor", Round::Floor), ("ceiling", Round::Ceiling), ("truncate", Round::Truncate), ("round", Round::Nearest)] {
                oracle.case(name, std::slice::from_ref(&xs), h.show(round(&h, x, mode).unwrap()));
            }
            let e = rng.below(13) as i64 - 6;
            match expt(&h, x, e) {
                Ok(z) => oracle.case("rexpt", &[xs, hex_i64(e)], h.show_rational(z)),
                Err(err) => {
                    assert_eq!(err, TestError::Num(NumError::DivideByZero));
                    assert!(e < 0 && sign(&h, x) == Ordering::Equal);
                }
            }
        }
    }
    oracle.check();
}

#[test]
fn halves_round_to_even() {
    let h = TestHost::new(64);
    for (num, want) in [(1, 0), (3, 2), (5, 2), (7, 4), (-1, 0), (-3, -2), (-5, -2), (-7, -4)] {
        let x = from_parts(&h, int::from_i64(&h, num).unwrap(), int::from_i64(&h, 2).unwrap()).unwrap();
        assert_eq!(int::to_i64(&h, round(&h, x, Round::Nearest).unwrap()), Some(want), "{num}/2");
    }
}

/// A ratio whose parts are up to `max_len` digits each, so its exponent can be far outside
/// what doubles hold.
fn spread(h: &TestHost, rng: &mut Rng, max_len: usize) -> TestRational {
    let num = int::from_digits(h, rng.bool(), crate::bigint::Digits::new(&rng.nonzero(max_len))).unwrap();
    let den = int::from_digits(h, false, crate::bigint::Digits::new(&rng.nonzero(max_len))).unwrap();
    from_parts(h, num, den).unwrap()
}

fn power_of_two(h: &TestHost, k: i64) -> TestRational {
    let one = int::from_i64(h, 1).unwrap();
    expt(h, from_parts(h, int::from_i64(h, 2).unwrap(), one).unwrap(), k).unwrap()
}

#[test]
fn conversion_to_doubles_rounds_once() {
    let (mut rng, mut oracle) = (Rng(37), Oracle::default());
    for bits in WIDTHS {
        let h = TestHost::new(bits);
        let mut cases: Vec<TestRational> = (0..ROUNDS / WIDTHS.len()).map(|_| spread(&h, &mut rng, 20)).collect();
        cases.extend((0..ROUNDS / WIDTHS.len()).map(|_| h.random_rational(&mut rng, 2)));
        // Around the smallest subnormal, ties in the subnormal range, and the overflow edge.
        let k = |odd: i64, e: i64| mul(&h, from_parts(&h, int::from_i64(&h, odd).unwrap(), int::from_i64(&h, 1).unwrap()).unwrap(), power_of_two(&h, e)).unwrap();
        for e in [-1076, -1075, -1074, -1073, -1060, -1023, -1022, -1021, 1022, 1023, 1024] {
            for odd in [1, 3, 5, -1, -3, 2049, 4095, (1 << 53) - 1, (1 << 54) - 1, (1 << 54) + 1] {
                cases.push(k(odd, e));
            }
        }
        for x in cases {
            let f = to_f64(&h, x).unwrap();
            oracle.case("f64", &[h.show_rational(x)], format!("{:x}", f.to_bits()));
        }
    }
    oracle.check();
}

#[test]
fn doubles_convert_exactly() {
    let (mut rng, mut oracle) = (Rng(38), Oracle::default());
    for bits in WIDTHS {
        let h = TestHost::new(bits);
        let mut doubles = vec![0.5, -0.5, 0.1, f64::MIN_POSITIVE, -f64::MIN_POSITIVE, 5e-324, -5e-324, f64::MAX, 1.5, 1e300];
        doubles.extend((0..ROUNDS / WIDTHS.len()).map(|_| f64::from_bits(rng.u64())).filter(|f| f.is_finite()));
        for f in doubles {
            let x = from_f64(&h, f).unwrap();
            oracle.case("rfromf64", &[format!("{:x}", f.to_bits())], h.show_rational(x));
            assert_eq!(to_f64(&h, x).unwrap().to_bits(), f.to_bits(), "{f:e} round trips");
        }
        for f in [f64::INFINITY, f64::NEG_INFINITY, f64::NAN] {
            assert!(matches!(from_f64(&h, f), Err(TestError::Num(NumError::NoExactValue))));
        }
    }
    oracle.check();
}

#[test]
fn equal_rationals_hash_the_same_however_they_are_held() {
    let mut rng = Rng(39);
    let hosts = WIDTHS.map(TestHost::new);
    let hash_of = |h: &TestHost, x| {
        let mut state = std::hash::DefaultHasher::new();
        hash(h, x, &mut state);
        std::hash::Hasher::finish(&state)
    };
    for _ in 0..ROUNDS / 4 {
        let x = hosts[0].random_rational(&mut rng, 3);
        let (num, den) = (numerator(&hosts[0], x), denominator(&hosts[0], x).unwrap());
        let want = hash_of(&hosts[0], x);
        for h in &hosts[1..] {
            let rebuild = |n| {
                let text = int::to_string(&hosts[0], n, 16).unwrap();
                let (negative, digits) = text.strip_prefix('-').map_or((false, text.as_str()), |rest| (true, rest));
                int::parse(h, digits.as_bytes(), 16, negative).unwrap().unwrap()
            };
            let same = from_parts(h, rebuild(num), rebuild(den)).unwrap();
            assert_eq!(hash_of(h, same), want);
        }
    }
}

#[test]
fn ratios_print_as_num_over_den() {
    let h = TestHost::new(64);
    let x = from_parts(&h, int::from_i64(&h, -6).unwrap(), int::from_i64(&h, 4).unwrap()).unwrap();
    assert_eq!(to_string(&h, x, 10).unwrap(), "-3/2");
    let y = from_parts(&h, int::from_i64(&h, 8).unwrap(), int::from_i64(&h, -4).unwrap()).unwrap();
    assert_eq!(to_string(&h, y, 10).unwrap(), "-2");
    assert!(is_integer(&h, y) && !is_integer(&h, x));
}
