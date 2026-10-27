use std::cmp::Ordering;

use crate::bigint::Digits;
use crate::int::*;
use crate::testing::{Oracle, ROUNDS, Rng, TestError, TestHost, TestInt, WIDTHS, hex_i64};

fn binary(oracle_op: &str, seed: u64, max_len: usize, op: fn(&TestHost, TestInt, TestInt) -> Result<TestInt, TestError>) {
    let (mut rng, mut oracle) = (Rng(seed), Oracle::default());
    for bits in WIDTHS {
        let h = TestHost::new(bits);
        for _ in 0..ROUNDS / WIDTHS.len() {
            let (x, y) = (h.random(&mut rng, max_len), h.random(&mut rng, max_len));
            match op(&h, x, y) {
                Ok(z) => oracle.case(oracle_op, &[h.show(x), h.show(y)], h.show(z)),
                Err(TestError::Num(NumError::DivideByZero)) => assert_eq!(sign(&h, y), Ordering::Equal),
                Err(e) => panic!("{e:?}"),
            }
        }
    }
    oracle.check();
}

#[test]
fn addition() {
    binary("add", 11, 4, add);
}

#[test]
fn subtraction() {
    binary("sub", 12, 4, sub);
}

/// Long operands that cancel down to a few digits or a small integer.
#[test]
fn cancelling_subtraction() {
    let (mut rng, mut oracle) = (Rng(23), Oracle::default());
    for bits in WIDTHS {
        let h = TestHost::new(bits);
        for _ in 0..ROUNDS / WIDTHS.len() {
            let (x, d) = (h.random(&mut rng, 8), h.random(&mut rng, 2));
            let y = add(&h, x, d).unwrap();
            oracle.case("sub", &[h.show(y), h.show(x)], h.show(sub(&h, y, x).unwrap()));
        }
    }
    oracle.check();
}

#[test]
fn multiplication() {
    binary("mul", 13, 4, mul);
}

#[test]
fn quotients() {
    binary("quot", 14, 6, quotient);
}

#[test]
fn remainders() {
    binary("rem", 15, 6, remainder);
}

#[test]
fn moduli() {
    binary("mod", 16, 6, modulo);
}

#[test]
fn floor_quotients() {
    binary("fquot", 17, 6, floor_quotient);
}

#[test]
fn gcds() {
    binary("gcd", 18, 6, gcd);
}

#[test]
fn lcms() {
    binary("lcm", 19, 4, lcm);
}

#[test]
fn bitwise_and_or_xor() {
    binary("and", 20, 4, bitwise_and);
    binary("or", 21, 4, bitwise_or);
    binary("xor", 22, 4, bitwise_xor);
}

#[test]
fn quotient_and_remainder_together_match_apart() {
    let mut rng = Rng(23);
    for bits in WIDTHS {
        let h = TestHost::new(bits);
        for _ in 0..ROUNDS / WIDTHS.len() {
            let (x, y) = (h.random(&mut rng, 6), h.random(&mut rng, 6));
            if sign(&h, y) == Ordering::Equal {
                assert_eq!(quotient_remainder(&h, x, y).unwrap_err(), TestError::Num(NumError::DivideByZero));
                continue;
            }
            let (q, r) = quotient_remainder(&h, x, y).unwrap();
            assert_eq!(h.show(q), h.show(quotient(&h, x, y).unwrap()));
            assert_eq!(h.show(r), h.show(remainder(&h, x, y).unwrap()));
        }
    }
}

#[test]
fn comparisons_and_predicates() {
    let (mut rng, mut oracle) = (Rng(24), Oracle::default());
    for bits in WIDTHS {
        let h = TestHost::new(bits);
        for _ in 0..ROUNDS / WIDTHS.len() {
            let (x, y) = (h.random(&mut rng, 3), h.random(&mut rng, 3));
            let (xs, ys) = (h.show(x), h.show(y));
            oracle.case("cmp", &[xs.clone(), ys], (compare(&h, x, y) as i8).to_string());
            oracle.case("cmp", &[xs.clone(), "0".into()], (sign(&h, x) as i8).to_string());
            oracle.case("even", std::slice::from_ref(&xs), (is_even(&h, x) as u8).to_string());
            oracle.case("ilen", std::slice::from_ref(&xs), format!("{:x}", integer_length(&h, x)));
            oracle.case("f64", std::slice::from_ref(&xs), format!("{:x}", to_f64(&h, x).to_bits()));
            oracle.case("neg", std::slice::from_ref(&xs), h.show(neg(&h, x).unwrap()));
            oracle.case("abs", std::slice::from_ref(&xs), h.show(abs(&h, x).unwrap()));
            oracle.case("not", std::slice::from_ref(&xs), h.show(bitwise_not(&h, x).unwrap()));
            let small = to_i64(&h, x).map_or("none".into(), hex_i64);
            oracle.case("i64", &[xs], small);
        }
    }
    oracle.check();
}

fn hash_of(h: &TestHost, x: TestInt) -> u64 {
    let mut state = std::hash::DefaultHasher::new();
    hash(h, x, &mut state);
    std::hash::Hasher::finish(&state)
}

#[test]
fn equal_integers_hash_the_same_however_they_are_held() {
    let mut rng = Rng(29);
    let hosts = WIDTHS.map(TestHost::new);
    let mut seen = std::collections::HashMap::new();
    for _ in 0..ROUNDS {
        let x = hosts[0].random(&mut rng, 4);
        let text = to_string(&hosts[0], x, 16).unwrap();
        let (negative, digits) = text.strip_prefix('-').map_or((false, text.as_str()), |rest| (true, rest));
        let want = hash_of(&hosts[0], x);
        for h in &hosts[1..] {
            let same = parse(h, digits.as_bytes(), 16, negative).unwrap().unwrap();
            assert_eq!(hash_of(h, same), want, "{text}");
        }
        // Different values should practically never collide.
        if let Some(other) = seen.insert(want, text.clone()) {
            assert_eq!(other, text, "hash collision");
        }
    }
    // Values a digit apart in every position, and either sign.
    let h = &hosts[2];
    let (mut values, mut hashes) = (std::collections::HashSet::new(), std::collections::HashSet::new());
    for len in 0..4 {
        for digit in [0, 1, u64::MAX] {
            for negative in [false, true] {
                let mut digits = vec![digit; len];
                digits.push(1);
                if values.insert((negative, digits.clone())) {
                    let x = from_digits(h, negative, Digits::new(&digits)).unwrap();
                    assert!(hashes.insert(hash_of(h, x)), "{negative} {digits:?}");
                }
            }
        }
    }
}

#[test]
fn shifts() {
    let (mut rng, mut oracle) = (Rng(25), Oracle::default());
    for bits in WIDTHS {
        let h = TestHost::new(bits);
        for _ in 0..ROUNDS / WIDTHS.len() {
            let x = h.random(&mut rng, 4);
            let shift = rng.below(400) as i64 - 200;
            let ours = h.show(arithmetic_shift(&h, x, shift).unwrap());
            oracle.case("ash", &[h.show(x), hex_i64(shift)], ours);
        }
        // Shifts too big to make, and right shifts past everything.
        let x = from_i64(&h, -5).unwrap();
        assert_eq!(arithmetic_shift(&h, x, i64::MAX).unwrap_err(), TestError::TooBig);
        assert_eq!(h.show(arithmetic_shift(&h, x, i64::MIN).unwrap()), "-1");
        let zero = from_i64(&h, 0).unwrap();
        assert_eq!(h.show(arithmetic_shift(&h, zero, i64::MAX).unwrap()), "0");
    }
    oracle.check();
}

#[test]
fn powers() {
    let (mut rng, mut oracle) = (Rng(26), Oracle::default());
    for bits in WIDTHS {
        let h = TestHost::new(bits);
        for _ in 0..ROUNDS / WIDTHS.len() / 4 {
            let x = h.random(&mut rng, 2);
            let e = rng.below(40);
            oracle.case("expt", &[h.show(x), format!("{e:x}")], h.show(expt(&h, x, e).unwrap()));
        }
    }
    oracle.check();
}

#[test]
fn doubles_convert_exactly() {
    let (mut rng, mut oracle) = (Rng(27), Oracle::default());
    for bits in WIDTHS {
        let h = TestHost::new(bits);
        let mut edges = vec![0.0, -0.0, 1.0, -1.0, 9.223_372_036_854_776e18, -9.223_372_036_854_776e18, f64::MAX, -f64::MAX];
        edges.extend((0..ROUNDS / WIDTHS.len()).map(|_| f64::from_bits(rng.u64()).trunc()).filter(|f| f.is_finite()));
        for f in edges {
            let x = from_integral_f64(&h, f).unwrap();
            oracle.case("fromf64", &[format!("{:x}", f.to_bits())], h.show(x));
            assert_eq!(to_f64(&h, x), f);
        }
    }
    oracle.check();
}

#[test]
fn strings_round_trip() {
    let (mut rng, mut oracle) = (Rng(28), Oracle::default());
    for bits in WIDTHS {
        let h = TestHost::new(bits);
        for _ in 0..ROUNDS / WIDTHS.len() {
            let x = h.random(&mut rng, 5);
            let radix = rng.below(35) as u32 + 2;
            let text = to_string(&h, x, radix).unwrap();
            oracle.case("radix", &[h.show(x), format!("{radix:x}")], text.clone());
            let (negative, digits) = match text.strip_prefix('-') {
                Some(rest) => (true, rest),
                None => (false, text.as_str()),
            };
            let back = parse(&h, digits.as_bytes(), radix, negative).unwrap().unwrap();
            assert_eq!(compare(&h, back, x), Ordering::Equal);
            h.show(back);
        }
        assert!(parse(&h, b"", 10, false).unwrap().is_none());
        assert!(parse(&h, b"12a", 10, false).unwrap().is_none());
        assert!(parse(&h, b"-1", 10, false).unwrap().is_none());
        assert_eq!(h.show(parse(&h, b"0000", 10, true).unwrap().unwrap()), "0");
    }
    oracle.check();
}

/// Integer square roots of squares, their neighbours, and anything else.
#[test]
fn square_roots() {
    let (mut rng, mut oracle) = (Rng(24), Oracle::default());
    for bits in WIDTHS {
        let h = TestHost::new(bits);
        for _ in 0..ROUNDS / WIDTHS.len() {
            let s = abs(&h, h.random(&mut rng, 6)).unwrap();
            let square = mul(&h, s, s).unwrap();
            let one = from_i64(&h, 1).unwrap();
            let below = if sign(&h, square) == Ordering::Greater { sub(&h, square, one).unwrap() } else { square };
            for x in [square, below, add(&h, square, one).unwrap(), abs(&h, h.random(&mut rng, 8)).unwrap()] {
                oracle.case("isqrt", &[h.show(x)], h.show(isqrt(&h, x).unwrap()));
            }
        }
    }
    oracle.check();
}
