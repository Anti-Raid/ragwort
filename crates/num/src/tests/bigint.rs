use std::cmp::Ordering;

use super::*;
use crate::testing::{Oracle, ROUNDS, Rng, hex, signed};

#[test]
fn addition_subtraction_and_comparison() {
    let (mut rng, mut oracle) = (Rng(1), Oracle::default());
    for _ in 0..ROUNDS {
        let (x, y) = (rng.digits(12), rng.digits(12));
        let (x, y) = (Digits::new(&x), Digits::new(&y));
        let mut z = vec![7; x.len().max(y.len()) + 3];
        add(RWDigits::new(&mut z), x, y);
        oracle.case("add", &[hex(x), hex(y)], hex(Digits::new(&z)));
        let order = compare(x, y);
        oracle.case("cmp", &[hex(x), hex(y)], (order as i8).to_string());
        let (big, small) = if order == Ordering::Less { (y, x) } else { (x, y) };
        let mut z = vec![7; big.len() + 2];
        subtract(RWDigits::new(&mut z), big, small);
        oracle.case("sub", &[hex(big), hex(small)], hex(Digits::new(&z)));
    }
    oracle.check();
}

#[test]
fn signed_addition_and_subtraction() {
    let (mut rng, mut oracle) = (Rng(2), Oracle::default());
    for _ in 0..ROUNDS {
        let (x, y) = (rng.digits(6), rng.digits(6));
        let (x, y) = (Digits::new(&x), Digits::new(&y));
        let (xn, yn) = (rng.bool(), rng.bool());
        let mut z = vec![7; x.len().max(y.len()) + 1];
        let negative = add_signed(RWDigits::new(&mut z), x, xn, y, yn);
        assert!(!(negative && Digits::new(&z).is_zero()), "negative zero");
        oracle.case("add", &[signed(x, xn), signed(y, yn)], signed(Digits::new(&z), negative));
        let negative = subtract_signed(RWDigits::new(&mut z), x, xn, y, yn);
        assert!(!(negative && Digits::new(&z).is_zero()), "negative zero");
        oracle.case("sub", &[signed(x, xn), signed(y, yn)], signed(Digits::new(&z), negative));
    }
    oracle.check();
}

#[test]
fn multiplication() {
    let (mut rng, mut oracle) = (Rng(3), Oracle::default());
    for _ in 0..ROUNDS {
        let (x, y) = (rng.digits(10), rng.digits(10));
        let (x, y) = (Digits::new(&x), Digits::new(&y));
        let mut z = vec![7; x.len() + y.len() + 1];
        multiply(RWDigits::new(&mut z), x, y);
        oracle.case("mul", &[hex(x), hex(y)], hex(Digits::new(&z)));
    }
    oracle.check();
}

#[test]
fn division() {
    let (mut rng, mut oracle) = (Rng(4), Oracle::default());
    for round in 0..ROUNDS {
        let y = rng.nonzero(6);
        // Dividends made from the divisor hit the add-back step, which random ones rarely do.
        let x = match round % 3 {
            0 => rng.digits(12),
            _ => {
                let m = rng.nonzero(2);
                let mut x = vec![0; y.len() + m.len()];
                multiply(RWDigits::new(&mut x), Digits::new(&y), Digits::new(&m));
                let x = Digits::new(&x).normalize();
                let mut s = vec![0; x.len() + 1];
                if rng.bool() {
                    add_one(RWDigits::new(&mut s), x);
                } else {
                    subtract_one(RWDigits::new(&mut s), x);
                }
                s
            }
        };
        let (x, y) = (Digits::new(&x).normalize(), Digits::new(&y));
        let mut q = vec![7; x.len().saturating_sub(y.len()) + 1];
        let mut r = vec![7; y.len()];
        let mut scratch = vec![7; divide_scratch(x, y)];
        divide(Some(RWDigits::new(&mut q)), Some(RWDigits::new(&mut r)), x, y, RWDigits::new(&mut scratch));
        let ours = format!("{} {}", hex(Digits::new(&q)), hex(Digits::new(&r)));
        oracle.case("divrem", &[hex(x), hex(y)], ours);
        let mut only_r = vec![7; y.len()];
        divide(None, Some(RWDigits::new(&mut only_r)), x, y, RWDigits::new(&mut scratch));
        assert_eq!(only_r, r);
    }
    oracle.check();
}

#[test]
fn shifts() {
    let (mut rng, mut oracle) = (Rng(5), Oracle::default());
    for _ in 0..ROUNDS {
        let x = rng.digits(6);
        let x = Digits::new(&x);
        let shift = rng.below(300) as usize;
        let args = [hex(x), format!("{shift:x}")];
        let mut z = vec![7; x.len() + shift / DIGIT_BITS + 1];
        left_shift(RWDigits::new(&mut z), x, shift);
        oracle.case("shl", &args, hex(Digits::new(&z)));
        let mut z = vec![7; x.len()];
        right_shift(RWDigits::new(&mut z), x, shift);
        oracle.case("shr", &args, hex(Digits::new(&z)));
        oracle.case("lost", &args, (shifts_out_ones(x, shift) as u8).to_string());
    }
    oracle.check();
}

#[test]
fn bitwise_operations_are_twos_complement() {
    type Op = fn(RWDigits<'_>, Digits<'_>, Digits<'_>);
    type Len = fn(Digits<'_>, Digits<'_>) -> usize;
    type Case = (&'static str, [(Op, Len); 3], fn(bool, bool) -> bool);
    let ops: [Case; 3] = [
        ("and", [(and_pos_pos, and_pos_pos_len), (and_pos_neg, and_pos_neg_len), (and_neg_neg, and_neg_neg_len)], |a, b| a && b),
        ("or", [(or_pos_pos, or_pos_pos_len), (or_pos_neg, or_pos_neg_len), (or_neg_neg, or_neg_neg_len)], |a, b| a || b),
        ("xor", [(xor_pos_pos, xor_pos_pos_len), (xor_pos_neg, xor_pos_neg_len), (xor_neg_neg, xor_neg_neg_len)], |a, b| a != b),
    ];
    let (mut rng, mut oracle) = (Rng(6), Oracle::default());
    for _ in 0..ROUNDS {
        let (x, y) = (rng.nonzero(5), rng.nonzero(5));
        let (x, y) = (Digits::new(&x), Digits::new(&y));
        for (name, fns, negative) in &ops {
            for (case, (xn, yn)) in [(false, false), (false, true), (true, true)].into_iter().enumerate() {
                let (op, len) = fns[case];
                let mut z = vec![7; len(x, y)];
                op(RWDigits::new(&mut z), x, y);
                let ours = signed(Digits::new(&z), negative(xn, yn));
                oracle.case(name, &[signed(x, xn), signed(y, yn)], ours);
            }
        }
    }
    oracle.check();
}

#[test]
fn conversion_to_doubles_rounds_to_nearest_even() {
    let (mut rng, mut oracle) = (Rng(7), Oracle::default());
    let mut case = |x: &[Digit]| {
        let x = Digits::new(x);
        oracle.case("f64", &[hex(x)], format!("{:x}", to_f64(x).to_bits()));
    };
    // Ties either side of even, the largest finite double, and past it.
    let mut edges = vec![vec![(1 << 53) + 1], vec![(1 << 53) + 3], vec![(1 << 54) + 2], vec![0, (1 << 53) + 1]];
    edges.push([vec![0; 15], vec![1 << 63]].concat());
    // Ties that only a one bit further down breaks, digit aligned and not.
    edges.push(vec![1, (1 << 63) | (1 << 10)]);
    edges.push(vec![1 << 40, 0, (1 << 63) | (1 << 10)]);
    edges.push(vec![1, (1 << 62) | (1 << 9)]);
    edges.push(vec![1 << 2, (1 << 3) | (1 << 2)]);
    edges.push(vec![Digit::MAX; 16]);
    edges.push([vec![0; 15], vec![Digit::MAX << 11]].concat());
    edges.push([vec![0; 16], vec![1]].concat());
    for x in &edges {
        case(x);
    }
    for _ in 0..ROUNDS {
        case(&rng.digits(18));
    }
    oracle.check();
}

#[test]
fn strings_in_every_radix() {
    let (mut rng, mut oracle) = (Rng(8), Oracle::default());
    for _ in 0..ROUNDS / 4 {
        let x = rng.digits(8);
        let x = Digits::new(&x);
        let radix = rng.below(35) as u32 + 2;
        let mut out = vec![0u8; to_string_len(x, radix)];
        let mut scratch = vec![0; x.len()];
        let start = to_string(x, radix, RWDigits::new(&mut scratch), &mut out);
        let text = std::str::from_utf8(&out[start..]).unwrap();
        oracle.case("radix", &[hex(x), format!("{radix:x}")], text.to_owned());
        let mut back = vec![7; from_string_len(text.len(), radix)];
        from_string(RWDigits::new(&mut back), text.as_bytes(), radix).unwrap();
        assert_eq!(hex(Digits::new(&back)), hex(x));
        from_string(RWDigits::new(&mut back), text.to_uppercase().as_bytes(), radix).unwrap();
        assert_eq!(hex(Digits::new(&back)), hex(x));
    }
    let mut z = vec![0; 4];
    assert!(from_string(RWDigits::new(&mut z), b"12a", 10).is_none());
    assert!(from_string(RWDigits::new(&mut z), b"102", 2).is_none());
    oracle.check();
}
