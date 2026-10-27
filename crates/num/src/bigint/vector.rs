//! Comparison, addition, subtraction and shifts, digit by digit.

use std::cmp::Ordering;

use super::{DIGIT_BITS, Digit, Digits, RWDigits, digit_add, digit_sub};

pub fn compare(x: Digits<'_>, y: Digits<'_>) -> Ordering {
    let (x, y) = (x.normalize(), y.normalize());
    x.len().cmp(&y.len()).then_with(|| x.as_slice().iter().rev().cmp(y.as_slice().iter().rev()))
}

/// `z = x + y`. `z` needs `max(x, y) + 1` digits.
pub fn add(mut z: RWDigits<'_>, x: Digits<'_>, y: Digits<'_>) {
    let (x, y) = if x.len() >= y.len() { (x, y) } else { (y, x) };
    let mut carry = 0;
    for i in 0..x.len() {
        (z[i], carry) = digit_add(x[i], y.get(i), carry);
    }
    z[x.len()] = carry;
    z.offset(x.len() + 1).clear();
}

/// `z = x - y` for `x >= y`. `z` needs `x` digits, normalized.
pub fn subtract(mut z: RWDigits<'_>, x: Digits<'_>, y: Digits<'_>) {
    let (x, y) = (x.normalize(), y.normalize());
    let mut borrow = 0;
    for i in 0..x.len() {
        (z[i], borrow) = digit_sub(x[i], y.get(i), borrow);
    }
    debug_assert_eq!(borrow, 0, "subtract needs x >= y");
    z.offset(x.len()).clear();
}

/// `z += x` in place, returning the carry out of `z`.
pub fn add_and_return_carry(mut z: RWDigits<'_>, x: Digits<'_>) -> Digit {
    let mut carry = 0;
    for i in 0..z.len() {
        if i >= x.len() && carry == 0 {
            break;
        }
        (z[i], carry) = digit_add(z[i], x.get(i), carry);
    }
    carry
}

/// `z -= x` in place, returning the borrow out of `z`.
pub fn subtract_and_return_borrow(mut z: RWDigits<'_>, x: Digits<'_>) -> Digit {
    let mut borrow = 0;
    for i in 0..z.len() {
        if i >= x.len() && borrow == 0 {
            break;
        }
        (z[i], borrow) = digit_sub(z[i], x.get(i), borrow);
    }
    borrow
}

/// `z += d` in place, returning the carry.
pub fn add_digit(z: RWDigits<'_>, d: Digit) -> Digit {
    add_and_return_carry(z, Digits::new(&[d]))
}

/// `z = x + 1`. `z` needs `x + 1` digits.
pub fn add_one(mut z: RWDigits<'_>, x: Digits<'_>) {
    let mut carry = 1;
    for i in 0..x.len() {
        (z[i], carry) = digit_add(x[i], 0, carry);
    }
    z[x.len()] = carry;
    z.offset(x.len() + 1).clear();
}

/// `z = x - 1` for `x >= 1`. `z` needs `x` digits.
pub fn subtract_one(mut z: RWDigits<'_>, x: Digits<'_>) {
    let mut borrow = 1;
    for i in 0..x.len() {
        (z[i], borrow) = digit_sub(x[i], 0, borrow);
    }
    debug_assert_eq!(borrow, 0, "subtract_one needs x >= 1");
    z.offset(x.len()).clear();
}

/// `z = x + y` with signs, returning whether `z` is negative. `z` needs `max(x, y) + 1`
/// digits.
pub fn add_signed(mut z: RWDigits<'_>, x: Digits<'_>, x_negative: bool, y: Digits<'_>, y_negative: bool) -> bool {
    if x_negative == y_negative {
        add(z.reborrow(), x, y);
        return x_negative && !z.read().is_zero();
    }
    match compare(x, y) {
        Ordering::Less => {
            subtract(z.reborrow(), y, x);
            y_negative
        }
        _ => {
            subtract(z.reborrow(), x, y);
            x_negative && !z.read().is_zero()
        }
    }
}

/// `z = x - y` with signs, as [`add_signed`].
pub fn subtract_signed(z: RWDigits<'_>, x: Digits<'_>, x_negative: bool, y: Digits<'_>, y_negative: bool) -> bool {
    add_signed(z, x, x_negative, y, !y_negative)
}

/// `z = x << shift`. `z` needs `x + shift / DIGIT_BITS + 1` digits.
pub fn left_shift(mut z: RWDigits<'_>, x: Digits<'_>, shift: usize) {
    let (digits, bits) = (shift / DIGIT_BITS, shift % DIGIT_BITS);
    z.slice(0, digits).clear();
    if bits == 0 {
        for i in 0..x.len() {
            z[digits + i] = x[i];
        }
        z.offset(digits + x.len()).clear();
        return;
    }
    let mut carry = 0;
    for i in 0..x.len() {
        z[digits + i] = x[i] << bits | carry;
        carry = x[i] >> (DIGIT_BITS - bits);
    }
    z[digits + x.len()] = carry;
    z.offset(digits + x.len() + 1).clear();
}

/// `z = x >> shift`, rounding toward zero. `z` needs `x - shift / DIGIT_BITS` digits.
pub fn right_shift(mut z: RWDigits<'_>, x: Digits<'_>, shift: usize) {
    let (digits, bits) = (shift / DIGIT_BITS, shift % DIGIT_BITS);
    let n = x.len().saturating_sub(digits);
    for i in 0..n {
        let lo = x[digits + i];
        z[i] = if bits == 0 { lo } else { lo >> bits | x.get(digits + i + 1) << (DIGIT_BITS - bits) };
    }
    z.offset(n).clear();
}

/// Whether `x >> shift` drops any one bits, which makes a negative shift round down.
pub fn shifts_out_ones(x: Digits<'_>, shift: usize) -> bool {
    let (digits, bits) = (shift / DIGIT_BITS, shift % DIGIT_BITS);
    x.slice(0, digits).as_slice().iter().any(|&d| d != 0) || (bits != 0 && x.get(digits) << (DIGIT_BITS - bits) != 0)
}

/// The magnitude as the nearest double, ties to even.
pub fn to_f64(x: Digits<'_>) -> f64 {
    let x = x.normalize();
    let bits = x.bit_len();
    if bits <= DIGIT_BITS {
        return x.get(0) as f64;
    }
    // The top digit's worth of bits, with any lower one bit folded into the lowest bit, so
    // the conversion rounds ties correctly.
    let shift = bits - DIGIT_BITS;
    let (digit, s) = (shift / DIGIT_BITS, shift % DIGIT_BITS);
    let mut top = x[digit] >> s;
    if s != 0 {
        top |= x[digit + 1] << (DIGIT_BITS - s);
    }
    let sticky = shifts_out_ones(x, shift);
    if shift > 1023 {
        return f64::INFINITY;
    }
    (top | sticky as Digit) as f64 * f64::from_bits(((1023 + shift) as u64) << 52)
}
