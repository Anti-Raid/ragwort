//! Comparison, addition, subtraction and shifts, digit by digit.

use std::cmp::Ordering;

use super::{DIGIT_BITS, Digit, Digits, RWDigits, digit_add, digit_sub};

pub fn compare(x: Digits<'_>, y: Digits<'_>) -> Ordering {
    let (x, y) = (x.normalize(), y.normalize());
    x.len().cmp(&y.len()).then_with(|| x.iter().rev().cmp(y.iter().rev()))
}

/// Computes `z = x + y`. `z` needs one more digit than the longer of `x` and `y`.
pub fn add(mut z: RWDigits<'_>, x: Digits<'_>, y: Digits<'_>) {
    let (x, y) = if x.len() >= y.len() {
        (x, y)
    } else {
        (y, x)
    };
    let mut carry = 0;
    for i in 0..x.len() {
        carry = z.put(i, digit_add(x.at(i), y.get(i), carry));
    }
    z.set(x.len(), carry);
    z.offset(x.len() + 1).clear();
}

/// Computes `z = x - y` for `x >= y`. `z` needs as many digits as the normalized `x`.
pub fn subtract(mut z: RWDigits<'_>, x: Digits<'_>, y: Digits<'_>) {
    let (x, y) = (x.normalize(), y.normalize());
    let mut borrow = 0;
    for i in 0..x.len() {
        borrow = z.put(i, digit_sub(x.at(i), y.get(i), borrow));
    }
    debug_assert_eq!(borrow, 0, "subtract needs x >= y");
    z.offset(x.len()).clear();
}

/// Computes `z += x` in place and returns the carry out of `z`.
pub fn add_and_return_carry(mut z: RWDigits<'_>, x: Digits<'_>) -> Digit {
    let mut carry = 0;
    for i in 0..z.len() {
        if i >= x.len() && carry == 0 {
            break;
        }
        carry = z.put(i, digit_add(z.at(i), x.get(i), carry));
    }
    carry
}

/// Computes `z -= x` in place and returns the borrow out of `z`.
pub fn subtract_and_return_borrow(mut z: RWDigits<'_>, x: Digits<'_>) -> Digit {
    let mut borrow = 0;
    for i in 0..z.len() {
        if i >= x.len() && borrow == 0 {
            break;
        }
        borrow = z.put(i, digit_sub(z.at(i), x.get(i), borrow));
    }
    borrow
}

/// Computes `z += digit` in place and returns the carry.
pub fn add_digit(z: RWDigits<'_>, digit: Digit) -> Digit {
    add_and_return_carry(z, Digits::of_mut(&mut [digit]))
}

/// Computes `z = x + 1`. `z` needs one more digit than `x`.
pub fn add_one(mut z: RWDigits<'_>, x: Digits<'_>) {
    let mut carry = 1;
    for i in 0..x.len() {
        carry = z.put(i, digit_add(x.at(i), 0, carry));
    }
    z.set(x.len(), carry);
    z.offset(x.len() + 1).clear();
}

/// Computes `z = x - 1` for `x >= 1`. `z` needs as many digits as `x`.
pub fn subtract_one(mut z: RWDigits<'_>, x: Digits<'_>) {
    let mut borrow = 1;
    for i in 0..x.len() {
        borrow = z.put(i, digit_sub(x.at(i), 0, borrow));
    }
    debug_assert_eq!(borrow, 0, "subtract_one needs x >= 1");
    z.offset(x.len()).clear();
}

/// Computes `z = x + y` for signed operands and returns whether `z` is negative. `z` needs one more digit than the longer
/// of `x` and `y`.
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

/// Computes `z = x - y` for signed operands, with the conventions of [`add_signed`].
pub fn subtract_signed(z: RWDigits<'_>, x: Digits<'_>, x_negative: bool, y: Digits<'_>, y_negative: bool) -> bool {
    add_signed(z, x, x_negative, y, !y_negative)
}

/// Computes `z = x << shift`. `z` needs `x.len() + shift / DIGIT_BITS + 1` digits.
pub fn left_shift(mut z: RWDigits<'_>, x: Digits<'_>, shift: usize) {
    let (digits, bits) = (shift / DIGIT_BITS, shift % DIGIT_BITS);
    z.slice(0, digits).clear();
    if bits == 0 {
        for i in 0..x.len() {
            z.set(digits + i, x.at(i));
        }
        z.offset(digits + x.len()).clear();
        return;
    }
    let mut carry = 0;
    for i in 0..x.len() {
        z.set(digits + i, x.at(i) << bits | carry);
        carry = x.at(i) >> (DIGIT_BITS - bits);
    }
    z.set(digits + x.len(), carry);
    z.offset(digits + x.len() + 1).clear();
}

/// Computes `z = x >> shift`, rounding toward zero. `z` needs `x.len() - shift / DIGIT_BITS` digits.
pub fn right_shift(mut z: RWDigits<'_>, x: Digits<'_>, shift: usize) {
    let (digits, bits) = (shift / DIGIT_BITS, shift % DIGIT_BITS);
    let n = x.len().saturating_sub(digits);
    for i in 0..n {
        let lo = x.at(digits + i);
        let digit = if bits == 0 {
            lo
        } else {
            lo >> bits | x.get(digits + i + 1) << (DIGIT_BITS - bits)
        };
        z.set(i, digit);
    }
    z.offset(n).clear();
}

/// Returns whether `x >> shift` drops any one bits. If it does, the right shift of a negative number rounds toward negative infinity, so the caller adds one to the shifted magnitude.
pub fn shifts_out_ones(x: Digits<'_>, shift: usize) -> bool {
    let (digits, bits) = (shift / DIGIT_BITS, shift % DIGIT_BITS);
    x.slice(0, digits).iter().any(|digit| digit != 0) || (bits != 0 && x.get(digits) << (DIGIT_BITS - bits) != 0)
}

/// Returns the `f64` nearest to the magnitude `x`, with ties to even.
pub fn to_f64(x: Digits<'_>) -> f64 {
    let x = x.normalize();
    let bits = x.bit_len();
    if bits <= DIGIT_BITS {
        return x.get(0) as f64;
    }
    // Take the top `DIGIT_BITS` bits of `x`. OR a sticky bit for any lower one bit into the lowest bit, so that
    // the conversion to `f64` rounds ties correctly.
    let shift = bits - DIGIT_BITS;
    let (digit, bit_shift) = (shift / DIGIT_BITS, shift % DIGIT_BITS);
    let mut top = x.at(digit) >> bit_shift;
    if bit_shift != 0 {
        top |= x.at(digit + 1) << (DIGIT_BITS - bit_shift);
    }
    let sticky = shifts_out_ones(x, shift);
    if shift > 1023 {
        return f64::INFINITY;
    }
    (top | sticky as Digit) as f64 * f64::from_bits(((1023 + shift) as u64) << 52)
}
