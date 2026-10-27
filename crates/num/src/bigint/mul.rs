//! Multiplication.

use super::{Digit, Digits, RWDigits, digit_mul_add};

/// `z = x * y` for a single digit `y`. `z` needs `x + 1` digits.
pub fn multiply_single(mut z: RWDigits<'_>, x: Digits<'_>, y: Digit) {
    let mut carry = 0;
    for i in 0..x.len() {
        (z[i], carry) = digit_mul_add(x[i], y, 0, carry);
    }
    z[x.len()] = carry;
    z.offset(x.len() + 1).clear();
}

/// `z = z * m + add` in place, returning the carry.
pub fn multiply_add_in_place(mut z: RWDigits<'_>, m: Digit, add: Digit) -> Digit {
    let mut carry = add;
    for i in 0..z.len() {
        (z[i], carry) = digit_mul_add(z[i], m, 0, carry);
    }
    carry
}

/// `z = x * y`. `z` needs `x + y` digits and must not overlap them.
pub fn multiply_schoolbook(mut z: RWDigits<'_>, x: Digits<'_>, y: Digits<'_>) {
    let (x, y) = (x.normalize(), y.normalize());
    if x.is_empty() || y.is_empty() {
        return z.clear();
    }
    let mut carry = 0;
    for j in 0..y.len() {
        (z[j], carry) = digit_mul_add(x[0], y[j], 0, carry);
    }
    z[y.len()] = carry;
    for i in 1..x.len() {
        let xi = x[i];
        let mut carry = 0;
        if xi != 0 {
            for j in 0..y.len() {
                (z[i + j], carry) = digit_mul_add(xi, y[j], z[i + j], carry);
            }
        }
        // The rows so far fit below digit `i + y.len()`, so the carry is all of it.
        z[i + y.len()] = carry;
    }
    z.offset(x.len() + y.len()).clear();
}

/// `z = x * y`. `z` needs `x + y` digits.
pub fn multiply(z: RWDigits<'_>, x: Digits<'_>, y: Digits<'_>) {
    let (x, y) = (x.normalize(), y.normalize());
    if y.len() == 1 {
        return multiply_single(z, x, y[0]);
    }
    if x.len() == 1 {
        return multiply_single(z, y, x[0]);
    }
    multiply_schoolbook(z, x, y);
}

/// The work [`multiply`] does, in digit operations.
pub fn multiply_cost(x: Digits<'_>, y: Digits<'_>) -> u64 {
    x.normalize().len() as u64 * y.normalize().len() as u64
}
