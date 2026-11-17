//! Multiplication.

use super::{Digit, Digits, RWDigits, digit_mul_add};

/// Computes `z = x * y` for a single digit `y`. `z` needs one more digit than `x`.
pub fn multiply_single(mut z: RWDigits<'_>, x: Digits<'_>, y: Digit) {
    let mut carry = 0;
    for i in 0..x.len() {
        carry = z.put(i, digit_mul_add(x.at(i), y, 0, carry));
    }
    z.set(x.len(), carry);
    z.offset(x.len() + 1).clear();
}

/// Computes `z = z * factor + add` in place and returns the carry.
pub fn multiply_add_in_place(mut z: RWDigits<'_>, factor: Digit, add: Digit) -> Digit {
    let mut carry = add;
    for i in 0..z.len() {
        carry = z.put(i, digit_mul_add(z.at(i), factor, 0, carry));
    }
    carry
}

/// Computes `z = x * y` by schoolbook multiplication. `z` needs `x.len() + y.len()` digits and must not overlap `x` or `y`.
pub fn multiply_schoolbook(mut z: RWDigits<'_>, x: Digits<'_>, y: Digits<'_>) {
    let (x, y) = (x.normalize(), y.normalize());
    if x.is_empty() || y.is_empty() {
        return z.clear();
    }
    let mut carry = 0;
    for j in 0..y.len() {
        carry = z.put(j, digit_mul_add(x.at(0), y.at(j), 0, carry));
    }
    z.set(y.len(), carry);
    for i in 1..x.len() {
        let xi = x.at(i);
        let mut carry = 0;
        if xi != 0 {
            for j in 0..y.len() {
                carry = z.put(i + j, digit_mul_add(xi, y.at(j), z.at(i + j), carry));
            }
        }
        // The rows added so far fit below digit `i + y.len()`. So that digit is still unset, and the carry is its whole value.
        z.set(i + y.len(), carry);
    }
    z.offset(x.len() + y.len()).clear();
}

/// Computes `z = x * y`. `z` needs `x.len() + y.len()` digits.
pub fn multiply(z: RWDigits<'_>, x: Digits<'_>, y: Digits<'_>) {
    let (x, y) = (x.normalize(), y.normalize());
    if y.len() == 1 {
        return multiply_single(z, x, y.at(0));
    }
    if x.len() == 1 {
        return multiply_single(z, y, x.at(0));
    }
    multiply_schoolbook(z, x, y);
}

/// Returns the cost of [`multiply`], in digit operations.
pub fn multiply_cost(x: Digits<'_>, y: Digits<'_>) -> u64 {
    x.normalize().len() as u64 * y.normalize().len() as u64
}
