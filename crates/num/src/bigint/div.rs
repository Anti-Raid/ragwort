//! Division.

use std::cmp::Ordering;

use super::{DIGIT_BITS, Digit, Digits, RWDigits, TwoDigits, compare, digit_add, digit_sub};

/// `quotient = x / y` for a single digit `y != 0`, returning `x % y`. `quotient` needs `x` digits, and
/// may be left out to only get the remainder.
pub fn divide_single(mut quotient: Option<RWDigits<'_>>, x: Digits<'_>, y: Digit) -> Digit {
    assert!(y != 0, "division by zero");
    let mut rem: Digit = 0;
    for i in (0..x.len()).rev() {
        let num = (rem as TwoDigits) << DIGIT_BITS | x.at(i) as TwoDigits;
        rem = (num % y as TwoDigits) as Digit;
        if let Some(quotient) = &mut quotient {
            quotient.set(i, (num / y as TwoDigits) as Digit);
        }
    }
    if let Some(mut quotient) = quotient {
        quotient.offset(x.len()).clear();
    }
    rem
}

/// Scratch digits [`divide`] needs.
pub fn divide_scratch(x: Digits<'_>, y: Digits<'_>) -> usize {
    x.normalize().len() + 1 + y.normalize().len()
}

/// `quotient = x / y` and `remainder = x % y` for `y != 0`, either of which may be left out. `quotient` needs
/// `x - y + 1` digits and `remainder` needs `y`.
pub fn divide(
    quotient: Option<RWDigits<'_>>,
    remainder: Option<RWDigits<'_>>,
    x: Digits<'_>,
    y: Digits<'_>,
    scratch: RWDigits<'_>,
) {
    let (x, y) = (x.normalize(), y.normalize());
    assert!(!y.is_empty(), "division by zero");
    if compare(x, y) == Ordering::Less {
        if let Some(mut quotient) = quotient {
            quotient.clear();
        }
        if let Some(mut remainder) = remainder {
            remainder.copy_from(x);
        }
        return;
    }
    if y.len() == 1 {
        let rem = divide_single(quotient, x, y.at(0));
        if let Some(mut remainder) = remainder {
            remainder.clear();
            remainder.set(0, rem);
        }
        return;
    }
    divide_schoolbook(quotient, remainder, x, y, scratch);
}

/// Knuth's algorithm D, for normalized `x >= y` with at least two digits in `y`.
fn divide_schoolbook(
    mut quotient: Option<RWDigits<'_>>,
    remainder: Option<RWDigits<'_>>,
    x: Digits<'_>,
    y: Digits<'_>,
    scratch: RWDigits<'_>,
) {
    let (n, excess) = (y.len(), x.len() - y.len());
    let (mut dividend, divisor) = scratch.split(x.len() + 1);
    let mut divisor = divisor.truncate(n);
    // Shift so the divisor's top bit is set, which keeps each quotient guess within 2.
    let shift = y.msd().leading_zeros() as usize;
    shift_into(divisor.reborrow(), y, shift);
    let top_bits = shift_into(dividend.reborrow(), x, shift);
    dividend.set(x.len(), top_bits);
    let (top, next) = (divisor.at(n - 1) as TwoDigits, divisor.at(n - 2) as TwoDigits);
    if let Some(quotient) = &mut quotient {
        quotient.offset(excess + 1).clear();
    }
    for j in (0..=excess).rev() {
        let num = (dividend.at(j + n) as TwoDigits) << DIGIT_BITS | dividend.at(j + n - 1) as TwoDigits;
        let (mut qhat, mut rhat) = (num / top, num % top);
        while qhat >> DIGIT_BITS != 0 || qhat * next > (rhat << DIGIT_BITS | dividend.at(j + n - 2) as TwoDigits) {
            qhat -= 1;
            rhat += top;
            if rhat >> DIGIT_BITS != 0 {
                break;
            }
        }
        // u[j..=j + n] -= qhat * v
        let (mut carry, mut borrow) = (0 as Digit, 0 as Digit);
        for i in 0..n {
            let product = qhat * divisor.at(i) as TwoDigits + carry as TwoDigits;
            carry = (product >> DIGIT_BITS) as Digit;
            borrow = dividend.put(i + j, digit_sub(dividend.at(i + j), product as Digit, borrow));
        }
        let negative = dividend.put(j + n, digit_sub(dividend.at(j + n), carry, borrow));
        if negative != 0 {
            // The guess was one too big, which is rare: add the divisor back.
            qhat -= 1;
            let mut add_carry = 0;
            for i in 0..n {
                add_carry = dividend.put(i + j, digit_add(dividend.at(i + j), divisor.at(i), add_carry));
            }
            dividend.set(j + n, dividend.at(j + n).wrapping_add(add_carry));
        }
        if let Some(quotient) = &mut quotient {
            quotient.set(j, qhat as Digit);
        }
    }
    if let Some(mut remainder) = remainder {
        // The remainder is below the divisor, so it fits in `n` digits.
        super::right_shift(remainder.reborrow(), dividend.read().slice(0, n), shift);
    }
}

/// `z = x << shift` for `shift < DIGIT_BITS` into `x` digits, returning the bits shifted out.
fn shift_into(mut z: RWDigits<'_>, x: Digits<'_>, shift: usize) -> Digit {
    if shift == 0 {
        z.copy_from(x);
        return 0;
    }
    let mut carry = 0;
    for i in 0..x.len() {
        z.set(i, x.at(i) << shift | carry);
        carry = x.at(i) >> (DIGIT_BITS - shift);
    }
    carry
}

/// The work [`divide`] does, in digit operations.
pub fn divide_cost(x: Digits<'_>, y: Digits<'_>) -> u64 {
    let (x, y) = (x.normalize().len() as u64, y.normalize().len() as u64);
    x.saturating_sub(y).saturating_add(1).saturating_mul(y.max(1))
}
