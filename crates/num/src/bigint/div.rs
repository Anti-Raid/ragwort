//! Division.

use std::cmp::Ordering;

use super::{DIGIT_BITS, Digit, Digits, RWDigits, TwoDigits, compare, digit_add, digit_sub};

/// `q = x / y` for a single digit `y != 0`, returning `x % y`. `q` needs `x` digits, and
/// may be left out to only get the remainder.
pub fn divide_single(mut q: Option<RWDigits<'_>>, x: Digits<'_>, y: Digit) -> Digit {
    assert!(y != 0, "division by zero");
    let mut rem: Digit = 0;
    for i in (0..x.len()).rev() {
        let t = (rem as TwoDigits) << DIGIT_BITS | x[i] as TwoDigits;
        rem = (t % y as TwoDigits) as Digit;
        if let Some(q) = &mut q {
            q[i] = (t / y as TwoDigits) as Digit;
        }
    }
    if let Some(mut q) = q {
        q.offset(x.len()).clear();
    }
    rem
}

/// Scratch digits [`divide`] needs.
pub fn divide_scratch(x: Digits<'_>, y: Digits<'_>) -> usize {
    x.normalize().len() + 1 + y.normalize().len()
}

/// `q = x / y` and `r = x % y` for `y != 0`, either of which may be left out. `q` needs
/// `x - y + 1` digits and `r` needs `y`.
pub fn divide(
    q: Option<RWDigits<'_>>,
    r: Option<RWDigits<'_>>,
    x: Digits<'_>,
    y: Digits<'_>,
    scratch: RWDigits<'_>,
) {
    let (x, y) = (x.normalize(), y.normalize());
    assert!(!y.is_empty(), "division by zero");
    if compare(x, y) == Ordering::Less {
        if let Some(mut q) = q {
            q.clear();
        }
        if let Some(mut r) = r {
            r.copy_from(x);
        }
        return;
    }
    if y.len() == 1 {
        let rem = divide_single(q, x, y[0]);
        if let Some(mut r) = r {
            r.clear();
            r[0] = rem;
        }
        return;
    }
    divide_schoolbook(q, r, x, y, scratch);
}

/// Knuth's algorithm D, for normalized `x >= y` with at least two digits in `y`.
fn divide_schoolbook(
    mut q: Option<RWDigits<'_>>,
    r: Option<RWDigits<'_>>,
    x: Digits<'_>,
    y: Digits<'_>,
    scratch: RWDigits<'_>,
) {
    let (n, m) = (y.len(), x.len() - y.len());
    let (mut u, v) = scratch.split(x.len() + 1);
    let mut v = v.truncate(n);
    // Shift so the divisor's top bit is set, which keeps each quotient guess within 2.
    let s = y.msd().leading_zeros() as usize;
    shift_into(v.reborrow(), y, s);
    u[x.len()] = shift_into(u.reborrow(), x, s);
    let (top, next) = (v[n - 1] as TwoDigits, v[n - 2] as TwoDigits);
    if let Some(q) = &mut q {
        q.offset(m + 1).clear();
    }
    for j in (0..=m).rev() {
        let num = (u[j + n] as TwoDigits) << DIGIT_BITS | u[j + n - 1] as TwoDigits;
        let (mut qhat, mut rhat) = (num / top, num % top);
        while qhat >> DIGIT_BITS != 0 || qhat * next > (rhat << DIGIT_BITS | u[j + n - 2] as TwoDigits) {
            qhat -= 1;
            rhat += top;
            if rhat >> DIGIT_BITS != 0 {
                break;
            }
        }
        // u[j..=j + n] -= qhat * v
        let (mut carry, mut borrow) = (0 as Digit, 0 as Digit);
        for i in 0..n {
            let p = qhat * v[i] as TwoDigits + carry as TwoDigits;
            carry = (p >> DIGIT_BITS) as Digit;
            (u[i + j], borrow) = digit_sub(u[i + j], p as Digit, borrow);
        }
        let negative;
        (u[j + n], negative) = digit_sub(u[j + n], carry, borrow);
        if negative != 0 {
            // The guess was one too big, which is rare: add the divisor back.
            qhat -= 1;
            let mut c = 0;
            for i in 0..n {
                (u[i + j], c) = digit_add(u[i + j], v[i], c);
            }
            u[j + n] = u[j + n].wrapping_add(c);
        }
        if let Some(q) = &mut q {
            q[j] = qhat as Digit;
        }
    }
    if let Some(mut r) = r {
        // The remainder is below the divisor, so it fits in `n` digits.
        super::right_shift(r.reborrow(), u.read().slice(0, n), s);
    }
}

/// `z = x << s` for `s < DIGIT_BITS` into `x` digits, returning the bits shifted out.
fn shift_into(mut z: RWDigits<'_>, x: Digits<'_>, s: usize) -> Digit {
    if s == 0 {
        z.copy_from(x);
        return 0;
    }
    let mut carry = 0;
    for i in 0..x.len() {
        z[i] = x[i] << s | carry;
        carry = x[i] >> (DIGIT_BITS - s);
    }
    carry
}

/// The work [`divide`] does, in digit operations.
pub fn divide_cost(x: Digits<'_>, y: Digits<'_>) -> u64 {
    let (x, y) = (x.normalize().len() as u64, y.normalize().len() as u64);
    x.saturating_sub(y).saturating_add(1).saturating_mul(y.max(1))
}
