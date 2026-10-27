//! Bitwise operations with two's complement semantics on sign and magnitude, without
//! converting: a negative `-y` is `!(y - 1)`, and the borrow of `y - 1` runs along with the
//! loop. Each function names the signs of `x` and `y`; callers put the positive one first.
//! The `_len` functions give how many digits `z` needs.

use super::{Digits, RWDigits, add_digit, digit_sub};

pub fn and_pos_pos(mut z: RWDigits<'_>, x: Digits<'_>, y: Digits<'_>) {
    let pairs = x.len().min(y.len());
    for i in 0..pairs {
        z[i] = x[i] & y[i];
    }
    z.offset(pairs).clear();
}

pub fn and_pos_pos_len(x: Digits<'_>, y: Digits<'_>) -> usize {
    x.len().min(y.len())
}

/// `-x & -y == -(((x - 1) | (y - 1)) + 1)`
pub fn and_neg_neg(mut z: RWDigits<'_>, x: Digits<'_>, y: Digits<'_>) {
    let (mut xb, mut yb) = (1, 1);
    let n = x.len().max(y.len());
    for i in 0..n {
        let (xd, yd);
        (xd, xb) = digit_sub(x.get(i), 0, xb);
        (yd, yb) = digit_sub(y.get(i), 0, yb);
        z[i] = if i < x.len() { xd } else { 0 } | if i < y.len() { yd } else { 0 };
    }
    z.offset(n).clear();
    add_digit(z, 1);
}

pub fn and_neg_neg_len(x: Digits<'_>, y: Digits<'_>) -> usize {
    x.len().max(y.len()) + 1
}

/// `x & -y == x & !(y - 1)`
pub fn and_pos_neg(mut z: RWDigits<'_>, x: Digits<'_>, y: Digits<'_>) {
    let mut borrow = 1;
    for i in 0..x.len() {
        let yd;
        (yd, borrow) = digit_sub(y.get(i), 0, borrow);
        z[i] = x[i] & if i < y.len() { !yd } else { !0 };
    }
    z.offset(x.len()).clear();
}

pub fn and_pos_neg_len(x: Digits<'_>, _y: Digits<'_>) -> usize {
    x.len()
}

pub fn or_pos_pos(mut z: RWDigits<'_>, x: Digits<'_>, y: Digits<'_>) {
    let n = x.len().max(y.len());
    for i in 0..n {
        z[i] = x.get(i) | y.get(i);
    }
    z.offset(n).clear();
}

pub fn or_pos_pos_len(x: Digits<'_>, y: Digits<'_>) -> usize {
    x.len().max(y.len())
}

/// `-x | -y == -(((x - 1) & (y - 1)) + 1)`
pub fn or_neg_neg(mut z: RWDigits<'_>, x: Digits<'_>, y: Digits<'_>) {
    let (mut xb, mut yb) = (1, 1);
    let pairs = x.len().min(y.len());
    for i in 0..pairs {
        let (xd, yd);
        (xd, xb) = digit_sub(x[i], 0, xb);
        (yd, yb) = digit_sub(y[i], 0, yb);
        z[i] = xd & yd;
    }
    z.offset(pairs).clear();
    add_digit(z, 1);
}

pub fn or_neg_neg_len(x: Digits<'_>, y: Digits<'_>) -> usize {
    x.len().min(y.len()) + 1
}

/// `x | -y == -(((y - 1) & !x) + 1)`
pub fn or_pos_neg(mut z: RWDigits<'_>, x: Digits<'_>, y: Digits<'_>) {
    let mut borrow = 1;
    for i in 0..y.len() {
        let yd;
        (yd, borrow) = digit_sub(y[i], 0, borrow);
        z[i] = yd & !x.get(i);
    }
    z.offset(y.len()).clear();
    add_digit(z, 1);
}

pub fn or_pos_neg_len(_x: Digits<'_>, y: Digits<'_>) -> usize {
    y.len() + 1
}

pub fn xor_pos_pos(mut z: RWDigits<'_>, x: Digits<'_>, y: Digits<'_>) {
    let n = x.len().max(y.len());
    for i in 0..n {
        z[i] = x.get(i) ^ y.get(i);
    }
    z.offset(n).clear();
}

pub fn xor_pos_pos_len(x: Digits<'_>, y: Digits<'_>) -> usize {
    x.len().max(y.len())
}

/// `-x ^ -y == (x - 1) ^ (y - 1)`
pub fn xor_neg_neg(mut z: RWDigits<'_>, x: Digits<'_>, y: Digits<'_>) {
    let (mut xb, mut yb) = (1, 1);
    let n = x.len().max(y.len());
    for i in 0..n {
        let (xd, yd);
        (xd, xb) = digit_sub(x.get(i), 0, xb);
        (yd, yb) = digit_sub(y.get(i), 0, yb);
        z[i] = if i < x.len() { xd } else { 0 } ^ if i < y.len() { yd } else { 0 };
    }
    z.offset(n).clear();
}

pub fn xor_neg_neg_len(x: Digits<'_>, y: Digits<'_>) -> usize {
    x.len().max(y.len())
}

/// `x ^ -y == -((x ^ (y - 1)) + 1)`
pub fn xor_pos_neg(mut z: RWDigits<'_>, x: Digits<'_>, y: Digits<'_>) {
    let mut borrow = 1;
    let n = x.len().max(y.len());
    for i in 0..n {
        let yd;
        (yd, borrow) = digit_sub(y.get(i), 0, borrow);
        z[i] = x.get(i) ^ if i < y.len() { yd } else { 0 };
    }
    z.offset(n).clear();
    add_digit(z, 1);
}

pub fn xor_pos_neg_len(x: Digits<'_>, y: Digits<'_>) -> usize {
    x.len().max(y.len()) + 1
}
