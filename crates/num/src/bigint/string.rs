//! Conversion to and from text in radixes 2 to 36. Both work a digit's worth of characters
//! at a time, which is quadratic: callers charge for it, and cap literal sizes.

use super::{DIGIT_BITS, Digit, Digits, RWDigits, TwoDigits, multiply_add_in_place};

const CHARS: &[u8; 36] = b"0123456789abcdefghijklmnopqrstuvwxyz";

/// The largest power of `radix` that fits in a digit, and its exponent.
pub fn chunk(radix: u32) -> (Digit, usize) {
    let (mut power, mut chars) = (radix as Digit, 1);
    while let Some(next) = power.checked_mul(radix as Digit) {
        power = next;
        chars += 1;
    }
    (power, chars)
}

fn bits_per_char_floor(radix: u32) -> usize {
    (u32::BITS - 1 - radix.leading_zeros()) as usize
}

/// Characters [`to_string`] may need, without a sign.
pub fn to_string_len(x: Digits<'_>, radix: u32) -> usize {
    x.bit_len().div_ceil(bits_per_char_floor(radix)).max(1)
}

/// Writes `x` in `radix` at the end of `out`, which needs [`to_string_len`] bytes, and returns
/// where it starts. `scratch` needs `x` digits.
pub fn to_string(x: Digits<'_>, radix: u32, mut scratch: RWDigits<'_>, out: &mut [u8]) -> usize {
    assert!((2..=36).contains(&radix), "radix out of range");
    let x = x.normalize();
    let mut at = out.len();
    if x.is_empty() {
        out[at - 1] = b'0';
        return at - 1;
    }
    let (power, chars) = chunk(radix);
    scratch.copy_from(x);
    let mut len = x.len();
    while len > 0 {
        let mut rem = divide_in_place(scratch.slice(0, len), power);
        while len > 0 && scratch[len - 1] == 0 {
            len -= 1;
        }
        // Every chunk but the most significant has all its characters, leading zeros too.
        let full = len > 0;
        let mut written = 0;
        while rem != 0 || (full && written < chars) {
            at -= 1;
            out[at] = CHARS[(rem % radix as Digit) as usize];
            rem /= radix as Digit;
            written += 1;
        }
    }
    at
}

fn divide_in_place(mut z: RWDigits<'_>, d: Digit) -> Digit {
    let mut rem: Digit = 0;
    for i in (0..z.len()).rev() {
        let t = (rem as TwoDigits) << DIGIT_BITS | z[i] as TwoDigits;
        z[i] = (t / d as TwoDigits) as Digit;
        rem = (t % d as TwoDigits) as Digit;
    }
    rem
}

/// Digits [`from_string`] may need for `chars` characters.
pub fn from_string_len(chars: usize, radix: u32) -> usize {
    let bits_per_char = bits_per_char_floor(radix) + usize::from(!radix.is_power_of_two());
    (chars * bits_per_char).div_ceil(DIGIT_BITS).max(1)
}

fn char_value(c: u8) -> Option<u32> {
    match c {
        b'0'..=b'9' => Some((c - b'0') as u32),
        b'a'..=b'z' => Some((c - b'a') as u32 + 10),
        b'A'..=b'Z' => Some((c - b'A') as u32 + 10),
        _ => None,
    }
}

/// Reads unsigned digits in `radix` into `z`, which needs [`from_string_len`] digits. Returns
/// `None` if a character isn't a digit in the radix.
pub fn from_string(mut z: RWDigits<'_>, text: &[u8], radix: u32) -> Option<()> {
    assert!((2..=36).contains(&radix), "radix out of range");
    z.clear();
    let (_, chars) = chunk(radix);
    let mut len = 0;
    for part in text.chunks(chars) {
        let (mut value, mut scale) = (0 as Digit, 1 as Digit);
        for &c in part {
            let d = char_value(c).filter(|&d| d < radix)?;
            value = value * radix as Digit + d as Digit;
            scale *= radix as Digit;
        }
        let carry = multiply_add_in_place(z.slice(0, len), scale, value);
        if carry != 0 {
            z[len] = carry;
            len += 1;
        }
    }
    Some(())
}
