//! Conversion to and from text in radixes 2 to 36. Both directions process one digit's worth of characters
//! at a time, which takes quadratic time. Callers charge for the work and cap the size of literals.

use super::{DIGIT_BITS, Digit, Digits, RWDigits, TwoDigits, multiply_add_in_place};

const CHARS: &[u8; 36] = b"0123456789abcdefghijklmnopqrstuvwxyz";

/// Returns the largest power of `radix` that fits in a digit, and the exponent of that power.
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

/// Returns an upper bound on the number of characters that [`to_string`] writes, not counting a sign.
pub fn to_string_len(x: Digits<'_>, radix: u32) -> usize {
    x.bit_len().div_ceil(bits_per_char_floor(radix)).max(1)
}

/// Writes `x` in `radix` at the end of `out` and returns the index where the text starts. `out` needs [`to_string_len`] bytes,
/// and `scratch` needs as many digits as `x`.
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
        while len > 0 && scratch.at(len - 1) == 0 {
            len -= 1;
        }
        // Every chunk except the most significant is written with all `chars` characters, including leading zeros.
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

fn divide_in_place(mut z: RWDigits<'_>, divisor: Digit) -> Digit {
    let mut rem: Digit = 0;
    for i in (0..z.len()).rev() {
        let num = (rem as TwoDigits) << DIGIT_BITS | z.at(i) as TwoDigits;
        z.set(i, (num / divisor as TwoDigits) as Digit);
        rem = (num % divisor as TwoDigits) as Digit;
    }
    rem
}

/// Returns an upper bound on the number of digits that [`from_string`] needs for `chars` characters.
pub fn from_string_len(chars: usize, radix: u32) -> usize {
    let bits_per_char = bits_per_char_floor(radix) + usize::from(!radix.is_power_of_two());
    (chars * bits_per_char).div_ceil(DIGIT_BITS).max(1)
}

fn char_value(character: u8) -> Option<u32> {
    match character {
        b'0'..=b'9' => Some((character - b'0') as u32),
        b'a'..=b'z' => Some((character - b'a') as u32 + 10),
        b'A'..=b'Z' => Some((character - b'A') as u32 + 10),
        _ => None,
    }
}

/// Parses `text` as unsigned digits in `radix` into `z`, which needs [`from_string_len`] digits. Returns
/// `None` if a character is not a digit in `radix`.
pub fn from_string(mut z: RWDigits<'_>, text: &[u8], radix: u32) -> Option<()> {
    assert!((2..=36).contains(&radix), "radix out of range");
    z.clear();
    let (_, chars) = chunk(radix);
    let mut len = 0;
    for part in text.chunks(chars) {
        let (mut value, mut scale) = (0 as Digit, 1 as Digit);
        for &character in part {
            let digit = char_value(character).filter(|&digit| digit < radix)?;
            value = value * radix as Digit + digit as Digit;
            scale *= radix as Digit;
        }
        let carry = multiply_add_in_place(z.slice(0, len), scale, value);
        if carry != 0 {
            z.set(len, carry);
            len += 1;
        }
    }
    Some(())
}
