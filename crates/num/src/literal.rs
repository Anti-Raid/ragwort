//! Number literals, as R7RS writes them: integers and ratios in any radix, decimals, the
//! infinities and NaNs, and complex numbers of them as `a+bi`, `+bi`, `a+i` or `m@angle`, after
//! any of the `#x`, `#b`, `#o`, `#d`, `#e` and `#i` prefixes.

use std::cmp::Ordering;

use crate::{ComplexHost, complex, int, rational, real};

/// The most a decimal's exponent can scale it by when it's read exact.
const MAX_EXACT_SCALE: u64 = 100_000;

/// The number `token` writes, made by the host `nums`, or `None` if it doesn't write one.
pub fn parse<H: ComplexHost>(nums: &H, token: &str) -> Result<Option<H::Number>, H::Error> {
    parse_in(nums, token, 10)
}

/// The number `token` writes in `radix` unless a prefix says otherwise, as [`parse`] reads it.
pub fn parse_in<H: ComplexHost>(nums: &H, token: &str, radix: u32) -> Result<Option<H::Number>, H::Error> {
    let (mut prefixed, mut exact, mut rest) = (None, None, token);
    while let [b'#', prefix, ..] = rest.as_bytes() {
        match prefix.to_ascii_lowercase() {
            b'x' if prefixed.is_none() => prefixed = Some(16),
            b'b' if prefixed.is_none() => prefixed = Some(2),
            b'o' if prefixed.is_none() => prefixed = Some(8),
            b'd' if prefixed.is_none() => prefixed = Some(10),
            b'e' if exact.is_none() => exact = Some(true),
            b'i' if exact.is_none() => exact = Some(false),
            _ => return Ok(None),
        }
        rest = &rest[2..];
    }
    let Some(z) = complex_number(nums, rest, prefixed.unwrap_or(radix), exact)? else { return Ok(None) };
    let z = match exact {
        Some(true) => complex::exact(nums, z)?,
        Some(false) => complex::inexact(nums, z)?,
        None => z,
    };
    Ok(Some(z))
}

fn complex_number<H: ComplexHost>(nums: &H, text: &str, radix: u32, exact: Option<bool>) -> Result<Option<H::Number>, H::Error> {
    let real = |text: &str| number(nums, text, radix, exact);
    if let Some((magnitude, angle)) = text.split_once('@') {
        let (Some(modulus), Some(a)) = (real(magnitude)?, real(angle)?) else { return Ok(None) };
        return Ok(Some(complex::polar(nums, modulus, a)?));
    }
    let Some(body) = text.strip_suffix(['i', 'I']) else { return Ok(real(text)?.map(|x| nums.of_real(x))) };
    // The imaginary part starts at the last sign that isn't an exponent's.
    let bytes = body.as_bytes();
    let split = (1..bytes.len()).rev().find(|&index| matches!(bytes[index], b'+' | b'-') && !(radix == 10 && matches!(bytes[index - 1], b'e' | b'E')));
    let (re, im) = match split {
        Some(index) => (Some(&body[..index]), &body[index..]),
        None => (None, body),
    };
    if !im.starts_with(['+', '-']) {
        return Ok(None);
    }
    let im = match im {
        "+" => real::from_i64(nums, 1)?,
        "-" => real::from_i64(nums, -1)?,
        _ => match real(im)? {
            Some(im) => im,
            None => return Ok(None),
        },
    };
    let re = match re {
        Some(re) => match real(re)? {
            Some(re) => re,
            None => return Ok(None),
        },
        None => real::from_i64(nums, 0)?,
    };
    Ok(Some(complex::rectangular(nums, re, im)?))
}

fn number<H: ComplexHost>(nums: &H, text: &str, radix: u32, exact: Option<bool>) -> Result<Option<H::Real>, H::Error> {
    let (negative, body) = match text.as_bytes().first() {
        Some(b'+') => (false, &text[1..]),
        Some(b'-') => (true, &text[1..]),
        _ => (false, text),
    };
    let sign = if negative { -1.0 } else { 1.0 };
    if body.len() < text.len() && radix == 10 {
        match body.to_ascii_lowercase().as_str() {
            "inf.0" => return Ok(Some(nums.flonum(sign * f64::INFINITY)?)),
            "nan.0" => return Ok(Some(nums.flonum(f64::NAN)?)),
            _ => {}
        }
    }
    if let Some((num, den)) = body.split_once('/') {
        let num = int::parse(nums, num.as_bytes(), radix, negative)?;
        let den = int::parse(nums, den.as_bytes(), radix, false)?;
        let (Some(num), Some(den)) = (num, den) else { return Ok(None) };
        if int::sign(nums, den) == Ordering::Equal {
            return Ok(None);
        }
        return Ok(Some(nums.of_rational(rational::from_parts(nums, num, den)?)));
    }
    if let Some(integer) = int::parse(nums, body.as_bytes(), radix, negative)? {
        return Ok(Some(nums.of_rational(nums.of_int(integer))));
    }
    if radix == 10 { decimal(nums, negative, body, exact) } else { Ok(None) }
}

/// `digits [. digits] [e [sign] digits]`, with a digit before or after the point.
fn decimal<H: ComplexHost>(nums: &H, negative: bool, body: &str, exact: Option<bool>) -> Result<Option<H::Real>, H::Error> {
    let (mantissa, exponent) = match body.find(['e', 'E']) {
        Some(i) => (&body[..i], Some(&body[i + 1..])),
        None => (body, None),
    };
    let (whole, fraction) = mantissa.split_once('.').unwrap_or((mantissa, ""));
    let digits = |text: &str| text.bytes().all(|byte| byte.is_ascii_digit());
    if whole.len() + fraction.len() == 0 || !digits(whole) || !digits(fraction) {
        return Ok(None);
    }
    let exponent = match exponent {
        None => 0,
        Some(text) if !text.is_empty() && digits(text.strip_prefix(['+', '-']).unwrap_or(text)) => match text.parse::<i64>() {
            Ok(value) => value,
            Err(_) => return Ok(None),
        },
        Some(_) => return Ok(None),
    };
    if exact == Some(true) {
        let scale = exponent.saturating_sub(fraction.len() as i64);
        if scale.unsigned_abs() > MAX_EXACT_SCALE {
            return Ok(None);
        }
        let significand = int::parse(nums, format!("{whole}{fraction}").as_bytes(), 10, negative)?.expect("checked digits");
        let power = int::parse(nums, format!("1{}", "0".repeat(scale.unsigned_abs() as usize)).as_bytes(), 10, false)?.expect("digits");
        let x = if scale >= 0 { nums.of_int(int::mul(nums, significand, power)?) } else { rational::from_parts(nums, significand, power)? };
        return Ok(Some(nums.of_rational(x)));
    }
    let Ok(value) = body.parse::<f64>() else { return Ok(None) };
    Ok(Some(nums.flonum(if negative { -value } else { value })?))
}
