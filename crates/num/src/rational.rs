//! Exact rationals with Racket's semantics: integers, and ratios in lowest terms whose
//! denominator is above one. A ratio is never an integer, so the two never compare equal.

use std::cmp::Ordering;
use std::hash::Hasher;

use crate::int::{self, Host, NumError, Rounding};

/// A rational as the host holds it.
#[derive(Clone, Copy, Debug)]
pub enum RationalView<I> {
    Integer(I),
    /// In lowest terms, with `den > 1`.
    Ratio { num: I, den: I },
}

/// A host that also holds ratios.
pub trait RationalHost: Host {
    /// An integer or a ratio.
    type Rational: Copy;

    fn rational_view(&self, x: Self::Rational) -> RationalView<Self::Int>;

    fn of_int(&self, x: Self::Int) -> Self::Rational;

    /// `num / den`, already reduced by the library: `den > 1` and they share no factor.
    fn ratio(&self, num: Self::Int, den: Self::Int) -> Result<Self::Rational, Self::Error>;
}

type Res<H> = Result<<H as RationalHost>::Rational, <H as Host>::Error>;
type IntRes<H> = Result<<H as Host>::Int, <H as Host>::Error>;

fn is_one<H: Host>(h: &H, x: H::Int) -> bool {
    int::to_i64(h, x) == Some(1)
}

fn is_zero<H: Host>(h: &H, x: H::Int) -> bool {
    int::sign(h, x) == Ordering::Equal
}

/// `x / divisor` for a `divisor` known to divide it.
fn exact_div<H: Host>(h: &H, x: H::Int, divisor: H::Int) -> IntRes<H> {
    if is_one(h, divisor) { Ok(x) } else { int::quotient(h, x, divisor) }
}

/// From a numerator and positive denominator with no common factor.
fn reduced<H: RationalHost>(h: &H, num: H::Int, den: H::Int) -> Res<H> {
    if is_one(h, den) || is_zero(h, num) { Ok(h.of_int(num)) } else { h.ratio(num, den) }
}

/// `num / den` in lowest terms, or an error if `den` is zero.
pub fn from_parts<H: RationalHost>(h: &H, num: H::Int, den: H::Int) -> Res<H> {
    let (num, den) = match int::sign(h, den) {
        Ordering::Equal => return Err(NumError::DivideByZero.into()),
        Ordering::Less => (int::neg(h, num)?, int::neg(h, den)?),
        Ordering::Greater => (num, den),
    };
    let divisor = int::gcd(h, num, den)?;
    reduced(h, exact_div(h, num, divisor)?, exact_div(h, den, divisor)?)
}

/// Numerator and denominator, with 1 for integers.
fn parts<H: RationalHost>(h: &H, x: H::Rational) -> Result<(H::Int, H::Int), H::Error> {
    match h.rational_view(x) {
        RationalView::Integer(n) => Ok((n, int::from_i64(h, 1)?)),
        RationalView::Ratio { num, den } => Ok((num, den)),
    }
}

pub fn numerator<H: RationalHost>(h: &H, x: H::Rational) -> H::Int {
    match h.rational_view(x) {
        RationalView::Integer(n) | RationalView::Ratio { num: n, .. } => n,
    }
}

pub fn denominator<H: RationalHost>(h: &H, x: H::Rational) -> IntRes<H> {
    match h.rational_view(x) {
        RationalView::Integer(_) => int::from_i64(h, 1),
        RationalView::Ratio { den, .. } => Ok(den),
    }
}

pub fn is_integer<H: RationalHost>(h: &H, x: H::Rational) -> bool {
    matches!(h.rational_view(x), RationalView::Integer(_))
}

/// How `x` compares to zero.
pub fn sign<H: RationalHost>(h: &H, x: H::Rational) -> Ordering {
    int::sign(h, numerator(h, x))
}

pub fn compare<H: RationalHost>(h: &H, x: H::Rational, y: H::Rational) -> Result<Ordering, H::Error> {
    if let (RationalView::Integer(a), RationalView::Integer(b)) = (h.rational_view(x), h.rational_view(y)) {
        return Ok(int::compare(h, a, b));
    }
    let (sx, sy) = (sign(h, x), sign(h, y));
    if sx != sy {
        return Ok(sx.cmp(&sy));
    }
    // Same sign: a/b against c/d is ad against cb, as denominators are positive.
    let ((a, b), (other_num, other_den)) = (parts(h, x)?, parts(h, y)?);
    Ok(int::compare(h, int::mul(h, a, other_den)?, int::mul(h, other_num, b)?))
}

/// Whether `x` and `y` are the same rational. Lowest terms make that a comparison of parts.
pub fn eqv<H: RationalHost>(h: &H, x: H::Rational, y: H::Rational) -> bool {
    let same = |a, b| int::compare(h, a, b) == Ordering::Equal;
    match (h.rational_view(x), h.rational_view(y)) {
        (RationalView::Integer(a), RationalView::Integer(b)) => same(a, b),
        (RationalView::Ratio { num: a, den: b }, RationalView::Ratio { num: other_num, den: other_den }) => same(a, other_num) && same(b, other_den),
        _ => false,
    }
}

/// Feeds `x`'s value to `state`. Integers hash as [`int::hash`] does.
pub fn hash<H: RationalHost, S: Hasher>(h: &H, x: H::Rational, state: &mut S) {
    match h.rational_view(x) {
        RationalView::Integer(n) => int::hash(h, n, state),
        RationalView::Ratio { num, den } => {
            int::hash(h, num, state);
            int::hash(h, den, state);
        }
    }
}

pub fn neg<H: RationalHost>(h: &H, x: H::Rational) -> Res<H> {
    match h.rational_view(x) {
        RationalView::Integer(n) => Ok(h.of_int(int::neg(h, n)?)),
        RationalView::Ratio { num, den } => h.ratio(int::neg(h, num)?, den),
    }
}

pub fn abs<H: RationalHost>(h: &H, x: H::Rational) -> Res<H> {
    if sign(h, x) == Ordering::Less { neg(h, x) } else { Ok(x) }
}

pub fn add<H: RationalHost>(h: &H, x: H::Rational, y: H::Rational) -> Res<H> {
    if let (RationalView::Integer(a), RationalView::Integer(b)) = (h.rational_view(x), h.rational_view(y)) {
        return Ok(h.of_int(int::add(h, a, b)?));
    }
    let ((a, b), (other_num, other_den)) = (parts(h, x)?, parts(h, y)?);
    add_parts(h, a, b, other_num, other_den)
}

pub fn sub<H: RationalHost>(h: &H, x: H::Rational, y: H::Rational) -> Res<H> {
    if let (RationalView::Integer(a), RationalView::Integer(b)) = (h.rational_view(x), h.rational_view(y)) {
        return Ok(h.of_int(int::sub(h, a, b)?));
    }
    let ((a, b), (other_num, other_den)) = (parts(h, x)?, parts(h, y)?);
    add_parts(h, a, b, int::neg(h, other_num)?, other_den)
}

/// `a/b + other_num/other_den` for reduced fractions, dividing out what the denominators share before
/// multiplying, as in Knuth 4.5.1.
fn add_parts<H: RationalHost>(h: &H, a: H::Int, b: H::Int, other_num: H::Int, other_den: H::Int) -> Res<H> {
    let common = int::gcd(h, b, other_den)?;
    if is_one(h, common) {
        // Nothing shared, so (ad + cb) / bd is already in lowest terms.
        let num = int::add(h, int::mul(h, a, other_den)?, int::mul(h, other_num, b)?)?;
        return reduced(h, num, int::mul(h, b, other_den)?);
    }
    let (b1, d1) = (int::quotient(h, b, common)?, int::quotient(h, other_den, common)?);
    let sum = int::add(h, int::mul(h, a, d1)?, int::mul(h, other_num, b1)?)?;
    // Only factors of g can be left in common between t and b1 * d.
    let g2 = int::gcd(h, sum, common)?;
    reduced(h, exact_div(h, sum, g2)?, int::mul(h, b1, exact_div(h, other_den, g2)?)?)
}

pub fn mul<H: RationalHost>(h: &H, x: H::Rational, y: H::Rational) -> Res<H> {
    if let (RationalView::Integer(a), RationalView::Integer(b)) = (h.rational_view(x), h.rational_view(y)) {
        return Ok(h.of_int(int::mul(h, a, b)?));
    }
    let ((a, b), (other_num, other_den)) = (parts(h, x)?, parts(h, y)?);
    mul_parts(h, a, b, other_num, other_den)
}

pub fn div<H: RationalHost>(h: &H, x: H::Rational, y: H::Rational) -> Res<H> {
    let ((a, b), (other_num, other_den)) = (parts(h, x)?, parts(h, y)?);
    // a/b ÷ c/d is a/b × d/c, with the sign of c moved to the top.
    match int::sign(h, other_num) {
        Ordering::Equal => Err(NumError::DivideByZero.into()),
        Ordering::Less => mul_parts(h, a, b, int::neg(h, other_den)?, int::neg(h, other_num)?),
        Ordering::Greater => mul_parts(h, a, b, other_den, other_num),
    }
}

/// `a/b × other_num/other_den` for reduced fractions, cancelling across before multiplying.
fn mul_parts<H: RationalHost>(h: &H, a: H::Int, b: H::Int, other_num: H::Int, other_den: H::Int) -> Res<H> {
    let (g1, g2) = (int::gcd(h, a, other_den)?, int::gcd(h, other_num, b)?);
    let num = int::mul(h, exact_div(h, a, g1)?, exact_div(h, other_num, g2)?)?;
    let den = int::mul(h, exact_div(h, b, g2)?, exact_div(h, other_den, g1)?)?;
    reduced(h, num, den)
}

/// `x^exponent`. Negative powers of zero divide by zero.
pub fn expt<H: RationalHost>(h: &H, x: H::Rational, exponent: i64) -> Res<H> {
    let (num, den) = parts(h, x)?;
    let n = exponent.unsigned_abs();
    let (num, den) = (int::expt(h, num, n)?, int::expt(h, den, n)?);
    if exponent >= 0 {
        return reduced(h, num, den);
    }
    match int::sign(h, num) {
        Ordering::Equal => Err(NumError::DivideByZero.into()),
        Ordering::Less => reduced(h, int::neg(h, den)?, int::neg(h, num)?),
        Ordering::Greater => reduced(h, den, num),
    }
}

/// Rounds to an integer: `floor`, `ceiling` and `truncate`, and `round`, which takes ties
/// to even.
pub fn round<H: RationalHost>(h: &H, x: H::Rational, mode: Round) -> IntRes<H> {
    let (num, den) = match h.rational_view(x) {
        RationalView::Integer(n) => return Ok(n),
        RationalView::Ratio { num, den } => (num, den),
    };
    match mode {
        Round::Floor => int::floor_quotient(h, num, den),
        Round::Ceiling => int::neg(h, int::floor_quotient(h, int::neg(h, num)?, den)?),
        Round::Truncate => int::quotient(h, num, den),
        Round::Nearest => {
            let (quotient, remainder) = int::divide(h, num, den, Rounding::Floor, true, true)?;
            let (quotient, remainder) = (quotient.expect("asked for the quotient"), remainder.expect("asked for the remainder"));
            // 0 <= r < den, and the fraction left over is r / den.
            let twice = int::arithmetic_shift(h, remainder, 1)?;
            let up = match int::compare(h, twice, den) {
                Ordering::Less => false,
                Ordering::Greater => true,
                Ordering::Equal => !int::is_even(h, quotient),
            };
            if up { int::add(h, quotient, int::from_i64(h, 1)?) } else { Ok(quotient) }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Round {
    Floor,
    Ceiling,
    Truncate,
    /// Ties to even.
    Nearest,
}

/// The nearest double, ties to even, as one rounding of the exact value.
pub fn to_f64<H: RationalHost>(h: &H, x: H::Rational) -> Result<f64, H::Error> {
    let (num, den) = match h.rational_view(x) {
        RationalView::Integer(n) => return Ok(int::to_f64(h, n)),
        RationalView::Ratio { num, den } => (num, den),
    };
    // Both exact as doubles, so one division rounds once.
    if let (Some(small_num), Some(small_den)) = (int::to_i64(h, num), int::to_i64(h, den))
        && small_num.unsigned_abs() <= 1 << 53
        && small_den <= 1 << 53
    {
        return Ok(small_num as f64 / small_den as f64);
    }
    let negative = int::sign(h, num) == Ordering::Less;
    let num = int::abs(h, num)?;
    let value = ratio_to_f64(h, num, den)?;
    Ok(if negative { -value } else { value })
}

/// `num / den` for positive `num` and `den`.
fn ratio_to_f64<H: Host>(h: &H, num: H::Int, den: H::Int) -> Result<f64, H::Error> {
    // n / d is in [2^(bn - bd - 1), 2^(bn - bd + 1)), so scaling by 2^shift puts the quotient
    // in [2^54, 2^56): enough bits for 53, a rounding bit and one to spare.
    let (bn, bd) = (int::integer_length(h, num) as i64, int::integer_length(h, den) as i64);
    let shift = 55 - (bn - bd);
    // Bits shifted or divided away only matter as one sticky bit below the rounding bit.
    let (quotient, remainder, lost) = if shift >= 0 {
        let (quotient, remainder) = int::quotient_remainder(h, int::arithmetic_shift(h, num, shift)?, den)?;
        (quotient, remainder, false)
    } else {
        let shifted = int::arithmetic_shift(h, num, shift)?;
        let lost = int::compare(h, int::arithmetic_shift(h, shifted, -shift)?, num) != Ordering::Equal;
        let (quotient, remainder) = int::quotient_remainder(h, shifted, den)?;
        (quotient, remainder, lost)
    };
    let sticky = lost || !is_zero(h, remainder);
    let quotient = int::to_i64(h, quotient).expect("the quotient has at most 56 bits") as u64;
    let len = 64 - quotient.leading_zeros() as i64;
    // The value is in [2^e, 2^(e + 1)).
    let exponent = len - 1 - shift;
    if exponent > 1023 {
        return Ok(f64::INFINITY);
    }
    // Below the normal range, fewer bits are left for the significand.
    let precision = if exponent >= -1022 { 53 } else { exponent + 1075 };
    let drop = len - precision;
    if drop > len {
        return Ok(0.0);
    }
    let kept = quotient >> drop;
    let half = (quotient >> (drop - 1)) & 1 == 1;
    let below = quotient & ((1 << (drop - 1)) - 1) != 0 || sticky;
    let kept = kept + (half && (below || kept & 1 == 1)) as u64;
    Ok(scale(kept as f64, exponent + 1 - precision))
}

/// `x * 2^exponent` for a result that's representable, or overflows to infinity.
fn scale(mut x: f64, mut exponent: i64) -> f64 {
    if exponent < -1022 {
        x *= f64::from_bits(1 << 52);
        exponent += 1022;
    }
    x * f64::from_bits(((exponent + 1023) as u64) << 52)
}

/// A finite double's exact value.
pub fn from_f64<H: RationalHost>(h: &H, value: f64) -> Res<H> {
    if !value.is_finite() {
        return Err(NumError::NoExactValue.into());
    }
    if value.fract() == 0.0 {
        return Ok(h.of_int(int::from_integral_f64(h, value)?));
    }
    let bits = value.to_bits();
    let (exponent, fraction) = ((bits >> 52) & 0x7ff, bits & ((1 << 52) - 1));
    let (mut significand, mut shift) = match exponent {
        0 => (fraction, -1074),
        _ => (fraction | 1 << 52, exponent as i64 - 1075),
    };
    // Not an integer, so e < 0 and the denominator is a power of two above one.
    let tz = (significand.trailing_zeros() as i64).min(-shift);
    significand >>= tz;
    shift += tz;
    let num = int::from_i64(h, if value < 0.0 { -(significand as i64) } else { significand as i64 })?;
    let den = int::arithmetic_shift(h, int::from_i64(h, 1)?, -shift)?;
    h.ratio(num, den)
}

/// `x` in `radix`, as `num/den` for ratios.
pub fn to_string<H: RationalHost>(h: &H, x: H::Rational, radix: u32) -> Result<String, H::Error> {
    match h.rational_view(x) {
        RationalView::Integer(n) => int::to_string(h, n, radix),
        RationalView::Ratio { num, den } => Ok(format!("{}/{}", int::to_string(h, num, radix)?, int::to_string(h, den, radix)?)),
    }
}
