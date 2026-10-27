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

/// `x / g` for a `g` known to divide it.
fn exact_div<H: Host>(h: &H, x: H::Int, g: H::Int) -> IntRes<H> {
    if is_one(h, g) { Ok(x) } else { int::quotient(h, x, g) }
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
    let g = int::gcd(h, num, den)?;
    reduced(h, exact_div(h, num, g)?, exact_div(h, den, g)?)
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
    let ((a, b), (c, d)) = (parts(h, x)?, parts(h, y)?);
    Ok(int::compare(h, int::mul(h, a, d)?, int::mul(h, c, b)?))
}

/// Whether `x` and `y` are the same rational. Lowest terms make that a comparison of parts.
pub fn eqv<H: RationalHost>(h: &H, x: H::Rational, y: H::Rational) -> bool {
    let same = |a, b| int::compare(h, a, b) == Ordering::Equal;
    match (h.rational_view(x), h.rational_view(y)) {
        (RationalView::Integer(a), RationalView::Integer(b)) => same(a, b),
        (RationalView::Ratio { num: a, den: b }, RationalView::Ratio { num: c, den: d }) => same(a, c) && same(b, d),
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
    let ((a, b), (c, d)) = (parts(h, x)?, parts(h, y)?);
    add_parts(h, a, b, c, d)
}

pub fn sub<H: RationalHost>(h: &H, x: H::Rational, y: H::Rational) -> Res<H> {
    if let (RationalView::Integer(a), RationalView::Integer(b)) = (h.rational_view(x), h.rational_view(y)) {
        return Ok(h.of_int(int::sub(h, a, b)?));
    }
    let ((a, b), (c, d)) = (parts(h, x)?, parts(h, y)?);
    add_parts(h, a, b, int::neg(h, c)?, d)
}

/// `a/b + c/d` for reduced fractions, dividing out what the denominators share before
/// multiplying, as in Knuth 4.5.1.
fn add_parts<H: RationalHost>(h: &H, a: H::Int, b: H::Int, c: H::Int, d: H::Int) -> Res<H> {
    let g = int::gcd(h, b, d)?;
    if is_one(h, g) {
        // Nothing shared, so (ad + cb) / bd is already in lowest terms.
        let num = int::add(h, int::mul(h, a, d)?, int::mul(h, c, b)?)?;
        return reduced(h, num, int::mul(h, b, d)?);
    }
    let (b1, d1) = (int::quotient(h, b, g)?, int::quotient(h, d, g)?);
    let t = int::add(h, int::mul(h, a, d1)?, int::mul(h, c, b1)?)?;
    // Only factors of g can be left in common between t and b1 * d.
    let g2 = int::gcd(h, t, g)?;
    reduced(h, exact_div(h, t, g2)?, int::mul(h, b1, exact_div(h, d, g2)?)?)
}

pub fn mul<H: RationalHost>(h: &H, x: H::Rational, y: H::Rational) -> Res<H> {
    if let (RationalView::Integer(a), RationalView::Integer(b)) = (h.rational_view(x), h.rational_view(y)) {
        return Ok(h.of_int(int::mul(h, a, b)?));
    }
    let ((a, b), (c, d)) = (parts(h, x)?, parts(h, y)?);
    mul_parts(h, a, b, c, d)
}

pub fn div<H: RationalHost>(h: &H, x: H::Rational, y: H::Rational) -> Res<H> {
    let ((a, b), (c, d)) = (parts(h, x)?, parts(h, y)?);
    // a/b ÷ c/d is a/b × d/c, with the sign of c moved to the top.
    match int::sign(h, c) {
        Ordering::Equal => Err(NumError::DivideByZero.into()),
        Ordering::Less => mul_parts(h, a, b, int::neg(h, d)?, int::neg(h, c)?),
        Ordering::Greater => mul_parts(h, a, b, d, c),
    }
}

/// `a/b × c/d` for reduced fractions, cancelling across before multiplying.
fn mul_parts<H: RationalHost>(h: &H, a: H::Int, b: H::Int, c: H::Int, d: H::Int) -> Res<H> {
    let (g1, g2) = (int::gcd(h, a, d)?, int::gcd(h, c, b)?);
    let num = int::mul(h, exact_div(h, a, g1)?, exact_div(h, c, g2)?)?;
    let den = int::mul(h, exact_div(h, b, g2)?, exact_div(h, d, g1)?)?;
    reduced(h, num, den)
}

/// `x^e`. Negative powers of zero divide by zero.
pub fn expt<H: RationalHost>(h: &H, x: H::Rational, e: i64) -> Res<H> {
    let (num, den) = parts(h, x)?;
    let n = e.unsigned_abs();
    let (num, den) = (int::expt(h, num, n)?, int::expt(h, den, n)?);
    if e >= 0 {
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
            let (q, r) = int::divide(h, num, den, Rounding::Floor, true, true)?;
            let (q, r) = (q.expect("asked for the quotient"), r.expect("asked for the remainder"));
            // 0 <= r < den, and the fraction left over is r / den.
            let twice = int::arithmetic_shift(h, r, 1)?;
            let up = match int::compare(h, twice, den) {
                Ordering::Less => false,
                Ordering::Greater => true,
                Ordering::Equal => !int::is_even(h, q),
            };
            if up { int::add(h, q, int::from_i64(h, 1)?) } else { Ok(q) }
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
    if let (Some(n), Some(d)) = (int::to_i64(h, num), int::to_i64(h, den))
        && n.unsigned_abs() <= 1 << 53
        && d <= 1 << 53
    {
        return Ok(n as f64 / d as f64);
    }
    let negative = int::sign(h, num) == Ordering::Less;
    let num = int::abs(h, num)?;
    let f = ratio_to_f64(h, num, den)?;
    Ok(if negative { -f } else { f })
}

/// `n / d` for positive `n` and `d`.
fn ratio_to_f64<H: Host>(h: &H, n: H::Int, d: H::Int) -> Result<f64, H::Error> {
    // n / d is in [2^(bn - bd - 1), 2^(bn - bd + 1)), so scaling by 2^shift puts the quotient
    // in [2^54, 2^56): enough bits for 53, a rounding bit and one to spare.
    let (bn, bd) = (int::integer_length(h, n) as i64, int::integer_length(h, d) as i64);
    let shift = 55 - (bn - bd);
    // Bits shifted or divided away only matter as one sticky bit below the rounding bit.
    let (q, r, lost) = if shift >= 0 {
        let (q, r) = int::quotient_remainder(h, int::arithmetic_shift(h, n, shift)?, d)?;
        (q, r, false)
    } else {
        let m = int::arithmetic_shift(h, n, shift)?;
        let lost = int::compare(h, int::arithmetic_shift(h, m, -shift)?, n) != Ordering::Equal;
        let (q, r) = int::quotient_remainder(h, m, d)?;
        (q, r, lost)
    };
    let sticky = lost || !is_zero(h, r);
    let q = int::to_i64(h, q).expect("the quotient has at most 56 bits") as u64;
    let len = 64 - q.leading_zeros() as i64;
    // The value is in [2^e, 2^(e + 1)).
    let e = len - 1 - shift;
    if e > 1023 {
        return Ok(f64::INFINITY);
    }
    // Below the normal range, fewer bits are left for the significand.
    let precision = if e >= -1022 { 53 } else { e + 1075 };
    let drop = len - precision;
    if drop > len {
        return Ok(0.0);
    }
    let kept = q >> drop;
    let half = (q >> (drop - 1)) & 1 == 1;
    let below = q & ((1 << (drop - 1)) - 1) != 0 || sticky;
    let kept = kept + (half && (below || kept & 1 == 1)) as u64;
    Ok(scale(kept as f64, e + 1 - precision))
}

/// `x * 2^k` for a result that's representable, or overflows to infinity.
fn scale(mut x: f64, mut k: i64) -> f64 {
    if k < -1022 {
        x *= f64::from_bits(1 << 52);
        k += 1022;
    }
    x * f64::from_bits(((k + 1023) as u64) << 52)
}

/// A finite double's exact value.
pub fn from_f64<H: RationalHost>(h: &H, f: f64) -> Res<H> {
    if !f.is_finite() {
        return Err(NumError::NoExactValue.into());
    }
    if f.fract() == 0.0 {
        return Ok(h.of_int(int::from_integral_f64(h, f)?));
    }
    let bits = f.to_bits();
    let (exponent, fraction) = ((bits >> 52) & 0x7ff, bits & ((1 << 52) - 1));
    let (mut m, mut e) = match exponent {
        0 => (fraction, -1074),
        _ => (fraction | 1 << 52, exponent as i64 - 1075),
    };
    // Not an integer, so e < 0 and the denominator is a power of two above one.
    let tz = (m.trailing_zeros() as i64).min(-e);
    m >>= tz;
    e += tz;
    let num = int::from_i64(h, if f < 0.0 { -(m as i64) } else { m as i64 })?;
    let den = int::arithmetic_shift(h, int::from_i64(h, 1)?, -e)?;
    h.ratio(num, den)
}

/// `x` in `radix`, as `num/den` for ratios.
pub fn to_string<H: RationalHost>(h: &H, x: H::Rational, radix: u32) -> Result<String, H::Error> {
    match h.rational_view(x) {
        RationalView::Integer(n) => int::to_string(h, n, radix),
        RationalView::Ratio { num, den } => Ok(format!("{}/{}", int::to_string(h, num, radix)?, int::to_string(h, den, radix)?)),
    }
}
