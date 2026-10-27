//! The whole tower with Racket's semantics: reals, and complex numbers whose parts are both
//! exact, both flonums, or an exact zero and a flonum, as in `(sqrt -4.0)`, which is `+2.0i`.
//! A complex with an exact zero imaginary part is a real; one with `0.0` stays complex.

use std::cmp::Ordering;
use std::f64::consts::{LN_2, PI};
use std::hash::Hasher;

use crate::cfloat::{self, C};
use crate::int::{self, Host, NumError};
use crate::rational::{self, RationalView};
use crate::real::{self, RealHost, RealView};

/// A number as the host holds it.
#[derive(Clone, Copy, Debug)]
pub enum ComplexView<R> {
    Real(R),
    /// As [`ComplexHost::complex`] makes it.
    Complex { re: R, im: R },
}

/// A host that also holds complex numbers.
pub trait ComplexHost: RealHost {
    /// Any number.
    type Number: Copy;

    fn complex_view(&self, x: Self::Number) -> ComplexView<Self::Real>;

    fn of_real(&self, x: Self::Real) -> Self::Number;

    /// `re + im·i`, as the library makes it: `im` isn't exact zero, and the parts are both
    /// exact, both flonums, or an exact zero `re` and a flonum `im`.
    fn complex(&self, re: Self::Real, im: Self::Real) -> Result<Self::Number, Self::Error>;
}

type Res<H> = Result<<H as ComplexHost>::Number, <H as Host>::Error>;
type RealRes<H> = Result<<H as RealHost>::Real, <H as Host>::Error>;

fn exact_int<H: ComplexHost>(h: &H, n: i64) -> Res<H> {
    Ok(h.of_real(real::from_i64(h, n)?))
}

fn flonum<H: ComplexHost>(h: &H, f: f64) -> Res<H> {
    Ok(h.of_real(h.flonum(f)?))
}

fn from_c<H: ComplexHost>(h: &H, z: C) -> Res<H> {
    h.complex(h.flonum(z.re)?, h.flonum(z.im)?)
}

fn to_c<H: ComplexHost>(h: &H, z: H::Number) -> Result<C, H::Error> {
    let (re, im) = parts(h, z)?;
    Ok(C { re: real::to_f64(h, re)?, im: real::to_f64(h, im)? })
}

/// The real and imaginary parts, with exact zero for a real's.
fn parts<H: ComplexHost>(h: &H, z: H::Number) -> Result<(H::Real, H::Real), H::Error> {
    match h.complex_view(z) {
        ComplexView::Real(x) => Ok((x, real::from_i64(h, 0)?)),
        ComplexView::Complex { re, im } => Ok((re, im)),
    }
}

pub fn real_part<H: ComplexHost>(h: &H, z: H::Number) -> H::Real {
    match h.complex_view(z) {
        ComplexView::Real(x) | ComplexView::Complex { re: x, .. } => x,
    }
}

/// Exact zero for reals, even inexact ones.
pub fn imag_part<H: ComplexHost>(h: &H, z: H::Number) -> RealRes<H> {
    Ok(parts(h, z)?.1)
}

pub fn is_real<H: ComplexHost>(h: &H, z: H::Number) -> bool {
    matches!(h.complex_view(z), ComplexView::Real(_))
}

pub fn is_exact<H: ComplexHost>(h: &H, z: H::Number) -> bool {
    match h.complex_view(z) {
        ComplexView::Real(x) => real::is_exact(h, x),
        ComplexView::Complex { re, im } => real::is_exact(h, re) && real::is_exact(h, im),
    }
}

fn is_exact_zero<H: ComplexHost>(h: &H, z: H::Number) -> bool {
    matches!(h.complex_view(z), ComplexView::Real(x) if real::is_exact_zero(h, x))
}

fn is_exact_one<H: ComplexHost>(h: &H, z: H::Number) -> bool {
    let ComplexView::Real(x) = h.complex_view(z) else { return false };
    let RealView::Exact(q) = h.real_view(x) else { return false };
    matches!(h.rational_view(q), RationalView::Integer(n) if int::to_i64(h, n) == Some(1))
}

/// `make-rectangular`: inexact if either part is, except that an exact zero real part
/// stays exact, and real when `im` is exact zero.
pub fn rectangular<H: ComplexHost>(h: &H, re: H::Real, im: H::Real) -> Res<H> {
    match (h.real_view(re), h.real_view(im)) {
        _ if real::is_exact_zero(h, im) => Ok(h.of_real(re)),
        (RealView::Exact(_), RealView::Exact(_)) | (RealView::Flonum(_), RealView::Flonum(_)) => h.complex(re, im),
        _ if real::is_exact_zero(h, re) => h.complex(re, im),
        _ => h.complex(real::inexact(h, re)?, real::inexact(h, im)?),
    }
}

/// `make-polar`: `m·cos(a) + m·sin(a)·i`.
pub fn polar<H: ComplexHost>(h: &H, m: H::Real, a: H::Real) -> Res<H> {
    let f = real::to_f64(h, a)?;
    let sin = if real::is_exact_zero(h, a) { a } else { h.flonum(f.sin())? };
    rectangular(h, real::mul(h, m, h.flonum(f.cos())?)?, real::mul(h, m, sin)?)
}

/// `=`: the same value, whatever the exactness.
pub fn equal<H: ComplexHost>(h: &H, x: H::Number, y: H::Number) -> Result<bool, H::Error> {
    let same = |a, b| Ok::<_, H::Error>(real::compare(h, a, b)? == Some(Ordering::Equal));
    if let (ComplexView::Real(a), ComplexView::Real(b)) = (h.complex_view(x), h.complex_view(y)) {
        return same(a, b);
    }
    let ((a, b), (c, d)) = (parts(h, x)?, parts(h, y)?);
    Ok(same(a, c)? && same(b, d)?)
}

/// `eqv?`: parts that are [`real::eqv`].
pub fn eqv<H: ComplexHost>(h: &H, x: H::Number, y: H::Number) -> bool {
    match (h.complex_view(x), h.complex_view(y)) {
        (ComplexView::Real(a), ComplexView::Real(b)) => real::eqv(h, a, b),
        (ComplexView::Complex { re: a, im: b }, ComplexView::Complex { re: c, im: d }) => real::eqv(h, a, c) && real::eqv(h, b, d),
        _ => false,
    }
}

/// Feeds `x` to `state` so that [`eqv`] numbers hash the same. Reals hash as
/// [`real::hash`] does.
pub fn hash<H: ComplexHost, S: Hasher>(h: &H, x: H::Number, state: &mut S) {
    match h.complex_view(x) {
        ComplexView::Real(a) => real::hash(h, a, state),
        ComplexView::Complex { re, im } => {
            real::hash(h, re, state);
            real::hash(h, im, state);
        }
    }
}

/// `exact->inexact`
pub fn inexact<H: ComplexHost>(h: &H, z: H::Number) -> Res<H> {
    match h.complex_view(z) {
        ComplexView::Real(x) => Ok(h.of_real(real::inexact(h, x)?)),
        ComplexView::Complex { re, im } => h.complex(real::inexact(h, re)?, real::inexact(h, im)?),
    }
}

/// `inexact->exact`. Infinities and NaNs have no exact value.
pub fn exact<H: ComplexHost>(h: &H, z: H::Number) -> Res<H> {
    match h.complex_view(z) {
        ComplexView::Real(x) => Ok(h.of_real(real::exact(h, x)?)),
        ComplexView::Complex { re, im } => rectangular(h, real::exact(h, re)?, real::exact(h, im)?),
    }
}

pub fn neg<H: ComplexHost>(h: &H, z: H::Number) -> Res<H> {
    match h.complex_view(z) {
        ComplexView::Real(x) => Ok(h.of_real(real::neg(h, x)?)),
        ComplexView::Complex { re, im } => rectangular(h, real::neg(h, re)?, real::neg(h, im)?),
    }
}

pub fn add<H: ComplexHost>(h: &H, x: H::Number, y: H::Number) -> Res<H> {
    match (h.complex_view(x), h.complex_view(y)) {
        (ComplexView::Real(a), ComplexView::Real(b)) => Ok(h.of_real(real::add(h, a, b)?)),
        (ComplexView::Real(a), ComplexView::Complex { re, im }) => rectangular(h, real::add(h, a, re)?, im),
        (ComplexView::Complex { re, im }, ComplexView::Real(b)) => rectangular(h, real::add(h, re, b)?, im),
        (ComplexView::Complex { re: a, im: b }, ComplexView::Complex { re: c, im: d }) => {
            rectangular(h, real::add(h, a, c)?, real::add(h, b, d)?)
        }
    }
}

pub fn sub<H: ComplexHost>(h: &H, x: H::Number, y: H::Number) -> Res<H> {
    match (h.complex_view(x), h.complex_view(y)) {
        (ComplexView::Real(a), ComplexView::Real(b)) => Ok(h.of_real(real::sub(h, a, b)?)),
        (ComplexView::Real(a), ComplexView::Complex { re, im }) => rectangular(h, real::sub(h, a, re)?, real::neg(h, im)?),
        (ComplexView::Complex { re, im }, ComplexView::Real(b)) => rectangular(h, real::sub(h, re, b)?, im),
        (ComplexView::Complex { re: a, im: b }, ComplexView::Complex { re: c, im: d }) => {
            rectangular(h, real::sub(h, a, c)?, real::sub(h, b, d)?)
        }
    }
}

pub fn mul<H: ComplexHost>(h: &H, x: H::Number, y: H::Number) -> Res<H> {
    match (h.complex_view(x), h.complex_view(y)) {
        (ComplexView::Real(a), ComplexView::Real(b)) => Ok(h.of_real(real::mul(h, a, b)?)),
        (ComplexView::Real(a), ComplexView::Complex { re, im }) | (ComplexView::Complex { re, im }, ComplexView::Real(a)) => {
            rectangular(h, real::mul(h, a, re)?, real::mul(h, a, im)?)
        }
        (ComplexView::Complex { re: a, im: b }, ComplexView::Complex { re: c, im: d }) => {
            let re = real::sub(h, real::mul(h, a, c)?, real::mul(h, b, d)?)?;
            rectangular(h, re, real::add(h, real::mul(h, a, d)?, real::mul(h, b, c)?)?)
        }
    }
}

/// Dividing by exact zero is an error, and exact zero divided by anything else is exact zero.
/// Inexact complex division is Smith's.
pub fn div<H: ComplexHost>(h: &H, x: H::Number, y: H::Number) -> Res<H> {
    match (h.complex_view(x), h.complex_view(y)) {
        (_, ComplexView::Real(b)) if real::is_exact_zero(h, b) => Err(NumError::DivideByZero.into()),
        (ComplexView::Real(a), ComplexView::Real(b)) => Ok(h.of_real(real::div(h, a, b)?)),
        (ComplexView::Complex { re, im }, ComplexView::Real(b)) => rectangular(h, real::div(h, re, b)?, real::div(h, im, b)?),
        _ if is_exact_zero(h, x) => Ok(x),
        _ if is_exact(h, x) && is_exact(h, y) => {
            // (a + bi) / (c + di) is ((ac + bd) + (bc - ad)i) / (c² + d²).
            let ((a, b), (c, d)) = (parts(h, x)?, parts(h, y)?);
            let den = real::add(h, real::mul(h, c, c)?, real::mul(h, d, d)?)?;
            let re = real::add(h, real::mul(h, a, c)?, real::mul(h, b, d)?)?;
            let im = real::sub(h, real::mul(h, b, c)?, real::mul(h, a, d)?)?;
            rectangular(h, real::div(h, re, den)?, real::div(h, im, den)?)
        }
        _ => from_c(h, cfloat::div(to_c(h, x)?, to_c(h, y)?)),
    }
}

/// `r · 2^k`, exactly.
fn times_power_of_two<H: RealHost>(h: &H, r: H::Rational, k: i64) -> Result<H::Rational, H::Error> {
    let power = h.of_int(int::arithmetic_shift(h, int::from_i64(h, 1)?, k.abs())?);
    if k >= 0 { rational::mul(h, r, power) } else { rational::div(h, r, power) }
}

/// About `log2 |r|` for a nonzero `r`, within one.
fn exponent<H: RealHost>(h: &H, r: H::Rational) -> Result<i64, H::Error> {
    let num = int::integer_length(h, rational::numerator(h, r)) as i64;
    Ok(num - int::integer_length(h, rational::denominator(h, r)?) as i64)
}

/// A positive `r` as `m · 2^k`, for values whose double would overflow or lose precision.
fn split<H: RealHost>(h: &H, r: H::Rational) -> Result<(f64, i64), H::Error> {
    let k = exponent(h, r)?;
    Ok((rational::to_f64(h, times_power_of_two(h, r, -k)?)?, k))
}

/// Exact `a` and `b` as doubles with a shared power of two taken out where either would
/// overflow or underflow, which keeps their ratio.
fn exact_pair<H: RealHost>(h: &H, a: H::Rational, b: H::Rational) -> Result<(f64, f64), H::Error> {
    let (fa, fb) = (rational::to_f64(h, a)?, rational::to_f64(h, b)?);
    let fits = |f: f64, r| f.is_normal() || rational::sign(h, r) == Ordering::Equal;
    if fits(fa, a) && fits(fb, b) {
        return Ok((fa, fb));
    }
    let mut k = i64::MIN;
    for r in [a, b] {
        if rational::sign(h, r) != Ordering::Equal {
            k = k.max(exponent(h, r)?);
        }
    }
    Ok((rational::to_f64(h, times_power_of_two(h, a, -k)?)?, rational::to_f64(h, times_power_of_two(h, b, -k)?)?))
}

/// The exact square root of `r >= 0`, if it's rational.
fn exact_sqrt<H: RealHost>(h: &H, r: H::Rational) -> Result<Option<H::Rational>, H::Error> {
    let root = |n| {
        let s = int::isqrt(h, n)?;
        Ok::<_, H::Error>((int::compare(h, int::mul(h, s, s)?, n) == Ordering::Equal).then_some(s))
    };
    let Some(num) = root(rational::numerator(h, r))? else { return Ok(None) };
    let Some(den) = root(rational::denominator(h, r)?)? else { return Ok(None) };
    Ok(Some(rational::from_parts(h, num, den)?))
}

/// The square root of a real that isn't below zero: exact when it can be.
fn sqrt_real<H: RealHost>(h: &H, x: H::Real) -> RealRes<H> {
    let r = match h.real_view(x) {
        RealView::Flonum(f) => return h.flonum(f.sqrt()),
        RealView::Exact(r) => r,
    };
    if let Some(s) = exact_sqrt(h, r)? {
        return Ok(h.of_rational(s));
    }
    let f = rational::to_f64(h, r)?;
    if f.is_normal() {
        return h.flonum(f.sqrt());
    }
    let (m, k) = split(h, r)?;
    let (m, k) = if k % 2 == 0 { (m, k) } else { (m * 2.0, k - 1) };
    h.flonum(cfloat::ldexp(m.sqrt(), k / 2))
}

/// The log of a real that isn't below zero: exact 0 for exact 1.
fn log_real<H: RealHost>(h: &H, x: H::Real) -> RealRes<H> {
    let r = match h.real_view(x) {
        RealView::Flonum(f) => return h.flonum(f.ln()),
        RealView::Exact(r) => r,
    };
    if let RationalView::Integer(n) = h.rational_view(r) {
        match int::to_i64(h, n) {
            Some(0) => return Err(NumError::DivideByZero.into()),
            Some(1) => return real::from_i64(h, 0),
            _ => {}
        }
    }
    let f = rational::to_f64(h, r)?;
    if f.is_normal() {
        return h.flonum(f.ln());
    }
    let (m, k) = split(h, r)?;
    h.flonum(m.ln() + k as f64 * LN_2)
}

/// Exact 0 for any positive real, and an error for exact 0.
pub fn angle<H: ComplexHost>(h: &H, z: H::Number) -> RealRes<H> {
    let (re, im) = match h.complex_view(z) {
        ComplexView::Real(x) => {
            return match h.real_view(x) {
                RealView::Exact(r) => match rational::sign(h, r) {
                    Ordering::Equal => Err(NumError::DivideByZero.into()),
                    Ordering::Greater => real::from_i64(h, 0),
                    Ordering::Less => h.flonum(PI),
                },
                RealView::Flonum(f) if f.is_nan() => Ok(x),
                RealView::Flonum(f) if f.is_sign_negative() => h.flonum(PI),
                RealView::Flonum(_) => real::from_i64(h, 0),
            };
        }
        ComplexView::Complex { re, im } => (re, im),
    };
    let (a, b) = match (h.real_view(re), h.real_view(im)) {
        (RealView::Exact(a), RealView::Exact(b)) => exact_pair(h, a, b)?,
        _ => (real::to_f64(h, re)?, real::to_f64(h, im)?),
    };
    h.flonum(b.atan2(a))
}

/// Exact when the parts are and the result is rational, as for `3+4i`.
pub fn magnitude<H: ComplexHost>(h: &H, z: H::Number) -> RealRes<H> {
    let (re, im) = match h.complex_view(z) {
        ComplexView::Real(x) => return real::abs(h, x),
        ComplexView::Complex { re, im } => (re, im),
    };
    match (h.real_view(re), h.real_view(im)) {
        (RealView::Exact(a), RealView::Exact(b)) => {
            let sum = rational::add(h, rational::mul(h, a, a)?, rational::mul(h, b, b)?)?;
            sqrt_real(h, h.of_rational(sum))
        }
        _ => h.flonum(real::to_f64(h, re)?.hypot(real::to_f64(h, im)?)),
    }
}

/// The principal square root: exact when `z` is exact and its root is too.
pub fn sqrt<H: ComplexHost>(h: &H, z: H::Number) -> Res<H> {
    let (re, im) = match h.complex_view(z) {
        ComplexView::Real(x) if real::sign(h, x) == Some(Ordering::Less) => {
            return rectangular(h, real::from_i64(h, 0)?, sqrt_real(h, real::neg(h, x)?)?);
        }
        ComplexView::Real(x) => return Ok(h.of_real(sqrt_real(h, x)?)),
        ComplexView::Complex { re, im } => (re, im),
    };
    if let (RealView::Exact(a), RealView::Exact(b)) = (h.real_view(re), h.real_view(im)) {
        // (p + qi)² = a + bi for p = √((|z| + a) / 2) and q = ±√((|z| - a) / 2).
        let sum = rational::add(h, rational::mul(h, a, a)?, rational::mul(h, b, b)?)?;
        if let Some(m) = exact_sqrt(h, sum)? {
            let half = |x| rational::div(h, x, h.of_int(int::from_i64(h, 2)?));
            let p = exact_sqrt(h, half(rational::add(h, m, a)?)?)?;
            let q = exact_sqrt(h, half(rational::sub(h, m, a)?)?)?;
            if let (Some(p), Some(q)) = (p, q) {
                let q = if rational::sign(h, b) == Ordering::Less { rational::neg(h, q)? } else { q };
                return rectangular(h, h.of_rational(p), h.of_rational(q));
            }
        }
    }
    from_c(h, cfloat::sqrt(to_c(h, z)?))
}

/// Exact 1 for exact 0.
pub fn exp<H: ComplexHost>(h: &H, z: H::Number) -> Res<H> {
    match h.complex_view(z) {
        _ if is_exact_zero(h, z) => exact_int(h, 1),
        ComplexView::Real(x) => flonum(h, real::to_f64(h, x)?.exp()),
        ComplexView::Complex { .. } => from_c(h, cfloat::exp(to_c(h, z)?)),
    }
}

/// The natural log, `log |z| + angle(z)·i`. Exact 0 for exact 1, and exact 0 divides by zero.
pub fn log<H: ComplexHost>(h: &H, z: H::Number) -> Res<H> {
    if let ComplexView::Real(x) = h.complex_view(z)
        && real::sign(h, x) != Some(Ordering::Less)
    {
        return Ok(h.of_real(log_real(h, x)?));
    }
    if is_exact(h, z) || matches!(h.complex_view(z), ComplexView::Real(_)) {
        return rectangular(h, log_real(h, magnitude(h, z)?)?, angle(h, z)?);
    }
    from_c(h, cfloat::log(to_c(h, z)?))
}

/// `log z / log base`.
pub fn log_base<H: ComplexHost>(h: &H, z: H::Number, base: H::Number) -> Res<H> {
    div(h, log(h, z)?, log(h, base)?)
}

/// Exact 0 for exact 0.
pub fn sin<H: ComplexHost>(h: &H, z: H::Number) -> Res<H> {
    match h.complex_view(z) {
        _ if is_exact_zero(h, z) => Ok(z),
        ComplexView::Real(x) => flonum(h, real::to_f64(h, x)?.sin()),
        ComplexView::Complex { .. } => from_c(h, cfloat::sin(to_c(h, z)?)),
    }
}

pub fn cos<H: ComplexHost>(h: &H, z: H::Number) -> Res<H> {
    match h.complex_view(z) {
        ComplexView::Real(x) => flonum(h, real::to_f64(h, x)?.cos()),
        ComplexView::Complex { .. } => from_c(h, cfloat::cos(to_c(h, z)?)),
    }
}

/// Exact 0 for exact 0.
pub fn tan<H: ComplexHost>(h: &H, z: H::Number) -> Res<H> {
    match h.complex_view(z) {
        _ if is_exact_zero(h, z) => Ok(z),
        ComplexView::Real(x) => flonum(h, real::to_f64(h, x)?.tan()),
        ComplexView::Complex { .. } => from_c(h, cfloat::tan(to_c(h, z)?)),
    }
}

/// Exact 0 for exact 0, and complex for reals outside [-1, 1].
pub fn asin<H: ComplexHost>(h: &H, z: H::Number) -> Res<H> {
    if is_exact_zero(h, z) {
        return Ok(z);
    }
    inverse(h, z, f64::asin, cfloat::asin)
}

/// Complex for reals outside [-1, 1].
pub fn acos<H: ComplexHost>(h: &H, z: H::Number) -> Res<H> {
    inverse(h, z, f64::acos, cfloat::acos)
}

fn inverse<H: ComplexHost>(h: &H, z: H::Number, real: fn(f64) -> f64, complex: fn(C) -> C) -> Res<H> {
    if let ComplexView::Real(x) = h.complex_view(z) {
        let f = real::to_f64(h, x)?;
        if f.abs() <= 1.0 || f.is_nan() {
            return flonum(h, real(f));
        }
    }
    from_c(h, complex(to_c(h, z)?))
}

/// Exact 0 for exact 0. Exact `±i` divide by zero.
pub fn atan<H: ComplexHost>(h: &H, z: H::Number) -> Res<H> {
    match h.complex_view(z) {
        _ if is_exact_zero(h, z) => Ok(z),
        ComplexView::Real(x) => flonum(h, real::to_f64(h, x)?.atan()),
        ComplexView::Complex { re, im } => {
            if real::is_exact_zero(h, re) && let RealView::Exact(b) = h.real_view(im) {
                let one = h.of_int(int::from_i64(h, 1)?);
                if rational::eqv(h, rational::abs(h, b)?, one) {
                    return Err(NumError::DivideByZero.into());
                }
            }
            from_c(h, cfloat::atan(to_c(h, z)?))
        }
    }
}

/// The angle of `(x, y)`: exact 0 when `y` is exact 0 and `x` is positive, and an error when
/// both are exact 0.
pub fn atan2<H: RealHost>(h: &H, y: H::Real, x: H::Real) -> RealRes<H> {
    if real::is_exact_zero(h, y) {
        if real::is_exact_zero(h, x) {
            return Err(NumError::DivideByZero.into());
        }
        if real::sign(h, x) == Some(Ordering::Greater) {
            return Ok(y);
        }
    }
    let (fy, fx) = match (h.real_view(y), h.real_view(x)) {
        (RealView::Exact(a), RealView::Exact(b)) => exact_pair(h, a, b)?,
        _ => (real::to_f64(h, y)?, real::to_f64(h, x)?),
    };
    h.flonum(fy.atan2(fx))
}

/// `z^w` with the special cases Racket lists: exact powers of exact numbers stay exact, an
/// exact 1/2 power is [`sqrt`], real powers follow C's `pow` except that a negative base with
/// a non-integer power goes complex, and everything else is `exp(w · log z)`.
pub fn expt<H: ComplexHost>(h: &H, z: H::Number, w: H::Number) -> Res<H> {
    if is_exact_zero(h, w) || is_exact_one(h, z) {
        return exact_int(h, 1);
    }
    if is_exact_zero(h, z) {
        return match h.complex_view(w) {
            ComplexView::Real(e) => match h.real_view(e) {
                RealView::Flonum(0.0) => flonum(h, 1.0),
                RealView::Flonum(f) if f.is_nan() => flonum(h, f),
                _ if real::sign(h, e) == Some(Ordering::Less) => Err(NumError::DivideByZero.into()),
                _ => Ok(z),
            },
            ComplexView::Complex { re, .. } => match real::sign(h, re) {
                Some(Ordering::Greater) => Ok(z),
                None => flonum(h, f64::NAN),
                _ => Err(NumError::DivideByZero.into()),
            },
        };
    }
    let ComplexView::Real(e) = h.complex_view(w) else {
        return exp(h, mul(h, w, log(h, z)?)?);
    };
    if let RealView::Exact(q) = h.real_view(e) {
        match h.rational_view(q) {
            RationalView::Integer(n) => return integer_power(h, z, n),
            RationalView::Ratio { num, den } if int::to_i64(h, num) == Some(1) && int::to_i64(h, den) == Some(2) => {
                return sqrt(h, z);
            }
            RationalView::Ratio { .. } => {}
        }
    }
    if let ComplexView::Real(b) = h.complex_view(z) {
        let (fb, fe) = (real::to_f64(h, b)?, real::to_f64(h, e)?);
        if real::sign(h, b) != Some(Ordering::Less) || fe.is_finite() && fe.fract() == 0.0 {
            return flonum(h, fb.powf(fe));
        }
    }
    exp(h, mul(h, w, log(h, z)?)?)
}

/// `z^n` by squaring, for an exact integer `n`.
fn integer_power<H: ComplexHost>(h: &H, z: H::Number, n: H::Int) -> Res<H> {
    if let ComplexView::Real(b) = h.complex_view(z) {
        let q = match h.real_view(b) {
            RealView::Flonum(f) => return flonum(h, f.powf(int::to_f64(h, n))),
            RealView::Exact(q) => q,
        };
        return match int::to_i64(h, n) {
            Some(e) => Ok(h.of_real(h.of_rational(rational::expt(h, q, e)?))),
            None if real::eqv(h, b, real::from_i64(h, -1)?) => exact_int(h, if int::is_even(h, n) { 1 } else { -1 }),
            // Any other base needs more bits than memory holds.
            None => Err(int::too_big(h)),
        };
    }
    let Some(e) = int::to_i64(h, n) else {
        if is_exact(h, z) {
            return Err(int::too_big(h));
        }
        let w = h.of_real(h.of_rational(h.of_int(n)));
        return exp(h, mul(h, w, log(h, z)?)?);
    };
    let (mut result, mut base, mut left) = (exact_int(h, 1)?, z, e.unsigned_abs());
    while left != 0 {
        if left & 1 == 1 {
            result = mul(h, result, base)?;
        }
        left >>= 1;
        if left != 0 {
            base = mul(h, base, base)?;
        }
    }
    if e < 0 { div(h, exact_int(h, 1)?, result) } else { Ok(result) }
}
