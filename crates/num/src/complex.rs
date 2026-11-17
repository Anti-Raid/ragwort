//! The full numeric tower with Racket's semantics: reals and complex numbers. The two parts of a complex number are both
//! exact, both flonums, or an exact zero real part with a flonum imaginary part. An example of the last form is `(sqrt -4.0)`, which is `+2.0i`.
//! A number with an exact zero imaginary part is a real. A number with a `0.0` imaginary part stays complex.

use std::cmp::Ordering;
use std::f64::consts::{LN_2, PI};
use std::hash::Hasher;

use crate::cfloat::{self, C};
use crate::int::{self, Host, NumError};
use crate::rational::{self, RationalView};
use crate::real::{self, RealHost, RealView};

/// A number in the representation that the host stores.
#[derive(Clone, Copy, Debug)]
pub enum ComplexView<R> {
    Real(R),
    /// A complex number, with the invariants that [`ComplexHost::complex`] documents.
    Complex { re: R, im: R },
}

/// A host that also stores complex numbers.
pub trait ComplexHost: RealHost {
    /// Any number.
    type Number: Copy;

    fn complex_view(&self, x: Self::Number) -> ComplexView<Self::Real>;

    fn of_real(&self, x: Self::Real) -> Self::Number;

    /// Creates the complex number `re + im·i`. The library guarantees the following: `im` is not exact zero, and the parts are both
    /// exact, both flonums, or an exact zero `re` with a flonum `im`.
    fn complex(&self, re: Self::Real, im: Self::Real) -> Result<Self::Number, Self::Error>;
}

type Res<H> = Result<<H as ComplexHost>::Number, <H as Host>::Error>;
type RealRes<H> = Result<<H as RealHost>::Real, <H as Host>::Error>;

fn exact_int<H: ComplexHost>(h: &H, n: i64) -> Res<H> {
    Ok(h.of_real(real::from_i64(h, n)?))
}

fn flonum<H: ComplexHost>(h: &H, value: f64) -> Res<H> {
    Ok(h.of_real(h.flonum(value)?))
}

fn from_c<H: ComplexHost>(h: &H, z: C) -> Res<H> {
    h.complex(h.flonum(z.re)?, h.flonum(z.im)?)
}

fn to_c<H: ComplexHost>(h: &H, z: H::Number) -> Result<C, H::Error> {
    let (re, im) = parts(h, z)?;
    Ok(C { re: real::to_f64(h, re)?, im: real::to_f64(h, im)? })
}

/// Returns the real and imaginary parts of `z`. The imaginary part of a real is exact zero.
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

/// Returns the imaginary part of `z`. For a real, even an inexact one, this is exact zero.
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
    let RealView::Exact(fraction) = h.real_view(x) else { return false };
    matches!(h.rational_view(fraction), RationalView::Integer(integer) if int::to_i64(h, integer) == Some(1))
}

/// Implements `make-rectangular`. The result is inexact if either part is inexact, except that an exact zero real part
/// stays exact. The result is a real when `im` is exact zero.
pub fn rectangular<H: ComplexHost>(h: &H, re: H::Real, im: H::Real) -> Res<H> {
    match (h.real_view(re), h.real_view(im)) {
        _ if real::is_exact_zero(h, im) => Ok(h.of_real(re)),
        (RealView::Exact(_), RealView::Exact(_)) | (RealView::Flonum(_), RealView::Flonum(_)) => h.complex(re, im),
        _ if real::is_exact_zero(h, re) => h.complex(re, im),
        _ => h.complex(real::inexact(h, re)?, real::inexact(h, im)?),
    }
}

/// Implements `make-polar`: returns `modulus·cos(a) + modulus·sin(a)·i`.
pub fn polar<H: ComplexHost>(h: &H, modulus: H::Real, a: H::Real) -> Res<H> {
    let float = real::to_f64(h, a)?;
    let sin = if real::is_exact_zero(h, a) { a } else { h.flonum(float.sin())? };
    rectangular(h, real::mul(h, modulus, h.flonum(float.cos())?)?, real::mul(h, modulus, sin)?)
}

/// Implements `=`. Returns whether `x` and `y` have the same value, regardless of exactness.
pub fn equal<H: ComplexHost>(h: &H, x: H::Number, y: H::Number) -> Result<bool, H::Error> {
    #[inline(always)]
    fn same<H: ComplexHost>(h: &H, a: H::Real, b: H::Real) -> Result<bool, H::Error> {
        Ok(real::compare(h, a, b)? == Some(Ordering::Equal))
    }
    if let (ComplexView::Real(a), ComplexView::Real(b)) = (h.complex_view(x), h.complex_view(y)) {
        return same(h, a, b);
    }
    let ((a, b), (y_re, y_im)) = (parts(h, x)?, parts(h, y)?);
    Ok(same(h, a, y_re)? && same(h, b, y_im)?)
}

/// Returns `z` written in `radix`. A real is written as [`real::to_string`] writes it. A complex number is written as `a+bi`,
/// or as `+bi` when the real part is exact zero.
pub fn to_string<H: ComplexHost>(h: &H, z: H::Number, radix: u32) -> Result<String, H::Error> {
    let (re, im) = match h.complex_view(z) {
        ComplexView::Real(x) => return real::to_string(h, x, radix),
        ComplexView::Complex { re, im } => (re, im),
    };
    let zero = matches!(h.real_view(re), RealView::Exact(value) if rational::sign(h, value).is_eq());
    let mut out = if zero { String::new() } else { real::to_string(h, re, radix)? };
    let im = real::to_string(h, im, radix)?;
    if !im.starts_with(['+', '-']) {
        out.push('+');
    }
    out.push_str(&im);
    out.push('i');
    Ok(out)
}

/// Implements `eqv?`. Two numbers are equivalent if their parts are [`real::eqv`].
pub fn eqv<H: ComplexHost>(h: &H, x: H::Number, y: H::Number) -> bool {
    match (h.complex_view(x), h.complex_view(y)) {
        (ComplexView::Real(a), ComplexView::Real(b)) => real::eqv(h, a, b),
        (ComplexView::Complex { re: a, im: b }, ComplexView::Complex { re: y_re, im: y_im }) => real::eqv(h, a, y_re) && real::eqv(h, b, y_im),
        _ => false,
    }
}

/// Feeds `x` to `state`, so that numbers that are [`eqv`] hash the same. A real hashes as
/// [`real::hash`] hashes it.
pub fn hash<H: ComplexHost, S: Hasher>(h: &H, x: H::Number, state: &mut S) {
    match h.complex_view(x) {
        ComplexView::Real(a) => real::hash(h, a, state),
        ComplexView::Complex { re, im } => {
            real::hash(h, re, state);
            real::hash(h, im, state);
        }
    }
}

/// Converts `z` to an inexact number, as `exact->inexact` does.
pub fn inexact<H: ComplexHost>(h: &H, z: H::Number) -> Res<H> {
    match h.complex_view(z) {
        ComplexView::Real(x) => Ok(h.of_real(real::inexact(h, x)?)),
        ComplexView::Complex { re, im } => h.complex(real::inexact(h, re)?, real::inexact(h, im)?),
    }
}

/// Converts `z` to an exact number, as `inexact->exact` does. An infinity or a NaN has no exact value and gives [`NumError::NoExactValue`].
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
        (ComplexView::Complex { re: a, im: b }, ComplexView::Complex { re: y_re, im: y_im }) => {
            rectangular(h, real::add(h, a, y_re)?, real::add(h, b, y_im)?)
        }
    }
}

pub fn sub<H: ComplexHost>(h: &H, x: H::Number, y: H::Number) -> Res<H> {
    match (h.complex_view(x), h.complex_view(y)) {
        (ComplexView::Real(a), ComplexView::Real(b)) => Ok(h.of_real(real::sub(h, a, b)?)),
        (ComplexView::Real(a), ComplexView::Complex { re, im }) => rectangular(h, real::sub(h, a, re)?, real::neg(h, im)?),
        (ComplexView::Complex { re, im }, ComplexView::Real(b)) => rectangular(h, real::sub(h, re, b)?, im),
        (ComplexView::Complex { re: a, im: b }, ComplexView::Complex { re: y_re, im: y_im }) => {
            rectangular(h, real::sub(h, a, y_re)?, real::sub(h, b, y_im)?)
        }
    }
}

pub fn mul<H: ComplexHost>(h: &H, x: H::Number, y: H::Number) -> Res<H> {
    match (h.complex_view(x), h.complex_view(y)) {
        (ComplexView::Real(a), ComplexView::Real(b)) => Ok(h.of_real(real::mul(h, a, b)?)),
        (ComplexView::Real(a), ComplexView::Complex { re, im }) | (ComplexView::Complex { re, im }, ComplexView::Real(a)) => {
            rectangular(h, real::mul(h, a, re)?, real::mul(h, a, im)?)
        }
        (ComplexView::Complex { re: a, im: b }, ComplexView::Complex { re: y_re, im: y_im }) => {
            let re = real::sub(h, real::mul(h, a, y_re)?, real::mul(h, b, y_im)?)?;
            rectangular(h, re, real::add(h, real::mul(h, a, y_im)?, real::mul(h, b, y_re)?)?)
        }
    }
}

/// Returns `x / y`. Division by exact zero is an error. Exact zero divided by any other number is exact zero.
/// Inexact complex division uses Smith's method.
pub fn div<H: ComplexHost>(h: &H, x: H::Number, y: H::Number) -> Res<H> {
    match (h.complex_view(x), h.complex_view(y)) {
        (_, ComplexView::Real(b)) if real::is_exact_zero(h, b) => Err(NumError::DivideByZero.into()),
        (ComplexView::Real(a), ComplexView::Real(b)) => Ok(h.of_real(real::div(h, a, b)?)),
        (ComplexView::Complex { re, im }, ComplexView::Real(b)) => rectangular(h, real::div(h, re, b)?, real::div(h, im, b)?),
        _ if is_exact_zero(h, x) => Ok(x),
        _ if is_exact(h, x) && is_exact(h, y) => {
            // (a + bi) / (c + di) is ((ac + bd) + (bc - ad)i) / (c² + d²).
            let ((a, b), (y_re, y_im)) = (parts(h, x)?, parts(h, y)?);
            let den = real::add(h, real::mul(h, y_re, y_re)?, real::mul(h, y_im, y_im)?)?;
            let re = real::add(h, real::mul(h, a, y_re)?, real::mul(h, b, y_im)?)?;
            let im = real::sub(h, real::mul(h, b, y_re)?, real::mul(h, a, y_im)?)?;
            rectangular(h, real::div(h, re, den)?, real::div(h, im, den)?)
        }
        _ => from_c(h, cfloat::div(to_c(h, x)?, to_c(h, y)?)),
    }
}

/// Returns `value · 2^scale`, exactly.
fn times_power_of_two<H: RealHost>(h: &H, value: H::Rational, scale: i64) -> Result<H::Rational, H::Error> {
    let power = h.of_int(int::arithmetic_shift(h, int::from_i64(h, 1)?, scale.abs())?);
    if scale >= 0 { rational::mul(h, value, power) } else { rational::div(h, value, power) }
}

/// Returns an estimate of `log2 |value|` that is within one of the true value. `value` must not be zero.
fn exponent<H: RealHost>(h: &H, value: H::Rational) -> Result<i64, H::Error> {
    let num = int::integer_length(h, rational::numerator(h, value)) as i64;
    Ok(num - int::integer_length(h, rational::denominator(h, value)?) as i64)
}

/// Returns `(m, scale)` such that `value ≈ m · 2^scale`. `value` must be positive. This is for values whose `f64` would overflow or lose precision.
fn split<H: RealHost>(h: &H, value: H::Rational) -> Result<(f64, i64), H::Error> {
    let scale = exponent(h, value)?;
    Ok((rational::to_f64(h, times_power_of_two(h, value, -scale)?)?, scale))
}

/// Returns `(x, y, scale)` for exact `a` and `b`, such that `a ≈ x · 2^scale` and `b ≈ y · 2^scale`. `scale` is even.
/// It is zero unless the `f64` of `a` or of `b` would overflow or underflow.
fn exact_pair<H: RealHost>(h: &H, a: H::Rational, b: H::Rational) -> Result<(f64, f64, i64), H::Error> {
    let (fa, fb) = (rational::to_f64(h, a)?, rational::to_f64(h, b)?);
    #[inline(always)]
    fn fits<H: RealHost>(h: &H, double: f64, value: H::Rational) -> bool {
        double.is_normal() || rational::sign(h, value) == Ordering::Equal
    }
    if fits(h, fa, a) && fits(h, fb, b) {
        return Ok((fa, fb, 0));
    }
    let mut scale = i64::MIN;
    for value in [a, b] {
        if rational::sign(h, value) != Ordering::Equal {
            scale = scale.max(exponent(h, value)?);
        }
    }
    let scale = scale + (scale & 1);
    let scaled_a = rational::to_f64(h, times_power_of_two(h, a, -scale)?)?;
    let scaled_b = rational::to_f64(h, times_power_of_two(h, b, -scale)?)?;
    Ok((scaled_a, scaled_b, scale))
}

/// Returns the exact square root of `value` if the root is rational, or `None` otherwise. `value` must not be negative.
fn exact_sqrt<H: RealHost>(h: &H, value: H::Rational) -> Result<Option<H::Rational>, H::Error> {
    #[inline(always)]
    fn root<H: RealHost>(h: &H, integer: H::Int) -> Result<Option<H::Int>, H::Error> {
        let candidate = int::isqrt(h, integer)?;
        Ok((int::compare(h, int::mul(h, candidate, candidate)?, integer) == Ordering::Equal).then_some(candidate))
    }
    let Some(num) = root(h, rational::numerator(h, value))? else { return Ok(None) };
    let Some(den) = root(h, rational::denominator(h, value)?)? else { return Ok(None) };
    Ok(Some(rational::from_parts(h, num, den)?))
}

/// Returns the square root of `x`, which must not be negative. The result is exact when `x` is exact and its root is rational.
fn sqrt_real<H: RealHost>(h: &H, x: H::Real) -> RealRes<H> {
    let value = match h.real_view(x) {
        RealView::Flonum(float) => return h.flonum(float.sqrt()),
        RealView::Exact(value) => value,
    };
    if let Some(root) = exact_sqrt(h, value)? {
        return Ok(h.of_rational(root));
    }
    let float = rational::to_f64(h, value)?;
    if float.is_normal() {
        return h.flonum(float.sqrt());
    }
    let (mantissa, scale) = split(h, value)?;
    let (mantissa, scale) = if scale % 2 == 0 { (mantissa, scale) } else { (mantissa * 2.0, scale - 1) };
    h.flonum(cfloat::ldexp(mantissa.sqrt(), scale / 2))
}

/// Returns the natural logarithm of `x`, which must not be negative. The result for exact 1 is exact 0, and exact 0 gives a `DivideByZero` error.
fn log_real<H: RealHost>(h: &H, x: H::Real) -> RealRes<H> {
    let value = match h.real_view(x) {
        RealView::Flonum(float) => return h.flonum(float.ln()),
        RealView::Exact(value) => value,
    };
    if let RationalView::Integer(integer) = h.rational_view(value) {
        match int::to_i64(h, integer) {
            Some(0) => return Err(NumError::DivideByZero.into()),
            Some(1) => return real::from_i64(h, 0),
            _ => {}
        }
    }
    let float = rational::to_f64(h, value)?;
    if float.is_normal() {
        return h.flonum(float.ln());
    }
    let (mantissa, scale) = split(h, value)?;
    h.flonum(mantissa.ln() + scale as f64 * LN_2)
}

/// Returns the angle of `z`. The angle of any positive real is exact 0, and exact 0 gives a [`NumError::DivideByZero`] error.
pub fn angle<H: ComplexHost>(h: &H, z: H::Number) -> RealRes<H> {
    let (re, im) = match h.complex_view(z) {
        ComplexView::Real(x) => {
            return match h.real_view(x) {
                RealView::Exact(value) => match rational::sign(h, value) {
                    Ordering::Equal => Err(NumError::DivideByZero.into()),
                    Ordering::Greater => real::from_i64(h, 0),
                    Ordering::Less => h.flonum(PI),
                },
                RealView::Flonum(float) if float.is_nan() => Ok(x),
                RealView::Flonum(float) if float.is_sign_negative() => h.flonum(PI),
                RealView::Flonum(_) => real::from_i64(h, 0),
            };
        }
        ComplexView::Complex { re, im } => (re, im),
    };
    let (a, b) = match (h.real_view(re), h.real_view(im)) {
        (RealView::Exact(a), RealView::Exact(b)) => {
            let (x, y, _) = exact_pair(h, a, b)?;
            (x, y)
        }
        _ => (real::to_f64(h, re)?, real::to_f64(h, im)?),
    };
    h.flonum(b.atan2(a))
}

/// Returns the magnitude of `z`. The result is exact when both parts are exact and the magnitude is rational, as for `3+4i`.
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

/// Returns the principal square root of `z`. The result is exact when `z` is exact and both parts of the root are rational.
pub fn sqrt<H: ComplexHost>(h: &H, z: H::Number) -> Res<H> {
    let (re, im) = match h.complex_view(z) {
        ComplexView::Real(x) if real::sign(h, x) == Some(Ordering::Less) => {
            return rectangular(h, real::from_i64(h, 0)?, sqrt_real(h, real::neg(h, x)?)?);
        }
        ComplexView::Real(x) => return Ok(h.of_real(sqrt_real(h, x)?)),
        ComplexView::Complex { re, im } => (re, im),
    };
    if let (RealView::Exact(a), RealView::Exact(b)) = (h.real_view(re), h.real_view(im)) {
        // `(p + qi)² = a + bi` for `p = √((|z| + a) / 2)` and `q = ±√((|z| - a) / 2)`, where `q` takes the sign of `b`.
        let sum = rational::add(h, rational::mul(h, a, a)?, rational::mul(h, b, b)?)?;
        if let Some(modulus) = exact_sqrt(h, sum)? {
            #[inline(always)]
            fn half<H: ComplexHost>(h: &H, x: H::Rational) -> Result<H::Rational, H::Error> {
                rational::div(h, x, h.of_int(int::from_i64(h, 2)?))
            }
            let real_root = exact_sqrt(h, half(h, rational::add(h, modulus, a)?)?)?;
            let imag_root = exact_sqrt(h, half(h, rational::sub(h, modulus, a)?)?)?;
            if let (Some(real_root), Some(imag_root)) = (real_root, imag_root) {
                let imag_root = if rational::sign(h, b) == Ordering::Less { rational::neg(h, imag_root)? } else { imag_root };
                return rectangular(h, h.of_rational(real_root), h.of_rational(imag_root));
            }
        }
        let (x, y, scale) = exact_pair(h, a, b)?;
        let root = cfloat::sqrt(C { re: x, im: y });
        return from_c(h, C { re: cfloat::ldexp(root.re, scale / 2), im: cfloat::ldexp(root.im, scale / 2) });
    }
    from_c(h, cfloat::sqrt(to_c(h, z)?))
}

/// Returns `e^z`. The result for exact 0 is exact 1.
pub fn exp<H: ComplexHost>(h: &H, z: H::Number) -> Res<H> {
    match h.complex_view(z) {
        _ if is_exact_zero(h, z) => exact_int(h, 1),
        ComplexView::Real(x) => flonum(h, real::to_f64(h, x)?.exp()),
        ComplexView::Complex { .. } => from_c(h, cfloat::exp(to_c(h, z)?)),
    }
}

/// Returns the natural logarithm of `z`, which is `log |z| + angle(z)·i`. The result for exact 1 is exact 0, and exact 0 gives a [`NumError::DivideByZero`] error.
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

/// Returns the logarithm of `z` in `base`, computed as `log z / log base`.
pub fn log_base<H: ComplexHost>(h: &H, z: H::Number, base: H::Number) -> Res<H> {
    div(h, log(h, z)?, log(h, base)?)
}

/// Returns the sine of `z`. The result for exact 0 is exact 0.
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

/// Returns the tangent of `z`. The result for exact 0 is exact 0.
pub fn tan<H: ComplexHost>(h: &H, z: H::Number) -> Res<H> {
    match h.complex_view(z) {
        _ if is_exact_zero(h, z) => Ok(z),
        ComplexView::Real(x) => flonum(h, real::to_f64(h, x)?.tan()),
        ComplexView::Complex { .. } => from_c(h, cfloat::tan(to_c(h, z)?)),
    }
}

/// Returns the arcsine of `z`. The result for exact 0 is exact 0. A real outside [-1, 1] gives a complex result.
pub fn asin<H: ComplexHost>(h: &H, z: H::Number) -> Res<H> {
    if is_exact_zero(h, z) {
        return Ok(z);
    }
    inverse(h, z, f64::asin, cfloat::asin)
}

/// Returns the arccosine of `z`. A real outside [-1, 1] gives a complex result.
pub fn acos<H: ComplexHost>(h: &H, z: H::Number) -> Res<H> {
    inverse(h, z, f64::acos, cfloat::acos)
}

fn inverse<H: ComplexHost>(h: &H, z: H::Number, real: fn(f64) -> f64, complex: fn(C) -> C) -> Res<H> {
    if let ComplexView::Real(x) = h.complex_view(z) {
        let float = real::to_f64(h, x)?;
        if float.abs() <= 1.0 || float.is_nan() {
            return flonum(h, real(float));
        }
    }
    from_c(h, complex(to_c(h, z)?))
}

/// Returns the arctangent of `z`. The result for exact 0 is exact 0. Exact `±i` gives a [`NumError::DivideByZero`] error.
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

/// Returns the angle of the point `(x, y)`. The result is exact 0 when `y` is exact 0 and `x` is positive. Exact 0 for both
/// gives a [`NumError::DivideByZero`] error.
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
        (RealView::Exact(a), RealView::Exact(b)) => {
            let (y, x, _) = exact_pair(h, a, b)?;
            (y, x)
        }
        _ => (real::to_f64(h, y)?, real::to_f64(h, x)?),
    };
    h.flonum(fy.atan2(fx))
}

/// Returns `z^power`, with the special cases that Racket specifies. An exact integer power of an exact number stays exact.
/// An exact power of 1/2 is [`sqrt`]. A real power of a real follows C's `pow`, except that a negative base with
/// a non-integer power gives a complex result. Every other case is `exp(power · log z)`.
pub fn expt<H: ComplexHost>(h: &H, z: H::Number, power: H::Number) -> Res<H> {
    if is_exact_zero(h, power) || is_exact_one(h, z) {
        return exact_int(h, 1);
    }
    if is_exact_zero(h, z) {
        return match h.complex_view(power) {
            ComplexView::Real(exponent) => match h.real_view(exponent) {
                RealView::Flonum(0.0) => flonum(h, 1.0),
                RealView::Flonum(float) if float.is_nan() => flonum(h, float),
                _ if real::sign(h, exponent) == Some(Ordering::Less) => Err(NumError::DivideByZero.into()),
                _ => Ok(z),
            },
            ComplexView::Complex { re, .. } => match real::sign(h, re) {
                Some(Ordering::Greater) => Ok(z),
                None => flonum(h, f64::NAN),
                _ => Err(NumError::DivideByZero.into()),
            },
        };
    }
    let ComplexView::Real(exponent) = h.complex_view(power) else {
        return exp(h, mul(h, power, log(h, z)?)?);
    };
    if let RealView::Exact(fraction) = h.real_view(exponent) {
        match h.rational_view(fraction) {
            RationalView::Integer(n) => return integer_power(h, z, n),
            RationalView::Ratio { num, den } if int::to_i64(h, num) == Some(1) && int::to_i64(h, den) == Some(2) => {
                return sqrt(h, z);
            }
            RationalView::Ratio { .. } => {}
        }
    }
    if let ComplexView::Real(b) = h.complex_view(z) {
        let (fb, fe) = (real::to_f64(h, b)?, real::to_f64(h, exponent)?);
        let whole = matches!(h.real_view(exponent), RealView::Flonum(float) if float.is_finite() && float.fract() == 0.0);
        if real::sign(h, b) != Some(Ordering::Less) || whole {
            return flonum(h, fb.powf(fe));
        }
    }
    exp(h, mul(h, power, log(h, z)?)?)
}

/// Returns `z^n` for an exact integer `n`, by repeated squaring.
fn integer_power<H: ComplexHost>(h: &H, z: H::Number, n: H::Int) -> Res<H> {
    if let ComplexView::Real(b) = h.complex_view(z) {
        let fraction = match h.real_view(b) {
            RealView::Flonum(float) => return flonum(h, float.powf(int::to_f64(h, n))),
            RealView::Exact(fraction) => fraction,
        };
        return match int::to_i64(h, n) {
            Some(exponent) => Ok(h.of_real(h.of_rational(rational::expt(h, fraction, exponent)?))),
            None if real::eqv(h, b, real::from_i64(h, -1)?) => exact_int(h, if int::is_even(h, n) { 1 } else { -1 }),
            // The exponent does not fit in an `i64`, so the result for any other base needs more bits than memory can hold.
            None => Err(int::too_big(h)),
        };
    }
    let Some(exponent) = int::to_i64(h, n) else {
        if is_exact(h, z) {
            return Err(int::too_big(h));
        }
        let power = h.of_real(h.of_rational(h.of_int(n)));
        return exp(h, mul(h, power, log(h, z)?)?);
    };
    let (mut result, mut base, mut left) = (exact_int(h, 1)?, z, exponent.unsigned_abs());
    while left != 0 {
        if left & 1 == 1 {
            result = mul(h, result, base)?;
        }
        left >>= 1;
        if left != 0 {
            base = mul(h, base, base)?;
        }
    }
    if exponent < 0 { div(h, exact_int(h, 1)?, result) } else { Ok(result) }
}
