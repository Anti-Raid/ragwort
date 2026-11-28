//! Real numbers with Racket's semantics: exact rationals and flonums. Arithmetic with a
//! flonum gives a flonum. The exception is an exact zero, which stays exact where Racket specifies it, as in
//! `(* 0 +inf.0)`. An exact number and a flonum are compared by their exact values.

use std::cmp::Ordering;
use std::hash::Hasher;

use crate::int::{self, Host, NumError};
use crate::rational::{self, RationalHost, RationalView, Round};

/// A real number in the representation that the host stores.
#[derive(Clone, Copy, Debug)]
pub enum RealView<R> {
    Exact(R),
    Flonum(f64),
}

/// A host that also stores flonums.
pub trait RealHost: RationalHost {
    /// A rational or a flonum.
    type Real: Copy;

    fn real_view(&self, x: Self::Real) -> RealView<Self::Rational>;

    fn of_rational(&self, x: Self::Rational) -> Self::Real;

    fn flonum(&self, value: f64) -> Result<Self::Real, Self::Error>;
}

type Res<H> = Result<<H as RealHost>::Real, <H as Host>::Error>;

pub fn from_i64<H: RealHost>(h: &H, n: i64) -> Res<H> {
    Ok(h.of_rational(h.of_int(int::from_i64(h, n)?)))
}

pub fn is_exact<H: RealHost>(h: &H, x: H::Real) -> bool {
    matches!(h.real_view(x), RealView::Exact(_))
}

fn is_zero<H: RealHost>(h: &H, x: H::Rational) -> bool {
    rational::sign(h, x) == Ordering::Equal
}

/// Returns whether `x` is exact zero. Racket keeps an exact zero exact through `*` and `/`.
pub fn is_exact_zero<H: RealHost>(h: &H, x: H::Real) -> bool {
    matches!(h.real_view(x), RealView::Exact(fraction) if is_zero(h, fraction))
}

pub fn is_integer<H: RealHost>(h: &H, x: H::Real) -> bool {
    match h.real_view(x) {
        RealView::Exact(fraction) => rational::is_integer(h, fraction),
        RealView::Flonum(float) => float.is_finite() && float.fract() == 0.0,
    }
}

/// Returns the `f64` nearest to `x`.
pub fn to_f64<H: RealHost>(h: &H, x: H::Real) -> Result<f64, H::Error> {
    view_f64(h, h.real_view(x))
}

fn view_f64<H: RealHost>(h: &H, x: RealView<H::Rational>) -> Result<f64, H::Error> {
    match x {
        RealView::Exact(fraction) => rational::to_f64(h, fraction),
        RealView::Flonum(float) => Ok(float),
    }
}

/// Converts `x` to a flonum, as `exact->inexact` does.
pub fn inexact<H: RealHost>(h: &H, x: H::Real) -> Res<H> {
    match h.real_view(x) {
        RealView::Exact(fraction) => h.flonum(rational::to_f64(h, fraction)?),
        RealView::Flonum(_) => Ok(x),
    }
}

/// Converts `x` to an exact number, as `inexact->exact` does. An infinity or a NaN has no exact value and gives [`NumError::NoExactValue`].
pub fn exact<H: RealHost>(h: &H, x: H::Real) -> Res<H> {
    match h.real_view(x) {
        RealView::Exact(_) => Ok(x),
        RealView::Flonum(float) => Ok(h.of_rational(rational::from_f64(h, float)?)),
    }
}

/// Returns the ordering of `x` relative to zero, or `None` if `x` is NaN. Both `0.0` and `-0.0` compare equal to zero.
pub fn sign<H: RealHost>(h: &H, x: H::Real) -> Option<Ordering> {
    match h.real_view(x) {
        RealView::Exact(fraction) => Some(rational::sign(h, fraction)),
        RealView::Flonum(float) => float.partial_cmp(&0.0),
    }
}

/// Compares `x` and `y` by value. Returns `None` if either is NaN.
pub fn compare<H: RealHost>(h: &H, x: H::Real, y: H::Real) -> Result<Option<Ordering>, H::Error> {
    Ok(match (h.real_view(x), h.real_view(y)) {
        (RealView::Exact(a), RealView::Exact(b)) => Some(rational::compare(h, a, b)?),
        (RealView::Flonum(a), RealView::Flonum(b)) => a.partial_cmp(&b),
        (RealView::Exact(a), RealView::Flonum(b)) => compare_exact(h, a, b)?,
        (RealView::Flonum(a), RealView::Exact(b)) => compare_exact(h, b, a)?.map(Ordering::reverse),
    })
}

/// Compares `fraction` with `float` by their exact values. Returns `None` if `float` is NaN.
fn compare_exact<H: RealHost>(h: &H, fraction: H::Rational, float: f64) -> Result<Option<Ordering>, H::Error> {
    if float.is_nan() {
        return Ok(None);
    }
    if float.is_infinite() {
        let order = if float > 0.0 {
            Ordering::Less
        } else {
            Ordering::Greater
        };
        return Ok(Some(order));
    }
    // An integer of magnitude up to 2^53 is exact as an `f64`.
    if let RationalView::Integer(n) = h.rational_view(fraction)
        && let Some(n) = int::to_i64(h, n)
        && n.unsigned_abs() <= 1 << 53
    {
        return Ok((n as f64).partial_cmp(&float));
    }
    Ok(Some(rational::compare(h, fraction, rational::from_f64(h, float)?)?))
}

/// Implements `eqv?`. Two reals are equivalent if they have the same exactness and the same value. `0.0` and `-0.0` differ,
/// and all NaNs are equivalent.
pub fn eqv<H: RealHost>(h: &H, x: H::Real, y: H::Real) -> bool {
    match (h.real_view(x), h.real_view(y)) {
        (RealView::Exact(a), RealView::Exact(b)) => rational::eqv(h, a, b),
        (RealView::Flonum(a), RealView::Flonum(b)) => a.to_bits() == b.to_bits() || a.is_nan() && b.is_nan(),
        _ => false,
    }
}

/// Feeds `x` to `state`, so that reals that are [`eqv`] hash the same. An exact real hashes as
/// [`rational::hash`] hashes it.
pub fn hash<H: RealHost, S: Hasher>(h: &H, x: H::Real, state: &mut S) {
    match h.real_view(x) {
        RealView::Exact(fraction) => rational::hash(h, fraction, state),
        RealView::Flonum(float) => {
            let bits = if float.is_nan() {
                f64::NAN.to_bits()
            } else {
                float.to_bits()
            };
            state.write_u64(bits)
        }
    }
}

pub fn neg<H: RealHost>(h: &H, x: H::Real) -> Res<H> {
    match h.real_view(x) {
        RealView::Exact(fraction) => Ok(h.of_rational(rational::neg(h, fraction)?)),
        RealView::Flonum(float) => h.flonum(-float),
    }
}

pub fn abs<H: RealHost>(h: &H, x: H::Real) -> Res<H> {
    match h.real_view(x) {
        RealView::Exact(fraction) => Ok(h.of_rational(rational::abs(h, fraction)?)),
        RealView::Flonum(float) => h.flonum(float.abs()),
    }
}

pub fn add<H: RealHost>(h: &H, x: H::Real, y: H::Real) -> Res<H> {
    match (h.real_view(x), h.real_view(y)) {
        (RealView::Exact(a), RealView::Exact(b)) => Ok(h.of_rational(rational::add(h, a, b)?)),
        (a, b) => h.flonum(view_f64(h, a)? + view_f64(h, b)?),
    }
}

pub fn sub<H: RealHost>(h: &H, x: H::Real, y: H::Real) -> Res<H> {
    match (h.real_view(x), h.real_view(y)) {
        (RealView::Exact(a), RealView::Exact(b)) => Ok(h.of_rational(rational::sub(h, a, b)?)),
        (a, b) => h.flonum(view_f64(h, a)? - view_f64(h, b)?),
    }
}

/// Returns `x * y`. Exact zero times any number is exact zero.
pub fn mul<H: RealHost>(h: &H, x: H::Real, y: H::Real) -> Res<H> {
    match (h.real_view(x), h.real_view(y)) {
        (RealView::Exact(a), RealView::Exact(b)) => Ok(h.of_rational(rational::mul(h, a, b)?)),
        (RealView::Exact(a), _) if is_zero(h, a) => Ok(x),
        (_, RealView::Exact(b)) if is_zero(h, b) => Ok(y),
        (a, b) => h.flonum(view_f64(h, a)? * view_f64(h, b)?),
    }
}

/// Returns `x / y`. Division by exact zero is an error. Exact zero divided by any other number is exact zero.
pub fn div<H: RealHost>(h: &H, x: H::Real, y: H::Real) -> Res<H> {
    match (h.real_view(x), h.real_view(y)) {
        (_, RealView::Exact(b)) if is_zero(h, b) => Err(NumError::DivideByZero.into()),
        (RealView::Exact(a), RealView::Exact(b)) => Ok(h.of_rational(rational::div(h, a, b)?)),
        (RealView::Exact(a), _) if is_zero(h, a) => Ok(x),
        (a, b) => h.flonum(view_f64(h, a)? / view_f64(h, b)?),
    }
}

/// Returns the larger of `x` and `y`. The result is inexact if either operand is inexact, and NaN if either operand is NaN.
pub fn max<H: RealHost>(h: &H, x: H::Real, y: H::Real) -> Res<H> {
    extreme(h, x, y, Ordering::Greater)
}

/// Returns the smaller of `x` and `y`. The result is inexact if either operand is inexact, and NaN if either operand is NaN.
pub fn min<H: RealHost>(h: &H, x: H::Real, y: H::Real) -> Res<H> {
    extreme(h, x, y, Ordering::Less)
}

fn extreme<H: RealHost>(h: &H, x: H::Real, y: H::Real, want: Ordering) -> Res<H> {
    let pick = match compare(h, y, x)? {
        None => return h.flonum(f64::NAN),
        Some(order) if order == want => y,
        Some(_) => x,
    };
    if is_exact(h, x) && is_exact(h, y) {
        Ok(pick)
    } else {
        inexact(h, pick)
    }
}

/// Rounds `x` in the direction that `mode` selects: `floor`, `ceiling`, `truncate` or `round`, which rounds ties to even.
/// A flonum stays a flonum, and infinities and NaN round to themselves.
pub fn round<H: RealHost>(h: &H, x: H::Real, mode: Round) -> Res<H> {
    match h.real_view(x) {
        RealView::Exact(fraction) => Ok(h.of_rational(h.of_int(rational::round(h, fraction, mode)?))),
        RealView::Flonum(float) => h.flonum(match mode {
            Round::Floor => float.floor(),
            Round::Ceiling => float.ceil(),
            Round::Truncate => float.trunc(),
            Round::Nearest => float.round_ties_even(),
        }),
    }
}

/// Returns the numerator of `x` in lowest terms, with the exactness of `x`.
pub fn numerator<H: RealHost>(h: &H, x: H::Real) -> Res<H> {
    match h.real_view(x) {
        RealView::Exact(fraction) => Ok(h.of_rational(h.of_int(rational::numerator(h, fraction)))),
        RealView::Flonum(float) if float.fract() == 0.0 => Ok(x),
        RealView::Flonum(float) => {
            let num = rational::numerator(h, rational::from_f64(h, float)?);
            h.flonum(int::to_f64(h, num))
        }
    }
}

/// Returns the positive denominator of `x` in lowest terms, with the exactness of `x`.
pub fn denominator<H: RealHost>(h: &H, x: H::Real) -> Res<H> {
    match h.real_view(x) {
        RealView::Exact(fraction) => Ok(h.of_rational(h.of_int(rational::denominator(h, fraction)?))),
        RealView::Flonum(float) if float.fract() == 0.0 => h.flonum(1.0),
        RealView::Flonum(float) => {
            let den = rational::denominator(h, rational::from_f64(h, float)?)?;
            h.flonum(int::to_f64(h, den))
        }
    }
}

/// Implements `quotient`, which truncates. An inexact zero quotient is `-0.0` when the signs of the operands differ.
pub fn quotient<H: RealHost>(h: &H, x: H::Real, y: H::Real) -> Res<H> {
    integer_op(h, x, y, int::quotient, |x, y| x.is_sign_negative() != y.is_sign_negative())
}

/// Implements `remainder`. The result has the sign of the dividend.
pub fn remainder<H: RealHost>(h: &H, x: H::Real, y: H::Real) -> Res<H> {
    integer_op(h, x, y, int::remainder, |x, _| x.is_sign_negative())
}

/// Implements `modulo`. The result has the sign of the divisor.
pub fn modulo<H: RealHost>(h: &H, x: H::Real, y: H::Real) -> Res<H> {
    integer_op(h, x, y, int::modulo, |_, y| y.is_sign_negative())
}

/// Implements `floor-quotient`, which rounds down. An inexact zero quotient is `-0.0` when the signs of the operands differ.
pub fn floor_quotient<H: RealHost>(h: &H, x: H::Real, y: H::Real) -> Res<H> {
    integer_op(h, x, y, int::floor_quotient, |x, y| x.is_sign_negative() != y.is_sign_negative())
}

/// Applies the integer division `op` to `x` and `y`, which must be integers, exact or inexact. With an inexact operand, the division is done on exact integers
/// and the result is rounded once to a flonum. `negative_zero` receives the operands as `f64` and returns whether a zero result is `-0.0`.
fn integer_op<H: RealHost>(
    h: &H,
    x: H::Real,
    y: H::Real,
    op: fn(&H, H::Int, H::Int) -> int::Res<H>,
    negative_zero: fn(f64, f64) -> bool,
) -> Res<H> {
    #[inline(always)]
    fn integer<H: RealHost>(h: &H, view: RealView<H::Rational>) -> int::Res<H> {
        match view {
            RealView::Exact(fraction) => match h.rational_view(fraction) {
                RationalView::Integer(n) => Ok(n),
                RationalView::Ratio { .. } => Err(NumError::NotInteger.into()),
            },
            RealView::Flonum(float) if float.is_finite() && float.fract() == 0.0 => int::from_integral_f64(h, float),
            RealView::Flonum(_) => Err(NumError::NotInteger.into()),
        }
    }
    let (vx, vy) = (h.real_view(x), h.real_view(y));
    let n = op(h, integer(h, vx)?, integer(h, vy)?)?;
    if let (RealView::Exact(_), RealView::Exact(_)) = (vx, vy) {
        return Ok(h.of_rational(h.of_int(n)));
    }
    let float = int::to_f64(h, n);
    let signed = if float == 0.0 && negative_zero(view_f64(h, vx)?, view_f64(h, vy)?) {
        -0.0
    } else {
        float
    };
    h.flonum(signed)
}

/// Returns `x` written in `radix`, in a form that a reader reads back as the same number. `radix` must be 10 or a power of two.
/// In radix 10, a flonum is written with the shortest digits that round-trip. In a power-of-two radix, a flonum is written exactly,
/// because a binary fraction terminates in such a radix.
pub fn to_string<H: RealHost>(h: &H, x: H::Real, radix: u32) -> Result<String, H::Error> {
    assert!(radix == 10 || radix.is_power_of_two() && (2..=32).contains(&radix), "radix 10 or a power of two");
    match h.real_view(x) {
        RealView::Exact(fraction) => rational::to_string(h, fraction, radix),
        RealView::Flonum(float) if float.is_nan() => Ok("+nan.0".into()),
        RealView::Flonum(float) if float.is_infinite() => {
            let text = if float > 0.0 {
                "+inf.0"
            } else {
                "-inf.0"
            };
            Ok(text.into())
        }
        RealView::Flonum(float) if radix == 10 => Ok(format!("{float:?}")),
        RealView::Flonum(float) => flonum_in_radix(h, float, radix),
    }
}

/// Returns the exact digits of `float` in `radix`. `float` must be finite, and `radix` must be a power of two.
fn flonum_in_radix<H: RealHost>(h: &H, float: f64, radix: u32) -> Result<String, H::Error> {
    let sign = if float.is_sign_negative() {
        "-"
    } else {
        ""
    };
    let bits = float.abs().to_bits();
    let (exponent, fraction) = ((bits >> 52) as i64, bits & ((1 << 52) - 1));
    // `|float|` is `mantissa · 2^scale`.
    let (mantissa, scale) = if exponent == 0 {
        (fraction, -1074)
    } else {
        (fraction | 1 << 52, exponent - 1075)
    };
    if mantissa == 0 {
        return Ok(format!("{sign}0.0"));
    }
    if scale >= 0 {
        let n = int::arithmetic_shift(h, int::from_u64(h, mantissa)?, scale)?;
        return Ok(format!("{sign}{}.0", int::to_string(h, n, radix)?));
    }
    // The radix point is `places` digits from the right, and each digit holds `log` bits.
    let log = radix.trailing_zeros() as i64;
    let places = (-scale + log - 1) / log;
    let n = int::arithmetic_shift(h, int::from_u64(h, mantissa)?, places * log + scale)?;
    let digits = int::to_string(h, n, radix)?;
    let digits = format!("{}{digits}", "0".repeat((places as usize + 1).saturating_sub(digits.len())));
    let (whole, fraction) = digits.split_at(digits.len() - places as usize);
    let fraction = fraction.trim_end_matches('0');
    let shown = if fraction.is_empty() {
        "0"
    } else {
        fraction
    };
    Ok(format!("{sign}{whole}.{}", shown))
}
