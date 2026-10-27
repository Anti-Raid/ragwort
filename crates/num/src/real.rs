//! Real numbers with Racket's semantics: exact rationals and flonums. Arithmetic with a
//! flonum is inexact, except that an exact zero stays exact where Racket says so, as in
//! `(* 0 +inf.0)`. Exact and inexact numbers compare by their exact values.

use std::cmp::Ordering;
use std::hash::Hasher;

use crate::int::{self, Host, NumError};
use crate::rational::{self, RationalHost, RationalView, Round};

/// A real as the host holds it.
#[derive(Clone, Copy, Debug)]
pub enum RealView<R> {
    Exact(R),
    Flonum(f64),
}

/// A host that also holds flonums.
pub trait RealHost: RationalHost {
    /// A rational or a flonum.
    type Real: Copy;

    fn real_view(&self, x: Self::Real) -> RealView<Self::Rational>;

    fn of_rational(&self, x: Self::Rational) -> Self::Real;

    fn flonum(&self, f: f64) -> Result<Self::Real, Self::Error>;
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

/// Exact zero, which Racket keeps exact through `*` and `/`.
pub fn is_exact_zero<H: RealHost>(h: &H, x: H::Real) -> bool {
    matches!(h.real_view(x), RealView::Exact(r) if is_zero(h, r))
}

pub fn is_integer<H: RealHost>(h: &H, x: H::Real) -> bool {
    match h.real_view(x) {
        RealView::Exact(r) => rational::is_integer(h, r),
        RealView::Flonum(f) => f.is_finite() && f.fract() == 0.0,
    }
}

/// The nearest double.
pub fn to_f64<H: RealHost>(h: &H, x: H::Real) -> Result<f64, H::Error> {
    view_f64(h, h.real_view(x))
}

fn view_f64<H: RealHost>(h: &H, x: RealView<H::Rational>) -> Result<f64, H::Error> {
    match x {
        RealView::Exact(r) => rational::to_f64(h, r),
        RealView::Flonum(f) => Ok(f),
    }
}

/// `exact->inexact`
pub fn inexact<H: RealHost>(h: &H, x: H::Real) -> Res<H> {
    match h.real_view(x) {
        RealView::Exact(r) => h.flonum(rational::to_f64(h, r)?),
        RealView::Flonum(_) => Ok(x),
    }
}

/// `inexact->exact`. Infinities and NaNs have no exact value.
pub fn exact<H: RealHost>(h: &H, x: H::Real) -> Res<H> {
    match h.real_view(x) {
        RealView::Exact(_) => Ok(x),
        RealView::Flonum(f) => Ok(h.of_rational(rational::from_f64(h, f)?)),
    }
}

/// How `x` compares to zero, or `None` for NaN. Both zeros are zero.
pub fn sign<H: RealHost>(h: &H, x: H::Real) -> Option<Ordering> {
    match h.real_view(x) {
        RealView::Exact(r) => Some(rational::sign(h, r)),
        RealView::Flonum(f) => f.partial_cmp(&0.0),
    }
}

/// How `x` and `y` compare by value, or `None` if either is NaN.
pub fn compare<H: RealHost>(h: &H, x: H::Real, y: H::Real) -> Result<Option<Ordering>, H::Error> {
    Ok(match (h.real_view(x), h.real_view(y)) {
        (RealView::Exact(a), RealView::Exact(b)) => Some(rational::compare(h, a, b)?),
        (RealView::Flonum(a), RealView::Flonum(b)) => a.partial_cmp(&b),
        (RealView::Exact(a), RealView::Flonum(b)) => compare_exact(h, a, b)?,
        (RealView::Flonum(a), RealView::Exact(b)) => compare_exact(h, b, a)?.map(Ordering::reverse),
    })
}

/// `r` against `f`, exactly.
fn compare_exact<H: RealHost>(h: &H, r: H::Rational, f: f64) -> Result<Option<Ordering>, H::Error> {
    if f.is_nan() {
        return Ok(None);
    }
    if f.is_infinite() {
        return Ok(Some(if f > 0.0 { Ordering::Less } else { Ordering::Greater }));
    }
    // Integers of up to 53 bits are exact as doubles.
    if let RationalView::Integer(n) = h.rational_view(r)
        && let Some(n) = int::to_i64(h, n)
        && n.unsigned_abs() <= 1 << 53
    {
        return Ok((n as f64).partial_cmp(&f));
    }
    Ok(Some(rational::compare(h, r, rational::from_f64(h, f)?)?))
}

/// `eqv?`: the same exactness and value, where `0.0` and `-0.0` differ and NaNs are all
/// the same.
pub fn eqv<H: RealHost>(h: &H, x: H::Real, y: H::Real) -> bool {
    match (h.real_view(x), h.real_view(y)) {
        (RealView::Exact(a), RealView::Exact(b)) => rational::eqv(h, a, b),
        (RealView::Flonum(a), RealView::Flonum(b)) => a.to_bits() == b.to_bits() || a.is_nan() && b.is_nan(),
        _ => false,
    }
}

/// Feeds `x` to `state` so that [`eqv`] reals hash the same. Exact ones hash as
/// [`rational::hash`] does.
pub fn hash<H: RealHost, S: Hasher>(h: &H, x: H::Real, state: &mut S) {
    match h.real_view(x) {
        RealView::Exact(r) => rational::hash(h, r, state),
        RealView::Flonum(f) => state.write_u64(if f.is_nan() { f64::NAN.to_bits() } else { f.to_bits() }),
    }
}

pub fn neg<H: RealHost>(h: &H, x: H::Real) -> Res<H> {
    match h.real_view(x) {
        RealView::Exact(r) => Ok(h.of_rational(rational::neg(h, r)?)),
        RealView::Flonum(f) => h.flonum(-f),
    }
}

pub fn abs<H: RealHost>(h: &H, x: H::Real) -> Res<H> {
    match h.real_view(x) {
        RealView::Exact(r) => Ok(h.of_rational(rational::abs(h, r)?)),
        RealView::Flonum(f) => h.flonum(f.abs()),
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

/// Exact zero times anything is exact zero.
pub fn mul<H: RealHost>(h: &H, x: H::Real, y: H::Real) -> Res<H> {
    match (h.real_view(x), h.real_view(y)) {
        (RealView::Exact(a), RealView::Exact(b)) => Ok(h.of_rational(rational::mul(h, a, b)?)),
        (RealView::Exact(a), _) if is_zero(h, a) => Ok(x),
        (_, RealView::Exact(b)) if is_zero(h, b) => Ok(y),
        (a, b) => h.flonum(view_f64(h, a)? * view_f64(h, b)?),
    }
}

/// Dividing by exact zero is an error, and exact zero divided by anything else is exact zero.
pub fn div<H: RealHost>(h: &H, x: H::Real, y: H::Real) -> Res<H> {
    match (h.real_view(x), h.real_view(y)) {
        (_, RealView::Exact(b)) if is_zero(h, b) => Err(NumError::DivideByZero.into()),
        (RealView::Exact(a), RealView::Exact(b)) => Ok(h.of_rational(rational::div(h, a, b)?)),
        (RealView::Exact(a), _) if is_zero(h, a) => Ok(x),
        (a, b) => h.flonum(view_f64(h, a)? / view_f64(h, b)?),
    }
}

/// The larger, inexact if either is, or NaN if either is.
pub fn max<H: RealHost>(h: &H, x: H::Real, y: H::Real) -> Res<H> {
    extreme(h, x, y, Ordering::Greater)
}

/// The smaller, inexact if either is, or NaN if either is.
pub fn min<H: RealHost>(h: &H, x: H::Real, y: H::Real) -> Res<H> {
    extreme(h, x, y, Ordering::Less)
}

fn extreme<H: RealHost>(h: &H, x: H::Real, y: H::Real, want: Ordering) -> Res<H> {
    let pick = match compare(h, y, x)? {
        None => return h.flonum(f64::NAN),
        Some(o) if o == want => y,
        Some(_) => x,
    };
    if is_exact(h, x) && is_exact(h, y) { Ok(pick) } else { inexact(h, pick) }
}

/// `floor`, `ceiling`, `truncate` and `round`, which takes ties to even. Flonums stay
/// flonums, and infinities and NaN round to themselves.
pub fn round<H: RealHost>(h: &H, x: H::Real, mode: Round) -> Res<H> {
    match h.real_view(x) {
        RealView::Exact(r) => Ok(h.of_rational(h.of_int(rational::round(h, r, mode)?))),
        RealView::Flonum(f) => h.flonum(match mode {
            Round::Floor => f.floor(),
            Round::Ceiling => f.ceil(),
            Round::Truncate => f.trunc(),
            Round::Nearest => f.round_ties_even(),
        }),
    }
}

/// The numerator in lowest terms, as exact as `x`.
pub fn numerator<H: RealHost>(h: &H, x: H::Real) -> Res<H> {
    match h.real_view(x) {
        RealView::Exact(r) => Ok(h.of_rational(h.of_int(rational::numerator(h, r)))),
        RealView::Flonum(f) if f.fract() == 0.0 => Ok(x),
        RealView::Flonum(f) => {
            let n = rational::numerator(h, rational::from_f64(h, f)?);
            h.flonum(int::to_f64(h, n))
        }
    }
}

/// The positive denominator in lowest terms, as exact as `x`.
pub fn denominator<H: RealHost>(h: &H, x: H::Real) -> Res<H> {
    match h.real_view(x) {
        RealView::Exact(r) => Ok(h.of_rational(h.of_int(rational::denominator(h, r)?))),
        RealView::Flonum(f) if f.fract() == 0.0 => h.flonum(1.0),
        RealView::Flonum(f) => {
            let d = rational::denominator(h, rational::from_f64(h, f)?)?;
            h.flonum(int::to_f64(h, d))
        }
    }
}

/// `quotient`, truncating. A zero quotient is negative when the signs differ.
pub fn quotient<H: RealHost>(h: &H, x: H::Real, y: H::Real) -> Res<H> {
    integer_op(h, x, y, int::quotient, |x, y| x.is_sign_negative() != y.is_sign_negative())
}

/// `remainder`, with the dividend's sign.
pub fn remainder<H: RealHost>(h: &H, x: H::Real, y: H::Real) -> Res<H> {
    integer_op(h, x, y, int::remainder, |x, _| x.is_sign_negative())
}

/// `modulo`, with the divisor's sign.
pub fn modulo<H: RealHost>(h: &H, x: H::Real, y: H::Real) -> Res<H> {
    integer_op(h, x, y, int::modulo, |_, y| y.is_sign_negative())
}

/// An integer division of integers, exact or not. Inexact operands are worked out exactly
/// and the answer rounded once, with `negative_zero` saying the sign of a zero answer.
fn integer_op<H: RealHost>(
    h: &H,
    x: H::Real,
    y: H::Real,
    op: fn(&H, H::Int, H::Int) -> int::Res<H>,
    negative_zero: fn(f64, f64) -> bool,
) -> Res<H> {
    let integer = |v: RealView<H::Rational>| match v {
        RealView::Exact(r) => match h.rational_view(r) {
            RationalView::Integer(n) => Ok(n),
            RationalView::Ratio { .. } => Err(NumError::NotInteger.into()),
        },
        RealView::Flonum(f) if f.is_finite() && f.fract() == 0.0 => int::from_integral_f64(h, f),
        RealView::Flonum(_) => Err(NumError::NotInteger.into()),
    };
    let (vx, vy) = (h.real_view(x), h.real_view(y));
    let n = op(h, integer(vx)?, integer(vy)?)?;
    if let (RealView::Exact(_), RealView::Exact(_)) = (vx, vy) {
        return Ok(h.of_rational(h.of_int(n)));
    }
    let f = int::to_f64(h, n);
    let zero_sign = |v| view_f64(h, v);
    h.flonum(if f == 0.0 && negative_zero(zero_sign(vx)?, zero_sign(vy)?) { -0.0 } else { f })
}
