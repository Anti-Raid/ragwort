//! Exact integers with Racket's semantics, on any heap that implements [`Host`].
//!
//! Results are normalized. An integer that the host can hold as a small integer is never a big integer, and a big integer
//! never has high-order zero digits. Every function is generic over the host, so a host's small-integer path compiles down
//! to plain `i64` arithmetic.

use std::cmp::Ordering;
use std::hash::Hasher;

use crate::bigint::{self, DIGIT_BITS, Digit, Digits, RWDigits};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NumError {
    DivideByZero,
    /// An infinity or a NaN was converted to an exact number. Neither has an exact value.
    NoExactValue,
    /// An integer operation received a number that is not an integer, such as `1.5`.
    NotInteger,
}

/// An integer in the representation that the host stores.
#[derive(Clone, Copy, Debug)]
pub enum IntView<'a> {
    Small(i64),
    /// The magnitude of a value that [`Host::small`] cannot hold. The digits have no high-order zeros.
    Big { negative: bool, digits: Digits<'a> },
}

/// The heap that stores integers. The library reads integers through [`Host::view`] and creates them with
/// [`Host::small`] and [`Host::big`]. The library keeps results normalized.
pub trait Host {
    type Int: Copy;
    type Error: From<NumError>;

    fn view(&self, x: Self::Int) -> IntView<'_>;

    /// Returns `n` as a small integer, or `None` if the host can hold `n` only as a big integer.
    fn small(&self, n: i64) -> Option<Self::Int>;

    /// Allocates a big integer with `len` zeroed digits and calls `init` to fill them in. `init` returns the number of
    /// digits to keep. Views of other integers stay valid while `init` runs.
    fn big(&self, negative: bool, len: usize, init: impl FnOnce(RWDigits<'_>) -> usize) -> Result<Self::Int, Self::Error>;

    /// Called before the library performs about `work` digit operations. Returning an error aborts the operation.
    #[inline]
    fn charge(&self, work: u64) -> Result<(), Self::Error> {
        let _ = work;
        Ok(())
    }

    /// Called before the library allocates `digits` digits of temporary memory. The memory is freed before the
    /// operation returns.
    #[inline]
    fn scratch(&self, digits: usize) -> Result<(), Self::Error> {
        let _ = digits;
        Ok(())
    }

    /// Returns `x + y` if the host can compute it directly on its small representation, or `None` to
    /// take the general path.
    #[inline]
    fn small_add(&self, x: Self::Int, y: Self::Int) -> Option<Self::Int> {
        let _ = (x, y);
        None
    }

    #[inline]
    fn small_sub(&self, x: Self::Int, y: Self::Int) -> Option<Self::Int> {
        let _ = (x, y);
        None
    }

    #[inline]
    fn small_mul(&self, x: Self::Int, y: Self::Int) -> Option<Self::Int> {
        let _ = (x, y);
        None
    }
}

pub(crate) type Res<H> = Result<<H as Host>::Int, <H as Host>::Error>;
type Both<H> = Result<(Option<<H as Host>::Int>, Option<<H as Host>::Int>), <H as Host>::Error>;

/// An integer as a sign and a magnitude. The magnitude of a small integer is stored in a one-digit buffer that the caller provides.
#[derive(Clone, Copy)]
struct Signed<'a> {
    negative: bool,
    digits: Digits<'a>,
}

impl<'a> Signed<'a> {
    #[inline]
    fn new(view: IntView<'a>, buf: &'a mut [Digit; 1]) -> Self {
        match view {
            IntView::Small(n) => {
                buf[0] = n.unsigned_abs();
                Self { negative: n < 0, digits: Digits::of_mut(buf).normalize() }
            }
            IntView::Big { negative, digits } => {
                debug_assert_eq!(digits.normalize().len(), digits.len(), "big integers have no high zero digits");
                Self { negative, digits }
            }
        }
    }

    fn neg(self) -> Self {
        Self { negative: !self.negative && !self.digits.is_zero(), ..self }
    }
}

/// Results of at most this many digits are computed on the stack. So a result that turns out to be
/// small never allocates.
const STACK: usize = 4;

/// Returns the integer that `init` computes into a buffer of `len` digits. The result is normalized.
#[inline]
fn make<H: Host>(h: &H, negative: bool, len: usize, init: impl FnOnce(RWDigits<'_>)) -> Res<H> {
    if len <= STACK {
        let mut buf = [0; STACK];
        init(RWDigits::new(&mut buf[..len]));
        return from_digits(h, negative, Digits::of_mut(&mut buf[..len]));
    }
    // A result computed in many digits can still be short, for example when subtracting nearly equal numbers.
    let (mut short, mut kept) = (None, 0);
    let x = h.big(negative, len, |mut z| {
        init(z.reborrow());
        let digits = z.read().normalize();
        (short, kept) = (to_small(negative, digits), digits.len());
        kept
    })?;
    match short.and_then(|n| h.small(n)) {
        Some(small) => Ok(small),
        // Fewer than half of the digits were kept. Copy the result into an allocation of its own size. Otherwise the unused rest of
        // this allocation, up to a whole run of pages, would stay allocated with it. The copy costs less than computing the result did.
        None if kept * 2 < len => match h.view(x) {
            IntView::Big { negative, digits } => from_digits(h, negative, digits),
            IntView::Small(_) => Ok(x),
        },
        None => Ok(x),
    }
}

/// Like [`make`], for results that keep at least `len - 1` digits. A result that needs the heap
/// then never fits a small integer, so the check for a small result is skipped.
#[inline]
fn make_long<H: Host>(h: &H, negative: bool, len: usize, init: impl FnOnce(RWDigits<'_>)) -> Res<H> {
    if len <= STACK {
        return make(h, negative, len, init);
    }
    h.big(negative, len, |mut z| {
        init(z.reborrow());
        let kept = z.read().normalize().len();
        debug_assert!(kept + 1 >= len, "{kept} digits of {len} kept");
        kept
    })
}

/// Returns the value as an `i64` if it fits. `digits` must be normalized.
#[inline]
fn to_small(negative: bool, digits: Digits<'_>) -> Option<i64> {
    debug_assert_eq!(digits.normalize().len(), digits.len());
    match digits.len() {
        0 => Some(0),
        1 if negative => if digits.at(0) <= 1 << 63 {
            Some((digits.at(0) as i64).wrapping_neg())
        } else {
            None
        },
        1 => i64::try_from(digits.at(0)).ok(),
        _ => None,
    }
}

pub fn from_digits<H: Host>(h: &H, negative: bool, digits: Digits<'_>) -> Res<H> {
    let digits = digits.normalize();
    if let Some(n) = to_small(negative, digits)
        && let Some(x) = h.small(n)
    {
        return Ok(x);
    }
    h.big(negative && !digits.is_zero(), digits.len(), |mut z| {
        z.copy_from(digits);
        digits.len()
    })
}

#[inline]
pub fn from_i64<H: Host>(h: &H, n: i64) -> Res<H> {
    match h.small(n) {
        Some(x) => Ok(x),
        None => from_digits(h, n < 0, Digits::of_mut(&mut [n.unsigned_abs()])),
    }
}

#[inline]
pub fn from_u64<H: Host>(h: &H, n: u64) -> Res<H> {
    match i64::try_from(n).ok().and_then(|n| h.small(n)) {
        Some(x) => Ok(x),
        None => from_digits(h, false, Digits::of_mut(&mut [n])),
    }
}

#[inline]
pub fn from_i128<H: Host>(h: &H, n: i128) -> Res<H> {
    if let Ok(small) = i64::try_from(n)
        && let Some(x) = h.small(small)
    {
        return Ok(x);
    }
    let magnitude = n.unsigned_abs();
    from_digits(h, n < 0, Digits::of_mut(&mut [magnitude as Digit, (magnitude >> DIGIT_BITS) as Digit]))
}

pub fn to_u64<H: Host>(h: &H, x: H::Int) -> Option<u64> {
    match h.view(x) {
        IntView::Small(n) => u64::try_from(n).ok(),
        IntView::Big { negative, digits } => if !negative && digits.len() == 1 {
            Some(digits.at(0))
        } else {
            None
        },
    }
}

pub fn to_i64<H: Host>(h: &H, x: H::Int) -> Option<i64> {
    match h.view(x) {
        IntView::Small(n) => Some(n),
        IntView::Big { negative, digits } => to_small(negative, digits),
    }
}

/// Returns the exact integer value of `value`, which must be finite and integral.
pub fn from_integral_f64<H: Host>(h: &H, value: f64) -> Res<H> {
    debug_assert!(value.is_finite() && value.fract() == 0.0, "{value} isn't an integer");
    if value.abs() < -(i64::MIN as f64) {
        return from_i64(h, value as i64);
    }
    let bits = value.to_bits();
    let mantissa = bits & ((1 << 52) - 1) | 1 << 52;
    let shift = ((bits >> 52) & 0x7ff) as usize - 1075;
    make_long(h, value < 0.0, shift / DIGIT_BITS + 2, |z| bigint::left_shift(z, Digits::of_mut(&mut [mantissa]), shift))
}

/// Returns the `f64` nearest to `x`, with ties to even.
pub fn to_f64<H: Host>(h: &H, x: H::Int) -> f64 {
    match h.view(x) {
        IntView::Small(n) => n as f64,
        IntView::Big { negative, digits } => {
            let value = bigint::to_f64(digits);
            if negative {
                -value
            } else {
                value
            }
        }
    }
}

pub fn compare<H: Host>(h: &H, x: H::Int, y: H::Int) -> Ordering {
    let (mut bx, mut by) = ([0], [0]);
    match (h.view(x), h.view(y)) {
        (IntView::Small(a), IntView::Small(b)) => a.cmp(&b),
        (x, y) => compare_signed(Signed::new(x, &mut bx), Signed::new(y, &mut by)),
    }
}

fn compare_signed(x: Signed<'_>, y: Signed<'_>) -> Ordering {
    match (x.negative, y.negative) {
        (false, true) => Ordering::Greater,
        (true, false) => Ordering::Less,
        (false, false) => bigint::compare(x.digits, y.digits),
        (true, true) => bigint::compare(y.digits, x.digits),
    }
}

/// Feeds the value of `x` to `state`. Equal integers hash the same in either representation.
/// The hasher receives every digit, so a keyed hasher keeps collisions unpredictable.
#[inline]
pub fn hash<H: Host, S: Hasher>(h: &H, x: H::Int, state: &mut S) {
    match h.view(x) {
        IntView::Small(n) => state.write_i64(n),
        IntView::Big { negative, digits } => match to_small(negative, digits) {
            Some(n) => state.write_i64(n),
            None => {
                for i in 0..digits.len() {
                    state.write_u64(digits.at(i));
                }
                state.write_u8(negative as u8);
                state.write_usize(digits.len());
            }
        },
    }
}

/// Returns the ordering of `x` relative to zero.
pub fn sign<H: Host>(h: &H, x: H::Int) -> Ordering {
    match h.view(x) {
        IntView::Small(n) => n.cmp(&0),
        IntView::Big { negative: true, .. } => Ordering::Less,
        IntView::Big { negative: false, .. } => Ordering::Greater,
    }
}

pub fn is_even<H: Host>(h: &H, x: H::Int) -> bool {
    match h.view(x) {
        IntView::Small(n) => n & 1 == 0,
        IntView::Big { digits, .. } => digits.get(0) & 1 == 0,
    }
}

#[inline]
pub fn add<H: Host>(h: &H, x: H::Int, y: H::Int) -> Res<H> {
    if let Some(z) = h.small_add(x, y) {
        return Ok(z);
    }
    add_slow(h, x, y)
}

fn add_slow<H: Host>(h: &H, x: H::Int, y: H::Int) -> Res<H> {
    let (mut bx, mut by) = ([0], [0]);
    match (h.view(x), h.view(y)) {
        (IntView::Small(a), IntView::Small(b)) => from_i128(h, a as i128 + b as i128),
        (x, y) => add_signed(h, Signed::new(x, &mut bx), Signed::new(y, &mut by)),
    }
}

#[inline]
pub fn sub<H: Host>(h: &H, x: H::Int, y: H::Int) -> Res<H> {
    if let Some(z) = h.small_sub(x, y) {
        return Ok(z);
    }
    sub_slow(h, x, y)
}

fn sub_slow<H: Host>(h: &H, x: H::Int, y: H::Int) -> Res<H> {
    let (mut bx, mut by) = ([0], [0]);
    match (h.view(x), h.view(y)) {
        (IntView::Small(a), IntView::Small(b)) => from_i128(h, a as i128 - b as i128),
        (x, y) => add_signed(h, Signed::new(x, &mut bx), Signed::new(y, &mut by).neg()),
    }
}

fn add_signed<H: Host>(h: &H, x: Signed<'_>, y: Signed<'_>) -> Res<H> {
    let (xd, yd) = (x.digits, y.digits);
    h.charge(xd.len().max(yd.len()) as u64)?;
    if x.negative == y.negative {
        return make_long(h, x.negative, xd.len().max(yd.len()) + 1, |z| bigint::add(z, xd, yd));
    }
    match bigint::compare(xd, yd) {
        Ordering::Less => make(h, y.negative, yd.len(), |z| bigint::subtract(z, yd, xd)),
        _ => make(h, x.negative, xd.len(), |z| bigint::subtract(z, xd, yd)),
    }
}

#[inline]
pub fn mul<H: Host>(h: &H, x: H::Int, y: H::Int) -> Res<H> {
    if let Some(z) = h.small_mul(x, y) {
        return Ok(z);
    }
    mul_slow(h, x, y)
}

fn mul_slow<H: Host>(h: &H, x: H::Int, y: H::Int) -> Res<H> {
    let (mut bx, mut by) = ([0], [0]);
    match (h.view(x), h.view(y)) {
        (IntView::Small(a), IntView::Small(b)) => from_i128(h, a as i128 * b as i128),
        (x, y) => {
            let (x, y) = (Signed::new(x, &mut bx), Signed::new(y, &mut by));
            h.charge(x.digits.len() as u64 * y.digits.len() as u64)?;
            let len = x.digits.len() + y.digits.len();
            make_long(h, x.negative != y.negative, len, |z| bigint::multiply(z, x.digits, y.digits))
        }
    }
}

pub fn neg<H: Host>(h: &H, x: H::Int) -> Res<H> {
    match h.view(x) {
        IntView::Small(n) => from_i128(h, -(n as i128)),
        IntView::Big { negative, digits } => {
            h.charge(digits.len() as u64)?;
            from_digits(h, !negative, digits)
        }
    }
}

pub fn abs<H: Host>(h: &H, x: H::Int) -> Res<H> {
    match sign(h, x) {
        Ordering::Less => neg(h, x),
        _ => Ok(x),
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Rounding {
    /// Rounds the quotient toward zero, as `quotient` and `remainder` do. The remainder has the sign of the dividend.
    Truncate,
    /// Rounds the quotient down, as `floor/` does. The remainder is `modulo`, which has the sign of the divisor.
    Floor,
}

/// Returns the quotient and the remainder of `x / y`. The quotient is computed only if `want_q` is set and the remainder only if `want_r` is set. The other is `None`.
pub fn divide<H: Host>(
    h: &H,
    x: H::Int,
    y: H::Int,
    rounding: Rounding,
    want_q: bool,
    want_r: bool,
) -> Both<H> {
    let floor = rounding == Rounding::Floor;
    let (mut bx, mut by) = ([0], [0]);
    let (xs, ys) = match (h.view(x), h.view(y)) {
        (_, IntView::Small(0)) => return Err(NumError::DivideByZero.into()),
        (IntView::Small(a), IntView::Small(b)) => {
            let (a, b) = (a as i128, b as i128);
            let (mut quotient, mut remainder) = (a / b, a % b);
            if floor && remainder != 0 && (remainder < 0) != (b < 0) {
                quotient -= 1;
                remainder += b;
            }
            let quotient = if want_q {
                Some(from_i128(h, quotient)?)
            } else {
                None
            };
            let remainder = if want_r {
                Some(from_i128(h, remainder)?)
            } else {
                None
            };
            return Ok((quotient, remainder));
        }
        (xv, yv) => (Signed::new(xv, &mut bx), Signed::new(yv, &mut by)),
    };
    let (xd, yd) = (xs.digits, ys.digits);
    let q_negative = xs.negative != ys.negative;
    // Flooring needs an adjustment when the remainder is nonzero and the signs of the operands differ. The quotient is one less than
    // the truncated quotient, and the remainder becomes `|y| - |remainder|` with the sign of `y`.
    let adjust = floor && q_negative;
    h.charge((xd.len().saturating_sub(yd.len()) as u64 + 1) * yd.len() as u64)?;

    if bigint::compare(xd, yd) == Ordering::Less {
        let (quotient, remainder) = if !adjust || xd.is_zero() {
            (from_i64(h, 0)?, x)
        } else {
            (from_i64(h, -1)?, make(h, ys.negative, yd.len(), |z| bigint::subtract(z, yd, xd))?)
        };
        let kept_quotient = if want_q {
            Some(quotient)
        } else {
            None
        };
        let kept_remainder = if want_r {
            Some(remainder)
        } else {
            None
        };
        return Ok((kept_quotient, kept_remainder));
    }

    if yd.len() == 1 {
        let divisor = yd.at(0);
        let mut rem = 0;
        let quotient = if want_q {
            Some(make(h, q_negative, xd.len(), |mut z| {
                rem = bigint::divide_single(Some(z.reborrow()), xd, divisor);
                if adjust && rem != 0 {
                    bigint::add_digit(z, 1);
                }
            })?)
        } else {
            rem = bigint::divide_single(None, xd, divisor);
            None
        };
        let remainder = match (want_r, adjust && rem != 0) {
            (false, _) => None,
            (true, true) => Some(from_digits(h, ys.negative, Digits::of_mut(&mut [divisor - rem]))?),
            (true, false) => Some(from_digits(h, xs.negative, Digits::of_mut(&mut [rem]))?),
        };
        return Ok((quotient, remainder));
    }

    // Reserve one more quotient digit than the division needs, to hold the carry from the adjustment.
    let (q_len, r_len) = (xd.len() - yd.len() + 2, yd.len());
    let len = q_len + r_len + bigint::divide_scratch(xd, yd);
    h.scratch(len)?;
    let mut buf = vec![0; len];
    let (quotient_digits, rest) = buf.split_at_mut(q_len);
    let (remainder_digits, scratch) = rest.split_at_mut(r_len);
    let q_out = if want_q {
        Some(RWDigits::new(&mut quotient_digits[..q_len - 1]))
    } else {
        None
    };
    bigint::divide(q_out, Some(RWDigits::new(remainder_digits)), xd, yd, RWDigits::new(scratch));
    let adjust = adjust && !Digits::of_mut(remainder_digits).is_zero();
    let quotient = if want_q {
        if adjust {
            bigint::add_digit(RWDigits::new(quotient_digits), 1);
        }
        Some(from_digits(h, q_negative, Digits::of_mut(quotient_digits))?)
    } else {
        None
    };
    let remainder = match (want_r, adjust) {
        (false, _) => None,
        (true, true) => Some(make(h, ys.negative, r_len, |z| bigint::subtract(z, yd, Digits::of_mut(remainder_digits)))?),
        (true, false) => Some(from_digits(h, xs.negative, Digits::of_mut(remainder_digits))?),
    };
    Ok((quotient, remainder))
}

pub fn quotient<H: Host>(h: &H, x: H::Int, y: H::Int) -> Res<H> {
    Ok(divide(h, x, y, Rounding::Truncate, true, false)?.0.expect("asked for the quotient"))
}

pub fn remainder<H: Host>(h: &H, x: H::Int, y: H::Int) -> Res<H> {
    Ok(divide(h, x, y, Rounding::Truncate, false, true)?.1.expect("asked for the remainder"))
}

pub fn modulo<H: Host>(h: &H, x: H::Int, y: H::Int) -> Res<H> {
    Ok(divide(h, x, y, Rounding::Floor, false, true)?.1.expect("asked for the remainder"))
}

pub fn quotient_remainder<H: Host>(h: &H, x: H::Int, y: H::Int) -> Result<(H::Int, H::Int), H::Error> {
    let (quotient, remainder) = divide(h, x, y, Rounding::Truncate, true, true)?;
    Ok((quotient.expect("asked for the quotient"), remainder.expect("asked for the remainder")))
}

pub fn floor_quotient<H: Host>(h: &H, x: H::Int, y: H::Int) -> Res<H> {
    Ok(divide(h, x, y, Rounding::Floor, true, false)?.0.expect("asked for the quotient"))
}

fn gcd_u64(mut a: u64, mut b: u64) -> u64 {
    if a == 0 || b == 0 {
        return a | b;
    }
    let shift = (a | b).trailing_zeros();
    a >>= a.trailing_zeros();
    loop {
        b >>= b.trailing_zeros();
        if a > b {
            (a, b) = (b, a);
        }
        b -= a;
        if b == 0 {
            return a << shift;
        }
    }
}

/// Returns the greatest common divisor of `x` and `y`, which is never negative.
pub fn gcd<H: Host>(h: &H, x: H::Int, y: H::Int) -> Res<H> {
    let (mut bx, mut by) = ([0], [0]);
    let (x, y) = match (h.view(x), h.view(y)) {
        (IntView::Small(a), IntView::Small(b)) => return from_u64(h, gcd_u64(a.unsigned_abs(), b.unsigned_abs())),
        (xv, yv) => (Signed::new(xv, &mut bx).digits, Signed::new(yv, &mut by).digits),
    };
    let (x, y) = if bigint::compare(x, y) == Ordering::Less {
        (y, x)
    } else {
        (x, y)
    };
    if y.is_zero() {
        return from_digits(h, false, x);
    }
    // Euclid's algorithm. Three buffers rotate through the roles of `a`, `b` and `a mod b`.
    let len = x.len() + 1;
    h.scratch(3 * len + bigint::divide_scratch(x, y))?;
    let (mut a, mut b, mut remainder) = (x.iter().collect::<Vec<_>>(), y.iter().collect::<Vec<_>>(), vec![0; len]);
    let mut scratch = vec![0; bigint::divide_scratch(x, y)];
    loop {
        let (ad, bd) = (Digits::of_mut(&mut a).normalize(), Digits::of_mut(&mut b).normalize());
        if bd.is_zero() {
            return from_digits(h, false, ad);
        }
        if ad.len() == 1 {
            return from_u64(h, gcd_u64(ad.at(0), bd.get(0)));
        }
        h.charge(bigint::divide_cost(ad, bd))?;
        let bn = bd.len();
        bigint::divide(None, Some(RWDigits::new(&mut remainder[..bn])), ad, bd, RWDigits::new(&mut scratch));
        remainder[bn..].fill(0);
        std::mem::swap(&mut a, &mut b);
        std::mem::swap(&mut b, &mut remainder);
    }
}

/// Returns the least common multiple of `x` and `y`, which is never negative.
pub fn lcm<H: Host>(h: &H, x: H::Int, y: H::Int) -> Res<H> {
    if sign(h, x) == Ordering::Equal || sign(h, y) == Ordering::Equal {
        return from_i64(h, 0);
    }
    let divisor = gcd(h, x, y)?;
    let x = quotient(h, x, divisor)?;
    abs(h, mul(h, x, y)?)
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Bitwise {
    And,
    Or,
    Xor,
}

pub fn bitwise_and<H: Host>(h: &H, x: H::Int, y: H::Int) -> Res<H> {
    bitwise(h, x, y, Bitwise::And)
}

pub fn bitwise_or<H: Host>(h: &H, x: H::Int, y: H::Int) -> Res<H> {
    bitwise(h, x, y, Bitwise::Or)
}

pub fn bitwise_xor<H: Host>(h: &H, x: H::Int, y: H::Int) -> Res<H> {
    bitwise(h, x, y, Bitwise::Xor)
}

/// Applies `op` to `x` and `y` as two's-complement integers of unlimited width.
fn bitwise<H: Host>(h: &H, x: H::Int, y: H::Int, op: Bitwise) -> Res<H> {
    let (mut bx, mut by) = ([0], [0]);
    let (x, y) = match (h.view(x), h.view(y)) {
        (IntView::Small(a), IntView::Small(b)) => {
            return from_i64(h, match op {
                Bitwise::And => a & b,
                Bitwise::Or => a | b,
                Bitwise::Xor => a ^ b,
            });
        }
        (xv, yv) => (Signed::new(xv, &mut bx), Signed::new(yv, &mut by)),
    };
    // The digit functions take the positive operand first.
    let (x, y) = if x.negative && !y.negative {
        (y, x)
    } else {
        (x, y)
    };
    let (xd, yd) = (x.digits, y.digits);
    h.charge(xd.len().max(yd.len()) as u64)?;
    type Op = fn(RWDigits<'_>, Digits<'_>, Digits<'_>);
    type Len = fn(Digits<'_>, Digits<'_>) -> usize;
    let (function, len, negative): (Op, Len, bool) = match (op, x.negative, y.negative) {
        (Bitwise::And, false, false) => (bigint::and_pos_pos, bigint::and_pos_pos_len, false),
        (Bitwise::And, false, true) => (bigint::and_pos_neg, bigint::and_pos_neg_len, false),
        (Bitwise::And, _, _) => (bigint::and_neg_neg, bigint::and_neg_neg_len, true),
        (Bitwise::Or, false, false) => (bigint::or_pos_pos, bigint::or_pos_pos_len, false),
        (Bitwise::Or, false, true) => (bigint::or_pos_neg, bigint::or_pos_neg_len, true),
        (Bitwise::Or, _, _) => (bigint::or_neg_neg, bigint::or_neg_neg_len, true),
        (Bitwise::Xor, false, false) => (bigint::xor_pos_pos, bigint::xor_pos_pos_len, false),
        (Bitwise::Xor, false, true) => (bigint::xor_pos_neg, bigint::xor_pos_neg_len, true),
        (Bitwise::Xor, _, _) => (bigint::xor_neg_neg, bigint::xor_neg_neg_len, false),
    };
    make(h, negative, len(xd, yd), |z| function(z, xd, yd))
}

/// Returns the bitwise complement of `x`, which is `-x - 1`.
pub fn bitwise_not<H: Host>(h: &H, x: H::Int) -> Res<H> {
    match h.view(x) {
        IntView::Small(n) => from_i64(h, !n),
        IntView::Big { negative: true, digits } => make(h, false, digits.len(), |z| bigint::subtract_one(z, digits)),
        IntView::Big { negative: false, digits } => make_long(h, true, digits.len() + 1, |z| bigint::add_one(z, digits)),
    }
}

/// Returns `x * 2^shift`. A negative `shift` shifts right and rounds toward negative infinity.
pub fn arithmetic_shift<H: Host>(h: &H, x: H::Int, shift: i64) -> Res<H> {
    let mut bx = [0];
    let x = match h.view(x) {
        IntView::Small(n) if shift < 0 => return from_i64(h, n >> shift.unsigned_abs().min(63)),
        IntView::Small(n) if shift < 64 => return from_i128(h, (n as i128) << shift),
        _ if shift == 0 => return Ok(x),
        view => Signed::new(view, &mut bx),
    };
    let xd = x.digits;
    if xd.is_zero() {
        return from_i64(h, 0);
    }
    if shift > 0 {
        let shift = usize::try_from(shift).unwrap_or(usize::MAX);
        let len = (shift / DIGIT_BITS).saturating_add(xd.len() + 1);
        h.charge(len as u64)?;
        return make_long(h, x.negative, len, |z| bigint::left_shift(z, xd, shift));
    }
    let shift = usize::try_from(shift.unsigned_abs()).unwrap_or(usize::MAX);
    if shift / DIGIT_BITS >= xd.len() {
        let fill = if x.negative {
            -1
        } else {
            0
        };
        return from_i64(h, fill);
    }
    h.charge(xd.len() as u64)?;
    let round = x.negative && bigint::shifts_out_ones(xd, shift);
    make(h, x.negative, xd.len() - shift / DIGIT_BITS + 1, |mut z| {
        bigint::right_shift(z.reborrow(), xd, shift);
        if round {
            bigint::add_digit(z, 1);
        }
    })
}

/// Returns the number of bits needed to represent `x` in two's complement, not counting the sign bit.
pub fn integer_length<H: Host>(h: &H, x: H::Int) -> u64 {
    match h.view(x) {
        IntView::Small(n) => {
            let magnitude = if n < 0 {
                !n
            } else {
                n
            };
            (64 - magnitude.leading_zeros()) as u64
        }
        IntView::Big { negative, digits } => {
            let bits = digits.bit_len() as u64;
            // `-m` needs as many bits as `m - 1`. That is one fewer than `m` needs when `m` is a power of two, and the same number otherwise.
            let power_of_two = digits.msd().is_power_of_two() && digits.slice(0, digits.len() - 1).is_zero();
            bits - (negative && power_of_two) as u64
        }
    }
}

/// Returns the number of one bits in `x` if `x` is not negative, or the number of zero bits if `x` is negative.
pub fn bit_count<H: Host>(h: &H, x: H::Int) -> Result<u64, H::Error> {
    #[inline(always)]
    fn ones(digits: Digits<'_>) -> u64 {
        digits.iter().map(|digit| u64::from(digit.count_ones())).sum::<u64>()
    }
    Ok(match h.view(x) {
        IntView::Small(n) => {
            let magnitude = if n < 0 {
                !n
            } else {
                n
            };
            u64::from(magnitude.count_ones())
        }
        IntView::Big { negative, digits } => {
            h.charge(digits.len() as u64)?;
            // `-m` is `!(m - 1)`, so its zero bits are the one bits of `m - 1`. `m - 1` is `m` with its lowest one bit cleared
            // and the zero bits below it set.
            if negative {
                ones(digits) - 1 + trailing_zeros(digits)
            } else {
                ones(digits)
            }
        }
    })
}

/// Returns whether bit `index` of `x` is set, in two's complement.
pub fn bit_set<H: Host>(h: &H, x: H::Int, index: u64) -> bool {
    match h.view(x) {
        IntView::Small(n) => n >> index.min(63) & 1 == 1,
        IntView::Big { negative, digits } => {
            let at = usize::try_from(index / DIGIT_BITS as u64).unwrap_or(usize::MAX);
            let bit = digits.get(at) >> (index % DIGIT_BITS as u64) & 1 == 1;
            if !negative {
                return bit;
            }
            // The value is `-m`, which is `!(m - 1)`. Below the lowest one bit of `m`, `m - 1` has ones. At that bit it has a zero.
            // Above that bit it has the bits of `m`.
            match index.cmp(&trailing_zeros(digits)) {
                Ordering::Less => false,
                Ordering::Equal => true,
                Ordering::Greater => !bit,
            }
        }
    }
}

/// Returns bits `start..end` of `x` as a non-negative integer. `start` must be at most `end`.
pub fn bit_field<H: Host>(h: &H, x: H::Int, start: u64, end: u64) -> Res<H> {
    let width = end - start;
    if let IntView::Small(n) = h.view(x)
        && width < 63
    {
        return from_i64(h, n >> start.min(63) & ((1 << width) - 1));
    }
    let low = arithmetic_shift(h, x, -shift_count(start))?;
    // A non-negative `x` has only zero bits at and above its `integer_length`, so no mask is needed.
    if sign(h, x) != Ordering::Less && integer_length(h, x) <= end {
        return Ok(low);
    }
    bitwise_and(h, low, ones(h, width)?)
}

/// Returns `dest` with bits `start..end` replaced by the low bits of `source`. `start` must be at most `end`.
pub fn bit_field_replace<H: Host>(h: &H, dest: H::Int, source: H::Int, start: u64, end: u64) -> Res<H> {
    let width = end - start;
    if let (IntView::Small(small_dest), IntView::Small(small_source)) = (h.view(dest), h.view(source))
        && end < 63
    {
        let low = (1 << width) - 1;
        return from_i64(h, small_dest & !(low << start) | (small_source & low) << start);
    }
    // Build the result from the bits of `dest` below `start`, the bits of `dest` from `end` up, and the field. This needs no mask wider than the result.
    let low = bit_field(h, dest, 0, start)?;
    let high = arithmetic_shift(h, arithmetic_shift(h, dest, -shift_count(end))?, shift_count(end))?;
    let field = arithmetic_shift(h, bit_field(h, source, 0, width)?, shift_count(start))?;
    bitwise_or(h, bitwise_or(h, low, high)?, field)
}

/// Returns `2^width - 1`.
fn ones<H: Host>(h: &H, width: u64) -> Res<H> {
    let one = from_i64(h, 1)?;
    sub(h, arithmetic_shift(h, one, shift_count(width))?, one)
}

/// Converts a bit position to a shift count. A position too large for an `i64` saturates at `i64::MAX`.
fn shift_count(bits: u64) -> i64 {
    i64::try_from(bits).unwrap_or(i64::MAX)
}

/// Returns the number of zero bits below the lowest one bit of `digits`, which must not be zero.
fn trailing_zeros(digits: Digits<'_>) -> u64 {
    let zeros = digits.iter().take_while(|&digit| digit == 0).count();
    (zeros * DIGIT_BITS) as u64 + u64::from(digits.get(zeros).trailing_zeros())
}

/// Returns the host's error for an integer that is too large for any memory. The error is obtained by asking the host for `usize::MAX` digits.
pub(crate) fn too_big<H: Host>(h: &H) -> H::Error {
    match h.big(false, usize::MAX, |_| 0) {
        Err(error) => error,
        Ok(_) => panic!("the host made an integer of usize::MAX digits"),
    }
}

/// Returns `x^exponent`, by repeated squaring.
pub fn expt<H: Host>(h: &H, x: H::Int, mut exponent: u64) -> Res<H> {
    let mut result = from_i64(h, 1)?;
    let mut base = x;
    while exponent != 0 {
        if exponent & 1 == 1 {
            result = mul(h, result, base)?;
        }
        exponent >>= 1;
        if exponent != 0 {
            base = mul(h, base, base)?;
        }
    }
    Ok(result)
}

/// Returns `⌊√x⌋`. `x` must not be negative.
pub fn isqrt<H: Host>(h: &H, x: H::Int) -> Res<H> {
    assert!(sign(h, x) != Ordering::Less, "square root of a negative integer");
    if let Some(n) = to_i64(h, x) {
        let n = n as u64;
        // The `f64` square root can be off by one in either direction, so correct it.
        let mut root = (n as f64).sqrt() as u64;
        while root * root > n {
            root -= 1;
        }
        while (root + 1) * (root + 1) <= n {
            root += 1;
        }
        return from_u64(h, root);
    }
    // Newton's method. From a start above the root, the iterates decrease to `⌊√x⌋` and then stop decreasing. The start is a little
    // above the root. It comes from the `f64` square root of the top 100 or so bits of `x`, which has a relative error within 2^-50.
    let shift = (integer_length(h, x).saturating_sub(100) / 2) as i64;
    let top = to_f64(h, arithmetic_shift(h, x, -2 * shift)?);
    let mut root = arithmetic_shift(h, from_u64(h, top.sqrt() as u64 + 2)?, shift)?;
    loop {
        let next = arithmetic_shift(h, add(h, root, quotient(h, x, root)?)?, -1)?;
        if compare(h, next, root) != Ordering::Less {
            return Ok(root);
        }
        root = next;
    }
}

/// Parses `text` as unsigned digits in `radix` and returns the integer, negated if `negative`. Returns `None` if `text` is empty
/// or contains a character that is not a digit in `radix`.
pub fn parse<H: Host>(h: &H, text: &[u8], radix: u32, negative: bool) -> Result<Option<H::Int>, H::Error> {
    assert!((2..=36).contains(&radix), "radix out of range");
    if text.is_empty() || !text.iter().all(|&byte| (byte as char).is_digit(radix)) {
        return Ok(None);
    }
    let len = bigint::from_string_len(text.len(), radix);
    h.charge((len as u64).saturating_mul(len as u64))?;
    let x = make(h, negative, len, |z| {
        bigint::from_string(z, text, radix).expect("digits were checked");
    })?;
    Ok(Some(x))
}

/// Returns `x` written in `radix`, with a leading `-` if `x` is negative.
pub fn to_string<H: Host>(h: &H, x: H::Int, radix: u32) -> Result<String, H::Error> {
    let mut bx = [0];
    let x = Signed::new(h.view(x), &mut bx);
    let chars = bigint::to_string_len(x.digits, radix);
    h.charge((x.digits.len() as u64).saturating_mul(x.digits.len() as u64))?;
    h.scratch(x.digits.len() + chars.div_ceil(size_of::<Digit>()))?;
    let mut out = vec![0; chars + 1];
    let mut scratch = vec![0; x.digits.len()];
    let mut start = bigint::to_string(x.digits, radix, RWDigits::new(&mut scratch), &mut out);
    if x.negative {
        start -= 1;
        out[start] = b'-';
    }
    out.drain(..start);
    Ok(String::from_utf8(out).expect("digits are ascii"))
}
