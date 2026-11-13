//! Exact integers with Racket's semantics, on any heap that implements [`Host`].
//!
//! Results are normalized: an integer the host can hold small is never big, and a big one
//! never has high zero digits. Everything is generic, so a host's small path compiles down
//! to plain `i64` arithmetic.

use std::cmp::Ordering;
use std::hash::Hasher;

use crate::bigint::{self, DIGIT_BITS, Digit, Digits, RWDigits};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NumError {
    DivideByZero,
    /// Infinities and NaNs have no exact value.
    NoExactValue,
    /// An integer operation got a number that isn't one, like `1.5`.
    NotInteger,
}

/// An integer as the host holds it.
#[derive(Clone, Copy, Debug)]
pub enum IntView<'a> {
    Small(i64),
    /// Digits without high zeros, of a value [`Host::small`] can't hold.
    Big { negative: bool, digits: Digits<'a> },
}

/// Where integers live. The library reads them through [`Host::view`] and makes them with
/// [`Host::small`] and [`Host::big`], and keeps results normalized.
pub trait Host {
    type Int: Copy;
    type Error: From<NumError>;

    fn view(&self, x: Self::Int) -> IntView<'_>;

    /// `n` as a small integer, or `None` if the host only holds it big.
    fn small(&self, n: i64) -> Option<Self::Int>;

    /// A big integer from `len` zeroed digits that `init` fills in, keeping as many as it
    /// returns. Views of other integers stay valid while it runs.
    fn big(&self, negative: bool, len: usize, init: impl FnOnce(RWDigits<'_>) -> usize) -> Result<Self::Int, Self::Error>;

    /// Called before about `work` digit operations.
    #[inline]
    fn charge(&self, work: u64) -> Result<(), Self::Error> {
        let _ = work;
        Ok(())
    }

    /// Called before taking `digits` digits of temporary memory, which is freed before the
    /// operation returns.
    #[inline]
    fn scratch(&self, digits: usize) -> Result<(), Self::Error> {
        let _ = digits;
        Ok(())
    }

    /// `x + y` when the host can do it straight on its small representation, or `None` to
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

/// Sign and magnitude, with small integers' magnitudes in a buffer.
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

/// Results of up to this many digits are computed on the stack, so ones that come out
/// small never allocate.
const STACK: usize = 4;

/// The integer `init` computes into at most `len` digits.
#[inline]
fn make<H: Host>(h: &H, negative: bool, len: usize, init: impl FnOnce(RWDigits<'_>)) -> Res<H> {
    if len <= STACK {
        let mut buf = [0; STACK];
        init(RWDigits::new(&mut buf[..len]));
        return from_digits(h, negative, Digits::of_mut(&mut buf[..len]));
    }
    // A long result can still come out short, as when subtracting nearly equal numbers.
    let (mut short, mut kept) = (None, 0);
    let x = h.big(negative, len, |mut z| {
        init(z.reborrow());
        let digits = z.read().normalize();
        (short, kept) = (to_small(negative, digits), digits.len());
        kept
    })?;
    match short.and_then(|n| h.small(n)) {
        Some(small) => Ok(small),
        // Moved to an allocation its size, as the rest of this one, up to a whole run of pages,
        // would stay with it. The copy costs less than making it did.
        None if kept * 2 < len => match h.view(x) {
            IntView::Big { negative, digits } => from_digits(h, negative, digits),
            IntView::Small(_) => Ok(x),
        },
        None => Ok(x),
    }
}

/// Like [`make`], for results that keep at least `len - 1` digits. Those that need the heap
/// then never fit a small integer, so they skip checking.
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

/// `digits` are normalized.
#[inline]
fn to_small(negative: bool, digits: Digits<'_>) -> Option<i64> {
    debug_assert_eq!(digits.normalize().len(), digits.len());
    match digits.len() {
        0 => Some(0),
        1 if negative => (digits.at(0) <= 1 << 63).then(|| (digits.at(0) as i64).wrapping_neg()),
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
        IntView::Big { negative, digits } => (!negative && digits.len() == 1).then(|| digits.at(0)),
    }
}

pub fn to_i64<H: Host>(h: &H, x: H::Int) -> Option<i64> {
    match h.view(x) {
        IntView::Small(n) => Some(n),
        IntView::Big { negative, digits } => to_small(negative, digits),
    }
}

/// An integral, finite double, exactly.
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

/// The nearest double, ties to even.
pub fn to_f64<H: Host>(h: &H, x: H::Int) -> f64 {
    match h.view(x) {
        IntView::Small(n) => n as f64,
        IntView::Big { negative, digits } => {
            let value = bigint::to_f64(digits);
            if negative { -value } else { value }
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

/// Feeds `x`'s value to `state`. Equal integers hash the same however the host holds them,
/// and the hasher sees every digit, so a keyed hasher keeps collisions unpredictable.
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

/// How `x` compares to zero.
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
    /// Toward zero: `quotient` and `remainder`, whose sign is the dividend's.
    Truncate,
    /// Down: `floor/`, whose remainder is `modulo`, with the divisor's sign.
    Floor,
}

/// The quotient and remainder of `x / y`, each made only if asked for.
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
            let quotient = want_q.then(|| from_i128(h, quotient)).transpose()?;
            return Ok((quotient, want_r.then(|| from_i128(h, remainder)).transpose()?));
        }
        (xv, yv) => (Signed::new(xv, &mut bx), Signed::new(yv, &mut by)),
    };
    let (xd, yd) = (xs.digits, ys.digits);
    let q_negative = xs.negative != ys.negative;
    // Flooring with a nonzero remainder and differing signs takes one off the truncated
    // quotient and turns the remainder into `y - remainder`.
    let adjust = floor && q_negative;
    h.charge((xd.len().saturating_sub(yd.len()) as u64 + 1) * yd.len() as u64)?;

    if bigint::compare(xd, yd) == Ordering::Less {
        let (quotient, remainder) = if !adjust || xd.is_zero() {
            (from_i64(h, 0)?, x)
        } else {
            (from_i64(h, -1)?, make(h, ys.negative, yd.len(), |z| bigint::subtract(z, yd, xd))?)
        };
        return Ok((want_q.then_some(quotient), want_r.then_some(remainder)));
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

    // One more quotient digit than division needs, for the carry of adjusting it.
    let (q_len, r_len) = (xd.len() - yd.len() + 2, yd.len());
    let len = q_len + r_len + bigint::divide_scratch(xd, yd);
    h.scratch(len)?;
    let mut buf = vec![0; len];
    let (quotient_digits, rest) = buf.split_at_mut(q_len);
    let (remainder_digits, scratch) = rest.split_at_mut(r_len);
    let q_out = want_q.then(|| RWDigits::new(&mut quotient_digits[..q_len - 1]));
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

/// The greatest common divisor, never negative.
pub fn gcd<H: Host>(h: &H, x: H::Int, y: H::Int) -> Res<H> {
    let (mut bx, mut by) = ([0], [0]);
    let (x, y) = match (h.view(x), h.view(y)) {
        (IntView::Small(a), IntView::Small(b)) => return from_u64(h, gcd_u64(a.unsigned_abs(), b.unsigned_abs())),
        (xv, yv) => (Signed::new(xv, &mut bx).digits, Signed::new(yv, &mut by).digits),
    };
    let (x, y) = if bigint::compare(x, y) == Ordering::Less { (y, x) } else { (x, y) };
    if y.is_zero() {
        return from_digits(h, false, x);
    }
    // Euclid's algorithm, rotating three buffers: a, b, then a mod b.
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

/// The least common multiple, never negative.
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

/// Two's complement over infinitely many bits.
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
    let (x, y) = if x.negative && !y.negative { (y, x) } else { (x, y) };
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

/// `-x - 1`
pub fn bitwise_not<H: Host>(h: &H, x: H::Int) -> Res<H> {
    match h.view(x) {
        IntView::Small(n) => from_i64(h, !n),
        IntView::Big { negative: true, digits } => make(h, false, digits.len(), |z| bigint::subtract_one(z, digits)),
        IntView::Big { negative: false, digits } => make_long(h, true, digits.len() + 1, |z| bigint::add_one(z, digits)),
    }
}

/// `x * 2^shift`, rounding down for negative shifts.
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
        return from_i64(h, if x.negative { -1 } else { 0 });
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

/// Bits needed for `x` in two's complement, without the sign bit.
pub fn integer_length<H: Host>(h: &H, x: H::Int) -> u64 {
    match h.view(x) {
        IntView::Small(n) => (64 - if n < 0 { !n } else { n }.leading_zeros()) as u64,
        IntView::Big { negative, digits } => {
            let bits = digits.bit_len() as u64;
            // `-m` takes as many bits as `m - 1`, one fewer when `m` is a power of two.
            let power_of_two = digits.msd().is_power_of_two() && digits.slice(0, digits.len() - 1).is_zero();
            bits - (negative && power_of_two) as u64
        }
    }
}

/// The bits set in `x` if it isn't negative, or else those clear.
pub fn bit_count<H: Host>(h: &H, x: H::Int) -> Result<u64, H::Error> {
    let ones = |digits: Digits<'_>| digits.iter().map(|digit| u64::from(digit.count_ones())).sum::<u64>();
    Ok(match h.view(x) {
        IntView::Small(n) => u64::from(if n < 0 { !n } else { n }.count_ones()),
        IntView::Big { negative, digits } => {
            h.charge(digits.len() as u64)?;
            // `-m` is `!(m - 1)`, and `m - 1` is `m` with its lowest one cleared and the zeros
            // under it set.
            if negative { ones(digits) - 1 + trailing_zeros(digits) } else { ones(digits) }
        }
    })
}

/// Whether bit `index` of `x` is set, in two's complement.
pub fn bit_set<H: Host>(h: &H, x: H::Int, index: u64) -> bool {
    match h.view(x) {
        IntView::Small(n) => n >> index.min(63) & 1 == 1,
        IntView::Big { negative, digits } => {
            let at = usize::try_from(index / DIGIT_BITS as u64).unwrap_or(usize::MAX);
            let bit = digits.get(at) >> (index % DIGIT_BITS as u64) & 1 == 1;
            if !negative {
                return bit;
            }
            // Of `!(m - 1)`: under `m`'s lowest one, `m - 1` has ones, at it a zero, and over it
            // `m`'s bits.
            match index.cmp(&trailing_zeros(digits)) {
                Ordering::Less => false,
                Ordering::Equal => true,
                Ordering::Greater => !bit,
            }
        }
    }
}

/// Bits `start..end` of `x`, as a non-negative integer. `start` is at most `end`.
pub fn bit_field<H: Host>(h: &H, x: H::Int, start: u64, end: u64) -> Res<H> {
    let width = end - start;
    if let IntView::Small(n) = h.view(x)
        && width < 63
    {
        return from_i64(h, n >> start.min(63) & ((1 << width) - 1));
    }
    let low = arithmetic_shift(h, x, -shift_count(start))?;
    // Past its length, a non-negative `x` has only zeros, so needs no mask.
    if sign(h, x) != Ordering::Less && integer_length(h, x) <= end {
        return Ok(low);
    }
    bitwise_and(h, low, ones(h, width)?)
}

/// `dest` with bits `start..end` replaced by the low bits of `source`. `start` is at most `end`.
pub fn bit_field_replace<H: Host>(h: &H, dest: H::Int, source: H::Int, start: u64, end: u64) -> Res<H> {
    let width = end - start;
    if let (IntView::Small(small_dest), IntView::Small(small_source)) = (h.view(dest), h.view(source))
        && end < 63
    {
        let low = (1 << width) - 1;
        return from_i64(h, small_dest & !(low << start) | (small_source & low) << start);
    }
    // Made of the bits under `start` and over `end`, it takes no mask wider than the result.
    let low = bit_field(h, dest, 0, start)?;
    let high = arithmetic_shift(h, arithmetic_shift(h, dest, -shift_count(end))?, shift_count(end))?;
    let field = arithmetic_shift(h, bit_field(h, source, 0, width)?, shift_count(start))?;
    bitwise_or(h, bitwise_or(h, low, high)?, field)
}

/// `2^width - 1`.
fn ones<H: Host>(h: &H, width: u64) -> Res<H> {
    let one = from_i64(h, 1)?;
    sub(h, arithmetic_shift(h, one, shift_count(width))?, one)
}

/// A bit position as a shift count, those past an `i64` as far as one goes.
fn shift_count(bits: u64) -> i64 {
    i64::try_from(bits).unwrap_or(i64::MAX)
}

/// The zeros under the lowest one of a magnitude that isn't zero.
fn trailing_zeros(digits: Digits<'_>) -> u64 {
    let zeros = digits.iter().take_while(|&digit| digit == 0).count();
    (zeros * DIGIT_BITS) as u64 + u64::from(digits.get(zeros).trailing_zeros())
}

/// The host's error for an integer larger than any memory holds.
pub(crate) fn too_big<H: Host>(h: &H) -> H::Error {
    match h.big(false, usize::MAX, |_| 0) {
        Err(error) => error,
        Ok(_) => panic!("the host made an integer of usize::MAX digits"),
    }
}

/// `x^exponent`, by squaring.
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

/// `⌊√x⌋` for `x >= 0`.
pub fn isqrt<H: Host>(h: &H, x: H::Int) -> Res<H> {
    assert!(sign(h, x) != Ordering::Less, "square root of a negative integer");
    if let Some(n) = to_i64(h, x) {
        let n = n as u64;
        // The double's root can be off by one either way.
        let mut root = (n as f64).sqrt() as u64;
        while root * root > n {
            root -= 1;
        }
        while (root + 1) * (root + 1) <= n {
            root += 1;
        }
        return from_u64(h, root);
    }
    // Newton's method from above falls to the root and then stops falling. It starts a little
    // above the root of the top hundred-odd bits, which the double gets to within 2^-50.
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

/// Reads digits in `radix`, without a sign, or `None` if `text` is empty or has a character
/// that isn't a digit in the radix.
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

/// `x` in `radix`, with a `-` if negative.
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
