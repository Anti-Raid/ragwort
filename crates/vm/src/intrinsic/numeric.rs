//! Numeric intrinsics: arithmetic, comparison, bitwise operations and conversions.

use std::cmp::Ordering;

use ragwort_types::gc::{Mutation, Value};
use ragwort_types::num::rational::Round;
use ragwort_types::num::{ComplexHost, ComplexView, Integer, Number, NumError, Nums, RationalHost, RationalView, Real, RealHost, RealView, complex, int, literal, real};
use ragwort_types::string::{self, Strings};

use crate::op::Fuel;
use crate::{Fault, equal};

use super::{Intrinsic, Operands, boolean, fixnum, index, made};

impl Intrinsic {
    /// Evaluates advanced numeric intrinsics (beyond basic arithmetic) on `operands`.
    #[inline(never)]
    pub(super) fn numeric<'gc>(self, mc: &Mutation<'gc>, operands: impl Operands<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        #[inline(always)]
        fn number<'gc>(nums: &Nums<'_, 'gc>, value: Value<'gc>) -> Result<Number<'gc>, Fault> {
            nums.number(value).ok_or(Fault::WrongType)
        }
        #[inline(always)]
        fn real<'gc>(nums: &Nums<'_, 'gc>, value: Value<'gc>) -> Result<Real<'gc>, Fault> {
            nums.real(value).ok_or(Fault::WrongType)
        }
        let nums = Nums::new(mc);
        let made_of = match self {
            Intrinsic::IsNumber => return Ok(boolean(nums.number(operands.get(0)).is_some())),
            Intrinsic::IsReal => return Ok(boolean(nums.real(operands.get(0)).is_some())),
            Intrinsic::IsRational => return Ok(boolean(nums.real(operands.get(0)).is_some_and(|operand| !matches!(nums.real_view(operand), RealView::Flonum(float) if !float.is_finite())))),
            Intrinsic::IsInteger => return Ok(boolean(nums.real(operands.get(0)).is_some_and(|operand| real::is_integer(&nums, operand)))),
            Intrinsic::IsExactInteger => return Ok(boolean(nums.integer(operands.get(0)).is_some())),
            Intrinsic::IsExact | Intrinsic::IsInexact => return Ok(boolean(complex::is_exact(&nums, number(&nums, operands.get(0))?) == (self == Intrinsic::IsExact))),
            Intrinsic::IsNan | Intrinsic::IsInfinite | Intrinsic::IsFinite => {
                let parts = match nums.complex_view(number(&nums, operands.get(0))?) {
                    ComplexView::Real(part) => [part, part],
                    ComplexView::Complex { re, im } => [re, im],
                };
                let floats = parts.map(|part| match nums.real_view(part) {
                    RealView::Flonum(float) => float,
                    RealView::Exact(_) => 0.0,
                });
                return Ok(boolean(match self {
                    Intrinsic::IsNan => floats.iter().any(|float| float.is_nan()),
                    Intrinsic::IsInfinite => floats.iter().any(|float| float.is_infinite()),
                    _ => floats.iter().all(|float| float.is_finite()),
                }));
            }
            Intrinsic::IsZero => {
                return Ok(boolean(match nums.complex_view(number(&nums, operands.get(0))?) {
                    ComplexView::Real(operand) => real::sign(&nums, operand) == Some(Ordering::Equal),
                    ComplexView::Complex { .. } => false,
                }));
            }
            Intrinsic::IsPositive | Intrinsic::IsNegative => {
                let want = if self == Intrinsic::IsPositive {
                    Ordering::Greater
                } else {
                    Ordering::Less
                };
                return Ok(boolean(real::sign(&nums, real(&nums, operands.get(0))?) == Some(want)));
            }
            Intrinsic::IsOdd | Intrinsic::IsEven => {
                let even = match operands.get(0).as_fixnum() {
                    Some(integer) => integer % 2 == 0,
                    None => int::is_even(&nums, integral(mc, &nums, operands.get(0))?.0),
                };
                return Ok(boolean(even == (self == Intrinsic::IsEven)));
            }
            Intrinsic::Max | Intrinsic::Min if operands.count() == 0 => return Err(Fault::Arity),
            Intrinsic::Max | Intrinsic::Min => {
                let max = self == Intrinsic::Max;
                let mut acc = real(&nums, operands.get(0))?;
                for i in 1..operands.count() {
                    let next = real(&nums, operands.get(i))?;
                    acc = match (acc.value().as_fixnum(), next.value().as_fixnum()) {
                        (Some(left), Some(right)) => if (right > left) == max {
                            next
                        } else {
                            acc
                        },
                        _ if max => real::max(&nums, acc, next)?,
                        _ => real::min(&nums, acc, next)?,
                    };
                }
                nums.of_real(acc)
            }
            // Because fixnums use strictly fewer bits than an i64, `integer.abs()` cannot overflow
            // 64-bit integer limits, although the absolute value may exceed the fixnum range and
            // require bignum promotion.
            Intrinsic::Abs => match operands.get(0).as_fixnum().and_then(|integer| Value::fixnum(integer.abs())) {
                Some(value) => return Ok(value),
                None => nums.of_real(real::abs(&nums, real(&nums, operands.get(0))?)?),
            },
            Intrinsic::Gcd | Intrinsic::Lcm => {
                let gcd = self == Intrinsic::Gcd;
                let identity = if gcd {
                    0
                } else {
                    1
                };
                let (mut acc, mut exact) = (int::from_i64(&nums, identity)?, true);
                for i in 0..operands.count() {
                    let (integer, is_exact) = integral(mc, &nums, operands.get(i))?;
                    exact &= is_exact;
                    let words = int::integer_length(&nums, acc).max(int::integer_length(&nums, integer)) / 64;
                    fuel.spend(words.saturating_mul(words) / equal::PER_FUEL)?;
                    acc = if gcd {
                        int::gcd(&nums, acc, integer)?
                    } else {
                        int::lcm(&nums, acc, integer)?
                    };
                }
                let acc = nums.of_rational(nums.of_int(acc));
                let result = if exact {
                    acc
                } else {
                    real::inexact(&nums, acc)?
                };
                nums.of_real(result)
            }
            Intrinsic::Numerator => nums.of_real(real::numerator(&nums, real(&nums, operands.get(0))?)?),
            Intrinsic::Denominator => nums.of_real(real::denominator(&nums, real(&nums, operands.get(0))?)?),
            Intrinsic::Floor | Intrinsic::Ceiling | Intrinsic::Truncate | Intrinsic::Round => {
                if operands.get(0).is_fixnum() {
                    return Ok(operands.get(0));
                }
                let operand = real(&nums, operands.get(0))?;
                charge_squared(&nums, fuel, nums.of_real(operand))?;
                let mode = match self {
                    Intrinsic::Floor => Round::Floor,
                    Intrinsic::Ceiling => Round::Ceiling,
                    Intrinsic::Truncate => Round::Truncate,
                    _ => Round::Nearest,
                };
                nums.of_real(real::round(&nums, operand, mode)?)
            }
            Intrinsic::IntegerSqrt => {
                let integer = nums.integer(operands.get(0)).ok_or(Fault::WrongType)?;
                if int::sign(&nums, integer) == Ordering::Less {
                    return Err(Fault::OutOfRange);
                }
                charge_squared(&nums, fuel, number(&nums, operands.get(0))?)?;
                nums.of_real(nums.of_rational(nums.of_int(int::isqrt(&nums, integer)?)))
            }
            Intrinsic::Exact => complex::exact(&nums, number(&nums, operands.get(0))?)?,
            Intrinsic::Inexact => complex::inexact(&nums, number(&nums, operands.get(0))?)?,
            Intrinsic::StringToNumber if !(1..=2).contains(&operands.count()) => return Err(Fault::Arity),
            Intrinsic::StringToNumber => {
                let strings = Strings::new(mc);
                let string = strings.string(operands.get(0)).ok_or(Fault::WrongType)?;
                let radix = if operands.count() == 2 {
                    operands.get(1).as_fixnum().ok_or(Fault::WrongType)?
                } else {
                    10
                };
                let radix = [2, 8, 10, 16].into_iter().find(|&allowed| allowed == radix).ok_or(Fault::OutOfRange)? as u32;
                // Parsing a multi-precision integer has approximately quadratic computational
                // complexity relative to its digit count (up to 4 bits per digit).
                let len = string::len(&strings, string);
                let words = (len as u64).saturating_mul(4) / 64;
                fuel.spend(words.saturating_mul(words) / equal::PER_FUEL)?;
                mc.ensure(len.saturating_mul(4))?;
                let text: String = string::chars(&strings, string).collect();
                match literal::parse_in(&nums, &text, radix)? {
                    Some(parsed) => parsed,
                    None => return Ok(Value::FALSE),
                }
            }
            Intrinsic::Exp => complex::exp(&nums, number(&nums, operands.get(0))?)?,
            Intrinsic::Log if !(1..=2).contains(&operands.count()) => return Err(Fault::Arity),
            Intrinsic::Log if operands.count() == 2 => complex::log_base(&nums, number(&nums, operands.get(0))?, number(&nums, operands.get(1))?)?,
            Intrinsic::Log => complex::log(&nums, number(&nums, operands.get(0))?)?,
            Intrinsic::Sin => complex::sin(&nums, number(&nums, operands.get(0))?)?,
            Intrinsic::Cos => complex::cos(&nums, number(&nums, operands.get(0))?)?,
            Intrinsic::Tan => complex::tan(&nums, number(&nums, operands.get(0))?)?,
            Intrinsic::Asin => complex::asin(&nums, number(&nums, operands.get(0))?)?,
            Intrinsic::Acos => complex::acos(&nums, number(&nums, operands.get(0))?)?,
            Intrinsic::Atan if !(1..=2).contains(&operands.count()) => return Err(Fault::Arity),
            Intrinsic::Atan if operands.count() == 2 => nums.of_real(complex::atan2(&nums, real(&nums, operands.get(0))?, real(&nums, operands.get(1))?)?),
            Intrinsic::Atan => complex::atan(&nums, number(&nums, operands.get(0))?)?,
            Intrinsic::Sqrt => {
                let operand = number(&nums, operands.get(0))?;
                charge_squared(&nums, fuel, operand)?;
                complex::sqrt(&nums, operand)?
            }
            Intrinsic::MakeRectangular => complex::rectangular(&nums, real(&nums, operands.get(0))?, real(&nums, operands.get(1))?)?,
            Intrinsic::MakePolar => complex::polar(&nums, real(&nums, operands.get(0))?, real(&nums, operands.get(1))?)?,
            Intrinsic::RealPart => nums.of_real(complex::real_part(&nums, number(&nums, operands.get(0))?)),
            Intrinsic::ImagPart => nums.of_real(complex::imag_part(&nums, number(&nums, operands.get(0))?)?),
            Intrinsic::Magnitude => nums.of_real(complex::magnitude(&nums, number(&nums, operands.get(0))?)?),
            Intrinsic::Angle => nums.of_real(complex::angle(&nums, number(&nums, operands.get(0))?)?),
            _ => unreachable!("{self:?} isn't numeric"),
        };
        Ok(made(mc, fuel, made_of.value()))
    }

    /// Evaluates a bitwise intrinsic on `operands`.
    #[inline(never)]
    pub(super) fn bits<'gc>(self, mc: &Mutation<'gc>, operands: impl Operands<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        Ok(match self {
            Intrinsic::BitwiseAnd => bitwise(mc, fuel, self, -1, operands.from(0))?,
            Intrinsic::BitwiseIor | Intrinsic::BitwiseXor => bitwise(mc, fuel, self, 0, operands.from(0))?,
            Intrinsic::BitwiseNot | Intrinsic::ArithmeticShift | Intrinsic::BitField | Intrinsic::BitFieldReplace => {
                let nums = Nums::new(mc);
                let integer = nums.integer(operands.get(0)).ok_or(Fault::WrongType)?;
                let (len, negative) = (int::integer_length(&nums, integer), int::sign(&nums, integer) == Ordering::Less);
                let made_of = match self {
                    Intrinsic::BitwiseNot => int::bitwise_not(&nums, integer)?,
                    Intrinsic::ArithmeticShift => {
                        let count = operands.get(1).as_fixnum().ok_or(Fault::WrongType)?;
                        // Shifting zero produces zero without allocating additional bits, whereas
                        // left-shifting negative one increases its two's complement bit width.
                        if integer.value() != fixnum(0) {
                            charge_bits(mc, fuel, len.saturating_add(count.max(0) as u64))?;
                        }
                        int::arithmetic_shift(&nums, integer, count)?
                    }
                    Intrinsic::BitField => {
                        let (start, end) = bit_range(operands.get(1), operands.get(2))?;
                        let bits = if negative {
                            end - start
                        } else {
                            len.saturating_sub(start).min(end - start)
                        };
                        charge_bits(mc, fuel, bits)?;
                        int::bit_field(&nums, integer, start, end)?
                    }
                    _ => {
                        let (source, (start, end)) = (nums.integer(operands.get(1)).ok_or(Fault::WrongType)?, bit_range(operands.get(2), operands.get(3))?);
                        let field = if int::sign(&nums, source) == Ordering::Less {
                            end - start
                        } else {
                            int::integer_length(&nums, source).min(end - start)
                        };
                        let bits = if negative {
                            end
                        } else if field == 0 {
                            len
                        } else {
                            len.max(start + field)
                        };
                        charge_bits(mc, fuel, bits)?;
                        int::bit_field_replace(&nums, integer, source, start, end)?
                    }
                };
                made(mc, fuel, made_of.value())
            }
            Intrinsic::IntegerLength | Intrinsic::BitCount => {
                let nums = Nums::new(mc);
                let integer = nums.integer(operands.get(0)).ok_or(Fault::WrongType)?;
                let bits = if self == Intrinsic::IntegerLength {
                    int::integer_length(&nums, integer)
                } else {
                    fuel.spend(int::integer_length(&nums, integer) / 64 / equal::PER_FUEL)?;
                    int::bit_count(&nums, integer)?
                };
                fixnum(i64::try_from(bits).map_err(|_| Fault::OutOfRange)?)
            }
            Intrinsic::IsBitSet => {
                let nums = Nums::new(mc);
                let integer = nums.integer(operands.get(1)).ok_or(Fault::WrongType)?;
                // Testing bit flags on a negative multi-precision integer may require scanning
                // past its least significant set bit, traversing multiple words.
                if int::sign(&nums, integer) == Ordering::Less {
                    fuel.spend(int::integer_length(&nums, integer) / 64 / equal::PER_FUEL)?;
                }
                boolean(int::bit_set(&nums, integer, index(operands.get(0))? as u64))
            }
            _ => unreachable!("{self:?} isn't a bitwise procedure"),
        })
    }
}

/// Returns `Some(dividend / divisor)` if both `dividend` and `divisor` are fixnums, division by zero does not occur, and
/// the quotient is exactly representable as a fixnum; otherwise returns `None`.
fn fixnum_div<'gc>(dividend: Value<'gc>, divisor: Value<'gc>) -> Option<Value<'gc>> {
    let (dividend, divisor) = (dividend.as_fixnum()?, divisor.as_fixnum()?);
    if divisor != 0 && dividend % divisor == 0 {
        Value::fixnum(dividend / divisor)
    } else {
        None
    }
}

/// Folds the arithmetic operation `op` (`+`, `-`, `*` or `/`) over `first` and the elements of
/// `rest`. Fixnum arithmetic is used while the operands and the result stay fixnums. Otherwise the
/// step falls back to the full numeric tower.
#[inline(always)]
pub(super) fn arith<'gc>(mc: &Mutation<'gc>, fuel: &mut Fuel, op: Intrinsic, first: Value<'gc>, rest: impl Iterator<Item = Value<'gc>>) -> Result<Value<'gc>, Fault> {
    let mut acc = first;
    for operand in rest {
        let fast = match op {
            Intrinsic::Add => Value::fixnum_add(acc, operand),
            Intrinsic::Mul => Value::fixnum_mul(acc, operand),
            Intrinsic::Sub => Value::fixnum_sub(acc, operand),
            _ => fixnum_div(acc, operand),
        };
        acc = match fast {
            Some(acc) => acc,
            None => {
                let nums = Nums::new(mc);
                let (left, right) = (nums.number(acc).ok_or(Fault::WrongType)?, nums.number(operand).ok_or(Fault::WrongType)?);
                let result = match op {
                    Intrinsic::Add => complex::add(&nums, left, right),
                    Intrinsic::Mul => complex::mul(&nums, left, right),
                    Intrinsic::Sub => complex::sub(&nums, left, right),
                    _ => complex::div(&nums, left, right),
                };
                made(mc, fuel, result?.value())
            }
        };
    }
    Ok(acc)
}

/// Applies bitwise operation `op` across `first` and all elements of `rest` (requiring exact
/// integers), executing unboxed fixnum operations while values remain fixnums and falling back to
/// arbitrary-precision integers as necessary.
pub(super) fn bitwise<'gc>(mc: &Mutation<'gc>, fuel: &mut Fuel, op: Intrinsic, first: i64, rest: impl Iterator<Item = Value<'gc>>) -> Result<Value<'gc>, Fault> {
    let nums = Nums::new(mc);
    let mut acc = fixnum(first);
    for operand in rest {
        acc = match (acc.as_fixnum(), operand.as_fixnum()) {
            // Bitwise operations on two fixnum values are guaranteed to produce a result that
            // fits within a fixnum.
            (Some(left), Some(right)) => fixnum(match op {
                Intrinsic::BitwiseAnd => left & right,
                Intrinsic::BitwiseIor => left | right,
                _ => left ^ right,
            }),
            _ => {
                let (left, right) = (nums.integer(acc).ok_or(Fault::WrongType)?, nums.integer(operand).ok_or(Fault::WrongType)?);
                let result = match op {
                    Intrinsic::BitwiseAnd => int::bitwise_and(&nums, left, right),
                    Intrinsic::BitwiseIor => int::bitwise_or(&nums, left, right),
                    _ => int::bitwise_xor(&nums, left, right),
                };
                made(mc, fuel, result?.value())
            }
        };
    }
    Ok(acc)
}

/// Deducts fuel and reserves memory proportional to creating an integer of approximately `bits`
/// bits, preventing unbounded allocation during operations like arithmetic shifts that expand
/// numbers significantly.
fn charge_bits(mc: &Mutation<'_>, fuel: &mut Fuel, bits: u64) -> Result<(), Fault> {
    let words = bits / 64;
    if words < equal::PER_FUEL {
        return Ok(());
    }
    mc.ensure(usize::try_from(words.saturating_mul(8)).unwrap_or(usize::MAX))?;
    fuel.spend(words / equal::PER_FUEL)
}

/// Extracts and validates bit indices `(start, end)`, ensuring `start <= end` and returning
/// them as `(u64, u64)` or faulting on invalid bounds.
fn bit_range(start: Value<'_>, end: Value<'_>) -> Result<(u64, u64), Fault> {
    let (start, end) = (index(start)? as u64, index(end)? as u64);
    if end < start {
        return Err(Fault::OutOfRange);
    }
    Ok((start, end))
}

/// Computes `quotient`, `remainder`, `modulo`, or `floor-quotient` for `dividend` and `divisor`, using fast
/// in-place fixnum arithmetic when both operands are fixnums and non-zero, and falling back to
/// arbitrary-precision arithmetic otherwise.
pub(super) fn divide<'gc>(mc: &Mutation<'gc>, fuel: &mut Fuel, op: Intrinsic, dividend: Value<'gc>, divisor: Value<'gc>) -> Result<Value<'gc>, Fault> {
    if let (Some(left), Some(right)) = (dividend.as_fixnum(), divisor.as_fixnum())
        && right != 0
    {
        // Because fixnums use strictly fewer bits than an i64, operations cannot trigger 64-bit
        // signed integer overflow (such as `i64::MIN / -1`).
        let fast = match op {
            Intrinsic::Quotient => left / right,
            Intrinsic::Remainder => left % right,
            Intrinsic::FloorQuotient => {
                let quotient = left / right;
                if left % right != 0 && (left < 0) != (right < 0) {
                    quotient - 1
                } else {
                    quotient
                }
            }
            _ => {
                let remainder = left % right;
                if remainder != 0 && (remainder < 0) != (right < 0) {
                    remainder + right
                } else {
                    remainder
                }
            }
        };
        if let Some(value) = Value::fixnum(fast) {
            return Ok(value);
        }
    }
    let nums = Nums::new(mc);
    let (left, right) = (nums.real(dividend).ok_or(Fault::WrongType)?, nums.real(divisor).ok_or(Fault::WrongType)?);
    let generic = match op {
        Intrinsic::Quotient => real::quotient(&nums, left, right),
        Intrinsic::Remainder => real::remainder(&nums, left, right),
        Intrinsic::FloorQuotient => real::floor_quotient(&nums, left, right),
        _ => real::modulo(&nums, left, right),
    };
    Ok(made(mc, fuel, generic?.value()))
}

/// Formats fixnum `integer` in the given `radix` (2, 8, 10, or 16) by writing characters into a
/// stack-allocated buffer and constructing a Scheme string.
pub(super) fn fixnum_to_string<'gc>(mc: &Mutation<'gc>, integer: i64, radix: u32) -> Result<Value<'gc>, Fault> {
    // Buffer size of 65 bytes accommodates the worst-case representation: 64 base-2 digits
    // plus an optional minus sign.
    let mut digits = [0u8; 65];
    let (mut at, mut left) = (digits.len(), integer.unsigned_abs());
    loop {
        at -= 1;
        digits[at] = b"0123456789abcdef"[(left % radix as u64) as usize];
        left /= radix as u64;
        if left == 0 {
            break;
        }
    }
    if integer < 0 {
        at -= 1;
        digits[at] = b'-';
    }
    let text = std::str::from_utf8(&digits[at..]).expect("digits are ASCII");
    Ok(string::from_str(&Strings::new(mc), text)?.value())
}

/// Returns the total significant bit count of exact parts in number `number` beyond the initial
/// bit, such that 0, 1, and -1 yield zero bits.
pub(super) fn exact_bits<'gc>(nums: &Nums<'_, 'gc>, number: Number<'gc>) -> u64 {
    #[inline(always)]
    fn bits<'gc>(nums: &Nums<'_, 'gc>, integer: Integer<'gc>) -> u64 {
        int::integer_length(nums, integer).saturating_sub(1)
    }
    #[inline(always)]
    fn real<'gc>(nums: &Nums<'_, 'gc>, part: Real<'gc>) -> u64 {
        match nums.real_view(part) {
            RealView::Flonum(_) => 0,
            RealView::Exact(rational) => match nums.rational_view(rational) {
                RationalView::Integer(integer) => bits(nums, integer),
                RationalView::Ratio { num, den } => bits(nums, num) + bits(nums, den),
            },
        }
    }
    match nums.complex_view(number) {
        ComplexView::Real(part) => real(nums, part),
        ComplexView::Complex { re, im } => real(nums, re) + real(nums, im),
    }
}

/// Deducts VM fuel proportional to the square of the bit-length of the exact components of `number`,
/// modeling the quadratic complexity of multi-precision division and multiplication.
fn charge_squared<'gc>(nums: &Nums<'_, 'gc>, fuel: &mut Fuel, number: Number<'gc>) -> Result<(), Fault> {
    let words = exact_bits(nums, number) / 64;
    fuel.spend(words.saturating_mul(words) / equal::PER_FUEL)
}

/// Extracts `value` as an exact integer and returns a tuple containing the integer and a boolean
/// flag that is `true` if `value` was already an exact integer, or `false` if it was an inexact
/// floating-point number with an integral value.
fn integral<'gc>(mc: &Mutation<'gc>, nums: &Nums<'_, 'gc>, value: Value<'gc>) -> Result<(Integer<'gc>, bool), Fault> {
    if let Some(integer) = nums.integer(value) {
        return Ok((integer, true));
    }
    match value.as_flonum(mc) {
        Some(float) if float.is_finite() && float.fract() == 0.0 => Ok((int::from_integral_f64(nums, float)?, false)),
        _ if nums.number(value).is_some() => Err(Fault::Num(NumError::NotInteger)),
        _ => Err(Fault::WrongType),
    }
}

/// Deducts VM fuel and reserves heap memory before calculating exact exponentiation `base^exponent`,
/// accounting for both the memory footprint of the digits and the quadratic work required by
/// exponentiation-by-squaring.
pub(super) fn charge_power<'gc>(mc: &Mutation<'gc>, nums: &Nums<'_, 'gc>, fuel: &mut Fuel, base: Number<'gc>, exponent: Number<'gc>) -> Result<(), Fault> {
    let ComplexView::Real(power) = nums.complex_view(exponent) else { return Ok(()) };
    let RealView::Exact(power) = nums.real_view(power) else { return Ok(()) };
    let RationalView::Integer(power) = nums.rational_view(power) else { return Ok(()) };
    // An exact integer exponent that exceeds 64 bits would exhaust available memory for any
    // base other than 0, 1, or -1 (which are handled as special cases by `expt`).
    let Some(power) = int::to_i64(nums, power) else { return Ok(()) };
    let words = exact_bits(nums, base).saturating_mul(power.unsigned_abs()) / 64;
    mc.ensure(usize::try_from(words.saturating_mul(8)).unwrap_or(usize::MAX))?;
    fuel.spend(words.saturating_mul(words) / equal::PER_FUEL)
}

/// Tests whether relational operator `op` holds across pairwise consecutive numeric arguments
/// in `xs` (`=` accepts general complex numbers, whereas inequality operators require real
/// numbers). All arguments are validated for correct numeric types even if an earlier
/// comparison fails.
pub(super) fn compare<'gc>(mc: &Mutation<'gc>, op: Intrinsic, mut xs: impl Iterator<Item = Value<'gc>>) -> Result<bool, Fault> {
    #[inline(always)]
    fn holds(op: Intrinsic, order: Ordering) -> bool {
        match op {
            Intrinsic::Lt => order.is_lt(),
            Intrinsic::Gt => order.is_gt(),
            Intrinsic::Le => order.is_le(),
            Intrinsic::Ge => order.is_ge(),
            _ => order.is_eq(),
        }
    }
    #[inline(always)]
    fn number<'gc>(nums: &Nums<'_, 'gc>, value: Value<'gc>) -> Result<Number<'gc>, Fault> {
        nums.number(value).ok_or(Fault::WrongType)
    }
    #[inline(always)]
    fn real<'gc>(nums: &Nums<'_, 'gc>, value: Value<'gc>) -> Result<Real<'gc>, Fault> {
        nums.real(value).ok_or(Fault::WrongType)
    }
    #[inline(always)]
    fn check<'gc>(nums: &Nums<'_, 'gc>, op: Intrinsic, value: Value<'gc>) -> Result<(), Fault> {
        if op == Intrinsic::NumEq {
            number(nums, value).map(drop)
        } else {
            real(nums, value).map(drop)
        }
    }
    let nums = Nums::new(mc);
    let mut before = xs.next().ok_or(Fault::Arity)?;
    let mut so_far = true;
    if before.as_fixnum().is_none() {
        check(&nums, op, before)?;
    }
    for next in xs {
        let fixnums = before.as_fixnum().zip(next.as_fixnum());
        if fixnums.is_none() {
            check(&nums, op, next)?;
        }
        if so_far {
            so_far = match fixnums {
                Some((left, right)) => holds(op, left.cmp(&right)),
                None if op == Intrinsic::NumEq => complex::equal(&nums, number(&nums, before)?, number(&nums, next)?)?,
                None => real::compare(&nums, real(&nums, before)?, real(&nums, next)?)?.is_some_and(|order| holds(op, order)),
            };
        }
        before = next;
    }
    Ok(so_far)
}
