//! Vector and bytevector intrinsics.

use ragwort_types::bytevector::{AnyBytevector, Bytevectors};
use ragwort_types::gc::{Mutation, Value};
use ragwort_types::num::{Nums, int};
use ragwort_types::pair::Pairs;
use ragwort_types::vector::{AnyVector, Vectors};

use crate::op::Fuel;
use crate::{Fault, equal};

use super::{Intrinsic, Operands, boolean, fixnum, index, made, not_fixnum};

impl Intrinsic {
    /// Evaluates an intrinsic that makes or converts a vector on `operands`.
    #[inline(never)]
    pub(super) fn vector<'gc>(self, mc: &Mutation<'gc>, operands: impl Operands<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        Ok(match self {
            Intrinsic::MakeVector => {
                let fill = match operands.count() {
                    1 => fixnum(0),
                    2 => operands.get(1),
                    _ => return Err(Fault::Arity),
                };
                let len = index(operands.get(0))?;
                fuel.spend(len as u64 / equal::PER_FUEL)?;
                made(mc, fuel, Vectors::new(mc).make(len, fill)?.value(mc))
            }
            Intrinsic::MakeVectorOf => {
                let vector = Vectors::new(mc).make(operands.count(), Value::VOID)?;
                let items = vector.items(mc);
                (0..operands.count()).for_each(|i| items.set(mc, i, operands.get(i)));
                made(mc, fuel, vector.value(mc))
            }
            Intrinsic::VectorToList => {
                let vector = AnyVector::of(operands.get(0)).ok_or(Fault::WrongType)?;
                let len = vector.len(mc);
                fuel.spend(len as u64 / equal::PER_FUEL)?;
                let pairs = Pairs::new(mc);
                let mut list = Value::NULL;
                for i in (0..len).rev() {
                    list = pairs.cons(vector.get(mc, i).expect("in range"), list)?.value(mc);
                }
                made(mc, fuel, list)
            }
            Intrinsic::ListToVector => {
                let pairs = Pairs::new(mc);
                let len = pairs.list_len(operands.get(0)).ok_or(Fault::WrongType)?;
                fuel.spend(len / equal::PER_FUEL)?;
                let vector = Vectors::new(mc).make(usize::try_from(len).map_err(|_| Fault::OutOfMemory)?, Value::VOID)?;
                let items = vector.items(mc);
                pairs.elements(operands.get(0)).enumerate().for_each(|(i, item)| items.set(mc, i, item));
                made(mc, fuel, vector.value(mc))
            }
            _ => unreachable!("{self:?} isn't a vector procedure"),
        })
    }

    /// Evaluates a bytevector intrinsic on `operands`.
    #[inline(never)]
    pub(super) fn bytevector<'gc>(self, mc: &Mutation<'gc>, operands: impl Operands<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        Ok(match self {
            Intrinsic::IsBytevector => boolean(AnyBytevector::of(operands.get(0)).is_some()),
            Intrinsic::MakeBytevector => {
                let fill = match operands.count() {
                    1 => 0,
                    2 => byte(mc, operands.get(1))?,
                    _ => return Err(Fault::Arity),
                };
                made(mc, fuel, Bytevectors::new(mc).make(index(operands.get(0))?, fill)?.value(mc))
            }
            Intrinsic::BytevectorLength => {
                let len = AnyBytevector::of(operands.get(0)).ok_or(Fault::WrongType)?.len(mc);
                Value::fixnum(len as i64).expect("lengths are fixnums")
            }
            Intrinsic::BytevectorRef => {
                let bytes = AnyBytevector::of(operands.get(0)).ok_or(Fault::WrongType)?;
                let (big, (size, signed)) = (big_endian(operands.get(2))?, int_kind(operands.get(3))?);
                let number = bytes.get_uint(mc, index(operands.get(1))?, size).ok_or(Fault::OutOfRange)?;
                let unused = 64 - size as u32 * 8;
                let number = if big { number.swap_bytes() >> unused } else { number };
                let nums = Nums::new(mc);
                if signed {
                    let number = ((number << unused) as i64) >> unused;
                    match Value::fixnum(number) {
                        Some(value) => value,
                        None => made(mc, fuel, int::from_i64(&nums, number)?.value()),
                    }
                } else {
                    match i64::try_from(number).ok().and_then(Value::fixnum) {
                        Some(value) => value,
                        None => made(mc, fuel, int::from_u64(&nums, number)?.value()),
                    }
                }
            }
            Intrinsic::BytevectorSet => {
                let bytes = AnyBytevector::of(operands.get(0)).ok_or(Fault::WrongType)?;
                let nums = Nums::new(mc);
                let integer = nums.integer(operands.get(2)).ok_or(Fault::WrongType)?;
                let (big, (size, signed)) = (big_endian(operands.get(3))?, int_kind(operands.get(4))?);
                let unused = 64 - size as u32 * 8;
                let number = if signed {
                    int::to_i64(&nums, integer).filter(|&number| (number << unused) >> unused == number).map(|number| number as u64)
                } else {
                    int::to_u64(&nums, integer).filter(|&number| number <= u64::MAX >> unused)
                };
                let number = number.ok_or(Fault::OutOfRange)?;
                let AnyBytevector::Mutable(bytes) = bytes else { return Err(Fault::Immutable) };
                let number = if big { (number << unused).swap_bytes() } else { number };
                if !bytes.set_uint(mc, index(operands.get(1))?, size, number) {
                    return Err(Fault::OutOfRange);
                }
                Value::VOID
            }
            _ => unreachable!("{self:?} isn't a bytevector procedure"),
        })
    }
}

/// Parses a bytevector endianness indicator value into a boolean (`true` for big-endian `#t`,
/// `false` for little-endian `#f`).
fn big_endian(value: Value<'_>) -> Result<bool, Fault> {
    if value == Value::TRUE || value == Value::FALSE { Ok(value == Value::TRUE) } else { Err(Fault::WrongType) }
}

/// Parses a bytevector integer size and signedness descriptor, returning the byte width (1 to
/// 8) and a boolean indicating whether the integer is signed.
fn int_kind(value: Value<'_>) -> Result<(usize, bool), Fault> {
    let kind = value.as_fixnum().ok_or(Fault::WrongType)?;
    let size = kind.unsigned_abs() as usize;
    if !(1..=8).contains(&size) {
        return Err(Fault::OutOfRange);
    }
    Ok((size, kind < 0))
}

/// Validates that `value` is a fixnum in the range `0..=255`, returning `u8` on success,
/// [`Fault::OutOfRange`] for any other exact integer, or [`Fault::WrongType`].
pub(super) fn byte<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> Result<u8, Fault> {
    let number = value.as_fixnum().ok_or_else(|| not_fixnum(mc, value))?;
    u8::try_from(number).map_err(|_| Fault::OutOfRange)
}
