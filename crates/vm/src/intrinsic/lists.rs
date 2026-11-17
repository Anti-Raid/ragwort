//! Pair and list intrinsics.

use ragwort_types::gc::{Mutation, ScratchVec, Value};
use ragwort_types::pair::{Pair, Pairs};

use crate::op::Fuel;
use crate::{Fault, equal};

use super::{Intrinsic, made};

#[inline(always)]
pub(super) fn car<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> Result<Value<'gc>, Fault> {
    Ok(Pair::of(value).ok_or(Fault::WrongType)?.head(mc))
}

#[inline(always)]
pub(super) fn cdr<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> Result<Value<'gc>, Fault> {
    Ok(Pair::of(value).ok_or(Fault::WrongType)?.tail(mc))
}

/// Implements `(reverse xs)`, constructing and returning a newly allocated proper list
/// containing the elements of `xs` in reverse order while deducting fuel for list traversal.
pub(super) fn reverse<'gc>(mc: &Mutation<'gc>, xs: Value<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
    let pairs = Pairs::new(mc);
    let len = pairs.list_len(xs).ok_or(Fault::WrongType)?;
    if len == 0 {
        return Ok(Value::NULL);
    }
    fuel.spend(len / equal::PER_FUEL)?;
    let mut acc = Value::NULL;
    for item in pairs.elements(xs) {
        acc = pairs.cons(item, acc)?.value(mc);
    }
    Ok(made(mc, fuel, acc))
}

/// Implements list searching intrinsics `memq`, `memv`, `member`, `assq`, `assv`, and `assoc`
/// using the equality semantics appropriate for each variant.
pub(super) fn find<'gc>(mc: &Mutation<'gc>, kind: Intrinsic, target: Value<'gc>, mut xs: Value<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
    let assoc = matches!(kind, Intrinsic::Assq | Intrinsic::Assv | Intrinsic::Assoc);
    let mut steps = 0u64;
    while xs != Value::NULL {
        let pair = Pair::of(xs).ok_or(Fault::WrongType)?;
        let item = pair.head(mc);
        let candidate = if assoc { Pair::of(item).ok_or(Fault::WrongType)?.head(mc) } else { item };
        let prev = steps / equal::PER_FUEL;
        let matched = match kind {
            Intrinsic::Memq | Intrinsic::Assq => {
                steps += 1;
                target == candidate
            }
            Intrinsic::Memv | Intrinsic::Assv => {
                steps += 1;
                equal::eqv(mc, target, candidate)
            }
            _ => {
                // `most` is the largest number of comparisons that the remaining fuel pays for. The search spends one unit for every `PER_FUEL` steps, counted over the whole list. The `steps % PER_FUEL` steps since the last whole unit already count towards the next unit, so they are subtracted.
                let most = fuel
                    .left()
                    .saturating_add(1)
                    .saturating_mul(equal::PER_FUEL)
                    .saturating_sub(steps % equal::PER_FUEL)
                    .saturating_sub(1);
                let (same, compared) = equal::equal(mc, target, candidate, most)?;
                steps = steps.saturating_add(compared);
                same
            }
        };
        fuel.spend(steps / equal::PER_FUEL - prev)?;
        if matched {
            return Ok(if assoc { item } else { xs });
        }
        xs = pair.tail(mc);
    }
    Ok(Value::FALSE)
}

/// Implements `(append list ... [obj])`, copying each proper list preceding the final
/// non-empty argument onto the terminal tail. Because pairs are immutable, trailing empty list
/// `'()` arguments following a proper list require no copying.
pub(super) fn append<'gc>(mc: &Mutation<'gc>, args: impl ExactSizeIterator<Item = Value<'gc>>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
    let pairs = Pairs::new(mc);
    let mut lists = ScratchVec::new(mc);
    let len = args.len();
    for (i, arg) in args.enumerate() {
        if i + 1 < len && !pairs.is_list(arg) {
            return Err(Fault::WrongType);
        }
        lists.push(arg)?;
    }
    let Some(mut last) = len.checked_sub(1) else { return Ok(Value::NULL) };
    while last > 0 && lists[last] == Value::NULL {
        last -= 1;
    }
    let tail = lists[last];
    let total: u64 = (0..last).map(|i| pairs.list_len(lists[i]).unwrap_or(0)).sum();
    if total == 0 {
        return Ok(tail);
    }
    fuel.spend(total / equal::PER_FUEL)?;
    let mut items = ScratchVec::new(mc);
    for &list in &lists[..last] {
        for item in pairs.elements(list) {
            items.push(item)?;
        }
    }
    Ok(made(mc, fuel, pairs.list_with_tail(items.iter().copied(), tail)?))
}

/// Traverses `count` pair links starting from `xs` and returns the resulting sublist tail, faulting
/// if `xs` is too short or if `need_pair` is true and the resulting tail is not a pair.
pub(super) fn list_tail<'gc>(mc: &Mutation<'gc>, mut xs: Value<'gc>, count: usize, need_pair: bool, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
    if let Some(len) = Pairs::new(mc).list_len(xs) {
        let max = if need_pair { len } else { len.saturating_add(1) };
        if count as u64 >= max {
            return Err(Fault::OutOfRange);
        }
    }
    fuel.spend(count as u64 / equal::PER_FUEL)?;
    for _ in 0..count {
        let pair = Pair::of(xs).ok_or(if xs == Value::NULL { Fault::OutOfRange } else { Fault::WrongType })?;
        xs = pair.tail(mc);
    }
    if need_pair && Pair::of(xs).is_none() {
        return Err(if xs == Value::NULL { Fault::OutOfRange } else { Fault::WrongType });
    }
    Ok(xs)
}
