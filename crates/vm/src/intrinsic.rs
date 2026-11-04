//! An [`Intrinsic`] computes a value from its arguments in place, inside a step: it never touches frames
//! or calls a procedure, so it can't be captured halfway or re-enter the VM. Anything that calls a
//! procedure or changes the continuation is a [`crate::Request`] instead.

use ragwort_types::gc::{Frame, Mutation, Value};
use ragwort_types::num::{Nums, complex};
use ragwort_types::pair::{Pair, Pairs};

use crate::op::Fuel;
use crate::{Fault, equal};
use crate::objects::{self, BoxFields, Condition, MultiValue, MultiValueFields, Tag};

#[repr(u16)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Intrinsic {
    /// `+`: fixnums are added in place, anything else by the generic add.
    Add,
    /// (cons a d)
    Cons,
    /// (car lst)
    Car,
    /// (cdr lst)
    Cdr,
    /// `eq?`.
    Eq,
    /// `eqv?`: `eq?`, or numbers of the same exactness and value.
    Eqv,
    /// `equal?`: `eqv?`, or strings, pairs, vectors or boxes with `equal?` contents. It ends on
    /// cyclic ones, and spends a unit of fuel for each 1024 values it compares, faulting with
    /// [`Fault::OutOfFuel`] as soon as there's none left.
    Equal,
    /// `null?`.
    IsNull,
    /// `pair?`.
    IsPair,
    /// `box?`.
    IsBox,
    /// `(box x)`: create a new box holding `x` returning the newly created box
    MakeBox,
    /// `(unbox b)`: returns the contents of the box `b`
    Unbox,
    /// `(set-box! b x)`: sets the contents of the box `b` to `x` returning void.
    SetBox,
    /// `(make-continuation-prompt-tag [name])`.
    MakePromptTag,
    /// `(values x ...)`: `x` alone, or any other number of values as a [`MultiValue`].
    Values,
    /// `(values? x)`: whether `x` is a [`MultiValue`].
    IsValues,
    /// `(values-length mv)`.
    ValuesLength,
    /// `(values-ref mv k)`.
    ValuesRef,
    /// `(make-error message irritant ...)`: a `Condition` of [`Fault::Error`], which the
    /// prelude's `error` raises.
    MakeError,
}

impl Intrinsic {
    /// How many arguments it takes, or `None` for any number.
    pub fn arity(self) -> Option<u8> {
        match self {
            Intrinsic::Add | Intrinsic::MakePromptTag | Intrinsic::Values | Intrinsic::MakeError => None,
            Intrinsic::Car | Intrinsic::Cdr | Intrinsic::IsNull | Intrinsic::IsPair | Intrinsic::IsBox | Intrinsic::MakeBox | Intrinsic::Unbox => Some(1),
            Intrinsic::IsValues | Intrinsic::ValuesLength => Some(1),
            Intrinsic::Cons | Intrinsic::Eq | Intrinsic::Eqv | Intrinsic::Equal | Intrinsic::SetBox | Intrinsic::ValuesRef => Some(2),
        }
    }

    /// Runs it on the `args` registers from `base`, which the caller has checked are in the
    /// frame and as many as it takes, spending `fuel` on what does a lot of work.
    #[inline(always)]
    pub(crate) fn run<'gc>(self, mc: &Mutation<'gc>, frame: Frame<'_, 'gc>, base: u8, args: u8, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        let arg = |i: u8| frame.get(base + i);
        let boolean = |b: bool| if b { Value::TRUE } else { Value::FALSE };
        Ok(match self {
            Intrinsic::Add => {
                let mut sum = Value::fixnum(0).expect("0 is a fixnum");
                for i in 0..args {
                    let x = arg(i);
                    sum = match sum.fixnum_add(x) {
                        Some(sum) => sum,
                        None => {
                            let h = Nums::new(mc);
                            let (a, b) = (h.number(sum).ok_or(Fault::WrongType)?, h.number(x).ok_or(Fault::WrongType)?);
                            made(mc, fuel, complex::add(&h, a, b)?.value())
                        }
                    };
                }
                sum
            }
            Intrinsic::Cons => made(mc, fuel, Pairs::new(mc).cons(arg(0), arg(1))?.value(mc)),
            Intrinsic::Car => Pair::of(arg(0)).ok_or(Fault::WrongType)?.head(mc),
            Intrinsic::Cdr => Pair::of(arg(0)).ok_or(Fault::WrongType)?.tail(mc),
            Intrinsic::Eq => boolean(arg(0) == arg(1)),
            Intrinsic::Eqv => boolean(equal::eqv(mc, arg(0), arg(1))),
            Intrinsic::Equal => {
                let most = fuel.left().saturating_add(1).saturating_mul(equal::PER_FUEL) - 1;
                let (same, compared) = equal::equal(mc, arg(0), arg(1), most)?;
                fuel.spend(compared / equal::PER_FUEL)?;
                boolean(same)
            }
            Intrinsic::IsNull => boolean(arg(0) == Value::NIL),
            Intrinsic::IsPair => boolean(Pair::of(arg(0)).is_some()),
            Intrinsic::IsBox => boolean(arg(0).downcast::<objects::Box>(mc).is_some()),
            Intrinsic::MakeBox => made(mc, fuel, Value::object(mc, objects::Box::new(mc, arg(0))?)),
            Intrinsic::Unbox => arg(0).downcast::<objects::Box>(mc).ok_or(Fault::WrongType)?.value(mc),
            Intrinsic::SetBox => {
                arg(0).downcast::<objects::Box>(mc).ok_or(Fault::WrongType)?.set_value(mc, arg(1));
                Value::VOID
            }
            Intrinsic::MakePromptTag => match args {
                0 => made(mc, fuel, Value::object(mc, Tag::new(mc, Value::VOID)?)),
                1 => made(mc, fuel, Value::object(mc, Tag::new(mc, arg(0))?)),
                _ => return Err(Fault::Arity),
            },
            Intrinsic::Values => made(mc, fuel, values(mc, (0..args).map(arg))?),
            Intrinsic::IsValues => boolean(arg(0).downcast::<MultiValue>(mc).is_some()),
            Intrinsic::ValuesLength => {
                let items = arg(0).downcast::<MultiValue>(mc).ok_or(Fault::WrongType)?.items(mc);
                Value::fixnum(items.len() as i64).ok_or(Fault::WrongType)?
            }
            Intrinsic::ValuesRef => {
                let items = arg(0).downcast::<MultiValue>(mc).ok_or(Fault::WrongType)?.items(mc);
                let k = arg(1).as_fixnum().and_then(|k| usize::try_from(k).ok()).filter(|&k| k < items.len());
                items.get(k.ok_or(Fault::WrongType)?)
            }
            Intrinsic::MakeError if args == 0 => return Err(Fault::Arity),
            Intrinsic::MakeError => {
                let pairs = Pairs::new(mc);
                let mut irritants = Value::NIL;
                for i in (1..args).rev() {
                    irritants = pairs.cons(arg(i), irritants)?.value(mc);
                }
                made(mc, fuel, Value::object(mc, Condition::new(mc, mc.frozen(Fault::Error)?, arg(0), irritants)?))
            }
        })
    }
}

/// `value`, just made. If making it has made the step due, the run pauses at its next call or
/// jump, so the step can end and the collector keep up.
#[inline(always)]
fn made<'gc>(mc: &Mutation<'gc>, fuel: &mut Fuel, value: Value<'gc>) -> Value<'gc> {
    if mc.step_due() {
        fuel.pause();
    }
    value
}

/// What `(values x ...)` returns for `values`: one as itself, any other number as a [`MultiValue`].
pub(crate) fn values<'gc>(mc: &Mutation<'gc>, values: impl ExactSizeIterator<Item = Value<'gc>>) -> Result<Value<'gc>, Fault> {
    let mut values = values.peekable();
    if values.len() == 1 {
        return values.next().ok_or(Fault::Malformed);
    }
    let object = MultiValue::new(mc, values.len(), Value::VOID)?;
    let items = object.items(mc);
    values.enumerate().for_each(|(i, value)| items.set(mc, i, value));
    Ok(Value::object(mc, object))
}
