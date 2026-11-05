//! An [`Intrinsic`] computes a value from its arguments in place, inside a step: it never touches frames
//! or calls a procedure, so it can't be captured halfway or re-enter the VM. Anything that calls a
//! procedure or changes the continuation is a [`crate::Request`] instead.

use ragwort_types::Error;
use ragwort_types::bytevector::{AnyBytevector, Bytevectors};
use ragwort_types::gc::{Frame, Mutation, Value};
use ragwort_types::named;
use ragwort_types::num::{Number, Nums, complex};
use ragwort_types::pair::{Pair, Pairs};

use crate::op::Fuel;
use crate::{Fault, equal};
use crate::objects::{self, BoxFields, Condition, Global, GlobalFields, MultiValue, MultiValueFields, Tag};

named! {
    #[repr(u16)]
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum Intrinsic {
        /// `+`: fixnums are added in place, anything else by the generic add.
        Add = "+",
        /// `(- z)` negates, `(- z1 z2 ...)` subtracts the rest from the first.
        Sub = "-",
        /// `*`: fixnums are multiplied in place, anything else by the generic multiply.
        Mul = "*",
        /// `(/ z)` is the reciprocal, `(/ z1 z2 ...)` divides the first by the rest. Fixnums that
        /// divide exactly stay in place; an exact zero divisor faults with
        /// [`NumError::DivideByZero`](ragwort_types::num::NumError::DivideByZero).
        Div = "/",
        /// (cons a d)
        Cons = "cons",
        /// (car lst)
        Car = "car",
        // `caar` to `cddddr`: the `car`s and `cdr`s their names spell, the last letter first.
        /// (cdr lst)
        Cdr = "cdr",
        Caar = "caar",
        Cadr = "cadr",
        Cdar = "cdar",
        Cddr = "cddr",
        Caaar = "caaar",
        Caadr = "caadr",
        Cadar = "cadar",
        Caddr = "caddr",
        Cdaar = "cdaar",
        Cdadr = "cdadr",
        Cddar = "cddar",
        Cdddr = "cdddr",
        Caaaar = "caaaar",
        Caaadr = "caaadr",
        Caadar = "caadar",
        Caaddr = "caaddr",
        Cadaar = "cadaar",
        Cadadr = "cadadr",
        Caddar = "caddar",
        Cadddr = "cadddr",
        Cdaaar = "cdaaar",
        Cdaadr = "cdaadr",
        Cdadar = "cdadar",
        Cdaddr = "cdaddr",
        Cddaar = "cddaar",
        Cddadr = "cddadr",
        Cdddar = "cdddar",
        Cddddr = "cddddr",
        /// `eq?`.
        Eq = "eq?",
        /// `eqv?`: `eq?`, or numbers of the same exactness and value.
        Eqv = "eqv?",
        /// `equal?`: `eqv?`, or strings, pairs, vectors or boxes with `equal?` contents. It ends on
        /// cyclic ones, and spends a unit of fuel for each 1024 values it compares, faulting with
        /// [`Fault::OutOfFuel`] as soon as there's none left.
        Equal = "equal?",
        /// `null?`.
        IsNull = "null?",
        /// `pair?`.
        IsPair = "pair?",
        /// `box?`.
        IsBox = "box?",
        /// `boolean?`.
        IsBoolean = "boolean?",
        /// `(void x ...)`: void, whatever it's given.
        Void = "void",
        /// `bytevector?`.
        IsBytevector = "bytevector?",
        /// `(make-bytevector k [byte])`: a mutable bytevector of `k` copies of `byte`, or of 0.
        MakeBytevector = "make-bytevector",
        /// `(bytevector-length bv)`.
        BytevectorLength = "bytevector-length",
        /// `(bytevector-u8-ref bv k)`.
        BytevectorRef = "bytevector-u8-ref",
        /// `(bytevector-u8-set! bv k byte)` of a mutable bytevector, returning void.
        BytevectorSet = "bytevector-u8-set!",
        /// `(box x)`: create a new box holding `x` returning the newly created box
        MakeBox = "box",
        /// `(unbox b)`: returns the contents of the box `b`
        Unbox = "unbox",
        /// `(set-box! b x)`: sets the contents of the box `b` to `x` returning void.
        SetBox = "set-box!",
        /// `(make-continuation-prompt-tag [name])`.
        MakePromptTag = "make-continuation-prompt-tag",
        /// `(values x ...)`: `x` alone, or any other number of values as a [`MultiValue`].
        Values = "values",
        /// `(values? x)`: whether `x` is a [`MultiValue`].
        IsValues = "values?",
        /// `(values-length mv)`.
        ValuesLength = "values-length",
        /// `(values-ref mv k)`.
        ValuesRef = "values-ref",
        /// The value of the [`Global`] `g`, or [`Fault::Unbound`] if it isn't defined.
        GlobalRef = "global-ref",
        /// `(set! g v)` of the defined [`Global`] `g`, returning void.
        GlobalSet = "global-set!",
        /// `(define g v)` of the [`Global`] `g`, defined or not, returning void.
        DefineGlobal = "define-global",
        /// `(make-error message irritant ...)`: a `Condition` of [`Fault::Error`], which the
        /// prelude's `error` raises.
        MakeError = "make-error",
    }
}

impl Intrinsic {
    /// How many arguments it takes, or `None` for any number.
    pub fn arity(self) -> Option<u8> {
        match self {
            Intrinsic::Add | Intrinsic::Sub | Intrinsic::Mul | Intrinsic::Div => None,
            Intrinsic::MakePromptTag | Intrinsic::Values | Intrinsic::MakeError | Intrinsic::Void | Intrinsic::MakeBytevector => None,
            Intrinsic::IsBytevector | Intrinsic::BytevectorLength => Some(1),
            Intrinsic::Car | Intrinsic::Cdr | Intrinsic::IsNull | Intrinsic::IsPair | Intrinsic::IsBox | Intrinsic::MakeBox | Intrinsic::Unbox => Some(1),
            Intrinsic::IsValues | Intrinsic::ValuesLength | Intrinsic::GlobalRef | Intrinsic::IsBoolean => Some(1),
            Intrinsic::Caar | Intrinsic::Cadr | Intrinsic::Cdar | Intrinsic::Cddr | Intrinsic::Caaar | Intrinsic::Caadr | Intrinsic::Cadar | Intrinsic::Caddr | Intrinsic::Cdaar | Intrinsic::Cdadr | Intrinsic::Cddar | Intrinsic::Cdddr | Intrinsic::Caaaar | Intrinsic::Caaadr | Intrinsic::Caadar | Intrinsic::Caaddr | Intrinsic::Cadaar | Intrinsic::Cadadr | Intrinsic::Caddar | Intrinsic::Cadddr | Intrinsic::Cdaaar | Intrinsic::Cdaadr | Intrinsic::Cdadar | Intrinsic::Cdaddr | Intrinsic::Cddaar | Intrinsic::Cddadr | Intrinsic::Cdddar | Intrinsic::Cddddr => Some(1),
            Intrinsic::BytevectorRef => Some(2),
            Intrinsic::BytevectorSet => Some(3),
            Intrinsic::GlobalSet | Intrinsic::DefineGlobal => Some(2),
            Intrinsic::Cons | Intrinsic::Eq | Intrinsic::Eqv | Intrinsic::Equal | Intrinsic::SetBox | Intrinsic::ValuesRef => Some(2),
        }
    }

    /// Runs it on `args`, as the VM does on registers, but without a frame: for a compiler folding
    /// a call of constants, for one. Whether a call can be folded, as one that makes a new box
    /// or sets a global can't, is the caller's to know.
    #[inline]
    pub fn run<'gc>(self, mc: &Mutation<'gc>, args: &[Value<'gc>], fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        if self.arity().is_some_and(|arity| usize::from(arity) != args.len()) {
            return Err(Fault::Arity);
        }
        self.apply(mc, |i| args[i], args.len(), fuel)
    }

    /// Runs it on the `args` registers from `base`, which the caller has checked are in the
    /// frame and as many as it takes, spending `fuel` on what does a lot of work.
    #[inline(always)]
    pub(crate) fn exec<'gc>(self, mc: &Mutation<'gc>, frame: Frame<'_, 'gc>, base: u8, args: u8, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        self.apply(mc, |i| frame.get(base + i as u8), usize::from(args), fuel)
    }

    /// Runs it on the `args` values `arg` reads, as many as it takes.
    #[inline(always)]
    fn apply<'gc>(self, mc: &Mutation<'gc>, arg: impl Fn(usize) -> Value<'gc>, args: usize, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        let boolean = |b: bool| if b { Value::TRUE } else { Value::FALSE };
        Ok(match self {
            Intrinsic::Add => arith(mc, fuel, fixnum(0), (0..args).map(&arg), Value::fixnum_add, |h, a, b| complex::add(h, a, b))?,
            Intrinsic::Mul => arith(mc, fuel, fixnum(1), (0..args).map(&arg), Value::fixnum_mul, |h, a, b| complex::mul(h, a, b))?,
            Intrinsic::Sub | Intrinsic::Div if args == 0 => return Err(Fault::Arity),
            Intrinsic::Sub => {
                let (first, rest) = if args == 1 { (fixnum(0), 0) } else { (arg(0), 1) };
                arith(mc, fuel, first, (rest..args).map(&arg), Value::fixnum_sub, |h, a, b| complex::sub(h, a, b))?
            }
            Intrinsic::Div => {
                let (first, rest) = if args == 1 { (fixnum(1), 0) } else { (arg(0), 1) };
                arith(mc, fuel, first, (rest..args).map(&arg), fixnum_div, |h, a, b| complex::div(h, a, b))?
            }
            Intrinsic::Cons => made(mc, fuel, Pairs::new(mc).cons(arg(0), arg(1))?.value(mc)),
            Intrinsic::Car => Pair::of(arg(0)).ok_or(Fault::WrongType)?.head(mc),
            Intrinsic::Cdr => Pair::of(arg(0)).ok_or(Fault::WrongType)?.tail(mc),
            Intrinsic::Caar | Intrinsic::Cadr | Intrinsic::Cdar | Intrinsic::Cddr | Intrinsic::Caaar | Intrinsic::Caadr | Intrinsic::Cadar | Intrinsic::Caddr | Intrinsic::Cdaar | Intrinsic::Cdadr | Intrinsic::Cddar | Intrinsic::Cdddr | Intrinsic::Caaaar | Intrinsic::Caaadr | Intrinsic::Caadar | Intrinsic::Caaddr | Intrinsic::Cadaar | Intrinsic::Cadadr | Intrinsic::Caddar | Intrinsic::Cadddr | Intrinsic::Cdaaar | Intrinsic::Cdaadr | Intrinsic::Cdadar | Intrinsic::Cdaddr | Intrinsic::Cddaar | Intrinsic::Cddadr | Intrinsic::Cdddar | Intrinsic::Cddddr => {
                let path = self.name().as_bytes();
                let mut x = arg(0);
                for &step in path[1..path.len() - 1].iter().rev() {
                    let pair = Pair::of(x).ok_or(Fault::WrongType)?;
                    x = if step == b'a' { pair.head(mc) } else { pair.tail(mc) };
                }
                x
            }
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
            Intrinsic::IsBoolean => boolean(arg(0) == Value::TRUE || arg(0) == Value::FALSE),
            Intrinsic::Void => Value::VOID,
            Intrinsic::IsBytevector => boolean(AnyBytevector::of(arg(0)).is_some()),
            Intrinsic::MakeBytevector => {
                let fill = match args {
                    1 => 0,
                    2 => byte(arg(1))?,
                    _ => return Err(Fault::Arity),
                };
                made(mc, fuel, Bytevectors::new(mc).make(index(arg(0))?, fill)?.value(mc))
            }
            Intrinsic::BytevectorLength => {
                let len = AnyBytevector::of(arg(0)).ok_or(Fault::WrongType)?.len(mc);
                Value::fixnum(len as i64).expect("lengths are fixnums")
            }
            Intrinsic::BytevectorRef => {
                let bytes = AnyBytevector::of(arg(0)).ok_or(Fault::WrongType)?;
                let byte = bytes.get(mc, index(arg(1))?).ok_or(Fault::OutOfRange)?;
                Value::fixnum(i64::from(byte)).expect("bytes are fixnums")
            }
            Intrinsic::BytevectorSet => {
                let bytes = AnyBytevector::of(arg(0)).ok_or(Fault::WrongType)?;
                let byte = byte(arg(2))?;
                let AnyBytevector::Mutable(bytes) = bytes else { return Err(Fault::Immutable) };
                if !bytes.set(mc, index(arg(1))?, byte) {
                    return Err(Fault::OutOfRange);
                }
                Value::VOID
            }
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
                let k = index(arg(1))?;
                if k >= items.len() {
                    return Err(Fault::OutOfRange);
                }
                items.get(k)
            }
            Intrinsic::GlobalRef => {
                let global = arg(0).downcast::<Global>(mc).ok_or(Fault::WrongType)?;
                if !global.defined(mc) {
                    return Err(Fault::Unbound);
                }
                global.value(mc)
            }
            Intrinsic::GlobalSet | Intrinsic::DefineGlobal => {
                let global = arg(0).downcast::<Global>(mc).ok_or(Fault::WrongType)?;
                if self == Intrinsic::GlobalSet && !global.defined(mc) {
                    return Err(Fault::Unbound);
                }
                global.set_value(mc, arg(1));
                global.set_defined(mc, true);
                Value::VOID
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

fn fixnum<'gc>(n: i64) -> Value<'gc> {
    Value::fixnum(n).expect("a small fixnum")
}

/// `a / b` if both are fixnums and it's one.
fn fixnum_div<'gc>(a: Value<'gc>, b: Value<'gc>) -> Option<Value<'gc>> {
    let (a, b) = (a.as_fixnum()?, b.as_fixnum()?);
    (b != 0 && a % b == 0).then(|| a / b).and_then(Value::fixnum)
}

/// `first` combined with each of `rest` in turn, by `fast` while that's of two fixnums and makes
/// one, and otherwise by `generic`, on the numeric tower.
#[inline(always)]
fn arith<'gc>(
    mc: &Mutation<'gc>,
    fuel: &mut Fuel,
    first: Value<'gc>,
    rest: impl Iterator<Item = Value<'gc>>,
    fast: impl Fn(Value<'gc>, Value<'gc>) -> Option<Value<'gc>>,
    generic: impl Fn(&Nums<'_, 'gc>, Number<'gc>, Number<'gc>) -> Result<Number<'gc>, Error>,
) -> Result<Value<'gc>, Fault> {
    let mut acc = first;
    for x in rest {
        acc = match fast(acc, x) {
            Some(acc) => acc,
            None => {
                let h = Nums::new(mc);
                let (a, b) = (h.number(acc).ok_or(Fault::WrongType)?, h.number(x).ok_or(Fault::WrongType)?);
                made(mc, fuel, generic(&h, a, b)?.value())
            }
        };
    }
    Ok(acc)
}

/// A byte: a fixnum from 0 to 255, or [`Fault::WrongType`].
fn byte(v: Value<'_>) -> Result<u8, Fault> {
    v.as_fixnum().and_then(|b| u8::try_from(b).ok()).ok_or(Fault::WrongType)
}

/// An index: a fixnum, or [`Fault::WrongType`], and not negative, or [`Fault::OutOfRange`].
fn index(v: Value<'_>) -> Result<usize, Fault> {
    let k = v.as_fixnum().ok_or(Fault::WrongType)?;
    usize::try_from(k).map_err(|_| Fault::OutOfRange)
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
