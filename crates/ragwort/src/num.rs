//! Numbers in the arena: fixnums and most flonums in the value word, bignums as [`Big`]
//! objects, ratios as [`Ratio`] objects, and complex numbers as [`Complex`] objects.

use ragwort_gc::{Gc, Mutation, OutOfMemory, Plain, Trace, TypeTag, Value};
use ragwort_num::bigint::{Digits, RWDigits};
pub use ragwort_num::*;

pub use crate::Error;

/// A bignum: sign and magnitude, with digits inline and no high zeros. Never zero and never
/// in fixnum range.
#[derive(Trace, Plain)]
#[gc(items = u64)]
pub struct Big {
    negative: u64,
}

impl Big {
    #[doc(hidden)]
    pub fn new(negative: bool) -> Self {
        Self { negative: negative as u64 }
    }

    pub fn is_negative(&self) -> bool {
        self.negative != 0
    }
}

/// A fraction in lowest terms whose denominator is above one. Both parts are [`Integer`]s.
#[derive(Trace, Plain)]
pub struct Ratio<'gc> {
    num: Value<'gc>,
    den: Value<'gc>,
}

/// A complex number with a nonzero imaginary part. The parts are [`Real`]s, both exact,
/// both flonums, or an exact zero real part and a flonum imaginary part.
#[derive(Trace, Plain)]
pub struct Complex<'gc> {
    re: Value<'gc>,
    im: Value<'gc>,
}

/// A fixnum or a [`Big`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(transparent)]
pub struct Integer<'gc>(Value<'gc>);

impl<'gc> Integer<'gc> {
    pub fn value(self) -> Value<'gc> {
        self.0
    }
}

/// An [`Integer`] or a [`Ratio`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(transparent)]
pub struct Rational<'gc>(Value<'gc>);

impl<'gc> Rational<'gc> {
    pub fn value(self) -> Value<'gc> {
        self.0
    }
}

/// A [`Rational`] or a flonum.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(transparent)]
pub struct Real<'gc>(Value<'gc>);

impl<'gc> Real<'gc> {
    pub fn value(self) -> Value<'gc> {
        self.0
    }
}

/// A [`Real`] or a [`Complex`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(transparent)]
pub struct Number<'gc>(Value<'gc>);

impl<'gc> Number<'gc> {
    pub fn value(self) -> Value<'gc> {
        self.0
    }
}

/// The arena as a [`Host`] for `ragwort-num`.
#[derive(Clone, Copy)]
pub struct Nums<'a, 'gc> {
    mc: &'a Mutation<'gc>,
    big: TypeTag<'gc, Big>,
    ratio: TypeTag<'gc, Ratio<'gc>>,
    complex: TypeTag<'gc, Complex<'gc>>,
}

impl<'a, 'gc> Nums<'a, 'gc> {
    pub fn new(mc: &'a Mutation<'gc>) -> Result<Self, OutOfMemory> {
        Ok(Self { mc, big: mc.inline_type_tag()?, ratio: mc.type_tag()?, complex: mc.type_tag()? })
    }

    pub fn integer(&self, v: Value<'gc>) -> Option<Integer<'gc>> {
        (v.is_fixnum() || v.downcast_tag(self.mc, self.big).is_some()).then_some(Integer(v))
    }

    pub fn rational(&self, v: Value<'gc>) -> Option<Rational<'gc>> {
        (self.integer(v).is_some() || v.downcast_tag(self.mc, self.ratio).is_some()).then_some(Rational(v))
    }

    pub fn real(&self, v: Value<'gc>) -> Option<Real<'gc>> {
        (v.is_flonum() || self.rational(v).is_some()).then_some(Real(v))
    }

    pub fn number(&self, v: Value<'gc>) -> Option<Number<'gc>> {
        (self.real(v).is_some() || v.downcast_tag(self.mc, self.complex).is_some()).then_some(Number(v))
    }
}

impl<'gc> ComplexHost for Nums<'_, 'gc> {
    type Number = Number<'gc>;

    #[inline]
    fn complex_view(&self, x: Number<'gc>) -> ComplexView<Real<'gc>> {
        match x.0.downcast_tag(self.mc, self.complex) {
            Some(z) => ComplexView::Complex { re: Real(z.re), im: Real(z.im) },
            None => ComplexView::Real(Real(x.0)),
        }
    }

    #[inline]
    fn of_real(&self, x: Real<'gc>) -> Number<'gc> {
        Number(x.0)
    }

    fn complex(&self, re: Real<'gc>, im: Real<'gc>) -> Result<Number<'gc>, Error> {
        let z = self.mc.alloc(Complex { re: re.0, im: im.0 })?;
        Ok(Number(Value::object(self.mc, z)))
    }
}

impl<'gc> RealHost for Nums<'_, 'gc> {
    type Real = Real<'gc>;

    #[inline]
    fn real_view(&self, x: Real<'gc>) -> RealView<Rational<'gc>> {
        match x.0.as_flonum(self.mc) {
            Some(f) => RealView::Flonum(f),
            None => RealView::Exact(Rational(x.0)),
        }
    }

    #[inline]
    fn of_rational(&self, x: Rational<'gc>) -> Real<'gc> {
        Real(x.0)
    }

    #[inline]
    fn flonum(&self, f: f64) -> Result<Real<'gc>, Error> {
        Ok(Real(Value::flonum(self.mc, f)?))
    }
}

impl<'gc> RationalHost for Nums<'_, 'gc> {
    type Rational = Rational<'gc>;

    #[inline]
    fn rational_view(&self, x: Rational<'gc>) -> RationalView<Integer<'gc>> {
        match x.0.downcast_tag(self.mc, self.ratio) {
            Some(ratio) => RationalView::Ratio { num: Integer(ratio.num), den: Integer(ratio.den) },
            None => RationalView::Integer(Integer(x.0)),
        }
    }

    #[inline]
    fn of_int(&self, x: Integer<'gc>) -> Rational<'gc> {
        Rational(x.0)
    }

    fn ratio(&self, num: Integer<'gc>, den: Integer<'gc>) -> Result<Rational<'gc>, Error> {
        let ratio = self.mc.alloc(Ratio { num: num.0, den: den.0 })?;
        Ok(Rational(Value::object(self.mc, ratio)))
    }
}

impl<'gc> Host for Nums<'_, 'gc> {
    type Int = Integer<'gc>;
    type Error = Error;

    #[inline]
    fn view(&self, x: Integer<'gc>) -> IntView<'_> {
        if let Some(n) = x.0.as_fixnum() {
            return IntView::Small(n);
        }
        let big = x.0.downcast_tag(self.mc, self.big).expect("integers are fixnums or bigs");
        IntView::Big { negative: big.negative != 0, digits: Digits::new(Gc::items(big)) }
    }

    #[inline]
    fn small(&self, n: i64) -> Option<Integer<'gc>> {
        Value::fixnum(n).map(Integer)
    }

    fn big(&self, negative: bool, len: usize, init: impl FnOnce(RWDigits<'_>) -> usize) -> Result<Integer<'gc>, Error> {
        let big = self.mc.alloc_inline_with(Big { negative: negative as u64 }, len, 0, |digits| init(RWDigits::new(digits)))?;
        Ok(Integer(Value::object(self.mc, big)))
    }

    fn scratch(&self, digits: usize) -> Result<(), Error> {
        Ok(self.mc.ensure(digits.saturating_mul(size_of::<u64>()))?)
    }

    #[inline]
    fn small_add(&self, x: Integer<'gc>, y: Integer<'gc>) -> Option<Integer<'gc>> {
        x.0.fixnum_add(y.0).map(Integer)
    }

    #[inline]
    fn small_sub(&self, x: Integer<'gc>, y: Integer<'gc>) -> Option<Integer<'gc>> {
        x.0.fixnum_sub(y.0).map(Integer)
    }

    #[inline]
    fn small_mul(&self, x: Integer<'gc>, y: Integer<'gc>) -> Option<Integer<'gc>> {
        x.0.fixnum_mul(y.0).map(Integer)
    }
}

#[cfg(test)]
mod tests;
