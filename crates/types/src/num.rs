//! Numbers in the arena, for `ragwort-num`: fixnums and most flonums in the value word, bignums
//! as [`Big`] objects with their digits in their items, ratios as [`Ratio`] objects, and complex
//! numbers as [`Complex`] objects.

use ragwort_num::bigint::{Digits, RWDigits};
pub use ragwort_num::*;

pub use crate::gc::Error;
use crate::gc::{Mutation, Value};

#[cfg(test)]
#[path = "tests/nums.rs"]
mod tests;

crate::gc::objects! {
    /// Every kind of number that's an object, but boxed flonums.
    pub kind Numbers after crate::string::Text;

    /// Sign and magnitude, with no high zero digits. Never zero and never in fixnum range. The
    /// magnitude is the first `digits` items; the rest, left over from making it, are zero.
    pub struct Big { negative: bool, digits: u64 } items u64
    /// A fraction in lowest terms whose denominator is above one. Both parts are [`Integer`]s.
    pub struct Ratio { num: Value, den: Value }
    /// A complex number with a nonzero imaginary part. The parts are [`Real`]s, both exact,
    /// both flonums, or an exact zero real part and a flonum imaginary part.
    pub struct Complex { re: Value, im: Value }
}

macro_rules! views {
    ($($(#[$doc:meta])* $name:ident,)*) => {$(
        $(#[$doc])*
        #[derive(Clone, Copy, PartialEq, Eq, Debug)]
        pub struct $name<'gc>(Value<'gc>);

        impl<'gc> $name<'gc> {
            pub fn value(self) -> Value<'gc> {
                self.0
            }
        }
    )*};
}

views! {
    /// A fixnum or a [`Big`].
    Integer,
    /// An [`Integer`] or a [`Ratio`].
    Rational,
    /// A [`Rational`] or a flonum.
    Real,
    /// A [`Real`] or a [`Complex`].
    Number,
}

/// The arena as a [`Host`] for `ragwort-num`.
#[derive(Clone, Copy)]
pub struct Nums<'a, 'gc> {
    mc: &'a Mutation<'gc>,
}

impl<'a, 'gc> Nums<'a, 'gc> {
    pub fn new(mc: &'a Mutation<'gc>) -> Self {
        Self { mc }
    }

    #[inline]
    pub fn integer(&self, v: Value<'gc>) -> Option<Integer<'gc>> {
        (v.is_fixnum() || matches!(Numbers::of(v), Some(Numbers::Big(_)))).then_some(Integer(v))
    }

    #[inline]
    pub fn rational(&self, v: Value<'gc>) -> Option<Rational<'gc>> {
        (v.is_fixnum() || matches!(Numbers::of(v), Some(Numbers::Big(_) | Numbers::Ratio(_)))).then_some(Rational(v))
    }

    #[inline]
    pub fn real(&self, v: Value<'gc>) -> Option<Real<'gc>> {
        (v.is_flonum() || self.rational(v).is_some()).then_some(Real(v))
    }

    #[inline]
    pub fn number(&self, v: Value<'gc>) -> Option<Number<'gc>> {
        (v.is_flonum() || v.is_fixnum() || Numbers::of(v).is_some()).then_some(Number(v))
    }
}

impl<'gc> ComplexHost for Nums<'_, 'gc> {
    type Number = Number<'gc>;

    #[inline]
    fn complex_view(&self, x: Number<'gc>) -> ComplexView<Real<'gc>> {
        match Numbers::of(x.0) {
            Some(Numbers::Complex(z)) => ComplexView::Complex { re: Real(z.re(self.mc)), im: Real(z.im(self.mc)) },
            _ => ComplexView::Real(Real(x.0)),
        }
    }

    #[inline]
    fn of_real(&self, x: Real<'gc>) -> Number<'gc> {
        Number(x.0)
    }

    fn complex(&self, re: Real<'gc>, im: Real<'gc>) -> Result<Number<'gc>, Error> {
        Ok(Number(Value::object(self.mc, Complex::new(self.mc, re.0, im.0)?)))
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
        match Numbers::of(x.0) {
            Some(Numbers::Ratio(r)) => RationalView::Ratio { num: Integer(r.num(self.mc)), den: Integer(r.den(self.mc)) },
            _ => RationalView::Integer(Integer(x.0)),
        }
    }

    #[inline]
    fn of_int(&self, x: Integer<'gc>) -> Rational<'gc> {
        Rational(x.0)
    }

    fn ratio(&self, num: Integer<'gc>, den: Integer<'gc>) -> Result<Rational<'gc>, Error> {
        Ok(Rational(Value::object(self.mc, Ratio::new(self.mc, num.0, den.0)?)))
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
        let Some(Numbers::Big(big)) = Numbers::of(x.0) else { panic!("integers are fixnums or bigs") };
        let digits = &big.items(self.mc).words()[..big.digits(self.mc) as usize];
        IntView::Big { negative: big.negative(self.mc), digits: Digits::new(digits) }
    }

    #[inline]
    fn small(&self, n: i64) -> Option<Integer<'gc>> {
        Value::fixnum(n).map(Integer)
    }

    fn big(&self, negative: bool, len: usize, init: impl FnOnce(RWDigits<'_>) -> usize) -> Result<Integer<'gc>, Error> {
        let big = self.mc.alloc_zeroed::<Big, 2>([u64::from(negative), 0], len)?;
        let kept = init(RWDigits::of_cells(big.items(self.mc).words())).min(len);
        big.set_digits(self.mc, kept as u64);
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
