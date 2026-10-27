use std::fmt;
use std::marker::PhantomData;

use super::{AnyRef, Gc, Invariant, Member, Mutation, OutOfMemory, Plain, Trace, Tracer, TypeTag};

// The low bits say what a word holds:
//   ...0    fixnum, shifted left by one
//   ...11   flonum: a double with two redundant exponent bits dropped
//   ..0001  object, offset in the upper 32 bits and check bits in the 28 below
//   ..1001  boxed flonum, laid out like an object
//   ..0101  char, scalar value in the upper 32 bits
//   ..1101  constant, id in the upper 32 bits
const TAG: u64 = 0b1111;
const OBJECT: u64 = 0b0001;
const BOXED: u64 = 0b1001;
const CHAR: u64 = 0b0101;
const CONSTANT: u64 = 0b1101;
/// Both tags that hold an offset end in 001.
const REFERENCE: u64 = 0b0111;
/// +0.0 takes the word of the one inline double whose encoding would end up here.
const ZERO: u64 = 0x8000_0000_0000_0003;
const COLLIDES_WITH_ZERO: u64 = 0x3000_0000_0000_0000;

/// A double that doesn't fit in a word: ±0 aside, magnitudes beyond about 1e±77, -0.0,
/// infinities and NaNs.
#[derive(Trace, Plain)]
struct Boxed(f64);

fn encode(f: f64) -> Option<u64> {
    let bits = f.to_bits();
    if bits == 0 {
        return Some(ZERO);
    }
    // Exponents starting 011 or 100: the second and third bits copy the inverse of the first.
    let top = bits >> 60 & 0b111;
    ((top == 0b011 || top == 0b100) && bits != COLLIDES_WITH_ZERO).then(|| bits.rotate_left(3) | 0b11)
}

fn decode(word: u64) -> f64 {
    if word == ZERO {
        return 0.0;
    }
    let first = word >> 63;
    f64::from_bits((word & !0b11 | (2 - first)).rotate_right(3))
}

/// A Scheme value in one word: a fixnum, flonum, char, constant or arena object.
///
/// Equality is `eq?`. Every copy of an object's offset is rewritten when the object moves, so
/// it holds across steps, but the bits themselves only hold within a step.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct Value<'gc> {
    word: u64,
    _brand: Invariant<'gc>,
}

/// What a [`Value`] holds, for matching on.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Unpacked<'gc> {
    Fixnum(i64),
    Flonum(f64),
    Char(char),
    Bool(bool),
    Nil,
    Eof,
    Void,
    /// A variable that hasn't been given a value yet.
    Unbound,
    Object(AnyRef<'gc>),
}

impl<'gc> Value<'gc> {
    pub const FALSE: Self = Self::constant(0);
    pub const TRUE: Self = Self::constant(1);
    pub const NIL: Self = Self::constant(2);
    pub const EOF: Self = Self::constant(3);
    pub const VOID: Self = Self::constant(4);
    pub const UNBOUND: Self = Self::constant(5);

    pub const MIN_FIXNUM: i64 = i64::MIN >> 1;
    pub const MAX_FIXNUM: i64 = i64::MAX >> 1;

    const fn from_word(word: u64) -> Self {
        Self { word, _brand: PhantomData }
    }

    const fn constant(id: u32) -> Self {
        Self::from_word((id as u64) << 32 | CONSTANT)
    }

    const fn tagged(tag: u64, payload: u32) -> Self {
        Self::from_word((payload as u64) << 32 | tag)
    }

    const fn payload(self) -> u32 {
        (self.word >> 32) as u32
    }

    /// The reference word with the object tag, whichever reference tag the value has.
    fn reference(self) -> AnyRef<'gc> {
        AnyRef::from_word(self.word & !TAG | OBJECT)
    }

    /// `None` outside `MIN_FIXNUM..=MAX_FIXNUM`.
    pub const fn fixnum(n: i64) -> Option<Self> {
        match n >= Self::MIN_FIXNUM && n <= Self::MAX_FIXNUM {
            true => Some(Self::from_word((n << 1) as u64)),
            false => None,
        }
    }

    pub const fn bool(b: bool) -> Self {
        if b { Self::TRUE } else { Self::FALSE }
    }

    pub const fn char(c: char) -> Self {
        Self::tagged(CHAR, c as u32)
    }

    pub fn object<T>(mc: &Mutation<'gc>, gc: Gc<'gc, T>) -> Self {
        AnyRef::new(mc, gc).into()
    }

    pub fn from_member<T>(mc: &Mutation<'gc>, member: Member<'gc, T>) -> Self {
        AnyRef::from_member(mc, member).into()
    }

    /// Stores the double in the word when it fits, and boxes it otherwise.
    pub fn flonum(mc: &Mutation<'gc>, f: f64) -> Result<Self, OutOfMemory> {
        match encode(f) {
            Some(word) => Ok(Self::from_word(word)),
            None => {
                let boxed = AnyRef::new(mc, mc.alloc(Boxed(f))?);
                Ok(Self::from_word(boxed.to_bits() & !TAG | BOXED))
            }
        }
    }

    /// The double as a value without allocating, if it fits in the word.
    pub fn inline_flonum(f: f64) -> Option<Self> {
        encode(f).map(Self::from_word)
    }

    pub const fn is_true(self) -> bool {
        self.word != Self::FALSE.word
    }

    pub const fn is_fixnum(self) -> bool {
        self.word & 1 == 0
    }

    pub const fn is_flonum(self) -> bool {
        self.word & 0b11 == 0b11 || self.word & TAG == BOXED
    }

    pub const fn as_fixnum(self) -> Option<i64> {
        match self.is_fixnum() {
            true => Some(self.word as i64 >> 1),
            false => None,
        }
    }

    pub fn as_flonum(self, mc: &Mutation<'gc>) -> Option<f64> {
        if self.word & 0b11 == 0b11 {
            Some(decode(self.word))
        } else if self.word & TAG == BOXED {
            Some(self.reference().downcast::<Boxed>(mc).map_or(f64::NAN, |b| b.0))
        } else {
            None
        }
    }

    pub fn as_char(self) -> Option<char> {
        (self.word & TAG == CHAR).then(|| char::from_u32(self.payload()).unwrap_or(char::REPLACEMENT_CHARACTER))
    }

    pub fn as_bool(self) -> Option<bool> {
        match self {
            Self::TRUE => Some(true),
            Self::FALSE => Some(false),
            _ => None,
        }
    }

    pub fn as_object(self) -> Option<AnyRef<'gc>> {
        (self.word & TAG == OBJECT).then(|| self.reference())
    }

    /// Whether the value is an object of type `T`.
    pub fn is<T: Plain<'gc> + 'gc>(self, mc: &Mutation<'gc>) -> bool {
        self.as_object().is_some_and(|r| r.is::<T>(mc))
    }

    pub fn downcast<T: Plain<'gc> + 'gc>(self, mc: &Mutation<'gc>) -> Option<Gc<'gc, T>> {
        self.as_object()?.downcast(mc)
    }

    /// Like [`Value::downcast`], but compares a single number.
    #[inline]
    pub fn downcast_tag<T: Plain<'gc> + 'gc>(self, mc: &Mutation<'gc>, tag: TypeTag<'gc, T>) -> Option<Gc<'gc, T>> {
        self.as_object()?.downcast_tag(mc, tag)
    }

    pub fn unpack(self, mc: &Mutation<'gc>) -> Unpacked<'gc> {
        if let Some(n) = self.as_fixnum() {
            return Unpacked::Fixnum(n);
        }
        if let Some(f) = self.as_flonum(mc) {
            return Unpacked::Flonum(f);
        }
        match self.word & TAG {
            OBJECT => Unpacked::Object(self.reference()),
            CHAR => Unpacked::Char(char::from_u32(self.payload()).unwrap_or(char::REPLACEMENT_CHARACTER)),
            _ => match self {
                Self::FALSE => Unpacked::Bool(false),
                Self::TRUE => Unpacked::Bool(true),
                Self::NIL => Unpacked::Nil,
                Self::EOF => Unpacked::Eof,
                Self::UNBOUND => Unpacked::Unbound,
                _ => Unpacked::Void,
            },
        }
    }

    /// Fixnum addition, or `None` if either isn't a fixnum or the sum doesn't fit.
    #[inline]
    pub fn fixnum_add(self, other: Self) -> Option<Self> {
        if (self.word | other.word) & 1 != 0 {
            return None;
        }
        (self.word as i64).checked_add(other.word as i64).map(|w| Self::from_word(w as u64))
    }

    #[inline]
    pub fn fixnum_sub(self, other: Self) -> Option<Self> {
        if (self.word | other.word) & 1 != 0 {
            return None;
        }
        (self.word as i64).checked_sub(other.word as i64).map(|w| Self::from_word(w as u64))
    }

    #[inline]
    pub fn fixnum_mul(self, other: Self) -> Option<Self> {
        let n = self.as_fixnum()?;
        if !other.is_fixnum() {
            return None;
        }
        n.checked_mul(other.word as i64).map(|w| Self::from_word(w as u64))
    }

    /// The word. Object offsets in it only hold until the step ends.
    pub const fn to_bits(self) -> u64 {
        self.word
    }

    /// # Safety
    /// If the bits hold a reference (an object or a boxed flonum), they must come from
    /// [`Value::to_bits`] in the same arena, in the same step. Other bits are always valid.
    pub const unsafe fn from_bits(bits: u64) -> Self {
        Self::from_word(bits)
    }
}

impl Default for Value<'_> {
    fn default() -> Self {
        Self::VOID
    }
}

impl From<bool> for Value<'_> {
    fn from(b: bool) -> Self {
        Self::bool(b)
    }
}

impl From<char> for Value<'_> {
    fn from(c: char) -> Self {
        Self::char(c)
    }
}

impl<'gc> From<AnyRef<'gc>> for Value<'gc> {
    fn from(r: AnyRef<'gc>) -> Self {
        Self::from_word(r.to_bits())
    }
}

impl fmt::Debug for Value<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(n) = self.as_fixnum() {
            return write!(f, "{n}");
        }
        if self.word & 0b11 == 0b11 {
            return write!(f, "{:?}", decode(self.word));
        }
        match self.word & TAG {
            OBJECT => write!(f, "Object({:#x})", self.payload()),
            BOXED => write!(f, "Flonum({:#x})", self.payload()),
            CHAR => write!(f, "{:?}", char::from_u32(self.payload()).unwrap_or(char::REPLACEMENT_CHARACTER)),
            _ => f.write_str(match *self {
                Self::FALSE => "#f",
                Self::TRUE => "#t",
                Self::NIL => "()",
                Self::EOF => "#<eof>",
                Self::UNBOUND => "#<unbound>",
                _ => "#<void>",
            }),
        }
    }
}

unsafe impl<'gc> Plain<'gc> for Value<'gc> {}

unsafe impl Trace for Value<'_> {
    #[inline]
    fn trace(&mut self, t: &mut Tracer<'_>) {
        if self.holds_refs() {
            t.value(&mut self.word);
        }
    }

    #[inline]
    fn holds_refs(&self) -> bool {
        self.word & REFERENCE == OBJECT
    }
}
