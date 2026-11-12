//! A plain binary form for the values an image holds outside the arena, such as a function's
//! instructions. See [`crate::gc::image`] for the image itself.
//!
//! A type that can be saved implements [`Wire`], which `#[derive(Wire)]` writes for a struct or
//! an enum whose fields can all be saved:
//!
//! ```text
//! #[derive(Wire)]
//! enum Capture {
//!     Register(u8),
//!     Spill { spill: u8, slot: u32 },
//! }
//! ```
//!
//! # The form
//!
//! - A number is its bytes, the lowest first.
//! - A struct is its fields in order.
//! - An enum is its variant's place, as a `u16`, then the variant's fields.
//! - A sequence or a string is its length, as a `u32`, then its elements or bytes.
//!
//! Nothing says what type the bytes are of. What's read must be what was written, by the same
//! build: [`Wire::SHAPE`] changes when a type's fields do, and an image is stamped with the
//! shapes of what it holds. A derived shape mixes the shapes of its field types transitively
//! (breaking const cycles on recursive data structures).

#[cfg(test)]
#[path = "tests/wire.rs"]
mod tests;

use std::any::Any;
use std::ops::Range;

/// The most values inside one another that are read, so bytes that aren't an image's can't
/// run the reader out of stack.
const DEPTH: u32 = 512;

/// Bytes that aren't the form of what's read from them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Malformed;

#[derive(Default)]
pub struct Writer {
    bytes: Vec<u8>,
}

impl Writer {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn u8(&mut self, n: u8) {
        self.bytes.push(n);
    }

    pub fn u16(&mut self, n: u16) {
        self.bytes.extend(n.to_le_bytes());
    }

    pub fn u32(&mut self, n: u32) {
        self.bytes.extend(n.to_le_bytes());
    }

    pub fn u64(&mut self, n: u64) {
        self.bytes.extend(n.to_le_bytes());
    }

    /// `bytes`, after how many there are.
    pub fn bytes(&mut self, bytes: &[u8]) {
        self.length(bytes.len());
        self.bytes.extend(bytes);
    }

    /// The length of a sequence.
    ///
    /// # Panics
    ///
    /// If it's `u32::MAX` or more, which nothing an arena holds is.
    pub fn length(&mut self, len: usize) {
        self.u32(u32::try_from(len).expect("a sequence shorter than 2^32"));
    }

    pub fn len(&self) -> usize {
        self.bytes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }

    pub fn finish(self) -> Vec<u8> {
        self.bytes
    }
}

/// Bytes being read, and what the reader was given for the values that need it: a host
/// function is found by its name in a table that's there.
pub struct Reader<'a> {
    bytes: &'a [u8],
    context: &'a dyn Any,
    depth: u32,
}

impl<'a> Reader<'a> {
    pub fn new(bytes: &'a [u8], context: &'a dyn Any) -> Self {
        Self { bytes, context, depth: 0 }
    }

    fn take<const N: usize>(&mut self) -> Result<[u8; N], Malformed> {
        let (taken, rest) = self.bytes.split_first_chunk::<N>().ok_or(Malformed)?;
        self.bytes = rest;
        Ok(*taken)
    }

    pub fn u8(&mut self) -> Result<u8, Malformed> {
        Ok(u8::from_le_bytes(self.take()?))
    }

    pub fn u16(&mut self) -> Result<u16, Malformed> {
        Ok(u16::from_le_bytes(self.take()?))
    }

    pub fn u32(&mut self) -> Result<u32, Malformed> {
        Ok(u32::from_le_bytes(self.take()?))
    }

    pub fn u64(&mut self) -> Result<u64, Malformed> {
        Ok(u64::from_le_bytes(self.take()?))
    }

    /// The bytes [`Writer::bytes`] wrote.
    pub fn bytes(&mut self) -> Result<&'a [u8], Malformed> {
        let len = self.u32()? as usize;
        let (taken, rest) = self.bytes.split_at_checked(len).ok_or(Malformed)?;
        self.bytes = rest;
        Ok(taken)
    }

    /// A sequence's length, which is no more than the bytes left could hold elements for.
    pub fn length(&mut self) -> Result<usize, Malformed> {
        let len = self.u32()? as usize;
        if len > self.bytes.len() {
            return Err(Malformed);
        }
        Ok(len)
    }

    pub fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }

    /// What the reader was given, if it's a `T`.
    pub fn context<T: Any>(&self) -> Result<&'a T, Malformed> {
        self.context.downcast_ref().ok_or(Malformed)
    }

    /// Reads a value that's inside another.
    pub fn inner<T>(&mut self, read: impl FnOnce(&mut Self) -> Result<T, Malformed>) -> Result<T, Malformed> {
        if self.depth == DEPTH {
            return Err(Malformed);
        }
        self.depth += 1;
        let value = read(self);
        self.depth -= 1;
        value
    }
}

/// A number that's different for different text, for [`Wire::SHAPE`].
pub const fn shape_of(text: &str) -> u64 {
    let bytes = text.as_bytes();
    let mut hash = 0xCBF2_9CE4_8422_2325u64;
    let mut i = 0;
    while i < bytes.len() {
        hash = (hash ^ bytes[i] as u64).wrapping_mul(0x0000_0100_0000_01B3);
        i += 1;
    }
    hash
}

/// One number of two, different if either is.
pub const fn mix(a: u64, b: u64) -> u64 {
    (a.rotate_left(23) ^ b).wrapping_mul(0x9E37_79B9_7F4A_7C15)
}

/// A value with a binary form.
pub trait Wire: Sized {
    /// A number that changes when the form does.
    const SHAPE: u64;

    fn write(&self, out: &mut Writer);

    fn read(input: &mut Reader<'_>) -> Result<Self, Malformed>;
}

macro_rules! numbers {
    ($($ty:ident as $as:ident),*) => {$(
        impl Wire for $ty {
            const SHAPE: u64 = shape_of(stringify!($ty));

            fn write(&self, out: &mut Writer) {
                out.$as(*self as $as);
            }

            fn read(input: &mut Reader<'_>) -> Result<Self, Malformed> {
                Ok(input.$as()? as $ty)
            }
        }
    )*};
}

numbers!(u8 as u8, u16 as u16, u32 as u32, u64 as u64, i8 as u8, i16 as u16, i32 as u32, i64 as u64);

impl Wire for bool {
    const SHAPE: u64 = shape_of("bool");

    fn write(&self, out: &mut Writer) {
        out.u8(u8::from(*self));
    }

    fn read(input: &mut Reader<'_>) -> Result<Self, Malformed> {
        match input.u8()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(Malformed),
        }
    }
}

impl Wire for String {
    const SHAPE: u64 = shape_of("String");

    fn write(&self, out: &mut Writer) {
        out.bytes(self.as_bytes());
    }

    fn read(input: &mut Reader<'_>) -> Result<Self, Malformed> {
        Ok(std::str::from_utf8(input.bytes()?).map_err(|_| Malformed)?.to_string())
    }
}

impl Wire for Box<str> {
    const SHAPE: u64 = shape_of("Box<str>");

    fn write(&self, out: &mut Writer) {
        out.bytes(self.as_bytes());
    }

    fn read(input: &mut Reader<'_>) -> Result<Self, Malformed> {
        Ok(String::read(input)?.into_boxed_str())
    }
}

impl<T: Wire> Wire for Option<T> {
    const SHAPE: u64 = mix(shape_of("Option"), T::SHAPE);

    fn write(&self, out: &mut Writer) {
        match self {
            None => out.u8(0),
            Some(value) => {
                out.u8(1);
                value.write(out);
            }
        }
    }

    fn read(input: &mut Reader<'_>) -> Result<Self, Malformed> {
        match input.u8()? {
            0 => Ok(None),
            1 => Ok(Some(T::read(input)?)),
            _ => Err(Malformed),
        }
    }
}

impl<T: Wire> Wire for Vec<T> {
    const SHAPE: u64 = mix(shape_of("Vec"), T::SHAPE);

    fn write(&self, out: &mut Writer) {
        out.length(self.len());
        self.iter().for_each(|item| item.write(out));
    }

    fn read(input: &mut Reader<'_>) -> Result<Self, Malformed> {
        let len = input.length()?;
        let mut items = Vec::with_capacity(len);
        for _ in 0..len {
            items.push(input.inner(T::read)?);
        }
        Ok(items)
    }
}

impl<T: Wire> Wire for Box<[T]> {
    const SHAPE: u64 = mix(shape_of("Box<[]>"), T::SHAPE);

    fn write(&self, out: &mut Writer) {
        out.length(self.len());
        self.iter().for_each(|item| item.write(out));
    }

    fn read(input: &mut Reader<'_>) -> Result<Self, Malformed> {
        Ok(Vec::read(input)?.into_boxed_slice())
    }
}

impl<T: Wire> Wire for Box<T> {
    const SHAPE: u64 = mix(shape_of("Box"), T::SHAPE);

    fn write(&self, out: &mut Writer) {
        (**self).write(out);
    }

    fn read(input: &mut Reader<'_>) -> Result<Self, Malformed> {
        Ok(Box::new(input.inner(T::read)?))
    }
}

impl<T: Wire, const N: usize> Wire for [T; N] {
    const SHAPE: u64 = mix(mix(shape_of("array"), N as u64), T::SHAPE);

    fn write(&self, out: &mut Writer) {
        self.iter().for_each(|item| item.write(out));
    }

    fn read(input: &mut Reader<'_>) -> Result<Self, Malformed> {
        let mut items = Vec::with_capacity(N);
        for _ in 0..N {
            items.push(input.inner(T::read)?);
        }
        items.try_into().map_err(|_| Malformed)
    }
}

impl<T: Wire> Wire for Range<T> {
    const SHAPE: u64 = mix(shape_of("Range"), T::SHAPE);

    fn write(&self, out: &mut Writer) {
        self.start.write(out);
        self.end.write(out);
    }

    fn read(input: &mut Reader<'_>) -> Result<Self, Malformed> {
        Ok(T::read(input)?..T::read(input)?)
    }
}

impl<A: Wire, B: Wire> Wire for (A, B) {
    const SHAPE: u64 = mix(shape_of("pair"), mix(A::SHAPE, B::SHAPE));

    fn write(&self, out: &mut Writer) {
        self.0.write(out);
        self.1.write(out);
    }

    fn read(input: &mut Reader<'_>) -> Result<Self, Malformed> {
        Ok((A::read(input)?, B::read(input)?))
    }
}

/// A value that refers to no object is its word.
impl Wire for crate::gc::Immediate {
    const SHAPE: u64 = shape_of("Immediate");

    fn write(&self, out: &mut Writer) {
        out.u64(self.value().to_bits());
    }

    fn read(input: &mut Reader<'_>) -> Result<Self, Malformed> {
        crate::gc::Value::from_bits(input.u64()?).immediate().ok_or(Malformed)
    }
}

impl Wire for () {
    const SHAPE: u64 = shape_of("()");

    fn write(&self, _: &mut Writer) {}

    fn read(_: &mut Reader<'_>) -> Result<Self, Malformed> {
        Ok(())
    }
}

macro_rules! places {
    ($ty:ty: $($variant:ident),*) => {
        impl Wire for $ty {
            const SHAPE: u64 = shape_of(stringify!($ty $($variant)*));

            fn write(&self, out: &mut Writer) {
                let places = [$(Self::$variant),*];
                let place = places.iter().position(|place| place == self).expect("every variant is listed");
                out.u8(place as u8);
            }

            fn read(input: &mut Reader<'_>) -> Result<Self, Malformed> {
                [$(Self::$variant),*].get(usize::from(input.u8()?)).copied().ok_or(Malformed)
            }
        }
    };
}

places!(ragwort_num::NumError: DivideByZero, NoExactValue, NotInteger);
places!(ragwort_string::StrError: OutOfRange, TooLong, NotNarrowest, NotUtf8);
