//! Bytevectors, of fixed length, their bytes packed eight to a word. A [`Bytevector`] can be
//! written to; an immutable one, such as a literal, can only be read. [`AnyBytevector`] reads
//! either.

use crate::gc::{Gc, Mutation, OutOfMemory, Value};
use crate::objects::{self, BytevectorFields, Data, ImmutableBytevectorFields};

#[cfg(test)]
#[path = "tests/bytevector.rs"]
mod tests;

fn words(len: usize) -> usize {
    len.div_ceil(8)
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Bytevector<'gc>(Gc<'gc, objects::Bytevector>);

impl<'gc> Bytevector<'gc> {
    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        Value::object(mc, self.0)
    }

    /// Sets the byte at `index`, or returns `false` if there's none.
    pub fn set(self, mc: &Mutation<'gc>, index: usize, byte: u8) -> bool {
        if index as u64 >= self.0.bytes(mc) {
            return false;
        }
        let items = self.0.items(mc);
        let shift = index % 8 * 8;
        let word = items.get(index / 8) & !(0xff << shift) | u64::from(byte) << shift;
        items.set(mc, index / 8, word);
        true
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ImmutableBytevector<'gc>(Gc<'gc, objects::ImmutableBytevector>);

/// Either kind of bytevector, for reading.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AnyBytevector<'gc> {
    Mutable(Bytevector<'gc>),
    Immutable(ImmutableBytevector<'gc>),
}

impl<'gc> AnyBytevector<'gc> {
    #[inline]
    pub fn of(v: Value<'gc>) -> Option<Self> {
        match Data::of(v) {
            Some(Data::Bytevector(v)) => Some(Self::Mutable(Bytevector(v))),
            Some(Data::ImmutableBytevector(v)) => Some(Self::Immutable(ImmutableBytevector(v))),
            _ => None,
        }
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        match self {
            Self::Mutable(v) => v.value(mc),
            Self::Immutable(v) => Value::object(mc, v.0),
        }
    }

    pub fn is_mutable(self) -> bool {
        matches!(self, Self::Mutable(_))
    }

    pub fn len(self, mc: &Mutation<'gc>) -> usize {
        match self {
            Self::Mutable(v) => v.0.bytes(mc) as usize,
            Self::Immutable(v) => v.0.bytes(mc) as usize,
        }
    }

    pub fn is_empty(self, mc: &Mutation<'gc>) -> bool {
        self.len(mc) == 0
    }

    fn word(self, mc: &Mutation<'gc>, index: usize) -> u64 {
        match self {
            Self::Mutable(v) => v.0.items(mc).get(index),
            Self::Immutable(v) => v.0.items(mc).get(index),
        }
    }

    #[inline]
    pub fn get(self, mc: &Mutation<'gc>, index: usize) -> Option<u8> {
        (index < self.len(mc)).then(|| (self.word(mc, index / 8) >> (index % 8 * 8)) as u8)
    }

    pub fn to_vec(self, mc: &Mutation<'gc>) -> Vec<u8> {
        let len = self.len(mc);
        let mut bytes: Vec<u8> = (0..words(len)).flat_map(|i| self.word(mc, i).to_le_bytes()).collect();
        bytes.truncate(len);
        bytes
    }

    /// Whether the two hold the same bytes, a word at a time.
    pub fn same_bytes(self, mc: &Mutation<'gc>, other: Self) -> bool {
        let len = self.len(mc);
        len == other.len(mc) && (0..words(len)).all(|i| self.word(mc, i) == other.word(mc, i))
    }
}

/// Bytevector operations for one step.
#[derive(Clone, Copy)]
pub struct Bytevectors<'a, 'gc> {
    mc: &'a Mutation<'gc>,
}

impl<'a, 'gc> Bytevectors<'a, 'gc> {
    pub fn new(mc: &'a Mutation<'gc>) -> Self {
        Self { mc }
    }

    pub fn bytevector(&self, v: Value<'gc>) -> Option<AnyBytevector<'gc>> {
        AnyBytevector::of(v)
    }

    /// `v` if it's a bytevector that can be written to.
    pub fn mutable(&self, v: Value<'gc>) -> Option<Bytevector<'gc>> {
        match AnyBytevector::of(v) {
            Some(AnyBytevector::Mutable(v)) => Some(v),
            _ => None,
        }
    }

    /// A bytevector of `len` copies of `fill`.
    pub fn make(&self, len: usize, fill: u8) -> Result<Bytevector<'gc>, OutOfMemory> {
        let word = u64::from_le_bytes([fill; 8]);
        let v = objects::Bytevector::new(self.mc, len as u64, words(len), word)?;
        clear_slack(len, |i, w| v.items(self.mc).set(self.mc, i, w), word);
        Ok(Bytevector(v))
    }

    pub fn from_slice(&self, bytes: &[u8]) -> Result<Bytevector<'gc>, OutOfMemory> {
        let v = objects::Bytevector::new(self.mc, bytes.len() as u64, words(bytes.len()), 0)?;
        pack(bytes, |i, w| v.items(self.mc).set(self.mc, i, w));
        Ok(Bytevector(v))
    }

    pub fn immutable_from_slice(&self, bytes: &[u8]) -> Result<AnyBytevector<'gc>, OutOfMemory> {
        let v = objects::ImmutableBytevector::new(self.mc, bytes.len() as u64, words(bytes.len()), 0)?;
        pack(bytes, |i, w| v.items(self.mc).set(self.mc, i, w));
        Ok(AnyBytevector::Immutable(ImmutableBytevector(v)))
    }
}

fn pack(bytes: &[u8], mut set: impl FnMut(usize, u64)) {
    for (i, chunk) in bytes.chunks(8).enumerate() {
        let mut word = [0; 8];
        word[..chunk.len()].copy_from_slice(chunk);
        set(i, u64::from_le_bytes(word));
    }
}

/// Zeroes the bytes past `len` in the last word, so equal bytevectors have equal words.
fn clear_slack(len: usize, mut set: impl FnMut(usize, u64), fill: u64) {
    if !len.is_multiple_of(8) {
        set(len / 8, fill & (u64::MAX >> (64 - len % 8 * 8)));
    }
}
