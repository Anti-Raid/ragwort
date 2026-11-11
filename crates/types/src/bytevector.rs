//! Bytevectors, of fixed length, their bytes packed eight to a word. A [`Bytevector`] can be
//! written to; an immutable one, such as a literal, can only be read. An external one's bytes
//! the program running the arena made and gave it, a buffer of them if it's one that's
//! written to. [`AnyBytevector`] reads any of them.
//!
//! External bytes are an [`ExternalBuffer`], for a bytevector that's only read, or an
//! [`ExternalBufferMut`], for one that's written to. A type that's one promises what the arena
//! relies on and can't check: that the bytes' number never changes, and for an
//! [`ExternalBuffer`], that their values don't either.

use std::borrow::Cow;
use std::cell::{RefCell, RefMut};
use std::rc::Rc;
use std::sync::Arc;

use crate::gc::{Gc, Mutation, OutOfMemory, Slots, Value, slot};
use crate::objects::{self, BytevectorFields, Data, ExternBytevectorFields, ExternMutBytevectorFields, ImmutableBytevectorFields};

#[cfg(test)]
#[path = "tests/bytevector.rs"]
mod tests;

fn words(len: usize) -> usize {
    len.div_ceil(8)
}

/// A bytevector that can be written to, its bytes in the arena or outside it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Bytevector<'gc>(Kept<'gc>);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kept<'gc> {
    Inside(Gc<'gc, objects::Bytevector>),
    Outside(Gc<'gc, objects::ExternMutBytevector>),
}

/// The bytes of `v`'s buffer, for one read or write: as many as it had when `v` was made.
fn outside<'gc>(mc: &Mutation<'gc>, v: Gc<'gc, objects::ExternMutBytevector>) -> Option<RefMut<'gc, [u8]>> {
    let len = v.bytes(mc) as usize;
    Some(RefMut::map(v.buffer(mc)?.borrow_mut(), |buffer| {
        let bytes = (**buffer).as_mut();
        let len = len.min(bytes.len());
        &mut bytes[..len]
    }))
}

/// The word of the eight bytes from `index * 8` that `byte` reads, zeros past the last.
fn word_of(len: usize, index: usize, byte: impl Fn(usize) -> u8) -> u64 {
    let mut word = [0; 8];
    for (i, b) in word.iter_mut().enumerate().take(len.saturating_sub(index * 8)) {
        *b = byte(index * 8 + i);
    }
    u64::from_le_bytes(word)
}

impl<'gc> Bytevector<'gc> {
    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        match self.0 {
            Kept::Inside(v) => Value::object(mc, v),
            Kept::Outside(v) => Value::object(mc, v),
        }
    }

    /// Sets the byte at `index`, or returns `false` if there's none.
    pub fn set(self, mc: &Mutation<'gc>, index: usize, byte: u8) -> bool {
        let v = match self.0 {
            Kept::Inside(v) => v,
            Kept::Outside(v) => return outside(mc, v).and_then(|mut bytes| bytes.get_mut(index).map(|b| *b = byte)).is_some(),
        };
        if index as u64 >= v.bytes(mc) {
            return false;
        }
        let items = v.items(mc);
        let shift = index % 8 * 8;
        let word = items.get(index / 8) & !(0xff << shift) | u64::from(byte) << shift;
        items.set(mc, index / 8, word);
        true
    }

    /// Sets the `size` bytes from `index`, 1 to 8, to `value`'s low ones, least significant
    /// first, or returns `false` if they're not all there.
    pub fn set_uint(self, mc: &Mutation<'gc>, index: usize, size: usize, value: u64) -> bool {
        let v = match self.0 {
            Kept::Inside(v) => v,
            Kept::Outside(v) => {
                let Some(mut bytes) = outside(mc, v) else { return false };
                let Some(to) = index.checked_add(size).and_then(|end| bytes.get_mut(index..end)) else { return false };
                to.copy_from_slice(&value.to_le_bytes()[..size]);
                return true;
            }
        };
        if index.checked_add(size).is_none_or(|end| end as u64 > v.bytes(mc)) {
            return false;
        }
        let (items, at, shift, mask) = (v.items(mc), index / 8, index % 8 * 8, low_bytes(size));
        let value = value & mask;
        items.set(mc, at, items.get(at) & !(mask << shift) | value << shift);
        if shift + size * 8 > 64 {
            let rest = 64 - shift;
            items.set(mc, at + 1, items.get(at + 1) & !(mask >> rest) | value >> rest);
        }
        true
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ImmutableBytevector<'gc>(Gc<'gc, objects::ImmutableBytevector>);

/// Bytes kept outside the arena, for a bytevector that's only read: what gives them, the same
/// ones each time.
///
/// A type that's one promises that the bytes never change while it lives, in number or in value,
/// as a literal's don't: code that has read them may keep what it read. So one that shares them,
/// as an `Arc<[u8]>` does, is one whose other holders can't write to them, and bytes something
/// else can change, such as a file mapped into memory, aren't one. Breaking the promise makes
/// the bytevector read wrongly; it reads no more bytes than there were when it was made.
pub trait ExternalBuffer: AsRef<[u8]> + 'static {}

/// A buffer kept outside the arena, for a bytevector that's written to: what gives its bytes,
/// the same ones each time.
///
/// A type that's one promises that the number of bytes never changes while it lives, as a
/// bytevector's length doesn't, and that nothing else writes them: the arena owns the buffer.
pub trait ExternalBufferMut: AsMut<[u8]> + 'static {}

impl ExternalBuffer for Vec<u8> {}
impl ExternalBuffer for Box<[u8]> {}
impl ExternalBuffer for Rc<[u8]> {}
impl ExternalBuffer for Arc<[u8]> {}
impl ExternalBuffer for &'static [u8] {}
impl<const N: usize> ExternalBuffer for [u8; N] {}
impl ExternalBuffer for String {}
impl ExternalBuffer for &'static str {}
impl ExternalBuffer for Cow<'static, [u8]> {}

impl ExternalBufferMut for Vec<u8> {}
impl ExternalBufferMut for Box<[u8]> {}
impl<const N: usize> ExternalBufferMut for [u8; N] {}

/// Fewer external bytes are copied: keeping them outside costs more than they do.
const COPY_EXTERNAL: usize = 64;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ExternalBytevector<'gc>(Gc<'gc, objects::ExternBytevector>);

impl<'gc> ExternalBytevector<'gc> {
    /// Its bytes: as many as there were when it was made.
    fn bytes(self, mc: &Mutation<'gc>) -> &'gc [u8] {
        let bytes = self.0.owner(mc).map_or(&[][..], |owner| (**owner).as_ref());
        &bytes[..bytes.len().min(self.0.bytes(mc) as usize)]
    }
}

/// Any kind of bytevector, for reading.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AnyBytevector<'gc> {
    Mutable(Bytevector<'gc>),
    Immutable(ImmutableBytevector<'gc>),
    External(ExternalBytevector<'gc>),
}

impl<'gc> AnyBytevector<'gc> {
    #[inline]
    pub fn of(v: Value<'gc>) -> Option<Self> {
        match Data::of(v) {
            Some(Data::Bytevector(v)) => Some(Self::Mutable(Bytevector(Kept::Inside(v)))),
            Some(Data::ExternMutBytevector(v)) => Some(Self::Mutable(Bytevector(Kept::Outside(v)))),
            Some(Data::ImmutableBytevector(v)) => Some(Self::Immutable(ImmutableBytevector(v))),
            Some(Data::ExternBytevector(v)) => Some(Self::External(ExternalBytevector(v))),
            _ => None,
        }
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        match self {
            Self::Mutable(v) => v.value(mc),
            Self::Immutable(v) => Value::object(mc, v.0),
            Self::External(v) => Value::object(mc, v.0),
        }
    }

    /// Whether its bytes are kept outside the arena.
    pub fn is_external(self) -> bool {
        matches!(self, Self::External(_) | Self::Mutable(Bytevector(Kept::Outside(_))))
    }

    pub fn is_mutable(self) -> bool {
        matches!(self, Self::Mutable(_))
    }

    pub fn len(self, mc: &Mutation<'gc>) -> usize {
        match self {
            Self::Mutable(Bytevector(Kept::Inside(v))) => v.bytes(mc) as usize,
            Self::Mutable(Bytevector(Kept::Outside(v))) => v.bytes(mc) as usize,
            Self::Immutable(v) => v.0.bytes(mc) as usize,
            Self::External(v) => v.0.bytes(mc) as usize,
        }
    }

    pub fn is_empty(self, mc: &Mutation<'gc>) -> bool {
        self.len(mc) == 0
    }

    fn word(self, mc: &Mutation<'gc>, index: usize) -> u64 {
        match self {
            Self::Mutable(Bytevector(Kept::Inside(v))) => v.items(mc).get(index),
            Self::Mutable(Bytevector(Kept::Outside(v))) => outside(mc, v).map_or(0, |bytes| word_of(bytes.len(), index, |i| bytes[i])),
            Self::Immutable(v) => v.0.items(mc).get(index),
            Self::External(v) => {
                let bytes = v.bytes(mc);
                word_of(bytes.len(), index, |i| bytes[i])
            }
        }
    }

    /// How many bytes there are and the words they're packed in, if they're in the arena.
    #[inline(always)]
    fn inside(self, mc: &Mutation<'gc>) -> Option<(usize, Slots<'gc, slot::u64>)> {
        match self {
            Self::Mutable(Bytevector(Kept::Inside(v))) => Some((v.bytes(mc) as usize, v.items(mc))),
            Self::Immutable(v) => Some((v.0.bytes(mc) as usize, v.0.items(mc))),
            _ => None,
        }
    }

    /// What `f` makes of the bytes, which are kept outside the arena. It's out of line so that
    /// reading the ones in the arena stays short.
    #[inline(never)]
    fn outside<R>(self, mc: &Mutation<'gc>, f: impl FnOnce(&[u8]) -> R) -> R {
        match self {
            Self::External(v) => f(v.bytes(mc)),
            Self::Mutable(Bytevector(Kept::Outside(v))) => match outside(mc, v) {
                Some(bytes) => f(&bytes),
                None => f(&[]),
            },
            _ => f(&[]),
        }
    }

    #[inline]
    pub fn get(self, mc: &Mutation<'gc>, index: usize) -> Option<u8> {
        let Some((len, words)) = self.inside(mc) else { return self.outside(mc, |bytes| bytes.get(index).copied()) };
        (index < len).then(|| (words.get(index / 8) >> (index % 8 * 8)) as u8)
    }

    /// The `size` bytes from `index`, 1 to 8, least significant first, if they're all there.
    #[inline]
    pub fn get_uint(self, mc: &Mutation<'gc>, index: usize, size: usize) -> Option<u64> {
        let Some((len, words)) = self.inside(mc) else {
            return self.outside(mc, |bytes| {
                let part = bytes.get(index..index.checked_add(size)?)?;
                // Eight bytes are read at once where there are that many.
                Some(match bytes.get(index..index + 8).and_then(|eight| <[u8; 8]>::try_from(eight).ok()) {
                    Some(eight) => u64::from_le_bytes(eight) & low_bytes(size),
                    None => part.iter().rev().fold(0, |value, &byte| value << 8 | u64::from(byte)),
                })
            });
        };
        if index.checked_add(size)? > len {
            return None;
        }
        let (at, shift) = (index / 8, index % 8 * 8);
        let mut value = words.get(at) >> shift;
        if shift + size * 8 > 64 {
            value |= words.get(at + 1) << (64 - shift);
        }
        Some(value & low_bytes(size))
    }

    pub fn to_vec(self, mc: &Mutation<'gc>) -> Vec<u8> {
        self.bytes(mc, 0, self.len(mc)).into_owned()
    }

    /// The bytes from `start` up to `end`, which are in it: an external one's as they are, and
    /// the others' copied out.
    pub fn bytes(self, mc: &Mutation<'gc>, start: usize, end: usize) -> Cow<'gc, [u8]> {
        match self {
            Self::External(v) => return Cow::Borrowed(&v.bytes(mc)[start..end]),
            Self::Mutable(Bytevector(Kept::Outside(v))) => return Cow::Owned(outside(mc, v).map_or(Vec::new(), |bytes| bytes[start..end].to_vec())),
            _ => {}
        }
        let mut bytes: Vec<u8> = (start / 8..words(end)).flat_map(|i| self.word(mc, i).to_le_bytes()).collect();
        bytes.truncate(end - start / 8 * 8);
        bytes.drain(..start % 8);
        Cow::Owned(bytes)
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
        clear_slack(self.mc, v.items(self.mc), len, word);
        Ok(Bytevector(Kept::Inside(v)))
    }

    pub fn from_slice(&self, bytes: &[u8]) -> Result<Bytevector<'gc>, OutOfMemory> {
        let v = objects::Bytevector::new(self.mc, bytes.len() as u64, words(bytes.len()), 0)?;
        pack(self.mc, v.items(self.mc), bytes);
        Ok(Bytevector(Kept::Inside(v)))
    }

    pub fn immutable_from_slice(&self, bytes: &[u8]) -> Result<AnyBytevector<'gc>, OutOfMemory> {
        let v = objects::ImmutableBytevector::new(self.mc, bytes.len() as u64, words(bytes.len()), 0)?;
        pack(self.mc, v.items(self.mc), bytes);
        Ok(AnyBytevector::Immutable(ImmutableBytevector(v)))
    }

    /// A bytevector of bytes kept outside the arena, such as a `Vec<u8>` or an `Arc<[u8]>`, which
    /// can't be written to. The arena is charged for them until nothing reaches it.
    pub fn external(&self, bytes: impl ExternalBuffer) -> Result<AnyBytevector<'gc>, OutOfMemory> {
        let len = bytes.as_ref().len();
        if len < COPY_EXTERNAL {
            return self.immutable_from_slice(bytes.as_ref());
        }
        let owner: Box<dyn ExternalBuffer> = Box::new(bytes);
        let v = objects::ExternBytevector::new(self.mc, len as u64, self.mc.frozen_owning(owner, len)?)?;
        Ok(AnyBytevector::External(ExternalBytevector(v)))
    }

    /// A bytevector of a buffer kept outside the arena, such as a `Vec<u8>`, which can be written
    /// to, however short it is, and is as long as the buffer is now. The buffer is the arena's
    /// from here on, which is charged for its bytes until nothing reaches it.
    pub fn external_mutable(&self, mut buffer: impl ExternalBufferMut) -> Result<Bytevector<'gc>, OutOfMemory> {
        let len = buffer.as_mut().len();
        let buffer: RefCell<Box<dyn ExternalBufferMut>> = RefCell::new(Box::new(buffer));
        let v = objects::ExternMutBytevector::new(self.mc, len as u64, self.mc.frozen_owning(buffer, len)?)?;
        Ok(Bytevector(Kept::Outside(v)))
    }
}

/// A mask of the low `size` bytes of a word, `size` 1 to 8.
fn low_bytes(size: usize) -> u64 {
    u64::MAX >> (64 - size * 8)
}

/// Packs `bytes` into `words`, 8 to a word.
fn pack<'gc>(mc: &Mutation<'gc>, words: Slots<'gc, slot::u64>, bytes: &[u8]) {
    for (i, chunk) in bytes.chunks(8).enumerate() {
        let mut word = [0; 8];
        word[..chunk.len()].copy_from_slice(chunk);
        words.set(mc, i, u64::from_le_bytes(word));
    }
}

/// Zeroes the bytes past `len` in the last of `words`, each a `fill`, so equal bytevectors have
/// equal words.
fn clear_slack<'gc>(mc: &Mutation<'gc>, words: Slots<'gc, slot::u64>, len: usize, fill: u64) {
    if !len.is_multiple_of(8) {
        words.set(mc, len / 8, fill & (u64::MAX >> (64 - len % 8 * 8)));
    }
}
