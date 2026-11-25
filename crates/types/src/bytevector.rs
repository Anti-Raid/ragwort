//! Bytevectors. A bytevector's length is fixed when it is made. [`AnyBytevector`] reads any of
//! the three kinds:
//!
//! - [`Bytevector`]: writable. Its bytes are in the arena, packed eight to a word, or in a
//!   buffer the host handed over.
//! - [`ImmutableBytevector`]: read-only and in the arena, such as a literal.
//! - [`ExternalBytevector`]: read-only, with bytes the host owns.
//!
//! # External bytes
//!
//! The host passes external bytes as an [`ExternalBuffer`], for a read-only bytevector, or an
//! [`ExternalBufferMut`], for a writable one. The arena relies on two promises it cannot check:
//!
//! - The number of bytes never changes.
//! - For an [`ExternalBuffer`], the values of the bytes never change either.

use std::borrow::Cow;
use std::cell::{RefCell, RefMut};
use std::rc::Rc;
use std::sync::Arc;

use crate::gc::{FrozenRef, Gc, Mutation, OutOfMemory, Slots, Value, slot};
use crate::store::{STORE_MAX, Store, range_of, range_word};
use crate::objects::{self, BytevectorFields, Data, ExternBytevectorFields, ExternMutBytevectorFields, ImmutableBytevectorFields};

#[cfg(test)]
#[path = "tests/bytevector.rs"]
mod tests;

fn words(len: usize) -> usize {
    len.div_ceil(8)
}

/// A writable bytevector. Its bytes are stored in the arena, or outside it in a buffer that the host handed over.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Bytevector<'gc>(Kept<'gc>);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kept<'gc> {
    Inside(Gc<'gc, objects::Bytevector>),
    Outside(Gc<'gc, objects::ExternMutBytevector>),
}

/// Borrows the bytes of `bytevector`'s buffer for one read or write. The slice is limited to the length the buffer had when `bytevector` was created.
fn outside<'gc>(mc: &Mutation<'gc>, bytevector: Gc<'gc, objects::ExternMutBytevector>) -> Option<RefMut<'gc, [u8]>> {
    let len = bytevector.bytes(mc) as usize;
    Some(RefMut::map(bytevector.buffer(mc)?.borrow_mut(), |buffer| {
        let bytes = (**buffer).as_mut();
        let len = len.min(bytes.len());
        &mut bytes[..len]
    }))
}

/// Returns word `index` of `len` bytes: the eight bytes from `index * 8`, each read by calling `byte`, with the first byte in the lowest bits. Bytes past `len` are zero.
fn word_of(len: usize, index: usize, byte: impl Fn(usize) -> u8) -> u64 {
    let mut word = [0; 8];
    for (i, out) in word.iter_mut().enumerate().take(len.saturating_sub(index * 8)) {
        *out = byte(index * 8 + i);
    }
    u64::from_le_bytes(word)
}

impl<'gc> Bytevector<'gc> {
    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        match self.0 {
            Kept::Inside(bytevector) => Value::object(mc, bytevector),
            Kept::Outside(bytevector) => Value::object(mc, bytevector),
        }
    }

    /// Sets the byte at `index`. Returns `false` if `index` is out of range.
    pub fn set(self, mc: &Mutation<'gc>, index: usize, byte: u8) -> bool {
        let bytevector = match self.0 {
            Kept::Inside(bytevector) => bytevector,
            Kept::Outside(bytevector) => return outside(mc, bytevector).and_then(|mut bytes| bytes.get_mut(index).map(|out| *out = byte)).is_some(),
        };
        if index as u64 >= bytevector.bytes(mc) {
            return false;
        }
        let items = bytevector.items(mc);
        let shift = index % 8 * 8;
        let word = items.get(index / 8) & !(0xff << shift) | u64::from(byte) << shift;
        items.set(mc, index / 8, word);
        true
    }

    /// Sets the `size` bytes from `index` to the low `size` bytes of `value`, least significant
    /// first. `size` is 1 to 8. Returns `false` if the bytes are not all within the bytevector.
    pub fn set_uint(self, mc: &Mutation<'gc>, index: usize, size: usize, value: u64) -> bool {
        let bytevector = match self.0 {
            Kept::Inside(bytevector) => bytevector,
            Kept::Outside(bytevector) => {
                let Some(mut bytes) = outside(mc, bytevector) else { return false };
                let Some(to) = index.checked_add(size).and_then(|end| bytes.get_mut(index..end)) else { return false };
                to.copy_from_slice(&value.to_le_bytes()[..size]);
                return true;
            }
        };
        if index.checked_add(size).is_none_or(|end| end as u64 > bytevector.bytes(mc)) {
            return false;
        }
        let (items, at, shift, mask) = (bytevector.items(mc), index / 8, index % 8 * 8, low_bytes(size));
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

/// Bytes the host owns, for a read-only bytevector.
///
/// Implementing this trait is a promise that, for as long as the value lives:
///
/// - `as_ref` returns the same bytes on every call;
/// - the number of bytes never changes;
/// - the value of each byte never changes.
///
/// Code that has read the bytes may keep what it read, as it would for a literal. So the trait
/// is not for bytes that something else can change, such as a file mapped into memory, or for a
/// shared owner whose other holders can write to them.
///
/// Breaking the promise makes the bytevector return wrong data. It cannot cause memory
/// unsafety: the bytevector never reads past the length it had when it was made.
///
/// The trait is implemented here for the standard owners. A host wraps any other type, such as
/// `bytes::Bytes`, in a type of its own and implements the trait for that.
pub trait ExternalBuffer: AsRef<[u8]> + 'static {}

/// A buffer the host hands over, for a writable bytevector. The arena owns it from then on.
///
/// Implementing this trait is a promise that, for as long as the value lives:
///
/// - `as_mut` returns the same bytes on every call;
/// - the number of bytes never changes;
/// - nothing but the bytevector writes to them.
///
/// The trait is implemented here for the standard buffers. A host wraps any other type, such
/// as `bytes::BytesMut`, in a type of its own and implements the trait for that.
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

/// External buffers of fewer bytes than this are copied into the arena. Keeping them outside would cost more than the bytes.
const COPY_EXTERNAL: usize = 64;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ExternalBytevector<'gc>(Gc<'gc, objects::ExternBytevector>);

impl<'gc> ExternalBytevector<'gc> {
    /// Returns the bytes: the part of the store that the bytevector is a view of.
    fn bytes(self, mc: &Mutation<'gc>) -> &'gc [u8] {
        let (start, len) = range_of(self.0.bytes(mc));
        self.0.owner(mc).and_then(|store| store.bytes().get(start..start + len)).unwrap_or(&[])
    }

    /// Returns the store that the bytevector reads from, the start of its part in the store, and the number of bytes of the whole store.
    pub(crate) fn store(self, mc: &Mutation<'gc>) -> Option<(FrozenRef<'gc, Store>, usize, usize)> {
        let store = self.0.frozen_ref(mc, objects::ExternBytevector::OWNER)?;
        Some((store, range_of(self.0.bytes(mc)).0, self.0.owner(mc)?.bytes().len()))
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
    pub fn of(value: Value<'gc>) -> Option<Self> {
        match Data::of(value) {
            Some(Data::Bytevector(bytevector)) => Some(Self::Mutable(Bytevector(Kept::Inside(bytevector)))),
            Some(Data::ExternMutBytevector(bytevector)) => Some(Self::Mutable(Bytevector(Kept::Outside(bytevector)))),
            Some(Data::ImmutableBytevector(bytevector)) => Some(Self::Immutable(ImmutableBytevector(bytevector))),
            Some(Data::ExternBytevector(bytevector)) => Some(Self::External(ExternalBytevector(bytevector))),
            _ => None,
        }
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        match self {
            Self::Mutable(bytevector) => bytevector.value(mc),
            Self::Immutable(bytevector) => Value::object(mc, bytevector.0),
            Self::External(bytevector) => Value::object(mc, bytevector.0),
        }
    }

    /// Returns whether the bytes are stored outside the arena.
    pub fn is_external(self) -> bool {
        matches!(self, Self::External(_) | Self::Mutable(Bytevector(Kept::Outside(_))))
    }

    pub fn is_mutable(self) -> bool {
        matches!(self, Self::Mutable(_))
    }

    pub fn len(self, mc: &Mutation<'gc>) -> usize {
        match self {
            Self::Mutable(Bytevector(Kept::Inside(bytevector))) => bytevector.bytes(mc) as usize,
            Self::Mutable(Bytevector(Kept::Outside(bytevector))) => bytevector.bytes(mc) as usize,
            Self::Immutable(bytevector) => bytevector.0.bytes(mc) as usize,
            Self::External(bytevector) => range_of(bytevector.0.bytes(mc)).1,
        }
    }

    pub fn is_empty(self, mc: &Mutation<'gc>) -> bool {
        self.len(mc) == 0
    }

    fn word(self, mc: &Mutation<'gc>, index: usize) -> u64 {
        match self {
            Self::Mutable(Bytevector(Kept::Inside(bytevector))) => bytevector.items(mc).get(index),
            Self::Mutable(Bytevector(Kept::Outside(bytevector))) => outside(mc, bytevector).map_or(0, |bytes| word_of(bytes.len(), index, |i| bytes[i])),
            Self::Immutable(bytevector) => bytevector.0.items(mc).get(index),
            Self::External(bytevector) => {
                let bytes = bytevector.bytes(mc);
                word_of(bytes.len(), index, |i| bytes[i])
            }
        }
    }

    /// Returns the number of bytes and the words that they are packed in, or `None` if the bytes are not stored in the arena.
    #[inline(always)]
    fn inside(self, mc: &Mutation<'gc>) -> Option<(usize, Slots<'gc, slot::u64>)> {
        match self {
            Self::Mutable(Bytevector(Kept::Inside(bytevector))) => Some((bytevector.bytes(mc) as usize, bytevector.items(mc))),
            Self::Immutable(bytevector) => Some((bytevector.0.bytes(mc) as usize, bytevector.0.items(mc))),
            _ => None,
        }
    }

    /// Calls `read` with the bytes, which are stored outside the arena, and returns its result. It
    /// is kept out of line so that the code for reading bytes in the arena stays small.
    #[inline(never)]
    fn outside<R>(self, mc: &Mutation<'gc>, read: impl FnOnce(&[u8]) -> R) -> R {
        match self {
            Self::External(bytevector) => read(bytevector.bytes(mc)),
            Self::Mutable(Bytevector(Kept::Outside(bytevector))) => match outside(mc, bytevector) {
                Some(bytes) => read(&bytes),
                None => read(&[]),
            },
            _ => read(&[]),
        }
    }

    #[inline]
    pub fn get(self, mc: &Mutation<'gc>, index: usize) -> Option<u8> {
        let Some((len, words)) = self.inside(mc) else { return self.outside(mc, |bytes| bytes.get(index).copied()) };
        (index < len).then(|| (words.get(index / 8) >> (index % 8 * 8)) as u8)
    }

    /// Returns the `size` bytes from `index` as an integer, least significant first. `size` is 1 to 8. Returns `None` if the bytes are not all within the bytevector.
    #[inline]
    pub fn get_uint(self, mc: &Mutation<'gc>, index: usize, size: usize) -> Option<u64> {
        let Some((len, words)) = self.inside(mc) else {
            return self.outside(mc, |bytes| {
                let part = bytes.get(index..index.checked_add(size)?)?;
                // Read eight bytes at once if that many are left from `index`.
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

    /// Returns the bytes from `start` up to `end`, which must be within the bytevector. The bytes
    /// of a read-only external bytevector are borrowed. The bytes of any other kind are copied.
    pub fn bytes(self, mc: &Mutation<'gc>, start: usize, end: usize) -> Cow<'gc, [u8]> {
        match self {
            Self::External(bytevector) => return Cow::Borrowed(&bytevector.bytes(mc)[start..end]),
            Self::Mutable(Bytevector(Kept::Outside(bytevector))) => return Cow::Owned(outside(mc, bytevector).map_or(Vec::new(), |bytes| bytes[start..end].to_vec())),
            _ => {}
        }
        let mut bytes: Vec<u8> = (start / 8..words(end)).flat_map(|i| self.word(mc, i).to_le_bytes()).collect();
        bytes.truncate(end - start / 8 * 8);
        bytes.drain(..start % 8);
        Cow::Owned(bytes)
    }

    /// Returns whether the two bytevectors hold the same bytes. Bytes in the arena are compared a word at a time.
    pub fn same_bytes(self, mc: &Mutation<'gc>, other: Self) -> bool {
        let len = self.len(mc);
        if len != other.len(mc) {
            return false;
        }
        // Reading host-owned bytes word by word would go through the host for every word. So they are read once, as a slice.
        if self.is_external() || other.is_external() {
            return self.bytes(mc, 0, len) == other.bytes(mc, 0, len);
        }
        (0..words(len)).all(|i| self.word(mc, i) == other.word(mc, i))
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

    pub fn bytevector(&self, value: Value<'gc>) -> Option<AnyBytevector<'gc>> {
        AnyBytevector::of(value)
    }

    /// Returns `value` as a writable bytevector, or `None` if it is not one.
    pub fn mutable(&self, value: Value<'gc>) -> Option<Bytevector<'gc>> {
        match AnyBytevector::of(value) {
            Some(AnyBytevector::Mutable(bytevector)) => Some(bytevector),
            _ => None,
        }
    }

    /// Returns a bytevector of `len` copies of `fill`.
    pub fn make(&self, len: usize, fill: u8) -> Result<Bytevector<'gc>, OutOfMemory> {
        let word = u64::from_le_bytes([fill; 8]);
        let bytevector = objects::Bytevector::new(self.mc, len as u64, words(len), word)?;
        clear_slack(self.mc, bytevector.items(self.mc), len, word);
        Ok(Bytevector(Kept::Inside(bytevector)))
    }

    pub fn from_slice(&self, bytes: &[u8]) -> Result<Bytevector<'gc>, OutOfMemory> {
        let bytevector = objects::Bytevector::new(self.mc, bytes.len() as u64, words(bytes.len()), 0)?;
        pack(self.mc, bytevector.items(self.mc), bytes);
        Ok(Bytevector(Kept::Inside(bytevector)))
    }

    pub fn immutable_from_slice(&self, bytes: &[u8]) -> Result<AnyBytevector<'gc>, OutOfMemory> {
        let bytevector = objects::ImmutableBytevector::new(self.mc, bytes.len() as u64, words(bytes.len()), 0)?;
        pack(self.mc, bytevector.items(self.mc), bytes);
        Ok(AnyBytevector::Immutable(ImmutableBytevector(bytevector)))
    }

    /// Makes a read-only bytevector whose bytes stay in `bytes`, outside the arena.
    ///
    /// - Fewer than 64 bytes are copied into the arena instead, as an ordinary immutable
    ///   bytevector.
    /// - The arena's budget is charged for the bytes until the bytevector is collected, which
    ///   drops `bytes`.
    pub fn external(&self, bytes: impl ExternalBuffer) -> Result<AnyBytevector<'gc>, OutOfMemory> {
        let len = bytes.as_ref().len();
        if len < COPY_EXTERNAL {
            return self.immutable_from_slice(bytes.as_ref());
        }
        let owner: Box<dyn ExternalBuffer> = Box::new(bytes);
        let len = len.min(STORE_MAX);
        let bytevector = objects::ExternBytevector::new(self.mc, range_word(0, len), self.mc.frozen_owning(Store::Bytes(owner), len)?)?;
        Ok(AnyBytevector::External(ExternalBytevector(bytevector)))
    }

    /// Makes a writable bytevector over `buffer`, which the arena takes ownership of.
    ///
    /// - The bytevector's length is the buffer's length now, and never changes.
    /// - The buffer is never copied, however short it is.
    /// - The arena's budget is charged for the bytes until the bytevector is collected, which
    ///   drops the buffer.
    pub fn external_mutable(&self, mut buffer: impl ExternalBufferMut) -> Result<Bytevector<'gc>, OutOfMemory> {
        let len = buffer.as_mut().len();
        let buffer: RefCell<Box<dyn ExternalBufferMut>> = RefCell::new(Box::new(buffer));
        let bytevector = objects::ExternMutBytevector::new(self.mc, len as u64, self.mc.frozen_owning(buffer, len)?)?;
        Ok(Bytevector(Kept::Outside(bytevector)))
    }
}

/// Returns a mask of the low `size` bytes of a word. `size` is 1 to 8.
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

/// Zeroes the bytes past `len` in the last word of `words`. Every word was initialized to
/// `fill`. Equal bytevectors then have equal words.
fn clear_slack<'gc>(mc: &Mutation<'gc>, words: Slots<'gc, slot::u64>, len: usize, fill: u64) {
    if !len.is_multiple_of(8) {
        words.set(mc, len / 8, fill & (u64::MAX >> (64 - len % 8 * 8)));
    }
}
