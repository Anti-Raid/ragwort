//! Strings in the arena, for `ragwort-string`. A string is UTF-8. It is stored in one of these ways:
//!
//! - A flat string of up to [`INLINE_BYTES`] bytes is stored inline in the value word.
//! - A flat string of up to [`BUILD`] words is a [`Flat`] object. Its bytes are packed into the object's items, eight to an item.
//! - A longer flat string is an [`Extern`] object: a view of a [`Store`], which holds the bytes outside the arena.
//!   The store is text that the host handed over, or bytes that the arena made for the string. Several strings can be views of one store.
//! - A rope is a [`Rope`] object.
//!
//! # Lengths
//!
//! A string has a number of bytes and a number of characters, and keeps both. The two are equal
//! exactly when the string is ASCII. A position that a program gives is a character index. In an
//! ASCII string it is used as a byte offset. In another string the characters before it are counted.
//!
//! # Hashes
//!
//! [`Strings::hash`] returns a hash of a string's bytes, for hash tables. A flat string
//! object, a rope and an external string keep the hash once it is computed, so the bytes of a
//! string that is hashed again and again are read once.
//!
//! The hash costs a string no memory. A flat string object has one word beside its bytes:
//!
//! ```text
//! bits 0 to 27    the number of characters
//! bits 28 to 30   the number of unused bytes in the last item
//! bit 31          set while the string is interned
//! bits 32 to 63   the hash, or 0 if it has not been computed
//! ```
//!
//! A rope has bits 31 to 63 of that layout in its `reads` word, with the number of reads by index in bits 0 to 30.
//! A view of a store has them in its `hash` word. Bits 0 to 30 of that word hold one more than the number of characters,
//! or 0 until the characters have been counted. So a flat string has at most [`FLAT_MAX`] bytes. A rope can be longer.
//!
//! # Interned strings
//!
//! The arena has one string for each text: the interned string. So two interned strings have the
//! same characters exactly when they are the same value, and comparing them reads no character.
//!
//! - A string in the value word is interned as it is. Equal ones are the same word already.
//! - A flat string object is interned when it is made. If the arena already has a string with
//!   the same characters, that string is returned and no object is made.
//! - A rope is not interned when it is made, so that joining strings stays cheap. It is interned
//!   the first time it is compared with a string of the same length, or used as the key of a
//!   table. Its hash is computed from its pieces, and nothing is copied.
//! - A view of a store is not interned when it is made either, so that handing a long text to the
//!   arena reads none of it. It is interned at the same two moments as a rope.
//!
//! ## Interned views
//!
//! If no string with its characters is interned, the view itself becomes the interned
//! string. Its bytes stay in its store.
//!
//! If another string is the interned string already, the view stays as it is and is not the interned string.
//! If that other string is a view too, the first view is pointed at the same part of the same store, and lets go of its own.
//! The two then read the same bytes, so a later comparison of them reads none, and a text that the arena was given twice is kept once.
//!
//! ## Interned ropes
//!
//! Interning a rope has one of two results:
//!
//! - No string with its characters is interned. The rope itself becomes the interned string. It
//!   keeps its two halves, so the pieces that it shares with other strings stay shared.
//! - Another string is the interned string already. The rope then keeps that string in place
//!   of its two halves, and it is read as that string from then on.
//!
//! A rope that is the interned string stays the interned string when it is flattened. The flat
//! copy belongs to the rope alone, and is not interned.
//!
//! ## The table
//!
//! The arena holds its interned strings weakly, in one table. An interned string that nothing
//! else refers to is collected, and making its text again registers a new string.
//!
//! The table is a hash table with linear probing, in one array of words. A slot is one word:
//! the string's hash in the upper half, and a weak reference to the string in the lower half. So a
//! string costs 8 bytes for each slot, and the table is kept between a quarter and three quarters full.
//!
//! - A slot of 0 was never used, and ends a probe.
//! - A slot with a hash and no reference held a string that has died. A probe goes on past it, and
//!   a new string can take it.
//! - When three quarters of the slots have been used, the living strings move to a new array.
//!
//! ## Making a string
//!
//! A new string of up to [`BUILD`] words is written into a buffer on the stack first. It is hashed
//! and looked up there. Only a text that the arena does not have yet is allocated. A longer string
//! is written into a store of its own outside the arena, and is a view of that store.
//!
//! The hash is seeded with the arena's seed, so it cannot be predicted from outside. An arena has
//! one seed for its whole life, and an image is loaded only into an arena with the image's seed,
//! so a hash that is kept in a string stays right.

pub use ragwort_string::*;

pub use crate::gc::Error;
use std::cell::Cell;

use crate::gc::{Gc, INLINE_STRING, Mutation, Slots, TAG, Value, slot};
use crate::bytevector::{AnyBytevector, Bytevectors};
use crate::gc::{FrozenRef, ScratchVec};
use crate::objects::{InternSlots, InternSlotsFields};
pub use crate::store::Store;
use crate::store::{STORE_MAX, range_of, range_word, shares};
use crate::symbol::Symbols;

#[cfg(test)]
#[path = "tests/strings.rs"]
mod tests;

crate::gc::objects! {
    /// Every kind of string object.
    pub kind Text after crate::gc::table::Containers;

    /// A flat string of UTF-8 bytes, packed eight to an item. `chars` holds the number of characters, the number of unused bytes in the last item, the interned flag and the hash. See the [module docs](self).
    pub struct Flat { chars: u64 } items u64
    /// The concatenation of two nonempty strings, `left` then `right`. `info` holds the number of bytes in its low 48 bits and the depth in its high 8 bits.
    /// `chars` is the number of characters.
    /// A rope whose `right` is `#f` is read as the string in `left`, and has let go of its two halves. That string is the flat copy of a rope that has been flattened, or the interned string of a rope that is not the interned string itself.
    /// `reads` holds the number of reads of the rope by character index, the interned flag and the hash. See the [module docs](self).
    pub struct Rope { left: Value, right: Value, info: u64, chars: u64, reads: u64 }
    /// A flat string whose bytes are a part of the store `owner`, outside the arena. The store is dropped once nothing reads from it.
    /// `hash` holds the number of characters, the interned flag and the hash. `range` holds the start of the part in its upper half and the length in its lower half. See the [module docs](self).
    pub struct Extern { owner: Frozen<Store>, hash: u64, range: u64 }
}

/// The most bytes that a flat string can have. A view of a store keeps its start, its length and its number of characters in 31 bits each. See the [module docs](self).
pub const FLAT_MAX: usize = STORE_MAX;

/// The bits of a flat string's `chars` word that hold the number of characters.
const COUNT: u64 = (1 << 28) - 1;
/// The bits of a view's `hash` word that hold one more than the number of characters, or 0 if the characters have not been counted.
const COUNTED: u64 = (1 << 31) - 1;
/// The low half of a `chars` or `hash` word: everything but the hash.
const LOW: u64 = (1 << 32) - 1;
/// The number of bits that the count of unused bytes in a flat string's `chars` word is shifted up by. The count takes three bits.
const UNUSED_SHIFT: u32 = 28;
/// The bits of a flat string's `chars` word that describe its bytes: the number of characters and the number of unused bytes.
const SHAPE: u64 = (1 << 31) - 1;
/// The bits of a rope's `reads` word that hold the number of reads.
const READS: u64 = (1 << 31) - 1;
/// The bit of a flat string's `chars` word, of a rope's `reads` word or of an external string's `hash` word that is set while the string is interned.
const INTERNED: u64 = 1 << 31;
/// The number of bits that the hash in one of those words is shifted up by.
const HASH_SHIFT: u32 = 32;
/// The number of bits that the depth in a rope's `info` word is shifted up by.
const DEPTH_SHIFT: u32 = 56;
/// The number of words of the buffer in which a new flat string is built before it is looked up. See the [module docs](self).
pub const BUILD: usize = 64;
/// The number of words of the smaller buffer, which a string that fits in it is built in. Clearing it takes less time.
const BUILD_SHORT: usize = 8;
/// The least number of slots in an intern table that has an array.
const MIN_SLOTS: usize = 8;

/// External strings of fewer bytes than this are copied into the arena. Keeping them outside would cost more than their characters.
const COPY_EXTERNAL: usize = 64;

/// A string of up to this many bytes is stored inline in the value word. Creating
/// one allocates nothing, and equal inline strings are the same value.
pub const INLINE_BYTES: usize = 7;

#[inline]
fn is_inline(value: Value<'_>) -> bool {
    value.to_bits() & TAG == INLINE_STRING
}

#[inline]
fn inline_value<'gc>(units: Inline) -> Value<'gc> {
    Value::from_bits(units.word() << 8 | (units.len() as u64) << 4 | INLINE_STRING)
}

#[inline]
fn inline_units(value: Value<'_>) -> Inline {
    let word = value.to_bits();
    Inline::new(word >> 8, (word >> 4 & 0xF) as usize)
}

/// A flat string, a [`Rope`] or an [`Extern`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Str<'gc>(Value<'gc>);

impl<'gc> Str<'gc> {
    pub fn value(self) -> Value<'gc> {
        self.0
    }
}

/// The arena as a [`Host`] for `ragwort-string`.
#[derive(Clone, Copy)]
pub struct Strings<'a, 'gc> {
    pub(crate) mc: &'a Mutation<'gc>,
}

impl<'a, 'gc> Strings<'a, 'gc> {
    pub fn new(mc: &'a Mutation<'gc>) -> Self {
        Self { mc }
    }

    pub fn mutation(&self) -> &'a Mutation<'gc> {
        self.mc
    }

    /// Returns a string whose text is stored outside the arena, in `text`, such as an
    /// [`ExternalText`]. The text must never change, because strings
    /// are immutable. Text of fewer than 64 bytes is copied into the arena instead.
    pub fn external(&self, text: impl External) -> Result<Str<'gc>, Error> {
        let bytes = text.text().len();
        check_external(text.text())?;
        if bytes < COPY_EXTERNAL {
            return from_str(self, text.text());
        }
        if bytes > FLAT_MAX {
            return Err(StrError::TooLong.into());
        }
        let store = self.mc.frozen_owning(Store::Text(Box::new(text)), bytes)?;
        self.view_of(store, 0, bytes, None)
    }

    /// Returns a string that is a view of `len` bytes of `store` from byte `start`. `chars` is the number of characters in them, if the caller knows it.
    fn view_of(&self, store: FrozenRef<'gc, Store>, start: usize, len: usize, chars: Option<usize>) -> Result<Str<'gc>, Error> {
        let counted = chars.map_or(0, |chars| chars as u64 + 1);
        Ok(Str(Value::object(self.mc, Extern::new(self.mc, store, counted, range_word(start, len))?)))
    }

    /// Returns a string with the text that the bytes of `bytevector` from `start` up to `end` hold. Fails with [`StrError::NotUtf8`] if they hold no text.
    ///
    /// The bytes are checked once. If `bytevector` reads from a store and the part is large enough to share, the string reads from the same store and nothing is copied.
    pub fn from_utf8_of(&self, bytevector: AnyBytevector<'gc>, start: usize, end: usize) -> Result<Str<'gc>, Error> {
        if let AnyBytevector::External(external) = bytevector
            && let Some((store, from, whole)) = external.store(self.mc)
            && shares(end - start, whole)
        {
            let part = bytevector.bytes(self.mc, start, end);
            let text = std::str::from_utf8(&part).map_err(|_| StrError::NotUtf8)?;
            return self.view_of(store, from + start, end - start, Some(text.chars().count()));
        }
        from_utf8(self, &bytevector.bytes(self.mc, start, end))
    }

    /// Returns the text of `string` without copying it, if `string` is a view of a store: a long string, or text that the host handed over. Text of the host is
    /// returned without a check. Returns `None` for any other string, whose text is in the arena and has to be copied out, as [`to_string`] and [`append_utf8`] do.
    pub fn as_str(&self, string: Str<'gc>) -> Option<&'gc str> {
        match Text::of(string.0) {
            Some(Text::Extern(external)) => {
                let (start, len) = range_of(external.range(self.mc));
                external.owner(self.mc)?.text(start..start + len)
            }
            _ => None,
        }
    }

    pub fn is_external(&self, string: Str<'gc>) -> bool {
        matches!(Text::of(string.0), Some(Text::Extern(_)))
    }

    /// Returns `value` as a string, or `None` if it is not a string. The check reads only the tag and the type number in the value word.
    #[inline]
    pub fn string(&self, value: Value<'gc>) -> Option<Str<'gc>> {
        (is_inline(value) || Text::of(value).is_some()).then_some(Str(value))
    }

    /// Returns a hash of the characters of `string`, seeded with the arena's seed. Two strings with the same characters have the same hash, however they are stored. The hash is never 0.
    ///
    /// A flat string object, a rope and an external string keep the hash, so it is computed from their characters once. A string in the value word is hashed in a few steps each time. A rope is hashed from its pieces each time, without being flattened.
    #[inline]
    pub fn hash(&self, string: Str<'gc>) -> Result<u32, Error> {
        let mc = self.mc;
        let kept = match Text::of(string.0) {
            Some(Text::Flat(flat)) => flat.chars(mc) >> HASH_SHIFT,
            Some(Text::Rope(rope)) => rope.reads(mc) >> HASH_SHIFT,
            Some(Text::Extern(external)) => external.hash(mc) >> HASH_SHIFT,
            None => 0,
        };
        if kept != 0 {
            return Ok(kept as u32);
        }
        self.hash_anew(string)
    }

    /// Computes the hash of `string` from its characters, and stores it in the string if the string keeps its hash.
    #[inline(never)]
    fn hash_anew(&self, string: Str<'gc>) -> Result<u32, Error> {
        let mc = self.mc;
        let seed = Symbols::of_arena(mc)?.seed(mc);
        let hash = u64::from(narrowed(ragwort_string::hash(self, string, seed)?));
        match Text::of(string.0) {
            Some(Text::Flat(flat)) => flat.set_chars(mc, flat.chars(mc) & (SHAPE | INTERNED) | hash << HASH_SHIFT),
            Some(Text::Rope(rope)) => rope.set_reads(mc, rope.reads(mc) & (READS | INTERNED) | hash << HASH_SHIFT),
            Some(Text::Extern(external)) => external.set_hash(mc, external.hash(mc) & LOW | hash << HASH_SHIFT),
            None => {}
        }
        Ok(hash as u32)
    }

    /// Returns the interned string with the characters of `string`. A flat string object is interned already, so this returns it. A rope or a view of a store is interned without a copy. See the [module docs](self).
    pub fn intern(&self, string: Str<'gc>) -> Result<Str<'gc>, Error> {
        match Text::of(string.0) {
            // A flat string object is interned when it is made.
            Some(Text::Flat(_)) => Ok(string),
            Some(Text::Rope(rope)) => self.intern_rope(rope, string),
            Some(Text::Extern(external)) => self.intern_extern(external, string),
            // A string in the value word is its own interned string.
            None => Ok(string),
        }
    }

    /// Returns the interned string with the characters of `string`, or `None` if no such string is interned. Nothing is registered, and a rope is left as it is.
    pub fn interned(&self, string: Str<'gc>) -> Result<Option<Str<'gc>>, Error> {
        if let Some(known) = self.known(string) {
            return Ok(Some(known));
        }
        let hash = self.hash(string)?;
        for candidate in Probe::new(self.mc, Symbols::of_arena(self.mc)?, hash) {
            if same_chars(self, candidate, string)? {
                return Ok(Some(candidate));
            }
        }
        Ok(None)
    }

    /// Returns whether `string` is an interned string: a string in the value word, or a string object that is registered as the string of its characters.
    #[inline]
    pub fn is_interned(&self, string: Str<'gc>) -> bool {
        let mc = self.mc;
        match Text::of(string.0) {
            Some(Text::Flat(flat)) => flat.chars(mc) & INTERNED != 0,
            Some(Text::Rope(rope)) => rope.reads(mc) & INTERNED != 0,
            Some(Text::Extern(external)) => external.hash(mc) & INTERNED != 0,
            None => true,
        }
    }

    /// Returns the interned string with the characters of the rope `rope`, which is `string`. If no string is that yet, the rope becomes it, as it is.
    fn intern_rope(&self, rope: Gc<'gc, Rope>, string: Str<'gc>) -> Result<Str<'gc>, Error> {
        let mc = self.mc;
        if let Some(known) = self.known(string) {
            return Ok(known);
        }
        let hash = self.hash(string)?;
        let symbols = Symbols::of_arena(mc)?;
        let mut probe = Probe::new(mc, symbols, hash);
        for candidate in probe.by_ref() {
            if same_chars(self, candidate, string)? {
                // The rope is read as the interned string from now on. That is done only if it makes the rope no deeper: the ropes that contain this rope were balanced for the depth that it has.
                if self.depth(candidate) <= (rope.info(mc) >> DEPTH_SHIFT) as u8 {
                    self.flattened(string, candidate);
                }
                return Ok(candidate);
            }
        }
        self.insert(symbols, &probe, string)?;
        rope.set_reads(mc, rope.reads(mc) | INTERNED);
        Ok(string)
    }

    /// Returns the interned string with the characters of the view `external`, which is `string`. If no string is that yet, the view becomes it, as it is.
    /// If another view is that already, `external` is pointed at the bytes of that view and lets go of its own.
    fn intern_extern(&self, external: Gc<'gc, Extern>, string: Str<'gc>) -> Result<Str<'gc>, Error> {
        let mc = self.mc;
        if external.hash(mc) & INTERNED != 0 {
            return Ok(string);
        }
        let hash = self.hash(string)?;
        let symbols = Symbols::of_arena(mc)?;
        let mut probe = Probe::new(mc, symbols, hash);
        for candidate in probe.by_ref() {
            let held = match Text::of(candidate.0) {
                Some(Text::Extern(held)) => Some(held),
                _ => None,
            };
            // Two views of the same part of one store have the same characters. No byte is read.
            if let Some(held) = held
                && same_part(mc, held, external)
            {
                return Ok(candidate);
            }
            if same_chars(self, candidate, string)? {
                if let Some(held) = held
                    && let Some(store) = held.frozen_ref(mc, Extern::OWNER)
                {
                    external.set_owner(mc, store);
                    external.set_range(mc, held.range(mc));
                }
                return Ok(candidate);
            }
        }
        self.insert(symbols, &probe, string)?;
        external.set_hash(mc, external.hash(mc) | INTERNED);
        Ok(string)
    }

    /// Returns the depth of `string` as a rope. A flat string and a rope that is read as a flat string have a depth of 0.
    fn depth(&self, string: Str<'gc>) -> u8 {
        match self.view(string) {
            StrView::Flat { .. } => 0,
            StrView::Rope { info, .. } => info.depth,
        }
    }

    /// Returns the bytes of the flat string `string` from byte `start` up to byte `end` as a view of the same store, if `string` reads from a store and the part is large enough to share.
    /// `chars` is the number of characters in the part, if the caller knows it.
    fn shared(&self, string: Str<'gc>, start: usize, end: usize, chars: Option<usize>) -> Result<Option<Str<'gc>>, Error> {
        let Some((store, from, whole)) = self.store_of(string) else { return Ok(None) };
        if !shares(end - start, whole) {
            return Ok(None);
        }
        self.view_of(store, from + start, end - start, chars).map(Some)
    }

    /// Returns the store that the flat string `string` reads from, the start of its part in the store, and the number of bytes of the whole store. Returns `None` for a string that reads from no store.
    fn store_of(&self, string: Str<'gc>) -> Option<(FrozenRef<'gc, Store>, usize, usize)> {
        let mc = self.mc;
        match Text::of(string.0) {
            Some(Text::Extern(external)) => Some((external.frozen_ref(mc, Extern::OWNER)?, range_of(external.range(mc)).0, external.owner(mc)?.bytes().len())),
            // A rope that is read as another string reads from the store of that string.
            Some(Text::Rope(rope)) if rope.right(mc) == Value::FALSE => self.store_of(Str(rope.left(mc))),
            _ => None,
        }
    }

    /// Returns the bytes of `string` from byte offset `start` up to, but not including, byte offset `end` as a read-only bytevector. The bytes are the UTF-8 of the characters in that part.
    ///
    /// If `string` reads from a store and the part is large enough to share, the bytevector reads from the same store and nothing is copied. Otherwise the bytes are copied into the arena.
    pub fn utf8_of(&self, string: Str<'gc>, start: usize, end: usize) -> Result<AnyBytevector<'gc>, Error> {
        let mc = self.mc;
        if let Some((store, from, whole)) = self.store_of(string)
            && shares(end - start, whole)
        {
            return Ok(Bytevectors::new(mc).view(store, from + start, end - start)?);
        }
        let mut bytes = ScratchVec::new(mc);
        bytes.extend_with(end - start, 0)?;
        copy_bytes(self, string, start, end, &mut bytes);
        Ok(Bytevectors::new(mc).immutable_from_slice(&bytes)?)
    }

    /// Returns the interned string with the bytes in `built`, which are the `bytes` bytes of a string that is not allocated yet. `shape` is the low half of the `chars` word of that string. If the arena has no such string, a string is allocated for the bytes and interned.
    fn settle(&self, built: &[Cell<u64>], bytes: usize, shape: u64) -> Result<Str<'gc>, Error> {
        let mc = self.mc;
        let symbols = Symbols::of_arena(mc)?;
        let units = Units::Packed(Packed::new(built, bytes));
        let hash = narrowed(hash_units(units, symbols.seed(mc)));
        let mut probe = Probe::new(mc, symbols, hash);
        for candidate in probe.by_ref() {
            // A string that fits in the buffer is never a rope. So a flat string object or an external string can have these bytes.
            match Text::of(candidate.0) {
                Some(Text::Extern(_)) => {
                    let StrView::Flat { units: held, .. } = self.view(candidate) else { continue };
                    if held.len() == bytes && held.equal(units) {
                        return Ok(candidate);
                    }
                }
                // Two flat string objects with the same number of bytes and the same words have the same bytes. The bits past the last byte are 0 in both.
                Some(Text::Flat(held)) => {
                    let words = held.items(mc).words();
                    if held.chars(mc) & SHAPE == shape && words.len() == built.len() && words.iter().zip(built).all(|(word, new)| word.get() == new.get()) {
                        return Ok(candidate);
                    }
                }
                _ => {}
            }
        }
        let object = mc.alloc_zeroed::<Flat, 1>([shape | INTERNED | u64::from(hash) << HASH_SHIFT], built.len())?;
        for (word, new) in object.items(mc).words().iter().zip(built) {
            word.set(new.get());
        }
        let string = Str(Value::object(mc, object));
        self.insert(symbols, &probe, string)?;
        Ok(string)
    }

    /// Puts the string object `string` into the table of interned strings, in the slot where `probe` ended. `probe` has found no string with the characters of `string`. The array of the table is made if it does not exist, and made anew if it is too full.
    fn insert(&self, symbols: Symbols<'gc>, probe: &Probe<'gc>, string: Str<'gc>) -> Result<(), Error> {
        let mc = self.mc;
        let used = symbols.strings_used(mc);
        // The slot of a string that has died is taken as it is. A slot that was never used is taken while the table stays at most three quarters used.
        if let (Some(slots), Some(index)) = (probe.slots, probe.free)
            && (!probe.fresh || (used + 1) * 4 <= slots.len() * 3)
        {
            slots.set(mc, index, (Some(string.0), probe.hash));
            if probe.fresh {
                symbols.count_string(mc);
            }
            return Ok(());
        }
        // The living strings move to a new array with room for as many again.
        let mut living = 0;
        if let Some(old) = probe.slots {
            for index in 0..old.len() {
                living += usize::from(old.get(index).0.is_some());
            }
        }
        let len = (2 * (living + 1)).next_power_of_two().max(MIN_SLOTS);
        let array = InternSlots::new(mc, len, (None, 0))?;
        let slots = array.items(mc);
        if let Some(old) = probe.slots {
            for index in 0..old.len() {
                if let (Some(held), hash) = old.get(index) {
                    place(mc, slots, hash, held);
                }
            }
        }
        place(mc, slots, probe.hash, string.0);
        symbols.set_strings(mc, array, living + 1);
        Ok(())
    }

    /// Returns whether `string` is a flat string object in the arena, and not a string in the value word, a rope or a view of a store.
    pub(crate) fn is_object(&self, string: Str<'gc>) -> bool {
        matches!(Text::of(string.0), Some(Text::Flat(_)))
    }

    /// Returns the number of interned string objects, for tests.
    #[cfg(test)]
    fn interned_count(&self) -> usize {
        let Some(slots) = Probe::new(self.mc, Symbols::of_arena(self.mc).expect("an intern table"), 1).slots else { return 0 };
        (0..slots.len()).filter(|&index| slots.get(index).0.is_some()).count()
    }
}

/// A search of the table of interned strings for the strings with one hash. It yields each interned string with that hash, in the order of the slots. Once it has ended, `free` is the slot that a new string with the hash can take, if the search passed one.
struct Probe<'gc> {
    /// The slots of the table, or `None` if the table has no array yet.
    slots: Option<Slots<'gc, slot::Tagged>>,
    hash: u32,
    /// The next slot to look at, and the number of slots that are left to look at.
    at: usize,
    left: usize,
    free: Option<usize>,
    /// Whether `free` is a slot that was never used. Taking such a slot makes the table fuller. Taking the slot of a string that has died does not.
    fresh: bool,
}

impl<'gc> Probe<'gc> {
    #[inline]
    fn new(mc: &Mutation<'gc>, symbols: Symbols<'gc>, hash: u32) -> Self {
        let slots = symbols.strings(mc).map(|array| array.items(mc));
        let len = slots.map_or(0, |slots| slots.len());
        Self { slots, hash, at: hash as usize & len.wrapping_sub(1), left: len, free: None, fresh: false }
    }
}

impl<'gc> Iterator for Probe<'gc> {
    type Item = Str<'gc>;

    #[inline]
    fn next(&mut self) -> Option<Str<'gc>> {
        let slots = self.slots?;
        let mask = slots.len().wrapping_sub(1);
        while self.left > 0 {
            let index = self.at;
            self.at = (index + 1) & mask;
            self.left -= 1;
            match slots.get(index) {
                (Some(held), hash) if hash == self.hash => return Some(Str(held)),
                (Some(_), _) => {}
                // A slot that was never used ends the search.
                (None, 0) => {
                    if self.free.is_none() {
                        (self.free, self.fresh) = (Some(index), true);
                    }
                    self.left = 0;
                }
                // The string of this slot has died. The slot can be taken, and the search goes on.
                (None, _) => self.free = self.free.or(Some(index)),
            }
        }
        None
    }
}

/// Puts `object`, whose hash is `hash`, into the first slot of `slots` that was never used, starting at the slot of its hash. `slots` is a new array, which has such a slot.
fn place<'gc>(mc: &Mutation<'gc>, slots: Slots<'gc, slot::Tagged>, hash: u32, object: Value<'gc>) {
    let mask = slots.len().wrapping_sub(1);
    let mut at = hash as usize & mask;
    for _ in 0..slots.len() {
        if slots.get(at) == (None, 0) {
            slots.set(mc, at, (Some(object), hash));
            return;
        }
        at = (at + 1) & mask;
    }
}

/// Returns the 32 bits of `hash` that a string keeps. 0 means that no hash is kept, so a hash of 0 becomes 1.
#[inline]
fn narrowed(hash: u64) -> u32 {
    (hash as u32).max(1)
}

impl<'gc> Strings<'_, 'gc> {
    /// Returns the view of a rope or an external string. It is kept out of line so that the views of flat strings inline.
    #[inline(never)]
    fn view_rest(&self, string: Str<'gc>) -> StrView<'_, Str<'gc>> {
        let mc = self.mc;
        match Text::of(string.0) {
            Some(Text::Rope(rope)) => {
                // A rope without a right half is read as the string in `left`.
                let right = rope.right(mc);
                if right == Value::FALSE {
                    return self.view(Str(rope.left(mc)));
                }
                StrView::Rope { left: Str(rope.left(mc)), right: Str(right), info: rope_info(mc, rope), flat: None }
            }
            Some(Text::Extern(external)) => {
                let (start, len) = range_of(external.range(mc));
                let bytes = external.owner(mc).and_then(|store| store.bytes().get(start..start + len)).unwrap_or(&[]);
                let units = Units::Slice(bytes);
                // The characters are counted the first time the string is read, and not when the host hands it over.
                let word = external.hash(mc);
                let chars = if word & COUNTED == 0 {
                    let chars = units.count_chars();
                    external.set_hash(mc, word | (chars as u64 + 1).min(COUNTED));
                    chars
                } else {
                    (word & COUNTED) as usize - 1
                };
                StrView::Flat { units, chars }
            }
            _ => panic!("strings are flat, ropes or external"),
        }
    }
}

/// Returns whether the views `first` and `second` read the same part of the same store.
fn same_part<'gc>(mc: &Mutation<'gc>, first: Gc<'gc, Extern>, second: Gc<'gc, Extern>) -> bool {
    let stores = (first.frozen_ref(mc, Extern::OWNER).map(FrozenRef::to_word), second.frozen_ref(mc, Extern::OWNER).map(FrozenRef::to_word));
    stores.0.is_some() && stores.0 == stores.1 && first.range(mc) == second.range(mc)
}

/// Returns the info of `rope`, which is read as its two halves.
#[inline]
fn rope_info<'gc>(mc: &Mutation<'gc>, rope: Gc<'gc, Rope>) -> Info {
    let word = rope.info(mc);
    Info { bytes: (word & MAX_LEN as u64) as usize, chars: rope.chars(mc) as usize, depth: (word >> DEPTH_SHIFT) as u8 }
}

impl<'gc> Host for Strings<'_, 'gc> {
    type Str = Str<'gc>;
    type Error = Error;

    #[inline(always)]
    fn view(&self, string: Str<'gc>) -> StrView<'_, Str<'gc>> {
        let mc = self.mc;
        match Text::of(string.0) {
            Some(Text::Flat(flat)) => {
                let (word, words) = (flat.chars(mc), flat.items(mc).words());
                let bytes = (words.len() * 8).saturating_sub((word >> UNUSED_SHIFT & 7) as usize);
                StrView::Flat { units: Units::Packed(Packed::new(words, bytes)), chars: (word & COUNT) as usize }
            }
            None => {
                debug_assert!(is_inline(string.0), "a string that's no object is inline");
                let inline = inline_units(string.0);
                StrView::Flat { units: Units::Inline(inline), chars: inline.chars() }
            }
            _ => self.view_rest(string),
        }
    }

    #[inline(always)]
    fn info(&self, string: Str<'gc>) -> Info {
        // A rope that is read as its two halves keeps its info in two words. Reading them takes less than a view of the rope.
        if let Some(Text::Rope(rope)) = Text::of(string.0)
            && rope.right(self.mc) != Value::FALSE
        {
            return rope_info(self.mc, rope);
        }
        match self.view(string) {
            StrView::Flat { units, chars } => Info { bytes: units.len(), chars, depth: 0 },
            StrView::Rope { info, .. } => info,
        }
    }

    fn flat(&self, bytes: usize, chars: usize, init: impl FnOnce(UnitsMut<'_>)) -> Result<Str<'gc>, Error> {
        if bytes <= INLINE_BYTES {
            return Ok(Str(inline_value(Inline::filled(bytes, init))));
        }
        if bytes > FLAT_MAX {
            return Err(StrError::TooLong.into());
        }
        let mc = self.mc;
        let words = bytes.div_ceil(8);
        let shape = chars as u64 | ((words * 8 - bytes) as u64) << UNUSED_SHIFT;
        // A short string is built on the stack and looked up there. It is allocated only if the arena does not have its bytes yet.
        if words <= BUILD {
            let (short, long);
            let built = if words <= BUILD_SHORT {
                short = [const { Cell::new(0) }; BUILD_SHORT];
                &short[..words]
            } else {
                long = [const { Cell::new(0) }; BUILD];
                &long[..words]
            };
            init(UnitsMut::Packed(PackedMut::new(built, bytes)));
            return self.settle(built, bytes, shape);
        }
        // A long string gets a store of its own outside the arena, and is a view of all of it. It is interned when it is first compared or used as a key.
        mc.ensure(bytes)?;
        let mut buffer = vec![0; bytes];
        init(UnitsMut::Slice(&mut buffer));
        let store = mc.frozen_owning(Store::Owned(buffer.into_boxed_slice()), bytes)?;
        self.view_of(store, 0, bytes, Some(chars))
    }

    fn slice(&self, string: Str<'gc>, start: usize, end: usize, chars: Option<usize>) -> Result<Option<Str<'gc>>, Error> {
        self.shared(string, start, end, chars)
    }

    #[inline]
    fn known(&self, string: Str<'gc>) -> Option<Str<'gc>> {
        let mc = self.mc;
        match Text::of(string.0) {
            Some(Text::Flat(flat)) => (flat.chars(mc) & INTERNED != 0).then_some(string),
            // A rope is the interned string itself, or it is read as another string, which can be the interned string. The flat copy of an interned rope is not interned.
            Some(Text::Rope(rope)) => {
                if rope.reads(mc) & INTERNED != 0 {
                    return Some(string);
                }
                if rope.right(mc) != Value::FALSE {
                    return None;
                }
                self.known(Str(rope.left(mc)))
            }
            Some(Text::Extern(external)) => (external.hash(mc) & INTERNED != 0).then_some(string),
            None => Some(string),
        }
    }

    fn canonical(&self, string: Str<'gc>) -> Result<Option<Str<'gc>>, Error> {
        self.intern(string).map(Some)
    }

    fn rope(&self, left: Str<'gc>, right: Str<'gc>, info: Info) -> Result<Str<'gc>, Error> {
        let rope = Rope::new(self.mc, left.0, right.0, info.bytes as u64 | u64::from(info.depth) << DEPTH_SHIFT, info.chars as u64, 0)?;
        Ok(Str(Value::object(self.mc, rope)))
    }

    fn flattened(&self, rope: Str<'gc>, flat: Str<'gc>) {
        // An interned rope that is flattened has taken its flat copy already, and is its own flat string.
        if rope == flat {
            return;
        }
        if let Some(Text::Rope(object)) = Text::of(rope.0) {
            // The rope is read as `flat` from now on, so it lets go of its halves. The characters are then held once.
            object.set_left(self.mc, flat.0);
            object.set_right(self.mc, Value::FALSE);
        }
    }

    fn count_read(&self, rope: Str<'gc>) -> u64 {
        let Some(Text::Rope(object)) = Text::of(rope.0) else { return 0 };
        let word = object.reads(self.mc);
        let reads = ((word & READS) + 1).min(READS);
        object.set_reads(self.mc, word & !READS | reads);
        reads
    }
}
