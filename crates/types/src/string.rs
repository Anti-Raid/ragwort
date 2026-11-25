//! Strings in the arena, for `ragwort-string`. A string is stored in one of these ways:
//!
//! - A flat string of up to [`INLINE_CHARS`] Latin-1 characters is stored inline in the value word.
//! - A longer flat string is a [`Str8`], [`Str16`] or [`Str32`] object, chosen by its widest
//!   character. The characters are packed into the object's items.
//! - A rope is a [`Rope`] object.
//! - A flat string whose characters are owned by the host is an [`Extern`] object.
//!
//! # Hashes
//!
//! [`Strings::hash`] returns a hash of a string's characters, for hash tables. A flat string
//! object, a rope and an external string keep the hash once it is computed, so the characters of a
//! string that is hashed again and again are read once.
//!
//! The hash costs a string no memory. A flat string object has one word for its number of
//! characters, and the hash is in the upper half of that word:
//!
//! ```text
//! bits 0 to 30    the number of characters
//! bit 31          set while the string is interned
//! bits 32 to 63   the hash, or 0 if it has not been computed
//! ```
//!
//! A rope has the same layout in its `reads` word, with the number of reads by index in bits 0 to 30.
//! An external string has it in its `hash` word, where bits 0 to 30 are not used.
//!
//! So a flat string has at most [`FLAT_MAX`] characters. A rope can be longer.
//!
//! # Interned strings
//!
//! The arena has one string for each text: the interned string. So two interned strings have the
//! same characters exactly when they are the same value, and comparing them reads no character.
//!
//! - A string in the value word is interned as it is. Equal ones are the same word already.
//! - A flat string object is interned when it is made. If the arena already has a string with
//!   the same characters, that string is returned and the new object is dropped.
//! - A rope is not interned when it is made, so that joining strings stays cheap. It is interned
//!   the first time it is compared with a string of the same length, or used as the key of a
//!   table. Its hash is computed from its pieces, and nothing is copied.
//! - An external string is not interned when it is made either, so that handing a string to the
//!   arena reads none of its characters. It is interned at the same two moments as a rope.
//!
//! ## Interned external strings
//!
//! If no string with its characters is interned, the external string itself becomes the interned
//! string. Its characters stay outside the arena. A flat string that is made with the same
//! characters afterwards is the external string.
//!
//! If another string is the interned string already, the external string stays as it is. It has
//! no field to keep that string in, so each comparison looks the interned string up by the kept
//! hash and compares the characters.
//!
//! ## Interned ropes
//!
//! Interning a rope has one of two results:
//!
//! - No string with its characters is interned. The rope itself becomes the interned string. It
//!   keeps its two halves, so the pieces that it shares with other strings stay shared.
//! - Another string is the interned string already. The rope then keeps that string in `flat`
//!   and lets go of its halves, and it is read as that string from then on.
//!
//! A rope that is the interned string stays the interned string when it is flattened. The flat
//! copy belongs to the rope alone: it is not interned, and no other value refers to it. So every
//! flat string object that a program can hold is interned.
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
//! is allocated first and looked up afterwards. If the interned string with its characters is a
//! rope, the new object becomes the flat copy of that rope, and the rope is returned.
//!
//! The hash is seeded with the arena's seed, so it cannot be predicted from outside. An arena has
//! one seed for its whole life, and an image is loaded only into an arena with the image's seed,
//! so a hash that is kept in a string stays right.

pub use ragwort_string::*;

pub use crate::gc::Error;
use std::cell::Cell;

use crate::gc::{Gc, INLINE_STRING, Mutation, Object, Slots, TAG, Value, slot};
use crate::objects::{InternSlots, InternSlotsFields};
use crate::symbol::Symbols;

#[cfg(test)]
#[path = "tests/strings.rs"]
mod tests;

crate::gc::objects! {
    /// Every kind of string object.
    pub kind Text after crate::gc::table::Containers;

    /// A flat string of characters, none above U+00FF, packed eight to an item. `chars` holds the number of characters and the hash. See the [module docs](self).
    pub struct Str8 { chars: u64 } items u64
    /// A flat string of characters, none above U+FFFF and at least one above U+00FF, packed four to an item. `chars` is as in [`Str8`].
    pub struct Str16 { chars: u64 } items u64
    /// A flat string with at least one character above U+FFFF, packed two to an item. `chars` is as in [`Str8`].
    pub struct Str32 { chars: u64 } items u64
    /// The concatenation of two nonempty strings, `left` then `right`. `info` is the packed `Info`
    /// of the rope. `flat` is the string that the rope is read as, and `#f` while the rope is read as its halves.
    /// It is the flat copy of a rope that has been flattened, or the interned string of a rope that is not the interned string itself.
    /// A rope with a `flat` has `#f` for `left` and `right`.
    /// `reads` holds the number of reads of the rope by character index, the interned flag and the hash. See the [module docs](self).
    pub struct Rope { left: Value, right: Value, info: u64, flat: Value, reads: u64 }
    /// A flat string whose characters are stored outside the arena, in `owner`. `owner` is dropped once the string is unreachable. `hash` holds the interned flag and the hash of the characters. See the [module docs](self).
    pub struct Extern { owner: Frozen<Box<dyn External>>, hash: u64 }
}

/// The most characters that a flat string object can have. Its word for the number of characters also holds the hash. See the [module docs](self).
pub const FLAT_MAX: usize = (1 << 31) - 1;

/// The bits of a flat string's `chars` word that hold the number of characters. The same bits of a rope's `reads` word hold the number of reads.
const COUNT: u64 = FLAT_MAX as u64;
/// The bit of a flat string's `chars` word, of a rope's `reads` word or of an external string's `hash` word that is set while the string is interned.
const INTERNED: u64 = 1 << 31;
/// The number of bits that the hash in one of those words is shifted up by.
const HASH_SHIFT: u32 = 32;
/// The number of words of the buffer in which a new flat string is built before it is looked up. See the [module docs](self).
pub const BUILD: usize = 64;
/// The number of words of the smaller buffer, which a string that fits in it is built in. Clearing it takes less time.
const BUILD_SHORT: usize = 8;
/// The least number of slots in an intern table that has an array.
const MIN_SLOTS: usize = 8;

/// External strings of fewer bytes than this are copied into the arena. Keeping them outside would cost more than their characters.
const COPY_EXTERNAL: usize = 64;

/// A string of up to this many Latin-1 characters is stored inline in the value word. Creating
/// one allocates nothing, and equal inline strings are the same value.
pub const INLINE_CHARS: usize = 7;

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

    /// Returns a string whose characters are stored outside the arena, in `chars`, such as an
    /// [`ExternalText`]. The characters must never change in number or in value, because strings
    /// are immutable. A string of fewer than 64 bytes is copied into the arena instead.
    pub fn external(&self, chars: impl External) -> Result<Str<'gc>, Error> {
        let units = chars.units();
        check_external(units)?;
        let bytes = units.len() * units.width().bytes();
        if bytes < COPY_EXTERNAL {
            return self.flat(units.width(), units.len(), |mut target| target.copy_from(units));
        }
        let owner: Box<dyn External> = Box::new(chars);
        let external = Extern::new(self.mc, self.mc.frozen_owning(owner, bytes)?, 0)?;
        Ok(Str(Value::object(self.mc, external)))
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
            Some(Text::Str8(flat)) => flat.chars(mc) >> HASH_SHIFT,
            Some(Text::Str16(flat)) => flat.chars(mc) >> HASH_SHIFT,
            Some(Text::Str32(flat)) => flat.chars(mc) >> HASH_SHIFT,
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
            Some(Text::Str8(flat)) => flat.set_chars(mc, flat.chars(mc) & (COUNT | INTERNED) | hash << HASH_SHIFT),
            Some(Text::Str16(flat)) => flat.set_chars(mc, flat.chars(mc) & (COUNT | INTERNED) | hash << HASH_SHIFT),
            Some(Text::Str32(flat)) => flat.set_chars(mc, flat.chars(mc) & (COUNT | INTERNED) | hash << HASH_SHIFT),
            Some(Text::Rope(rope)) => rope.set_reads(mc, rope.reads(mc) & (COUNT | INTERNED) | hash << HASH_SHIFT),
            Some(Text::Extern(external)) => external.set_hash(mc, external.hash(mc) & INTERNED | hash << HASH_SHIFT),
            None => {}
        }
        Ok(hash as u32)
    }

    /// Returns the interned string with the characters of `string`. A flat string that a program holds is interned already, so this returns it. A rope or an external string is interned without a copy. See the [module docs](self).
    pub fn intern(&self, string: Str<'gc>) -> Result<Str<'gc>, Error> {
        match Text::of(string.0) {
            Some(Text::Str8(flat)) => self.intern_flat(flat, string),
            Some(Text::Str16(flat)) => self.intern_flat(flat, string),
            Some(Text::Str32(flat)) => self.intern_flat(flat, string),
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
            Some(Text::Str8(flat)) => flat.chars(mc) & INTERNED != 0,
            Some(Text::Str16(flat)) => flat.chars(mc) & INTERNED != 0,
            Some(Text::Str32(flat)) => flat.chars(mc) & INTERNED != 0,
            Some(Text::Rope(rope)) => rope.reads(mc) & INTERNED != 0,
            Some(Text::Extern(external)) => external.hash(mc) & INTERNED != 0,
            None => true,
        }
    }

    /// Makes the flat string object `flat`, which is `string`, the interned string of its characters, unless another string is that already. Returns the interned string.
    ///
    /// If the interned string is a rope, the rope takes `flat` as its flat copy and is returned. The result is then read as a flat string too.
    fn intern_flat<T: Object>(&self, flat: Gc<'gc, T>, string: Str<'gc>) -> Result<Str<'gc>, Error>
    where
        Gc<'gc, T>: Flat<'gc>,
    {
        let mc = self.mc;
        if flat.count(mc) & INTERNED != 0 {
            return Ok(string);
        }
        let hash = self.hash(string)?;
        let symbols = Symbols::of_arena(mc)?;
        let mut probe = Probe::new(mc, symbols, hash);
        for candidate in probe.by_ref() {
            if same_chars(self, candidate, string)? {
                if let Some(Text::Rope(rope)) = Text::of(candidate.0)
                    && rope.flat(mc) == Value::FALSE
                {
                    self.flattened(candidate, string);
                }
                return Ok(candidate);
            }
        }
        self.insert(symbols, &probe, string)?;
        flat.set_count(mc, flat.count(mc) | INTERNED);
        Ok(string)
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
                if self.depth(candidate) <= Info::from_bits(rope.info(mc)).depth {
                    self.flattened(string, candidate);
                }
                return Ok(candidate);
            }
        }
        self.insert(symbols, &probe, string)?;
        rope.set_reads(mc, rope.reads(mc) | INTERNED);
        Ok(string)
    }

    /// Returns the interned string with the characters of the external string `external`, which is `string`. If no string is that yet, the external string becomes it, as it is.
    fn intern_extern(&self, external: Gc<'gc, Extern>, string: Str<'gc>) -> Result<Str<'gc>, Error> {
        let mc = self.mc;
        if external.hash(mc) & INTERNED != 0 {
            return Ok(string);
        }
        let hash = self.hash(string)?;
        let symbols = Symbols::of_arena(mc)?;
        let mut probe = Probe::new(mc, symbols, hash);
        for candidate in probe.by_ref() {
            if same_chars(self, candidate, string)? {
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
            StrView::Flat(_) => 0,
            StrView::Rope { info, .. } => info.depth,
        }
    }

    /// Returns the interned string with the characters in `built`, which are the `len` characters of a string that is not allocated yet. If the arena has no such string, a string is allocated for them and interned.
    fn settle<T: Object>(&self, built: &[Cell<u64>], len: usize) -> Result<Str<'gc>, Error>
    where
        Gc<'gc, T>: Flat<'gc>,
    {
        let mc = self.mc;
        let width = <Gc<'gc, T> as Flat<'gc>>::WIDTH;
        let symbols = Symbols::of_arena(mc)?;
        let hash = narrowed(hash_units(Units::Packed(Packed::new(built, len, width)), symbols.seed(mc)));
        let mut probe = Probe::new(mc, symbols, hash);
        for candidate in probe.by_ref() {
            // A string that fits in the buffer is never a rope. So a flat string of this width or an external string can have these characters.
            let Some(text) = Text::of(candidate.0) else { continue };
            if let Text::Extern(_) = text {
                let StrView::Flat(units) = self.view(candidate) else { continue };
                if units.len() == len && units.width() == width && units.equal(Units::Packed(Packed::new(built, len, width))) {
                    return Ok(candidate);
                }
                continue;
            }
            // Two flat strings of one width with the same number of characters and the same words have the same characters.
            let Some(held) = <Gc<'gc, T> as Flat<'gc>>::cast(text) else { continue };
            if held.count(mc) & COUNT == len as u64 && held.words(mc).iter().zip(built).all(|(word, new)| word.get() == new.get()) {
                return Ok(candidate);
            }
        }
        let object = mc.alloc_zeroed::<T, 1>([len as u64 | INTERNED | u64::from(hash) << HASH_SHIFT], built.len())?;
        for (word, new) in object.words(mc).iter().zip(built) {
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

    /// Returns whether `string` is a flat string object in the arena, and not a string in the value word, a rope or an external string.
    pub(crate) fn is_object(&self, string: Str<'gc>) -> bool {
        matches!(Text::of(string.0), Some(Text::Str8(_) | Text::Str16(_) | Text::Str32(_)))
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

/// A flat string object of one of the three unit widths.
trait Flat<'gc>: Copy + PartialEq {
    /// The width of the units of this type of string.
    const WIDTH: Width;

    /// Returns the `chars` word: the number of characters, the interned flag and the hash.
    fn count(self, mc: &Mutation<'gc>) -> u64;

    fn set_count(self, mc: &Mutation<'gc>, word: u64);

    /// Returns the words that hold the characters.
    fn words(self, mc: &Mutation<'gc>) -> &'gc [Cell<u64>];

    /// Returns `text` as a flat string of this type, or `None` if it is a string of another kind.
    fn cast(text: Text<'gc>) -> Option<Self>;
}

impl<'gc> Flat<'gc> for Gc<'gc, Str8> {
    const WIDTH: Width = Width::One;

    #[inline]
    fn count(self, mc: &Mutation<'gc>) -> u64 {
        self.chars(mc)
    }

    #[inline]
    fn set_count(self, mc: &Mutation<'gc>, word: u64) {
        self.set_chars(mc, word);
    }

    #[inline]
    fn words(self, mc: &Mutation<'gc>) -> &'gc [Cell<u64>] {
        self.items(mc).words()
    }
    #[inline]
    fn cast(text: Text<'gc>) -> Option<Self> {
        match text {
            Text::Str8(flat) => Some(flat),
            _ => None,
        }
    }
}

impl<'gc> Flat<'gc> for Gc<'gc, Str16> {
    const WIDTH: Width = Width::Two;

    #[inline]
    fn count(self, mc: &Mutation<'gc>) -> u64 {
        self.chars(mc)
    }

    #[inline]
    fn set_count(self, mc: &Mutation<'gc>, word: u64) {
        self.set_chars(mc, word);
    }

    #[inline]
    fn words(self, mc: &Mutation<'gc>) -> &'gc [Cell<u64>] {
        self.items(mc).words()
    }
    #[inline]
    fn cast(text: Text<'gc>) -> Option<Self> {
        match text {
            Text::Str16(flat) => Some(flat),
            _ => None,
        }
    }
}

impl<'gc> Flat<'gc> for Gc<'gc, Str32> {
    const WIDTH: Width = Width::Four;

    #[inline]
    fn count(self, mc: &Mutation<'gc>) -> u64 {
        self.chars(mc)
    }

    #[inline]
    fn set_count(self, mc: &Mutation<'gc>, word: u64) {
        self.set_chars(mc, word);
    }

    #[inline]
    fn words(self, mc: &Mutation<'gc>) -> &'gc [Cell<u64>] {
        self.items(mc).words()
    }
    #[inline]
    fn cast(text: Text<'gc>) -> Option<Self> {
        match text {
            Text::Str32(flat) => Some(flat),
            _ => None,
        }
    }
}

impl<'gc> Strings<'_, 'gc> {
    /// Returns the view of a rope or an external string. It is kept out of line so that the views of flat strings inline.
    #[inline(never)]
    fn view_rest(&self, string: Str<'gc>) -> StrView<'_, Str<'gc>> {
        let mc = self.mc;
        match Text::of(string.0) {
            Some(Text::Rope(rope)) => {
                // A rope with a `flat` is read as that string. It has let go of its halves.
                let flat = rope.flat(mc);
                if flat != Value::FALSE {
                    return self.view(Str(flat));
                }
                StrView::Rope { left: Str(rope.left(mc)), right: Str(rope.right(mc)), info: Info::from_bits(rope.info(mc)), flat: None }
            }
            Some(Text::Extern(external)) => StrView::Flat(external.owner(mc).map_or(Units::One(&[]), |owner| owner.units())),
            _ => panic!("strings are flat, ropes or external"),
        }
    }
}

impl<'gc> Host for Strings<'_, 'gc> {
    type Str = Str<'gc>;
    type Error = Error;

    #[inline(always)]
    fn view(&self, string: Str<'gc>) -> StrView<'_, Str<'gc>> {
        let mc = self.mc;
        match Text::of(string.0) {
            Some(Text::Str8(flat)) => StrView::Flat(Units::Packed(Packed::new(flat.items(mc).words(), (flat.chars(mc) & COUNT) as usize, Width::One))),
            Some(Text::Str16(flat)) => StrView::Flat(Units::Packed(Packed::new(flat.items(mc).words(), (flat.chars(mc) & COUNT) as usize, Width::Two))),
            Some(Text::Str32(flat)) => StrView::Flat(Units::Packed(Packed::new(flat.items(mc).words(), (flat.chars(mc) & COUNT) as usize, Width::Four))),
            None => {
                debug_assert!(is_inline(string.0), "a string that's no object is inline");
                StrView::Flat(Units::Inline(inline_units(string.0)))
            }
            _ => self.view_rest(string),
        }
    }

    fn flat(&self, width: Width, len: usize, init: impl FnOnce(UnitsMut<'_>)) -> Result<Str<'gc>, Error> {
        if width == Width::One && len <= INLINE_CHARS {
            return Ok(Str(inline_value(Inline::filled(len, init))));
        }
        if len > FLAT_MAX {
            return Err(StrError::TooLong.into());
        }
        let mc = self.mc;
        let (chars, words) = (len as u64, len.div_ceil(width.per_word()));
        // A short string is built on the stack and looked up there. It is allocated only if the arena does not have its characters yet.
        if words <= BUILD {
            let (short, long);
            let built = if words <= BUILD_SHORT {
                short = [const { Cell::new(0) }; BUILD_SHORT];
                &short[..words]
            } else {
                long = [const { Cell::new(0) }; BUILD];
                &long[..words]
            };
            init(UnitsMut::Packed(PackedMut::new(built, len, width)));
            return match width {
                Width::One => self.settle::<Str8>(built, len),
                Width::Two => self.settle::<Str16>(built, len),
                Width::Four => self.settle::<Str32>(built, len),
            };
        }
        // A long string is filled in place and then interned. If the arena has a string with the same characters, that string is returned, and the new object is left for the collector.
        match width {
            Width::One => {
                let object = mc.alloc_zeroed::<Str8, 1>([chars], words)?;
                init(UnitsMut::Packed(PackedMut::new(object.items(mc).words(), len, width)));
                self.intern_flat(object, Str(Value::object(mc, object)))
            }
            Width::Two => {
                let object = mc.alloc_zeroed::<Str16, 1>([chars], words)?;
                init(UnitsMut::Packed(PackedMut::new(object.items(mc).words(), len, width)));
                self.intern_flat(object, Str(Value::object(mc, object)))
            }
            Width::Four => {
                let object = mc.alloc_zeroed::<Str32, 1>([chars], words)?;
                init(UnitsMut::Packed(PackedMut::new(object.items(mc).words(), len, width)));
                self.intern_flat(object, Str(Value::object(mc, object)))
            }
        }
    }

    #[inline]
    fn known(&self, string: Str<'gc>) -> Option<Str<'gc>> {
        let mc = self.mc;
        match Text::of(string.0) {
            Some(Text::Str8(flat)) => (flat.chars(mc) & INTERNED != 0).then_some(string),
            Some(Text::Str16(flat)) => (flat.chars(mc) & INTERNED != 0).then_some(string),
            Some(Text::Str32(flat)) => (flat.chars(mc) & INTERNED != 0).then_some(string),
            // A rope is the interned string itself, or it keeps the interned string in `flat`. The flat copy of an interned rope is not interned.
            Some(Text::Rope(rope)) => {
                if rope.reads(mc) & INTERNED != 0 {
                    return Some(string);
                }
                let flat = rope.flat(mc);
                (flat != Value::FALSE).then_some(Str(flat))
            }
            Some(Text::Extern(external)) => (external.hash(mc) & INTERNED != 0).then_some(string),
            None => Some(string),
        }
    }

    fn canonical(&self, string: Str<'gc>) -> Result<Option<Str<'gc>>, Error> {
        self.intern(string).map(Some)
    }

    fn rope(&self, left: Str<'gc>, right: Str<'gc>, info: Info) -> Result<Str<'gc>, Error> {
        let rope = Rope::new(self.mc, left.0, right.0, info.to_bits(), Value::FALSE, 0)?;
        Ok(Str(Value::object(self.mc, rope)))
    }

    fn flattened(&self, rope: Str<'gc>, flat: Str<'gc>) {
        // An interned rope that is flattened has taken its flat copy already, and is its own flat string.
        if rope == flat {
            return;
        }
        if let Some(Text::Rope(object)) = Text::of(rope.0) {
            // The rope is read as `flat` from now on, so it lets go of its halves. The characters are then held once.
            object.set_flat(self.mc, flat.0);
            object.set_left(self.mc, Value::FALSE);
            object.set_right(self.mc, Value::FALSE);
        }
    }

    fn count_read(&self, rope: Str<'gc>) -> u64 {
        let Some(Text::Rope(object)) = Text::of(rope.0) else { return 0 };
        let word = object.reads(self.mc);
        let reads = ((word & COUNT) + 1).min(COUNT);
        object.set_reads(self.mc, word & !COUNT | reads);
        reads
    }
}
