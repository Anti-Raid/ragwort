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
//! object and an external string keep the hash once it is computed, so the characters of a string
//! that is hashed again and again are read once.
//!
//! The hash costs a flat string no memory. A flat string object has one word for its number of
//! characters, and the hash is in the upper half of that word:
//!
//! ```text
//! bits 0 to 30    the number of characters
//! bit 31          not used yet
//! bits 32 to 63   the hash, or 0 if it has not been computed
//! ```
//!
//! So a flat string has at most [`FLAT_MAX`] characters. A rope can be longer.
//!
//! # Interned strings
//!
//! The arena has one flat string for each text: the interned string. So two flat strings have the
//! same characters exactly when they are the same value, and comparing them reads no character.
//!
//! - A string in the value word is interned as it is. Equal ones are the same word already.
//! - A flat string object is interned when it is made. If the arena already has a string with
//!   the same characters, that string is returned and the new object is dropped. Bit 31 of the
//!   `chars` word marks an interned object.
//! - A rope is not interned when it is made, so that joining strings stays cheap. It is interned
//!   as its flat copy the first time it is compared with a string of the same length, or used as
//!   the key of a table. The rope then keeps the flat copy and lets go of its two halves.
//! - An external string is not interned yet. [`Strings::intern`] returns it unchanged, and it is
//!   compared by its characters.
//!
//! The arena holds its interned strings weakly, in one table for each width of unit. An interned
//! string that nothing else refers to is collected, and making its text again registers a new string.
//!
//! ## The tables
//!
//! An intern table is a hash table with linear probing, in one array of words. A slot is one word:
//! the string's hash in the upper half, and a weak reference to the string in the lower half. So a
//! string costs 8 bytes for each slot, and a table is kept between a quarter and three quarters full.
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
//! is allocated first and looked up afterwards.
//!
//! The hash is seeded with the arena's seed, so it cannot be predicted from outside. An arena has
//! one seed for its whole life, and an image is loaded only into an arena with the image's seed,
//! so a hash that is kept in a string stays right.

pub use ragwort_string::*;

pub use crate::gc::Error;
use std::cell::Cell;

use crate::gc::raw::Raw;
use crate::gc::table::WeakSlots;
use crate::gc::{Gc, INLINE_STRING, Mutation, Object, Slots, TAG, Value, slot};
use crate::objects::{Interns, InternsFields};
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
    /// of the rope. `flat` is the flat copy once the rope has been flattened, and `#f` until then.
    /// A flattened rope has `#f` for `left` and `right`: it is read as its flat copy.
    /// `reads` counts the reads of the rope by character index.
    pub struct Rope { left: Value, right: Value, info: u64, flat: Value, reads: u64 }
    /// A flat string whose characters are stored outside the arena, in `owner`. `owner` is dropped once the string is unreachable. `hash` is the hash of the characters, or 0 if it has not been computed.
    pub struct Extern { owner: Frozen<Box<dyn External>>, hash: u64 }
}

/// The most characters that a flat string object can have. Its word for the number of characters also holds the hash. See the [module docs](self).
pub const FLAT_MAX: usize = (1 << 31) - 1;

/// The bits of a flat string's `chars` word that hold the number of characters.
const COUNT: u64 = FLAT_MAX as u64;
/// The bit of a flat string's `chars` word that is set while the string is interned.
const INTERNED: u64 = 1 << 31;
/// The number of bits that the hash in a flat string's `chars` word is shifted up by.
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
    /// A flat string object and an external string keep the hash, so it is computed from their characters once. A string in the value word is hashed in a few steps each time. A rope is hashed from its pieces each time, without being flattened.
    #[inline]
    pub fn hash(&self, string: Str<'gc>) -> Result<u32, Error> {
        let mc = self.mc;
        let kept = match Text::of(string.0) {
            Some(Text::Str8(flat)) => flat.chars(mc) >> HASH_SHIFT,
            Some(Text::Str16(flat)) => flat.chars(mc) >> HASH_SHIFT,
            Some(Text::Str32(flat)) => flat.chars(mc) >> HASH_SHIFT,
            Some(Text::Extern(external)) => external.hash(mc),
            _ => 0,
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
            Some(Text::Extern(external)) => external.set_hash(mc, hash),
            _ => {}
        }
        Ok(hash as u32)
    }

    /// Returns the interned string with the characters of `string`. A flat string is interned already, so this returns it. A rope is flattened, and its flat copy is returned. See the [module docs](self).
    pub fn intern(&self, string: Str<'gc>) -> Result<Str<'gc>, Error> {
        match Text::of(string.0) {
            Some(Text::Str8(flat)) => self.intern_flat(flat, string),
            Some(Text::Str16(flat)) => self.intern_flat(flat, string),
            Some(Text::Str32(flat)) => self.intern_flat(flat, string),
            Some(Text::Rope(rope)) => {
                let flat = rope.flat(self.mc);
                if flat != Value::FALSE {
                    return Ok(Str(flat));
                }
                // The flat copy is interned when it is made, and the rope keeps it.
                flatten(self, string)
            }
            // A string in the value word is its own interned string. An external string is not interned yet.
            Some(Text::Extern(_)) | None => Ok(string),
        }
    }

    /// Returns the interned string with the characters of `string`, or `None` if no such string is interned. Nothing is registered, and a rope is not flattened.
    pub fn interned(&self, string: Str<'gc>) -> Result<Option<Str<'gc>>, Error> {
        if let Some(known) = self.known(string) {
            return Ok(Some(known));
        }
        // An interned string with these characters has units of the same width, so one table can hold it.
        let hash = self.hash(string)?;
        match width(self, string) {
            Width::One => self.twin::<Str8>(hash, string),
            Width::Two => self.twin::<Str16>(hash, string),
            Width::Four => self.twin::<Str32>(hash, string),
        }
    }

    /// Returns whether `string` is an interned string: a string in the value word, or a flat string object that [`Strings::intern`] has registered.
    #[inline]
    pub fn is_interned(&self, string: Str<'gc>) -> bool {
        let mc = self.mc;
        match Text::of(string.0) {
            Some(Text::Str8(flat)) => flat.chars(mc) & INTERNED != 0,
            Some(Text::Str16(flat)) => flat.chars(mc) & INTERNED != 0,
            Some(Text::Str32(flat)) => flat.chars(mc) & INTERNED != 0,
            Some(Text::Rope(_) | Text::Extern(_)) => false,
            None => true,
        }
    }

    /// Makes the flat string object `flat`, which is `string`, the interned string of its characters, unless another string is that already. Returns the interned string.
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
        let head = symbols.strings(mc, <Gc<'gc, T> as Flat<'gc>>::WIDTH);
        let mut probe = Probe::<T>::new(mc, head, hash);
        for candidate in probe.by_ref() {
            let candidate = Str(Value::object(mc, candidate));
            if same_chars(self, candidate, string)? {
                return Ok(candidate);
            }
        }
        self.insert(symbols, head, &probe, flat)?;
        flat.set_count(mc, flat.count(mc) | INTERNED);
        Ok(string)
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
        let head = symbols.strings(mc, width);
        let mut probe = Probe::<T>::new(mc, head, hash);
        for candidate in probe.by_ref() {
            // Two strings of one width with the same number of characters and the same words have the same characters.
            if candidate.count(mc) & COUNT == len as u64 && candidate.words(mc).iter().zip(built).all(|(held, new)| held.get() == new.get()) {
                return Ok(Str(Value::object(mc, candidate)));
            }
        }
        let object = mc.alloc_zeroed::<T, 1>([len as u64 | INTERNED | u64::from(hash) << HASH_SHIFT], built.len())?;
        for (word, new) in object.words(mc).iter().zip(built) {
            word.set(new.get());
        }
        self.insert(symbols, head, &probe, object)?;
        Ok(Str(Value::object(mc, object)))
    }

    /// Puts `object` into the intern table `head`, in the slot where `probe` ended. `probe` has found no string with the characters of `object`. The table and its array are made if they do not exist, and the array is made anew if it is too full.
    fn insert<T: Object>(&self, symbols: Symbols<'gc>, head: Option<Gc<'gc, Interns>>, probe: &Probe<'gc, T>, object: Gc<'gc, T>) -> Result<(), Error>
    where
        Gc<'gc, T>: Flat<'gc>,
    {
        let mc = self.mc;
        let head = match head {
            Some(head) => head,
            None => {
                let head = Interns::new(mc, Value::FALSE, 0)?;
                symbols.set_strings(mc, <Gc<'gc, T> as Flat<'gc>>::WIDTH, head);
                head
            }
        };
        let used = head.used(mc) as usize;
        // The slot of a string that has died is taken as it is. A slot that was never used is taken while the table stays at most three quarters used.
        if let (Some(slots), Some(index)) = (probe.slots, probe.free)
            && (!probe.fresh || (used + 1) * 4 <= slots.len() * 3)
        {
            slots.set(mc, index, (Some(object), probe.hash));
            if probe.fresh {
                head.set_used(mc, used as u64 + 1);
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
        let array = mc.alloc_items::<WeakSlots<T>, 0>([], len, Value::from_bits(0))?;
        let slots = array.item_slots::<slot::Tagged<T>>(mc);
        if let Some(old) = probe.slots {
            for index in 0..old.len() {
                if let (Some(held), hash) = old.get(index) {
                    place(mc, slots, hash, held);
                }
            }
        }
        place(mc, slots, probe.hash, object);
        head.set_array(mc, Value::object(mc, array));
        head.set_used(mc, living as u64 + 1);
        Ok(())
    }

    /// Returns the interned string of unit type `T` with the characters of `string`, if there is one. `hash` is the hash of `string`.
    fn twin<T: Object>(&self, hash: u32, string: Str<'gc>) -> Result<Option<Str<'gc>>, Error>
    where
        Gc<'gc, T>: Flat<'gc>,
    {
        let mc = self.mc;
        let head = Symbols::of_arena(mc)?.strings(mc, <Gc<'gc, T> as Flat<'gc>>::WIDTH);
        for candidate in Probe::<T>::new(mc, head, hash) {
            let candidate = Str(Value::object(mc, candidate));
            if same_chars(self, candidate, string)? {
                return Ok(Some(candidate));
            }
        }
        Ok(None)
    }

    /// Returns whether `string` is a flat string object in the arena, and not a string in the value word, a rope or an external string.
    pub(crate) fn is_object(&self, string: Str<'gc>) -> bool {
        matches!(Text::of(string.0), Some(Text::Str8(_) | Text::Str16(_) | Text::Str32(_)))
    }

    /// Returns the number of interned string objects, for tests.
    #[cfg(test)]
    fn interned_count(&self) -> usize {
        fn living<'gc, T: Object>(mc: &Mutation<'gc>, head: Option<Gc<'gc, Interns>>) -> usize {
            let Some(slots) = Probe::<T>::new(mc, head, 1).slots else { return 0 };
            (0..slots.len()).filter(|&index| slots.get(index).0.is_some()).count()
        }
        let mc = self.mc;
        let symbols = Symbols::of_arena(mc).expect("an intern table");
        living::<Str8>(mc, symbols.strings(mc, Width::One)) + living::<Str16>(mc, symbols.strings(mc, Width::Two)) + living::<Str32>(mc, symbols.strings(mc, Width::Four))
    }
}

/// A search of an intern table for the strings with one hash. It yields each interned string with that hash, in the order of the slots. Once it has ended, `free` is the slot that a new string with the hash can take, if the search passed one.
struct Probe<'gc, T: Object> {
    /// The slots of the table, or `None` if the table has no array yet.
    slots: Option<Slots<'gc, slot::Tagged<T>>>,
    hash: u32,
    /// The next slot to look at, and the number of slots that are left to look at.
    at: usize,
    left: usize,
    free: Option<usize>,
    /// Whether `free` is a slot that was never used. Taking such a slot makes the table fuller. Taking the slot of a string that has died does not.
    fresh: bool,
}

impl<'gc, T: Object> Probe<'gc, T> {
    fn new(mc: &Mutation<'gc>, head: Option<Gc<'gc, Interns>>, hash: u32) -> Self {
        let slots = head.and_then(|head| head.array(mc).downcast::<WeakSlots<T>>(mc)).map(|array| array.item_slots::<slot::Tagged<T>>(mc));
        let len = slots.map_or(0, |slots| slots.len());
        Self { slots, hash, at: hash as usize & len.wrapping_sub(1), left: len, free: None, fresh: false }
    }
}

impl<'gc, T: Object> Iterator for Probe<'gc, T> {
    type Item = Gc<'gc, T>;

    fn next(&mut self) -> Option<Gc<'gc, T>> {
        let slots = self.slots?;
        let mask = slots.len().wrapping_sub(1);
        while self.left > 0 {
            let index = self.at;
            self.at = (index + 1) & mask;
            self.left -= 1;
            match slots.get(index) {
                (Some(held), hash) if hash == self.hash => return Some(held),
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
fn place<'gc, T: Object>(mc: &Mutation<'gc>, slots: Slots<'gc, slot::Tagged<T>>, hash: u32, object: Gc<'gc, T>) {
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
}

impl<'gc> Strings<'_, 'gc> {
    /// Returns the view of a rope or an external string. It is kept out of line so that the views of flat strings inline.
    #[inline(never)]
    fn view_rest(&self, string: Str<'gc>) -> StrView<'_, Str<'gc>> {
        let mc = self.mc;
        match Text::of(string.0) {
            Some(Text::Rope(rope)) => {
                // A rope that has been flattened is read as its flat copy. It has let go of its halves.
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
            // A rope that has been flattened stands for its flat copy, which is interned.
            Some(Text::Rope(rope)) => {
                let flat = rope.flat(mc);
                (flat != Value::FALSE).then_some(Str(flat))
            }
            Some(Text::Extern(_)) => None,
            None => Some(string),
        }
    }

    fn canonical(&self, string: Str<'gc>) -> Result<Option<Str<'gc>>, Error> {
        if self.is_external(string) {
            return Ok(None);
        }
        self.intern(string).map(Some)
    }

    fn rope(&self, left: Str<'gc>, right: Str<'gc>, info: Info) -> Result<Str<'gc>, Error> {
        let rope = Rope::new(self.mc, left.0, right.0, info.to_bits(), Value::FALSE, 0)?;
        Ok(Str(Value::object(self.mc, rope)))
    }

    fn flattened(&self, rope: Str<'gc>, flat: Str<'gc>) {
        if let Some(Text::Rope(object)) = Text::of(rope.0) {
            // The rope is read as its flat copy from now on, so it lets go of its halves. The characters are then held once.
            object.set_flat(self.mc, flat.0);
            object.set_left(self.mc, Value::FALSE);
            object.set_right(self.mc, Value::FALSE);
        }
    }

    fn count_read(&self, rope: Str<'gc>) -> u64 {
        let Some(Text::Rope(object)) = Text::of(rope.0) else { return 0 };
        let reads = object.reads(self.mc) + 1;
        object.set_reads(self.mc, reads);
        reads
    }
}
