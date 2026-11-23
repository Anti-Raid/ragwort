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
//! The hash is seeded with the arena's seed, so it cannot be predicted from outside. An arena has
//! one seed for its whole life, and an image is loaded only into an arena with the image's seed,
//! so a hash that is kept in a string stays right.

pub use ragwort_string::*;

pub use crate::gc::Error;
use crate::gc::{INLINE_STRING, Mutation, TAG, Value};

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
    /// `reads` counts the reads of the rope by character index.
    pub struct Rope { left: Value, right: Value, info: u64, flat: Value, reads: u64 }
    /// A flat string whose characters are stored outside the arena, in `owner`. `owner` is dropped once the string is unreachable. `hash` is the hash of the characters, or 0 if it has not been computed.
    pub struct Extern { owner: Frozen<Box<dyn External>>, hash: u64 }
}

/// The most characters that a flat string object can have. Its word for the number of characters also holds the hash. See the [module docs](self).
pub const FLAT_MAX: usize = (1 << 31) - 1;

/// The bits of a flat string's `chars` word that hold the number of characters.
const COUNT: u64 = FLAT_MAX as u64;
/// The number of bits that the hash in a flat string's `chars` word is shifted up by.
const HASH_SHIFT: u32 = 32;

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
        let seed = crate::symbol::Symbols::of_arena(mc)?.seed(mc);
        // 0 means that no hash is kept, so a hash of 0 becomes 1.
        let hash = u64::from((ragwort_string::hash(self, string, seed)? as u32).max(1));
        match Text::of(string.0) {
            Some(Text::Str8(flat)) => flat.set_chars(mc, flat.chars(mc) & COUNT | hash << HASH_SHIFT),
            Some(Text::Str16(flat)) => flat.set_chars(mc, flat.chars(mc) & COUNT | hash << HASH_SHIFT),
            Some(Text::Str32(flat)) => flat.set_chars(mc, flat.chars(mc) & COUNT | hash << HASH_SHIFT),
            Some(Text::Extern(external)) => external.set_hash(mc, hash),
            _ => {}
        }
        Ok(hash as u32)
    }
}

impl<'gc> Strings<'_, 'gc> {
    /// Returns the view of a rope or an external string. It is kept out of line so that the views of flat strings inline.
    #[inline(never)]
    fn view_rest(&self, string: Str<'gc>) -> StrView<'_, Str<'gc>> {
        let mc = self.mc;
        match Text::of(string.0) {
            Some(Text::Rope(rope)) => {
                let flat = rope.flat(mc);
                let flat = (flat != Value::FALSE).then_some(Str(flat));
                StrView::Rope { left: Str(rope.left(mc)), right: Str(rope.right(mc)), info: Info::from_bits(rope.info(mc)), flat }
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
        let (value, items) = match width {
            Width::One => {
                let object = mc.alloc_zeroed::<Str8, 1>([chars], words)?;
                (Value::object(mc, object), object.items(mc))
            }
            Width::Two => {
                let object = mc.alloc_zeroed::<Str16, 1>([chars], words)?;
                (Value::object(mc, object), object.items(mc))
            }
            Width::Four => {
                let object = mc.alloc_zeroed::<Str32, 1>([chars], words)?;
                (Value::object(mc, object), object.items(mc))
            }
        };
        init(UnitsMut::Packed(PackedMut::new(items.words(), len, width)));
        Ok(Str(value))
    }

    fn rope(&self, left: Str<'gc>, right: Str<'gc>, info: Info) -> Result<Str<'gc>, Error> {
        let rope = Rope::new(self.mc, left.0, right.0, info.to_bits(), Value::FALSE, 0)?;
        Ok(Str(Value::object(self.mc, rope)))
    }

    fn flattened(&self, rope: Str<'gc>, flat: Str<'gc>) {
        if let Some(Text::Rope(object)) = Text::of(rope.0) {
            object.set_flat(self.mc, flat.0);
        }
    }

    fn count_read(&self, rope: Str<'gc>) -> u64 {
        let Some(Text::Rope(object)) = Text::of(rope.0) else { return 0 };
        let reads = object.reads(self.mc) + 1;
        object.set_reads(self.mc, reads);
        reads
    }
}
