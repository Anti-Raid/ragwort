//! Strings in the arena, for `ragwort-string`: flat strings of up to [`INLINE_CHARS`] Latin-1
//! characters in the value word; longer ones as [`Str8`], [`Str16`] or [`Str32`] objects, by
//! their widest character, with the characters packed into their items; ropes as [`Rope`]
//! objects; and flat strings whose characters the program running the arena owns, as
//! [`Extern`] objects.

pub use ragwort_string::*;

pub use crate::gc::Error;
use crate::gc::{INLINE_STRING, Mutation, TAG, Value};

#[cfg(test)]
#[path = "tests/strings.rs"]
mod tests;

crate::gc::objects! {
    /// Every kind of string.
    pub kind Text after crate::gc::table::Containers;

    /// A flat string of `chars` characters up to U+00FF, eight to an item.
    pub struct Str8 { chars: u64 } items u64
    /// A flat string of characters up to U+FFFF, one above U+00FF at least, four to an item.
    pub struct Str16 { chars: u64 } items u64
    /// A flat string with a character above U+FFFF, two to an item.
    pub struct Str32 { chars: u64 } items u64
    /// Two nonempty strings, one after the other, and what `Info` says of them, packed. Once
    /// flattened it keeps the flat copy, `#f` until then, and counts reads by position.
    pub struct Rope { left: Value, right: Value, info: u64, flat: Value, reads: u64 }
    /// A flat string whose characters live outside the arena, dropped once nothing reaches it.
    pub struct Extern { owner: Frozen<Box<dyn External>> }
}

/// Shorter externals are copied: keeping them outside costs more than their characters.
const COPY_EXTERNAL: usize = 64;

/// Strings of up to this many Latin-1 characters live in the value word, so making one
/// allocates nothing, and equal ones are the same value.
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

    /// A string of characters kept outside the arena, such as an [`ExternalText`], which must
    /// never change, in number or in value, as no string's do.
    pub fn external(&self, chars: impl External) -> Result<Str<'gc>, Error> {
        let units = chars.units();
        check_external(units)?;
        let bytes = units.len() * units.width().bytes();
        if bytes < COPY_EXTERNAL {
            return self.flat(units.width(), units.len(), |mut target| target.copy_from(units));
        }
        let owner: Box<dyn External> = Box::new(chars);
        let external = Extern::new(self.mc, self.mc.frozen_owning(owner, bytes)?)?;
        Ok(Str(Value::object(self.mc, external)))
    }

    pub fn is_external(&self, string: Str<'gc>) -> bool {
        matches!(Text::of(string.0), Some(Text::Extern(_)))
    }

    /// `value` as a string, if it is one: read from the type number `value` carries.
    #[inline]
    pub fn string(&self, value: Value<'gc>) -> Option<Str<'gc>> {
        (is_inline(value) || Text::of(value).is_some()).then_some(Str(value))
    }
}

impl<'gc> Strings<'_, 'gc> {
    /// Ropes and externals, kept out of line so flat strings' views inline.
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
            Some(Text::Str8(flat)) => StrView::Flat(Units::Packed(Packed::new(flat.items(mc).words(), flat.chars(mc) as usize, Width::One))),
            Some(Text::Str16(flat)) => StrView::Flat(Units::Packed(Packed::new(flat.items(mc).words(), flat.chars(mc) as usize, Width::Two))),
            Some(Text::Str32(flat)) => StrView::Flat(Units::Packed(Packed::new(flat.items(mc).words(), flat.chars(mc) as usize, Width::Four))),
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
