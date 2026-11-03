//! Strings in the arena, for `ragwort-string`: flat strings as [`Str8`], [`Str16`] or [`Str32`]
//! objects, by their widest character, with the characters packed into their items; ropes as [`Rope`]
//! objects; and flat strings whose characters the program running the arena owns, as
//! [`Extern`] objects.

pub use ragwort_string::*;

pub use crate::Error;
use crate::{Mutation, Value};

#[cfg(test)]
#[path = "tests/strings.rs"]
mod tests;

crate::objects! {
    /// Every kind of string.
    pub kind Text after crate::table::Containers;

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

    /// A string of characters kept outside the arena, such as an [`ExternalText`].
    pub fn external(&self, chars: impl External) -> Result<Str<'gc>, Error> {
        let units = chars.units();
        check_external(units)?;
        let bytes = units.len() * units.width().bytes();
        if bytes < COPY_EXTERNAL {
            return self.flat(units.width(), units.len(), |mut u| u.copy_from(units));
        }
        let owner: Box<dyn External> = Box::new(chars);
        let external = Extern::new(self.mc, self.mc.frozen_owning(owner, bytes)?)?;
        Ok(Str(Value::object(self.mc, external)))
    }

    pub fn is_external(&self, s: Str<'gc>) -> bool {
        matches!(Text::of(s.0), Some(Text::Extern(_)))
    }

    /// `v` as a string, if it is one: read from the type number `v` carries.
    #[inline]
    pub fn string(&self, v: Value<'gc>) -> Option<Str<'gc>> {
        Text::of(v).map(|_| Str(v))
    }
}

impl<'gc> Strings<'_, 'gc> {
    /// Ropes and externals, kept out of line so flat strings' views inline.
    #[inline(never)]
    fn view_rest(&self, s: Str<'gc>) -> StrView<'_, Str<'gc>> {
        let mc = self.mc;
        match Text::of(s.0) {
            Some(Text::Rope(r)) => {
                let flat = r.flat(mc);
                let flat = (flat != Value::FALSE).then_some(Str(flat));
                StrView::Rope { left: Str(r.left(mc)), right: Str(r.right(mc)), info: Info::from_bits(r.info(mc)), flat }
            }
            Some(Text::Extern(x)) => StrView::Flat(x.owner(mc).map_or(Units::One(&[]), |o| o.units())),
            _ => panic!("strings are flat, ropes or external"),
        }
    }
}

impl<'gc> Host for Strings<'_, 'gc> {
    type Str = Str<'gc>;
    type Error = Error;

    #[inline(always)]
    fn view(&self, s: Str<'gc>) -> StrView<'_, Str<'gc>> {
        let mc = self.mc;
        match Text::of(s.0) {
            Some(Text::Str8(x)) => StrView::Flat(Units::Packed(Packed::new(x.items(mc).words(), x.chars(mc) as usize, Width::One))),
            Some(Text::Str16(x)) => StrView::Flat(Units::Packed(Packed::new(x.items(mc).words(), x.chars(mc) as usize, Width::Two))),
            Some(Text::Str32(x)) => StrView::Flat(Units::Packed(Packed::new(x.items(mc).words(), x.chars(mc) as usize, Width::Four))),
            _ => self.view_rest(s),
        }
    }

    fn flat(&self, width: Width, len: usize, init: impl FnOnce(UnitsMut<'_>)) -> Result<Str<'gc>, Error> {
        let mc = self.mc;
        let (chars, words) = (len as u64, len.div_ceil(width.per_word()));
        let (v, items) = match width {
            Width::One => {
                let x = mc.alloc_zeroed::<Str8, 1>([chars], words)?;
                (Value::object(mc, x), x.items(mc))
            }
            Width::Two => {
                let x = mc.alloc_zeroed::<Str16, 1>([chars], words)?;
                (Value::object(mc, x), x.items(mc))
            }
            Width::Four => {
                let x = mc.alloc_zeroed::<Str32, 1>([chars], words)?;
                (Value::object(mc, x), x.items(mc))
            }
        };
        init(UnitsMut::Packed(PackedMut::new(items.words(), len, width)));
        Ok(Str(v))
    }

    fn rope(&self, left: Str<'gc>, right: Str<'gc>, info: Info) -> Result<Str<'gc>, Error> {
        let rope = Rope::new(self.mc, left.0, right.0, info.to_bits(), Value::FALSE, 0)?;
        Ok(Str(Value::object(self.mc, rope)))
    }

    fn flattened(&self, rope: Str<'gc>, flat: Str<'gc>) {
        if let Some(Text::Rope(r)) = Text::of(rope.0) {
            r.set_flat(self.mc, flat.0);
        }
    }

    fn count_read(&self, rope: Str<'gc>) -> u64 {
        let Some(Text::Rope(r)) = Text::of(rope.0) else { return 0 };
        let reads = r.reads(self.mc) + 1;
        r.set_reads(self.mc, reads);
        reads
    }
}
