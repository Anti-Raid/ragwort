//! Strings in the arena: flat strings as [`Str8`], [`Str16`] or [`Str32`] objects, by their
//! widest character, ropes as [`Rope`] objects, and flat strings whose characters the program
//! running the arena keeps as [`Extern`] objects.

use ragwort_gc::{Gc, HostRef, Lock, Mutation, OutOfMemory, Plain, Trace, TypeTag, Value};
pub use ragwort_string::*;

pub use crate::Error;

/// A flat string of characters up to U+00FF.
#[derive(Trace, Plain)]
#[gc(items = u8)]
pub struct Str8;

/// A flat string of characters up to U+FFFF, one above U+00FF at least.
#[derive(Trace, Plain)]
#[gc(items = u16)]
pub struct Str16;

/// A flat string with a character above U+FFFF.
#[derive(Trace, Plain)]
#[gc(items = u32)]
pub struct Str32;

/// Two nonempty [`Str`]s, one after the other, and what [`Info`] says of them, packed. Once
/// flattened, it keeps the flat copy, and counts reads by position until then.
#[derive(Trace, Plain)]
pub struct Rope<'gc> {
    left: Value<'gc>,
    right: Value<'gc>,
    info: u64,
    /// `#f` until flattened.
    flat: Lock<Value<'gc>>,
    reads: Lock<u64>,
}

/// A flat string whose characters live outside the arena, with an owner that's dropped once
/// nothing reaches the string.
#[derive(Trace, Plain)]
pub struct Extern<'gc> {
    chars: HostRef<'gc, Box<dyn External>>,
}

/// Shorter externals are copied: keeping them outside costs more than their characters.
const COPY_EXTERNAL: usize = 64;

/// A flat string, a [`Rope`] or an [`Extern`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(transparent)]
pub struct Str<'gc>(Value<'gc>);

impl<'gc> Str<'gc> {
    pub fn value(self) -> Value<'gc> {
        self.0
    }
}

/// The arena as a [`Host`] for `ragwort-string`.
#[derive(Clone, Copy)]
pub struct Strings<'a, 'gc> {
    mc: &'a Mutation<'gc>,
    one: TypeTag<'gc, Str8>,
    two: TypeTag<'gc, Str16>,
    four: TypeTag<'gc, Str32>,
    rope: TypeTag<'gc, Rope<'gc>>,
    external: TypeTag<'gc, Extern<'gc>>,
}

impl<'a, 'gc> Strings<'a, 'gc> {
    pub fn new(mc: &'a Mutation<'gc>) -> Result<Self, OutOfMemory> {
        Ok(Self {
            mc,
            one: mc.inline_type_tag()?,
            two: mc.inline_type_tag()?,
            four: mc.inline_type_tag()?,
            rope: mc.type_tag()?,
            external: mc.type_tag()?,
        })
    }

    /// A string of characters kept outside the arena, such as an [`ExternalText`].
    pub fn external(&self, chars: impl External) -> Result<Str<'gc>, Error> {
        let units = chars.units();
        check_external(units)?;
        if units.len() * units.width().bytes() < COPY_EXTERNAL {
            return self.flat(units.width(), units.len(), |mut u| u.copy_from(units));
        }
        let chars: Box<dyn External> = Box::new(chars);
        let external = self.mc.alloc(Extern { chars: self.mc.host(chars)? })?;
        Ok(Str(Value::object(self.mc, external)))
    }

    fn rope_of(&self, s: Str<'gc>) -> Gc<'gc, Rope<'gc>> {
        s.0.downcast_tag(self.mc, self.rope).expect("a rope")
    }

    /// Whether `s` is an [`Extern`].
    pub fn is_external(&self, s: Str<'gc>) -> bool {
        s.0.downcast_tag(self.mc, self.external).is_some()
    }

    pub fn string(&self, v: Value<'gc>) -> Option<Str<'gc>> {
        let is = v.downcast_tag(self.mc, self.one).is_some()
            || v.downcast_tag(self.mc, self.rope).is_some()
            || v.downcast_tag(self.mc, self.two).is_some()
            || v.downcast_tag(self.mc, self.four).is_some()
            || v.downcast_tag(self.mc, self.external).is_some();
        is.then_some(Str(v))
    }
}

impl<'gc> Host for Strings<'_, 'gc> {
    type Str = Str<'gc>;
    type Error = Error;

    #[inline]
    fn view(&self, s: Str<'gc>) -> StrView<'_, Str<'gc>> {
        if let Some(x) = s.0.downcast_tag(self.mc, self.one) {
            return StrView::Flat(Units::One(Gc::items(x)));
        }
        if let Some(r) = s.0.downcast_tag(self.mc, self.rope) {
            let flat = r.flat.get();
            let flat = (flat != Value::FALSE).then_some(Str(flat));
            return StrView::Rope { left: Str(r.left), right: Str(r.right), info: Info::from_bits(r.info), flat };
        }
        if let Some(x) = s.0.downcast_tag(self.mc, self.two) {
            return StrView::Flat(Units::Two(Gc::items(x)));
        }
        if let Some(x) = s.0.downcast_tag(self.mc, self.four) {
            return StrView::Flat(Units::Four(Gc::items(x)));
        }
        let x = s.0.downcast_tag(self.mc, self.external).expect("strings are flat, ropes or external");
        StrView::Flat(x.chars.get(self.mc).expect("reachable, so alive").units())
    }

    fn flat(&self, width: Width, len: usize, init: impl FnOnce(UnitsMut<'_>)) -> Result<Str<'gc>, Error> {
        let v = match width {
            Width::One => Value::object(self.mc, self.mc.alloc_inline_with(Str8, len, 0, |u| init_all(init, UnitsMut::One(u)))?),
            Width::Two => Value::object(self.mc, self.mc.alloc_inline_with(Str16, len, 0, |u| init_all(init, UnitsMut::Two(u)))?),
            Width::Four => Value::object(self.mc, self.mc.alloc_inline_with(Str32, len, 0, |u| init_all(init, UnitsMut::Four(u)))?),
        };
        Ok(Str(v))
    }

    fn rope(&self, left: Str<'gc>, right: Str<'gc>, info: Info) -> Result<Str<'gc>, Error> {
        let rope = Rope { left: left.0, right: right.0, info: info.to_bits(), flat: Lock::new(Value::FALSE), reads: Lock::new(0) };
        Ok(Str(Value::object(self.mc, self.mc.alloc(rope)?)))
    }

    fn flattened(&self, rope: Str<'gc>, flat: Str<'gc>) {
        self.rope_of(rope).flat.set(self.mc, flat.0);
    }

    fn count_read(&self, rope: Str<'gc>) -> u64 {
        let reads = &self.rope_of(rope).reads;
        reads.set(self.mc, reads.get() + 1);
        reads.get()
    }
}

fn init_all(init: impl FnOnce(UnitsMut<'_>), units: UnitsMut<'_>) -> usize {
    let len = units.len();
    init(units);
    len
}

#[cfg(test)]
mod tests;
