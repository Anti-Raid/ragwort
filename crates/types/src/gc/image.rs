//! An image: everything some values reach, as bytes, which another arena can be given.
//!
//! [`save`] writes the objects that `roots` reach, and [`load`] makes them again in an arena
//! and gives the roots back. What they made is theirs alone: the two arenas share nothing.
//!
//! ```text
//! let bytes = arena.mutate(|mc| image::save(mc, STAMP, &[library], &kinds))?;
//! // Later, or in another process:
//! let roots = other.mutate(|mc| image::load(mc, STAMP, &bytes, &descs, &kinds, &hosts))?;
//! ```
//!
//! # What's saved
//!
//! - An object is saved as its type's number, how many items it has, and its words. A word
//!   that refers to an object refers to it by its place in the image, so the objects can be
//!   anywhere in the arena they're loaded into.
//! - A symbol or keyword is saved as its name, and loaded as the arena's symbol of that name.
//! - A frozen value is saved by the [`Kind`] that knows its type, as [`Wire`] writes it.
//!
//! # What can't be
//!
//! [`save`] fails if a root reaches any of these:
//!
//! - A value the host owns: a `Host` field's, or a frozen one of no [`Kind`] given.
//! - An object of a type with no fixed number, or one not among the `descs` [`load`] is given.
//!   A stack's segment is one, so nothing that's running can be saved.
//!
//! # Trust
//!
//! An image is read as what the same build of the same program wrote. `stamp` says which
//! build that is, and [`load`] refuses another's, and bytes that have changed since they
//! were written. It doesn't check that each object's words suit its type: an image made up to
//! look right loads, and reading what it made can then panic, as reading any forged reference
//! can.

#[cfg(test)]
#[path = "tests/image.rs"]
mod tests;

use std::any::Any;
use std::collections::HashMap;

use super::frozen::FROZEN_COST;
use super::{Desc, Heap, Items, Mutation, OBJECT, Object, OutOfMemory, Phase, Role, TAG, TYPE_BITS, Value, mask};
use crate::objects::{Interned, Sym};
use crate::string::{Strings, chars};
use crate::symbol::{Keyword, Symbol, Symbols};
use crate::wire::{Malformed, Reader, Wire, Writer, mix, shape_of};

const MAGIC: &[u8; 8] = b"ragwort\x01";

/// How an object is saved.
const PLAIN: u8 = 0;
const SYMBOL: u8 = 1;
const KEYWORD: u8 = 2;
const SYMBOLS: u8 = 3;

/// A kind of frozen value that can be saved.
#[derive(Clone, Copy)]
pub struct Kind {
    /// Writes the value, if it's of this kind.
    pub save: fn(&dyn Any, &mut Writer) -> bool,
    /// Reads a value and freezes it, charged `cost` in all, and gives the word a field holds
    /// it by.
    pub load: for<'gc> fn(&Mutation<'gc>, &mut Reader<'_>, usize) -> Result<u64, LoadError>,
    /// A number that changes when the kind's form does.
    pub shape: u64,
}

impl Kind {
    /// The frozen values of type `T`, saved as [`Wire`] writes them.
    pub const fn of<T: Wire + Any>() -> Self {
        Self { save: save_as::<T>, load: load_as::<T>, shape: T::SHAPE }
    }
}

fn save_as<T: Wire + Any>(value: &dyn Any, out: &mut Writer) -> bool {
    match value.downcast_ref::<T>() {
        Some(value) => {
            value.write(out);
            true
        }
        None => false,
    }
}

fn load_as<'gc, T: Wire + Any>(mc: &Mutation<'gc>, input: &mut Reader<'_>, cost: usize) -> Result<u64, LoadError> {
    let value = T::read(input)?;
    Ok(freeze(mc, value, cost)?)
}

/// Freezes `value`, charged `cost` in all, as the value it's a copy of was. Gives the word a
/// field holds it by.
pub fn freeze<'gc, T: Any>(mc: &Mutation<'gc>, value: T, cost: usize) -> Result<u64, OutOfMemory> {
    let owned = cost.saturating_sub(size_of::<T>() + FROZEN_COST);
    Ok(mc.frozen_owning(value, owned)?.to_word())
}

/// The kinds of frozen value this crate's own objects hold.
pub const KINDS: [Kind; 2] = [Kind::of::<Box<[u8]>>(), Kind::of::<Box<[u32]>>()];

/// How the collector sees each type this crate's own objects have, but a stack's segments.
pub fn descs() -> Vec<&'static Desc> {
    let groups = [super::table::Containers::DESCS, crate::string::Text::DESCS, crate::num::Numbers::DESCS, crate::objects::Data::DESCS];
    std::iter::once(&super::Boxed::DESC).chain(groups.into_iter().flatten().copied()).collect()
}

/// A number for `stamp` that changes when the form of anything in `descs` or `kinds` does.
pub fn shape(descs: &[&'static Desc], kinds: &[Kind]) -> u64 {
    let mut shape = shape_of("image 1");
    for desc in descs {
        let items = match desc.items {
            Items::None => 0,
            Items::Values => 1,
            Items::Words => 2,
            Items::Ephemerons => 3,
            Items::Members => 4,
            Items::Weaks => 5,
        };
        let words = [u64::from(desc.number.unwrap_or(u16::MAX)), u64::from(desc.fields), desc.values, desc.members, desc.hosts, desc.weaks, desc.frozen, desc.ephemerons, items];
        shape = words.into_iter().fold(shape, mix);
    }
    kinds.iter().fold(shape, |shape, kind| mix(shape, kind.shape))
}

/// Why some values can't be saved.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SaveError {
    /// They reach a value the host owns, held by an object of the type with this number.
    Host(u16),
    /// They reach a frozen value of no kind given, held by an object of the type with this
    /// number.
    Frozen(u16),
    /// They reach an object of a type with no fixed number.
    Unnumbered,
    /// A collection is moving objects.
    Busy,
}

/// Why bytes can't be loaded.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LoadError {
    /// They aren't an image, or have changed since they were written.
    Malformed,
    /// Another build wrote them.
    Stamp,
    /// The arena has symbols already, hashed another way than the image's.
    Symbols,
    /// A collection is under way.
    Busy,
    OutOfMemory,
}

impl From<Malformed> for LoadError {
    fn from(_: Malformed) -> Self {
        Self::Malformed
    }
}

impl From<OutOfMemory> for LoadError {
    fn from(_: OutOfMemory) -> Self {
        Self::OutOfMemory
    }
}

impl From<crate::Error> for LoadError {
    fn from(e: crate::Error) -> Self {
        match e {
            crate::Error::OutOfMemory => Self::OutOfMemory,
            // A string or a number that can't be made comes from bytes that no build wrote.
            crate::Error::Num(_) | crate::Error::Str(_) => Self::Malformed,
        }
    }
}

fn number_of<T: Object>() -> u64 {
    u64::from(T::DESC.number.expect("a type of this crate's has a number"))
}

/// What's reached so far, as it's being saved.
struct Saver<'k, 'gc> {
    mc: &'k Mutation<'gc>,
    heap: Heap<'gc>,
    kinds: &'k [Kind],
    /// Each object reached, by its index, with its place from one, and those places in order.
    places: HashMap<u32, u32>,
    order: Vec<u32>,
    /// Each frozen value reached, by its word, with its place from one.
    frozen: HashMap<u64, u32>,
    frozen_out: Writer,
}

impl<'gc> Saver<'_, 'gc> {
    fn place(&mut self, index: u32) -> u32 {
        let next = self.order.len() as u32 + 1;
        let place = *self.places.entry(index).or_insert(next);
        if place == next {
            self.order.push(index);
        }
        place
    }

    /// A value's word, with the place of the object it refers to for its index.
    fn value(&mut self, word: u64) -> u64 {
        if word & TAG != OBJECT {
            return word;
        }
        u64::from(self.place((word >> 32) as u32)) << 32 | word & 0xFFFF_FFFF
    }

    fn member(&mut self, word: u64) -> u32 {
        if word == 0 { 0 } else { self.place(word as u32) }
    }

    fn frozen(&mut self, word: u64, holder: u16) -> Result<u32, SaveError> {
        if word == 0 {
            return Ok(0);
        }
        if let Some(&place) = self.frozen.get(&word) {
            return Ok(place);
        }
        let (value, cost) = self.heap.m.frozen.any(word).ok_or(SaveError::Frozen(holder))?;
        let mut out = Writer::new();
        let kind = self.kinds.iter().position(|kind| (kind.save)(value, &mut out)).ok_or(SaveError::Frozen(holder))?;
        self.frozen_out.u16(kind as u16);
        self.frozen_out.u64(cost as u64);
        self.frozen_out.bytes(&out.finish());
        let place = self.frozen.len() as u32 + 1;
        self.frozen.insert(word, place);
        Ok(place)
    }

    /// Writes the words of the object at `at`, whose header is `header`.
    fn object(&mut self, at: usize, header: u64, desc: &Desc, out: &mut Writer) -> Result<(), SaveError> {
        let (words, ty) = (self.heap.words, (header & TYPE_BITS) as u16);
        for field in 0..desc.fields as usize {
            let word = words[mask(at + 1 + field)].get();
            match desc.role(field) {
                Some(Role::Word) => out.u64(word),
                // An ephemeron's value is one too.
                Some(Role::Value | Role::Ephemeron) | None => {
                    let word = self.value(word);
                    out.u64(word);
                }
                Some(Role::Member | Role::Weak) => {
                    let place = self.member(word);
                    out.u32(place);
                }
                Some(Role::Host) if word == 0 => out.u32(0),
                Some(Role::Host) => return Err(SaveError::Host(ty)),
                Some(Role::Frozen) => {
                    let place = self.frozen(word, ty)?;
                    out.u32(place);
                }
            }
        }
        let items = at + 1 + desc.fields as usize;
        let len = if desc.items == Items::None { 0 } else { (header >> 32) as usize };
        for item in items..items + len {
            let word = words[mask(item)].get();
            match desc.items {
                Items::None => {}
                Items::Words => out.u64(word),
                Items::Values | Items::Ephemerons => {
                    let word = self.value(word);
                    out.u64(word);
                }
                Items::Members | Items::Weaks => {
                    let place = self.member(word);
                    out.u32(place);
                }
            }
        }
        Ok(())
    }

    /// Writes what the object in each place is, in `table`, and its words, in `words`, till
    /// every object reached is written.
    fn objects(&mut self, table: &mut Writer, words: &mut Writer) -> Result<(), SaveError> {
        let mut next = 0;
        while let Some(&index) = self.order.get(next) {
            next += 1;
            let at = index as usize;
            let header = self.heap.words[mask(at)].get();
            if header & super::FORWARDED != 0 {
                return Err(SaveError::Busy);
            }
            let ty = header & TYPE_BITS;
            let object = Value::from_bits(u64::from(index) << 32 | ty << 16 | OBJECT);
            if let Some(symbol) = Symbol::of(object) {
                table.u8(SYMBOL);
                let name: String = chars(&Strings::new(self.mc), symbol.name(self.mc)).collect();
                table.bytes(name.as_bytes());
            } else if let Some(keyword) = Keyword::of(object) {
                table.u8(KEYWORD);
                let symbol = self.value(keyword.symbol(self.mc).value(self.mc).to_bits());
                table.u32((symbol >> 32) as u32);
            } else if ty == number_of::<Interned>() {
                table.u8(SYMBOLS);
            } else {
                let desc = self.heap.desc(header).filter(|desc| desc.number.is_some()).ok_or(SaveError::Unnumbered)?;
                table.u8(PLAIN);
                table.u16(ty as u16);
                table.u32(if desc.items == Items::None { 0 } else { (header >> 32) as u32 });
                self.object(at, header, desc, words)?;
            }
        }
        Ok(())
    }
}

/// Everything `roots` reach, as bytes that [`load`] takes. `stamp` is the build's, which
/// `load` is to be given again: see [`shape`]. `kinds` are the kinds of frozen value there
/// can be, which `load` is to be given in the same order.
///
/// What's weakly held is saved as if it were held: collect first to leave out what's dead.
pub fn save<'gc>(mc: &Mutation<'gc>, stamp: u64, roots: &[Value<'gc>], kinds: &[Kind]) -> Result<Vec<u8>, SaveError> {
    let heap = mc.heap;
    let mut saver = Saver { mc, heap, kinds, places: HashMap::new(), order: Vec::new(), frozen: HashMap::new(), frozen_out: Writer::new() };
    let mut rooted = Writer::new();
    rooted.length(roots.len());
    for root in roots {
        let word = saver.value(root.to_bits());
        rooted.u64(word);
    }
    let (mut table, mut words) = (Writer::new(), Writer::new());
    saver.objects(&mut table, &mut words)?;
    let mut body = Writer::new();
    body.u64(Symbols::of(Value::from_bits(mc.interned().get())).map_or(0, |symbols| symbols.seed(mc)));
    body.u64(heap.m.evacuations.get());
    body.length(saver.frozen.len());
    body.bytes(&saver.frozen_out.finish());
    body.length(saver.order.len());
    body.bytes(&table.finish());
    body.bytes(&words.finish());
    body.bytes(&rooted.finish());
    let body = body.finish();
    let mut out = Writer::new();
    MAGIC.iter().for_each(|&byte| out.u8(byte));
    out.u64(stamp);
    out.u64(checksum(&body));
    let mut bytes = out.finish();
    bytes.extend(body);
    Ok(bytes)
}

fn checksum(bytes: &[u8]) -> u64 {
    let mut sum = 0xCBF2_9CE4_8422_2325u64;
    for chunk in bytes.chunks(8) {
        let mut word = [0; 8];
        word[..chunk.len()].copy_from_slice(chunk);
        sum = (sum ^ u64::from_le_bytes(word)).wrapping_mul(0x0000_0100_0000_01B3).rotate_left(29);
    }
    sum
}

/// What an image's objects are in the arena they're loaded into.
struct Loader<'gc> {
    heap: Heap<'gc>,
    /// The index of the object in each place, from one.
    indices: Vec<u32>,
    /// The word of the frozen value in each place, from one.
    frozen: Vec<u64>,
}

impl Loader<'_> {
    fn index(&self, place: u32) -> Result<u32, Malformed> {
        if place == 0 {
            return Ok(0);
        }
        self.indices.get(place as usize - 1).copied().ok_or(Malformed)
    }

    /// A value's word, with the index of the object in the place it names, and that object's
    /// type.
    fn value(&self, word: u64) -> Result<u64, Malformed> {
        if word & TAG != OBJECT {
            return Ok(word);
        }
        let index = self.index((word >> 32) as u32)?;
        if index == 0 {
            return Err(Malformed);
        }
        let ty = self.heap.words[mask(index as usize)].get() & TYPE_BITS;
        Ok(u64::from(index) << 32 | ty << 16 | OBJECT)
    }

    /// Reads the words of the object at `at`, which is of the type `desc` describes and has
    /// `len` items.
    fn object(&self, at: u32, desc: &Desc, len: usize, input: &mut Reader<'_>) -> Result<(), Malformed> {
        let (heap, start) = (self.heap, at as usize + 1);
        let mut field = 0;
        while field < desc.fields as usize {
            let slot = start + field;
            match desc.role(field) {
                Some(Role::Word) => heap.words[mask(slot)].set(input.u64()?),
                Some(Role::Value) | None => {
                    let word = self.value(input.u64()?)?;
                    heap.words[mask(slot)].set(word);
                    heap.barrier(slot, at, word);
                }
                Some(Role::Ephemeron) => {
                    let (key, value) = (self.value(input.u64()?)?, self.value(input.u64()?)?);
                    heap.set_ephemeron_at(slot, Value::from_bits(key), Value::from_bits(value));
                    field += 1;
                }
                Some(Role::Member) => {
                    let index = self.index(input.u32()?)?;
                    heap.words[mask(slot)].set(u64::from(index));
                    if index != 0 {
                        heap.barrier_ref(slot, at, index);
                    }
                }
                Some(Role::Weak) => {
                    heap.words[mask(slot)].set(u64::from(self.index(input.u32()?)?));
                    heap.dirty(slot);
                }
                Some(Role::Host) => {
                    if input.u32()? != 0 {
                        return Err(Malformed);
                    }
                }
                Some(Role::Frozen) => {
                    let place = input.u32()? as usize;
                    let word = if place == 0 { 0 } else { *self.frozen.get(place - 1).ok_or(Malformed)? };
                    heap.words[mask(slot)].set(word);
                }
            }
            field += 1;
        }
        let items = start + desc.fields as usize;
        let mut slot = items;
        while slot < items + len {
            match desc.items {
                Items::None => return Err(Malformed),
                Items::Words => heap.words[mask(slot)].set(input.u64()?),
                Items::Values => {
                    let word = self.value(input.u64()?)?;
                    heap.words[mask(slot)].set(word);
                    heap.barrier(slot, at, word);
                }
                Items::Ephemerons => {
                    if slot + 1 == items + len {
                        return Err(Malformed);
                    }
                    let (key, value) = (self.value(input.u64()?)?, self.value(input.u64()?)?);
                    heap.set_ephemeron_at(slot, Value::from_bits(key), Value::from_bits(value));
                    slot += 1;
                }
                Items::Members => {
                    let index = self.index(input.u32()?)?;
                    heap.words[mask(slot)].set(u64::from(index));
                    if index != 0 {
                        heap.barrier_ref(slot, at, index);
                    }
                }
                Items::Weaks => {
                    heap.words[mask(slot)].set(u64::from(self.index(input.u32()?)?));
                    heap.dirty(slot);
                }
            }
            slot += 1;
        }
        Ok(())
    }
}

/// What an image says the object in a place is.
enum Entry {
    Plain(&'static Desc, usize),
    Symbol,
    /// A keyword, by the place of its symbol.
    Keyword(u32),
    Symbols,
}

/// Makes what `bytes`, which [`save`] wrote, hold, and gives the roots it was given.
///
/// - `stamp`: the one `save` was given.
/// - `descs`: the types the image's objects can have: see [`descs`].
/// - `kinds`: the kinds `save` was given.
/// - `context`: what a frozen value's [`Wire::read`] needs to find, if any does.
///
/// The arena's symbols are made the way the image's were, so it mustn't have symbols made
/// another way already: load into a new arena, or one a load of an image made from this one
/// started.
pub fn load<'gc>(mc: &Mutation<'gc>, stamp: u64, bytes: &[u8], descs: &[&'static Desc], kinds: &[Kind], context: &dyn Any) -> Result<Vec<Value<'gc>>, LoadError> {
    let heap = mc.heap;
    if heap.m.phase.get() != Phase::Idle {
        return Err(LoadError::Busy);
    }
    let mut head = Reader::new(bytes, context);
    for &byte in MAGIC {
        if head.u8()? != byte {
            return Err(LoadError::Malformed);
        }
    }
    if head.u64()? != stamp {
        return Err(LoadError::Stamp);
    }
    let sum = head.u64()?;
    let body = &bytes[MAGIC.len() + 16..];
    if checksum(body) != sum {
        return Err(LoadError::Malformed);
    }
    let mut body = Reader::new(body, context);
    let seed = body.u64()?;
    let symbols = Symbols::with_seed(mc, seed)?;
    if symbols.seed(mc) != seed {
        return Err(LoadError::Symbols);
    }
    // Tables that hash by where an object is hashed by where it was.
    let moved = body.u64()?;
    heap.m.evacuations.set(heap.m.evacuations.get().max(moved) + 1);

    let frozen_count = body.length()?;
    let mut frozen_in = Reader::new(body.bytes()?, context);
    let mut frozen = Vec::with_capacity(frozen_count);
    for _ in 0..frozen_count {
        let kind = kinds.get(usize::from(frozen_in.u16()?)).ok_or(Malformed)?;
        let cost = frozen_in.u64()? as usize;
        let mut value = Reader::new(frozen_in.bytes()?, context);
        frozen.push((kind.load)(mc, &mut value, cost)?);
        if !value.is_empty() {
            return Err(LoadError::Malformed);
        }
    }

    let count = body.length()?;
    let mut table = Reader::new(body.bytes()?, context);
    let strings = Strings::new(mc);
    let mut entries = Vec::with_capacity(count);
    let mut loader = Loader { heap, indices: Vec::with_capacity(count), frozen };
    let index_of = |value: Value<'gc>| (value.to_bits() >> 32) as u32;
    for _ in 0..count {
        let (entry, index) = match table.u8()? {
            PLAIN => {
                let (ty, len) = (table.u16()?, table.u32()? as usize);
                let desc = *descs.iter().find(|desc| desc.number == Some(ty)).ok_or(Malformed)?;
                if desc.items == Items::None && len != 0 {
                    return Err(LoadError::Malformed);
                }
                (Entry::Plain(desc, len), heap.alloc_zeroed(desc, &[], len)?)
            }
            SYMBOL => {
                let name = std::str::from_utf8(table.bytes()?).map_err(|_| Malformed)?;
                (Entry::Symbol, index_of(symbols.intern_str(&strings, name)?.value(mc)))
            }
            // Made once its symbol is.
            KEYWORD => (Entry::Keyword(table.u32()?), 0),
            SYMBOLS => (Entry::Symbols, index_of(symbols.value(mc))),
            _ => return Err(LoadError::Malformed),
        };
        entries.push(entry);
        loader.indices.push(index);
    }
    for (place, entry) in entries.iter().enumerate() {
        let &Entry::Keyword(symbol) = entry else { continue };
        if !matches!(entries.get((symbol as usize).wrapping_sub(1)), Some(Entry::Symbol)) {
            return Err(LoadError::Malformed);
        }
        let symbol = Symbol::of(Value::from_bits(loader.value(u64::from(symbol) << 32 | number_of::<Sym>() << 16 | OBJECT)?)).ok_or(Malformed)?;
        loader.indices[place] = index_of(symbols.keyword(mc, symbol)?.value(mc));
    }

    let mut words = Reader::new(body.bytes()?, context);
    for (place, entry) in entries.iter().enumerate() {
        if let &Entry::Plain(desc, len) = entry {
            loader.object(loader.indices[place], desc, len, &mut words)?;
        }
    }
    let mut rooted = Reader::new(body.bytes()?, context);
    let mut roots = Vec::new();
    for _ in 0..rooted.length()? {
        roots.push(Value::from_bits(loader.value(rooted.u64()?)?));
    }
    if !(words.is_empty() && rooted.is_empty() && body.is_empty() && table.is_empty() && frozen_in.is_empty()) {
        return Err(LoadError::Malformed);
    }
    Ok(roots)
}
