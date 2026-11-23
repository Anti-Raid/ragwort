//! Heap images: the objects reachable from a set of values, serialized as bytes that another arena can load.
//!
//! [`save`] serializes the objects reachable from `roots`. [`load`] rebuilds them in an arena
//! and returns the roots. The loaded objects are copies: the two arenas share nothing.
//!
//! ```text
//! let bytes = arena.mutate(|mc| image::save(mc, STAMP, &[library], &kinds))?;
//! // Later, or in another process:
//! let roots = other.mutate(|mc| image::load(mc, STAMP, &bytes, &descs, &kinds, &hosts))?;
//! ```
//!
//! # What's saved
//!
//! - An object is saved as its type number, its item count, and its words. A word
//!   that refers to an object is saved as that object's position in the image. So the loaded objects can be
//!   anywhere in the arena.
//! - A symbol is saved as its name, and a keyword as its symbol. Each is loaded as the arena's interned symbol or keyword of that name.
//! - A frozen value is saved by the [`Kind`] that matches its type, in the format that [`Wire`] writes.
//!
//! # What can't be
//!
//! [`save`] fails if a root reaches any of these:
//!
//! - A value that the host owns: a host value in a `Host` field, or a frozen value that matches none of the given [`Kind`]s.
//! - An object of a type with no fixed number.
//!
//! [`load`] rejects an image that holds an object of a type that is not among the `descs` it is given.
//! A stack's segment has such a type, so running code cannot be saved and loaded.
//!
//! # Trust
//!
//! [`load`] trusts an image to be the output of the same build of the same program. `stamp` identifies
//! the build. `load` rejects an image with another stamp, and an image whose bytes have changed since they
//! were written. It does not check that the words of each object are valid for the object's type. So a forged image
//! with a matching stamp and checksum loads, and reading the loaded objects can then panic, as reading any forged reference
//! can.

#[cfg(test)]
#[path = "tests/image.rs"]
mod tests;

use std::any::Any;
use std::collections::HashMap;

use super::frozen::FROZEN_COST;
use super::{Desc, Gc, Heap, Items, Mutation, OBJECT, Object, OutOfMemory, Phase, Role, TAG, TYPE_BITS, Value, mask};
use crate::objects::{Interned, Sym, TableShape, TableShapeFields};
use crate::string::{Strings, chars};
use crate::symbol::{Keyword, Symbol, Symbols};
use crate::wire::{Malformed, Reader, Wire, Writer, mix, shape_of};

const MAGIC: &[u8; 8] = b"ragwort\x01";

/// The tag of an object's entry in the image's object table. It tells how the object is saved.
const PLAIN: u8 = 0;
const SYMBOL: u8 = 1;
const KEYWORD: u8 = 2;
const SYMBOLS: u8 = 3;

/// A kind of frozen value that can be saved.
#[derive(Clone, Copy)]
pub struct Kind {
    /// Writes the value and returns true, if the value is of this kind. Returns false otherwise.
    pub save: fn(&dyn Any, &mut Writer) -> bool,
    /// Reads a value and freezes it. The last argument is the total number of bytes to charge for the value. Returns the word that a frozen field holds
    /// for the value.
    pub load: for<'gc> fn(&Mutation<'gc>, &mut Reader<'_>, usize) -> Result<u64, LoadError>,
    /// A number that changes when the serialized format of the kind changes.
    pub shape: u64,
}

impl Kind {
    /// Returns the kind for frozen values of type `T`, which are saved in the format that [`Wire`] writes.
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

/// Freezes `value` with a total charge of `cost` bytes, which is the charge of the value that it is a copy of. Returns the word that a
/// frozen field holds for the value.
pub fn freeze<'gc, T: Any>(mc: &Mutation<'gc>, value: T, cost: usize) -> Result<u64, OutOfMemory> {
    let owned = cost.saturating_sub(size_of::<T>() + FROZEN_COST);
    Ok(mc.frozen_owning(value, owned)?.to_word())
}

/// The kinds of frozen value that this crate's own objects hold.
pub const KINDS: [Kind; 2] = [Kind::of::<Box<[u8]>>(), Kind::of::<Box<[u32]>>()];

/// Returns the descriptors of this crate's own object types, except the `Segment` of a stack.
pub fn descs() -> Vec<&'static Desc> {
    let groups = [super::table::Containers::DESCS, crate::string::Text::DESCS, crate::num::Numbers::DESCS, crate::objects::Data::DESCS];
    std::iter::once(&super::Boxed::DESC).chain(groups.into_iter().flatten().copied()).collect()
}

/// Returns a number to use in `stamp`. It changes when the layout of any type in `descs` or the format of any kind in `kinds` changes.
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

/// The reason why [`save`] failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SaveError {
    /// A root reaches a host value. The number is the type number of the object that holds it.
    Host(u16),
    /// A root reaches a frozen value that matches none of the given kinds. The number is the type number of the object
    /// that holds it.
    Frozen(u16),
    /// A root reaches an object of a type with no fixed number.
    Unnumbered,
    /// A collection is moving objects: a root reaches an object with a forwarding header.
    Busy,
}

/// The reason why [`load`] failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LoadError {
    /// The bytes are not an image, or have changed since they were written.
    Malformed,
    /// Another build wrote the image: its stamp differs.
    Stamp,
    /// The arena already has symbols, and their hash seed differs from the image's.
    Symbols,
    /// A major collection cycle is in progress.
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
    fn from(error: crate::Error) -> Self {
        match error {
            crate::Error::OutOfMemory => Self::OutOfMemory,
            // If a string or a number cannot be constructed, no build wrote these bytes.
            crate::Error::Num(_) | crate::Error::Str(_) => Self::Malformed,
        }
    }
}

fn number_of<T: Object>() -> u64 {
    u64::from(T::DESC.number.expect("a type of this crate's has a number"))
}

/// The state of a save in progress: the objects and frozen values reached so far.
struct Saver<'k, 'gc> {
    mc: &'k Mutation<'gc>,
    heap: Heap<'gc>,
    kinds: &'k [Kind],
    /// `places` maps the index of each object reached to its position in the image, counted from one. `order` lists the object indices by position.
    places: HashMap<u32, u32>,
    order: Vec<u32>,
    /// Maps the word of each frozen value reached to its position in the image, counted from one.
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

    /// Returns the word to save for the value `word`. If the value refers to an object, the object's index is replaced by the object's position in the image.
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
                // `None` is the value field of an ephemeron, which is saved as a value too.
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

    /// Writes each reached object in position order: its entry to `table` and its words to `words`. Writing an object can reach more objects, so this continues until
    /// every reached object is written.
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

/// Serializes every object reachable from `roots` into bytes that [`load`] accepts. `stamp` identifies the build, and
/// `load` must be given the same stamp. See [`shape`]. `kinds` lists the kinds of frozen value that
/// can occur, and `load` must be given the same kinds in the same order.
///
/// A weak reference or an ephemeron is saved as if it were a strong reference. Collect first, so that the image leaves out dead objects.
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

/// The state of a load in progress: where each object and frozen value of the image is in the arena.
struct Loader<'gc> {
    heap: Heap<'gc>,
    /// The arena index of the object at each position in the image. Positions count from one.
    indices: Vec<u32>,
    /// The field word of the frozen value at each position in the image. Positions count from one.
    frozen: Vec<u64>,
}

impl Loader<'_> {
    fn index(&self, place: u32) -> Result<u32, Malformed> {
        if place == 0 {
            return Ok(0);
        }
        self.indices.get(place as usize - 1).copied().ok_or(Malformed)
    }

    /// Returns the loaded word for the saved value `word`. If the saved value refers to an object by position, the result holds the object's arena index and
    /// type number.
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

    /// Reads the words of the object at `at`. `desc` is the descriptor of the object's type, and
    /// `len` is its item count.
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

/// An entry of the image's object table: how the object at one position was saved.
enum Entry {
    Plain(&'static Desc, usize),
    Symbol,
    /// A keyword, with the position of its symbol.
    Keyword(u32),
    Symbols,
}

/// Rebuilds the objects serialized in `bytes`, which [`save`] wrote, and returns the roots that `save` was given.
///
/// - `stamp`: the stamp that `save` was given.
/// - `descs`: the descriptors of the types that the image's objects can have. See [`descs`].
/// - `kinds`: the kinds that `save` was given, in the same order.
/// - `context`: data that the [`Wire::read`] of a frozen value can look up, if any needs it.
///
/// The arena's intern table is created with the image's hash seed, unless the arena already has one. An existing intern table must have
/// the same seed. So load into a new arena, or into an arena whose intern table was created by a load
/// of an image with the same seed.
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
    // An identity table in the image was hashed by the object indices of the arena that saved it, at an evacuation count no higher than the saved count. Advance this arena's count past both counts, so every loaded identity table rehashes on first use.
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
    #[inline(always)]
    fn index_of(value: Value<'_>) -> u32 {
        (value.to_bits() >> 32) as u32
    }
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
            // The keyword is created in the next loop, once its symbol exists.
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
    // A string that was interned when it was saved is registered in this arena's tables, unless the arena has an interned string with the same characters.
    for (place, entry) in entries.iter().enumerate() {
        if let &Entry::Plain(desc, _) = entry
            && crate::string::is_flat_type(desc)
            && let Some(string) = strings.string(Value::from_bits(u64::from(loader.indices[place]) << 32 | u64::from(desc.number.unwrap_or(0)) << 16 | OBJECT))
        {
            strings.adopt(string).map_err(|_| LoadError::OutOfMemory)?;
        }
    }
    // The image's tree of table shapes becomes the arena's, if the arena has none yet. Tables that are built in this arena then get the same shapes as the tables of the image's code. The shape without a parent is the root of the tree.
    if symbols.shapes(mc).is_none() {
        for (place, entry) in entries.iter().enumerate() {
            if let &Entry::Plain(desc, _) = entry
                && desc.number == TableShape::DESC.number
            {
                let shape: Gc<'gc, TableShape> = Gc::new(loader.indices[place]);
                if shape.parent(mc).is_none() {
                    symbols.set_shapes(mc, shape);
                    break;
                }
            }
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
