//! Heap images: the objects reachable from a set of values, serialized as bytes that another arena can load.
//!
//! [`save`] serializes the objects reachable from `roots`. [`load`] rebuilds them in an arena
//! and returns the roots. The loaded objects are copies: the two arenas share nothing.
//!
//! A [`Template`] is an image that is ready to be loaded into many arenas. It reads the image's frozen values once, and every arena
//! that loads the template refers to those same values. The objects are still copies. Frozen values never change, so an arena cannot tell
//! that it shares them. For code, they are most of what an image holds: the instructions, the position tables and the interfaces of the modules.
//!
//! ```text
//! let bytes = arena.mutate(|mc| image::save(mc, STAMP, &[library], &kinds))?;
//! // Later, or in another process:
//! let roots = other.mutate(|mc| image::load(mc, STAMP, &bytes, &descs, &kinds, &hosts))?;
//! ```
//!
//! # Images that build on other images
//!
//! [`save_linked`] saves an image that refers to objects of images saved before it, and does not hold copies of them. A library is saved
//! this way, on top of the image of the code that it uses. An arena then loads the library's image only if it needs the library, after
//! the images that the library refers to.
//!
//! - While saving, [`Known`] says which objects belong to earlier images. Each such object is saved as the number of its image and its
//!   position in that image.
//! - While loading, each earlier image is represented by its [`Exports`]: the objects at the positions that later images refer to.
//!   [`Template::load_linked`] takes them, and returns the exports of the image that it loads.
//!
//! # What's saved
//!
//! - An object is saved as its type number, its item count, and its words. A word
//!   that refers to an object is saved as that object's position in the image. So the loaded objects can be
//!   anywhere in the arena.
//! - A symbol is saved as its name, and a keyword as its symbol. Each is loaded as the arena's interned symbol or keyword of that name.
//! - The hash seed of the arena is not saved. Each arena that loads an image hashes with its own seed, and the loader rebuilds the
//!   indexes of the loaded tables with it. So the arenas that load one image do not share a seed, and a saved image does not fix one.
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
use std::rc::Rc;

use super::frozen::Shared;
use super::{Desc, Gc, Heap, Items, Mutation, OBJECT, Object, OutOfMemory, Role, TAG, TYPE_BITS, Value, mask};
use crate::objects::{Interned, Sym, TableShape, TableShapeFields};
use crate::string::{Strings, chars};
use crate::symbol::{Keyword, Symbol, Symbols};
use crate::wire::{Malformed, Reader, Wire, Writer, mix, shape_of};

const MAGIC: &[u8; 8] = b"ragwort\x02";

/// The tag of an object's entry in the image's object table. It tells how the object is saved.
const PLAIN: u8 = 0;
const SYMBOL: u8 = 1;
const KEYWORD: u8 = 2;
const SYMBOLS: u8 = 3;
/// A flat string, or a rope that is an interned string. It is saved as its text, and loaded as a string of the arena with that text: the interned string, if the text is short enough to be interned when it is made.
const STRING: u8 = 4;
/// An object of an image that was saved earlier. It is saved as the number of that image and the object's position in it.
const IMPORT: u8 = 5;

/// A kind of frozen value that can be saved.
#[derive(Clone, Copy)]
pub struct Kind {
    /// Writes the value and returns true, if the value is of this kind. Returns false otherwise.
    pub save: fn(&dyn Any, &mut Writer) -> bool,
    /// Reads a value. The loader freezes it in the arena that loads the image, or shares it among the arenas that load a [`Template`].
    pub read: fn(&mut Reader<'_>) -> Result<Box<dyn Any>, LoadError>,
    /// A number that changes when the serialized format of the kind changes.
    pub shape: u64,
}

impl Kind {
    /// Returns the kind for frozen values of type `T`, which are saved in the format that [`Wire`] writes.
    pub const fn of<T: Wire + Any>() -> Self {
        Self { save: save_as::<T>, read: read_as::<T>, shape: T::SHAPE }
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

fn read_as<T: Wire + Any>(input: &mut Reader<'_>) -> Result<Box<dyn Any>, LoadError> {
    Ok(Box::new(T::read(input)?))
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
    /// The arena holds as many [`Template`]s as it can, or the template has too many frozen values.
    TooMany,
    /// The image refers to an object of an image that the arena has not loaded, or that the given [`Exports`] do not hold.
    Unlinked,
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
    known: &'k Known,
    /// The objects of earlier images that were reached, as image and position.
    imports: Vec<(u32, u32)>,
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
        let (words, ty) = (self.heap.words(), (header & TYPE_BITS) as u16);
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
            let header = self.heap.words()[mask(at)].get();
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
            } else if let Some(string) = Strings::new(self.mc).string(object).filter(|&string| Strings::new(self.mc).is_object(string) || Strings::new(self.mc).is_external(string) || Strings::new(self.mc).is_interned(string)) {
                table.u8(STRING);
                let text: String = chars(&Strings::new(self.mc), string).collect();
                table.bytes(text.as_bytes());
            } else if let Some(&(image, place)) = self.known.objects.get(&index) {
                table.u8(IMPORT);
                table.u32(image);
                table.u32(place);
                self.imports.push((image, place));
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
    Ok(save_linked(mc, stamp, roots, kinds, &Known::default())?.bytes)
}

/// Which objects of the arena belong to images that were saved earlier. [`save_linked`] saves a reference to such an object, and not the
/// object.
///
/// It holds the places of the objects in the arena, so it is valid only in the step that made it. A collection can move the objects.
#[derive(Default)]
pub struct Known {
    /// Maps the index of an object to the number of its image and its position in that image, counted from one.
    objects: HashMap<u32, (u32, u32)>,
}

impl Known {
    /// Records the objects of the image with the number `image`. `objects` are the objects of that image in the order of
    /// [`Saved::objects`]. An object that an image before it holds already stays with that image.
    pub fn add<'gc>(&mut self, image: u32, objects: impl Iterator<Item = Value<'gc>>) {
        for (position, object) in objects.enumerate() {
            if object.to_bits() & TAG == OBJECT {
                self.objects.entry((object.to_bits() >> 32) as u32).or_insert((image, position as u32 + 1));
            }
        }
    }
}

/// What [`save_linked`] returns.
pub struct Saved<'gc> {
    pub bytes: Vec<u8>,
    /// The objects of the image, in the order of their positions. Give them to [`Known::add`] before a later image is saved. Keep them
    /// in the arena until then, for example in a vector, because a collection can move them.
    pub objects: Vec<Value<'gc>>,
    /// The objects of earlier images that the image refers to, each as the number of its image and its position in that image. An
    /// arena that loads this image needs them as [`Exports`] of those images.
    pub imports: Vec<(u32, u32)>,
}

/// Works like [`save`], for an image that builds on images saved earlier. An object that `known` lists is saved as a reference to it.
/// A symbol, a keyword or a string is saved as its name or text all the same, and is loaded as the arena's own.
pub fn save_linked<'gc>(mc: &Mutation<'gc>, stamp: u64, roots: &[Value<'gc>], kinds: &[Kind], known: &Known) -> Result<Saved<'gc>, SaveError> {
    let heap = mc.heap;
    let mut saver = Saver { mc, heap, kinds, places: HashMap::new(), order: Vec::new(), frozen: HashMap::new(), frozen_out: Writer::new(), known, imports: Vec::new() };
    let mut rooted = Writer::new();
    rooted.length(roots.len());
    for root in roots {
        let word = saver.value(root.to_bits());
        rooted.u64(word);
    }
    let (mut table, mut words) = (Writer::new(), Writer::new());
    saver.objects(&mut table, &mut words)?;
    let mut body = Writer::new();
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
    let mut objects = Vec::with_capacity(saver.order.len());
    for &index in &saver.order {
        let ty = heap.words()[mask(index as usize)].get() & TYPE_BITS;
        objects.push(Value::from_bits(u64::from(index) << 32 | ty << 16 | OBJECT));
    }
    Ok(Saved { bytes, objects, imports: saver.imports })
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
        let ty = self.heap.words()[mask(index as usize)].get() & TYPE_BITS;
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
                Some(Role::Word) => heap.words()[mask(slot)].set(input.u64()?),
                Some(Role::Value) | None => {
                    let word = self.value(input.u64()?)?;
                    heap.words()[mask(slot)].set(word);
                    heap.barrier(slot, at, word);
                }
                Some(Role::Ephemeron) => {
                    let (key, value) = (self.value(input.u64()?)?, self.value(input.u64()?)?);
                    heap.set_ephemeron_at(slot, Value::from_bits(key), Value::from_bits(value));
                    field += 1;
                }
                Some(Role::Member) => {
                    let index = self.index(input.u32()?)?;
                    heap.words()[mask(slot)].set(u64::from(index));
                    if index != 0 {
                        heap.barrier_ref(slot, at, index);
                    }
                }
                Some(Role::Weak) => {
                    heap.words()[mask(slot)].set(u64::from(self.index(input.u32()?)?));
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
                    heap.words()[mask(slot)].set(word);
                }
            }
            field += 1;
        }
        let items = start + desc.fields as usize;
        let mut slot = items;
        while slot < items + len {
            match desc.items {
                Items::None => return Err(Malformed),
                Items::Words => heap.words()[mask(slot)].set(input.u64()?),
                Items::Values => {
                    let word = self.value(input.u64()?)?;
                    heap.words()[mask(slot)].set(word);
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
                    heap.words()[mask(slot)].set(u64::from(index));
                    if index != 0 {
                        heap.barrier_ref(slot, at, index);
                    }
                }
                Items::Weaks => {
                    heap.words()[mask(slot)].set(u64::from(self.index(input.u32()?)?));
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
    String,
    /// An object of an image that the arena loaded earlier.
    Import,
}

/// The objects of one loaded image that later images refer to. `places` are their positions in the image, in ascending order, and
/// `objects` holds the object at each of those positions, in the same order.
#[derive(Clone, Copy)]
pub struct Exports<'a, 'gc> {
    pub places: &'a [u32],
    pub objects: crate::vector::ImmutableVector<'gc>,
}

/// What [`Template::load_linked`] returns.
pub struct Loaded<'gc> {
    /// The roots that the image was saved with.
    pub roots: Vec<Value<'gc>>,
    /// The objects at the positions that were asked for, in the same order.
    pub exported: Vec<Value<'gc>>,
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
    let head = Head::read(stamp, bytes, kinds, context)?;
    let frozen = &mc.heap.m.frozen;
    let mut words = Vec::with_capacity(head.frozen.len());
    for value in head.frozen {
        words.push(u64::from(frozen.alloc_boxed(&mc.heap.m.budget, false, value.value, value.cost)?) + 1);
    }
    Ok(build(mc, head.moved, &words, &bytes[head.rest..], descs, &[], &[])?.roots)
}

/// An image that is ready to be loaded into many arenas of one thread.
///
/// Its frozen values are read once, when the template is made. Every arena that loads the template refers to those values, and has no
/// copies of them. The objects of the image are copied into each arena as [`load`] copies them. Each arena is still charged for the frozen
/// values in full, so its limit means the same as it does without a template.
pub struct Template {
    moved: u64,
    frozen: Rc<[Shared]>,
    /// The part of the image after the frozen values: the object table, the words of the objects and the roots.
    rest: Box<[u8]>,
}

impl Template {
    /// Reads the image in `bytes`, which [`save`] wrote. `stamp`, `kinds` and `context` are as for [`load`].
    pub fn new(stamp: u64, bytes: &[u8], kinds: &[Kind], context: &dyn Any) -> Result<Self, LoadError> {
        let head = Head::read(stamp, bytes, kinds, context)?;
        Ok(Self { moved: head.moved, rest: bytes[head.rest..].into(), frozen: head.frozen.into() })
    }

    /// Rebuilds the image's objects in the arena and returns the roots that the image was saved with. See [`load`].
    ///
    /// An arena can load many templates. The load fails with [`LoadError::TooMany`] past the most that an arena can hold.
    pub fn load<'gc>(&self, mc: &Mutation<'gc>, descs: &[&'static Desc]) -> Result<Vec<Value<'gc>>, LoadError> {
        Ok(self.load_linked(mc, descs, &[], &[])?.roots)
    }

    /// Works like [`Template::load`], for an image that [`save_linked`] wrote.
    ///
    /// - `links` holds the exports of the images that the arena loaded earlier, at the number of each image. An image that the arena
    ///   has not loaded is `None`. The load fails with [`LoadError::Unlinked`] if this image refers to an object that `links` lacks.
    /// - `wanted` are the positions of this image that later images refer to, in ascending order. The objects there are returned, to
    ///   be kept as this image's [`Exports`].
    pub fn load_linked<'gc>(&self, mc: &Mutation<'gc>, descs: &[&'static Desc], links: &[Option<Exports<'_, 'gc>>], wanted: &[u32]) -> Result<Loaded<'gc>, LoadError> {
        let first = mc.heap.m.frozen.share(&mc.heap.m.budget, &self.frozen)?.ok_or(LoadError::TooMany)?;
        // The ids of the template's values follow each other from `first`, and a frozen field holds the id plus one.
        let words: Vec<u64> = (0..self.frozen.len() as u64).map(|position| u64::from(first) + position + 1).collect();
        build(mc, self.moved, &words, &self.rest, descs, links, wanted)
    }

    /// Returns the number of frozen values that the arenas loading the template share.
    pub fn frozen_values(&self) -> usize {
        self.frozen.len()
    }
}

/// What an image holds before its objects.
struct Head {
    /// The evacuation count of the arena that saved the image.
    moved: u64,
    /// The frozen values in the order of their positions, each with the bytes to charge for it.
    frozen: Vec<Shared>,
    /// Where the rest of the image starts in its bytes.
    rest: usize,
}

impl Head {
    /// Checks that `bytes` is an image of this build, and reads its frozen values.
    fn read(stamp: u64, bytes: &[u8], kinds: &[Kind], context: &dyn Any) -> Result<Self, LoadError> {
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
        let body_bytes = &bytes[MAGIC.len() + 16..];
        if checksum(body_bytes) != sum {
            return Err(LoadError::Malformed);
        }
        let mut body = Reader::new(body_bytes, context);
        let moved = body.u64()?;
        let frozen_count = body.length()?;
        let mut frozen_in = Reader::new(body.bytes()?, context);
        let mut frozen = Vec::with_capacity(frozen_count);
        for _ in 0..frozen_count {
            let kind = kinds.get(usize::from(frozen_in.u16()?)).ok_or(Malformed)?;
            let cost = frozen_in.u64()? as usize;
            let mut value = Reader::new(frozen_in.bytes()?, context);
            frozen.push(Shared { value: (kind.read)(&mut value)?, cost });
            if !value.is_empty() {
                return Err(LoadError::Malformed);
            }
        }
        if !frozen_in.is_empty() {
            return Err(LoadError::Malformed);
        }
        Ok(Self { moved, frozen, rest: bytes.len() - body.remaining() })
    }
}

/// Rebuilds the objects of an image in the arena. `rest` is the part of the image after the frozen values. `frozen` holds, for each frozen
/// value of the image in order, the word that a frozen field holds for it in this arena.
///
/// A load can run while a collection cycle is in progress. The loader allocates the objects as a program does, and fills them in before
/// the step ends. An object that is allocated while the collector marks is traced later, with the words that it then has.
fn build<'gc>(mc: &Mutation<'gc>, moved: u64, frozen: &[u64], rest: &[u8], descs: &[&'static Desc], links: &[Option<Exports<'_, 'gc>>], wanted: &[u32]) -> Result<Loaded<'gc>, LoadError> {
    let heap = mc.heap;
    // Nothing after the frozen values reads the context.
    let context: &dyn Any = &();
    let mut body = Reader::new(rest, context);
    // The arena hashes with its own seed, which is random unless the arena had symbols already. An image does not hold the seed of the
    // arena that saved it. The loaded strings and symbols are made in this arena, so they are hashed with its seed. The loaded tables
    // are given the seed below.
    let symbols = Symbols::of_arena(mc)?;
    let seed = symbols.seed(mc);
    // An identity table in the image was hashed by the object indices of the arena that saved it, at an evacuation count no higher than the saved count. Advance this arena's count past both counts, so every loaded identity table rehashes on first use.
    heap.m.evacuations.set(heap.m.evacuations.get().max(moved) + 1);

    let count = body.length()?;
    let mut table = Reader::new(body.bytes()?, context);
    let strings = Strings::new(mc);
    let mut entries = Vec::with_capacity(count);
    let mut loader = Loader { heap, indices: Vec::with_capacity(count), frozen: frozen.to_vec() };
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
            STRING => {
                let text = std::str::from_utf8(table.bytes()?).map_err(|_| Malformed)?;
                // A long text is not interned when it is made. It is interned here, because the image can hold it where only an interned string is found again, such as the key of a table.
                let string = strings.intern(crate::string::from_str(&strings, text)?)?.value();
                // A text that was saved as an object is too long for the value word, so it is an object again.
                if string.to_bits() & TAG != OBJECT {
                    return Err(LoadError::Malformed);
                }
                (Entry::String, index_of(string))
            }
            // The keyword is created in the next loop, once its symbol exists.
            KEYWORD => (Entry::Keyword(table.u32()?), 0),
            SYMBOLS => (Entry::Symbols, index_of(symbols.value(mc))),
            IMPORT => {
                let (image, place) = (table.u32()? as usize, table.u32()?);
                let exports = links.get(image).copied().flatten().ok_or(LoadError::Unlinked)?;
                let found = exports.places.binary_search(&place).map_err(|_| LoadError::Unlinked)?;
                let object = exports.objects.get(mc, found).filter(|object| object.to_bits() & TAG == OBJECT).ok_or(LoadError::Unlinked)?;
                (Entry::Import, index_of(object))
            }
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
    let (table_number, shape_number) = (crate::objects::Table::DESC.number, TableShape::DESC.number);
    // The arena indices of the objects that belong to images loaded earlier.
    let mut imported = std::collections::HashSet::new();
    for (place, entry) in entries.iter().enumerate() {
        if matches!(entry, Entry::Import) {
            imported.insert(loader.indices[place]);
        }
    }
    let mut rebuilt = HashMap::new();
    // The loaded shapes whose arrays belong to an earlier image, each with its number of keys.
    let mut borrowed: Vec<(u64, Gc<'gc, TableShape>)> = Vec::new();
    let mut shapes: Vec<Gc<'gc, TableShape>> = Vec::new();
    for (place, entry) in entries.iter().enumerate() {
        let &Entry::Plain(desc, _) = entry else { continue };
        if desc.number == table_number {
            crate::table::reseed_table(mc, Gc::new(loader.indices[place]), seed)?;
        } else if desc.number == shape_number {
            let shape: Gc<'gc, TableShape> = Gc::new(loader.indices[place]);
            let borrows = crate::table::shape_array(mc, shape).is_some_and(|array| imported.contains(&index_of(array)));
            crate::table::reseed_shape(mc, shape, seed, borrows, &mut rebuilt)?;
            if borrows {
                borrowed.push((crate::table::shape_keys(mc, shape), shape));
            }
            shapes.push(shape);
        }
    }
    borrowed.sort_by_key(|&(keys, _)| keys);
    for (_, shape) in borrowed {
        crate::table::reshare_shape(mc, shape)?;
    }
    for shape in shapes {
        crate::table::rejoin_shape(mc, shape)?;
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
    if !(words.is_empty() && rooted.is_empty() && body.is_empty() && table.is_empty()) {
        return Err(LoadError::Malformed);
    }
    let mut exported = Vec::with_capacity(wanted.len());
    for &place in wanted {
        exported.push(Value::from_bits(loader.value(u64::from(place) << 32 | OBJECT)?));
    }
    Ok(Loaded { roots, exported })
}
