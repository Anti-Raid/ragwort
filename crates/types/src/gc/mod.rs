//! Ragwort's garbage collector. The region is words in `Cell`s, references are word indices, 
//! and a type is described by data the collector reads rather than code it runs. A wrong description 
//! or a forged reference gives wrong results or a panic but never undefined behavior.
//!
//! It has 16 KiB pages of 128-byte lines, 512-byte cards, sticky mark bits for minor
//! collections, major cycles marked in incremental slices, weak references and ephemerons,
//! evacuation of fragmented pages through forwarding headers in the atomic phase, and lazy
//! sweeping. Free pages past a nursery's worth go back to the system through
//! `ragwort-gc-region`, which holds the only unsafe code in Ragwort (atleast in interpreter mode).
//! Memory is counted against a budget with a reserve, and VM stacks have segments, continuation capture and parking.
//!
//! The arena has a fixed number of value roots, set when it's made. A [`Root`] keeps an object
//! alive across steps from outside the arena, such as from a task.
//!
//! # Typed objects
//!
//! [`objects!`] declares a group of types. Each field names what it holds, and the macro
//! derives the collector's description from that, so the two can't disagree:
//!
//! ```
//! use ragwort_types::gc::*;
//!
//! objects! {
//!     /// Every type the program allocates.
//!     pub kind Kind;
//!
//!     pub struct Pair { car: Value, cdr: Value }
//!     pub struct Node { n: i64, next: Member<Node>, cache: Weak<Node> }
//!     pub struct Labelled { label: Host<String>, flags: u32 }
//!     pub struct Vector {} items Value
//! }
//!
//! let mut arena = Arena::new(1 << 20, 1);
//! arena.mutate(|mc| {
//!     let p = Pair::new(mc, Value::NIL, Value::TRUE).unwrap();
//!     assert_eq!(p.cdr(mc), Value::TRUE);
//!     p.set_car(mc, Value::fixnum(1).unwrap());
//!     assert_eq!(p.get(mc, Pair::CAR), Value::fixnum(1).unwrap());
//!
//!     let tail = Node::new(mc, 2, None, None).unwrap();
//!     let head = Node::new(mc, 1, Some(tail), None).unwrap();
//!     assert_eq!(head.next(mc).map(|n| n.n(mc)), Some(2));
//!
//!     let v = Vector::new(mc, 3, Value::NIL).unwrap();
//!     v.items(mc).set(mc, 0, Value::object(mc, p));
//!
//!     match Kind::of(v.items(mc).get(0)) {
//!         Some(Kind::Pair(p)) => assert_eq!(p.cdr(mc), Value::TRUE),
//!         _ => unreachable!(),
//!     }
//! });
//! ```
//!
//! For each `struct` it generates:
//! - a unit struct implementing [`Object`];
//! - a [`Field`] constant per field, named in capitals (`Pair::CAR`), for [`Gc::get`] and
//!   [`Gc::set`];
//! - `new(mc, fields…)`, which also takes a length and fill value when the type has items, or
//!   an entry count for `items Ephemeron`;
//! - a trait `PairFields` for `Gc<Pair>`, with a getter and a `set_` setter per field, and
//!   `items` for any items but ephemerons, which `Gc::entry` reads.
//!
//! A field holds a `Value`, a word (`u64`, `i64`, `u32`, `f64` or `bool`), a `Member<T>`, a
//! `Weak<T>`, a `Host<T>`, an `AnyHost`, a `Frozen<T>` or an `Ephemeron`. Items can be any of
//! these but hosts and frozen values. A `Host<T>` holds a [`HostRef`], and an `AnyHost`
//! an [`AnyHostRef`], a host value of any type whose reads check the type. Writes take the barrier their kind needs, and a member or weak read
//! checks that the target has the type the field or items declare.
//!
//! The group's enum, `Kind` here, has a variant per type. `Kind::of(value)` reads the type
//! number the value carries, so it needs no memory read. Types get fixed numbers from
//! `Kind::BASE`, in declaration order. Groups used in one arena mustn't overlap: declare the
//! second `kind Extra after Kind;`. If they overlap, the first allocation of a clashing type
//! panics. `kind Name at N;` starts the group at `N` instead.
//!
//! Fields can't take a name that a method of `Gc` or a constructor parameter uses. The raw API
//! beneath, fields by number, is in the hidden `raw` module.
//!
//! # Frozen values
//!
//! A `Frozen<T>` field holds a value outside the region, made once by [`Mutation::frozen`] and
//! read as `&'gc T`: for data too big to copy into items as cells, such as a source's text.
//! Nothing is freed while a step runs, so the borrow checker keeps a reference from outliving
//! it: a collection needs the arena mutably.
//!
//! ```
//! use ragwort_types::gc::*;
//!
//! objects! { kind Kind; struct Text { chars: Frozen<Box<[u8]>> } }
//!
//! let mut arena = Arena::new(1 << 20, 1);
//! arena.mutate(|mc| {
//!     let text = Text::new(mc, mc.frozen(Box::from(*b"hello")).unwrap()).unwrap();
//!     assert_eq!(text.chars(mc).map(|c| &c[..]), Some(&b"hello"[..]));
//! });
//! ```
//!
//! ```compile_fail
//! # use ragwort_types::gc::*;
//! # objects! { kind Kind; struct Text { chars: Frozen<Box<[u8]>> } }
//! let mut arena = Arena::new(1 << 20, 1);
//! let chars: &[u8] = arena.mutate(|mc| {
//!     let text = Text::new(mc, mc.frozen(Box::from(*b"hello")).unwrap()).unwrap();
//!     text.chars(mc).unwrap()
//! });
//! arena.collect();
//! ```
//!
//! # Containers, strings and numbers
//!
//! [`GcVec`] is a growable array, [`Table`] a hash table of strong, ephemeron or weak entries,
//! and [`ScratchVec`] a step's scratch space outside the arena, counted against its budget.
//! [`crate::string`] and [`crate::num`] hold `ragwort-string`'s strings and `ragwort-num`'s numbers: a flat
//! string's characters are packed into its own items, and a bignum's digits are its items.
//!
//! What doesn't compile: storing an object of the wrong type,
//!
//! ```compile_fail
//! # use ragwort_types::gc::*;
//! # objects! { kind Kind; struct Pair { car: Value, cdr: Value } struct Node { next: Member<Node> } }
//! # let mut arena = Arena::new(1 << 20, 1);
//! arena.mutate(|mc| {
//!     let pair = Pair::new(mc, Value::NIL, Value::NIL).unwrap();
//!     let node = Node::new(mc, None).unwrap();
//!     node.set_next(mc, Some(pair));
//! });
//! ```
//!
//! using one type's field on another,
//!
//! ```compile_fail
//! # use ragwort_types::gc::*;
//! # objects! { kind Kind; struct Pair { car: Value, cdr: Value } struct Node { next: Member<Node> } }
//! # let mut arena = Arena::new(1 << 20, 1);
//! arena.mutate(|mc| {
//!     let node = Node::new(mc, None).unwrap();
//!     node.get(mc, Pair::CAR);
//! });
//! ```
//!
//! a field handle whose kind doesn't match the description,
//!
//! ```compile_fail
//! # use ragwort_types::gc::*;
//! # objects! { kind Kind; struct Pair { car: Value, cdr: Value } }
//! const CAR_AS_WORD: Field<Pair, slot::u64> = Field::new(0);
//! # let mut arena = Arena::new(1 << 20, 1);
//! arena.mutate(|mc| {
//!     let pair = Pair::new(mc, Value::NIL, Value::NIL).unwrap();
//!     pair.get(mc, CAR_AS_WORD);
//! });
//! ```
//!
//! and a field named like a method of `Gc`:
//!
//! ```compile_fail
//! # use ragwort_types::gc::*;
//! objects! { kind Kind; struct Buffer { len: u64 } items u64 }
//! ```

use std::any::{Any, TypeId};
use std::cell::{Cell, OnceCell, Ref, RefCell};
use std::fmt;
use std::marker::PhantomData;
use std::ops::Range;
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};

use ragwort_gc_region::Region;


mod frozen;
mod budget;
#[doc(hidden)]
pub mod raw;
mod root;
pub mod slot;
mod scratch;
mod stack;
pub mod table;
mod vec;

use frozen::FrozenTable;
pub use frozen::FrozenRef;
use budget::Budget;
pub use budget::Charge;
use raw::Raw;
pub use ragwort_derive::objects;
use root::{ROOT_COST, RootRecord};
pub use root::{ForeignRoot, Root, ValueRoot};
use slot::{Item, Refs, Role, Slot};
use stack::{STACK_COST, StackRecord};
pub use scratch::ScratchVec;
pub use stack::{Frame, Segment, Stack};
pub use table::{Table, eq_hash};
pub use vec::{GcVec, VecHead};

#[cfg(test)]
#[path = "tests/heap.rs"]
mod tests;
#[cfg(test)]
#[path = "tests/stack.rs"]
mod stack_tests;
#[cfg(test)]
#[path = "tests/budget.rs"]
mod budget_tests;
#[cfg(test)]
#[path = "tests/objects.rs"]
mod objects_tests;
#[cfg(test)]
#[path = "tests/items.rs"]
mod items_tests;
#[cfg(test)]
#[path = "tests/frozen.rs"]
mod frozen_tests;
#[cfg(test)]
#[path = "tests/root.rs"]
mod root_tests;
#[cfg(test)]
#[path = "tests/fuzz.rs"]
mod fuzz_tests;

pub const REGION: usize = 64 << 20;
/// The region in words: twice `REGION`, so evacuation has fresh pages to copy into.
const WORDS: usize = 2 * REGION / 8;
/// The words of the region, as everything that reads them sees it.
type RegionWords = [Cell<u64>; WORDS + SLACK];
/// Page, line and card sizes in words.
const PAGE: usize = 2048;
const LINE: usize = 16;
const CARD: usize = 64;
const PAGES: usize = WORDS / PAGE;
/// Unused words past the region, so `mask(index) + 1 + field` for a constant field needs no
/// bounds check.
const SLACK: usize = 128;
const LINES: usize = PAGE / LINE;
/// How many registers a frame has: the slots a [`Frame`] or [`Window`] sees from its start. Every
/// register limit of the VM and compiler follows from it. A register is a byte, taken modulo
/// `WINDOW`, so no access needs a bounds check.
pub const WINDOW: usize = 64;
const _: () = assert!(WINDOW.is_power_of_two() && WINDOW >= 32 && WINDOW <= 256);

pub(crate) const TAG: u64 = 0b1111;
pub(crate) const OBJECT: u64 = 0b0001;
const CONSTANT: u64 = 0b1101;
/// The bit of a constant's id that makes it a character.
const CHAR: u64 = 1 << 31;
/// A string of [`crate::string::INLINE_CHARS`] Latin-1 characters or fewer: the length in the next
/// four bits, then a byte for each character, the first lowest.
pub(crate) const INLINE_STRING: u64 = 0b0101;
/// Inline flonums end in 11: a double with two redundant exponent bits dropped.
const FLONUM: u64 = 0b11;
/// The special doubles take the words of the lowest few inline ones, ±1.7272337110188889e-77
/// and the two above, which are boxed instead. The NaNs are the defaults ARM and x86 make.
const SPECIALS: [u64; 6] = [0, 1 << 63, 0x7FF0 << 48, 0xFFF0 << 48, 0x7FF8 << 48, 0xFFF8 << 48];
/// The first special's word. Each next one is 4 above it.
const ZERO: u64 = 0x8000_0000_0000_0003;
const LAST_SPECIAL: u64 = 4 * (SPECIALS.len() as u64 - 1);

#[inline]
fn encode(f: f64) -> Option<u64> {
    let bits = f.to_bits();
    // Exponents starting 011 or 100: the second and third bits copy the inverse of the first.
    let top = bits >> 60 & 0b111;
    if top == 0b011 || top == 0b100 {
        let word = bits.rotate_left(3) | FLONUM;
        return (word.wrapping_sub(ZERO) > LAST_SPECIAL).then_some(word);
    }
    let i = SPECIALS.iter().position(|&s| s == bits)?;
    Some(ZERO + 4 * i as u64)
}

#[inline]
fn decode(word: u64) -> f64 {
    let special = word.wrapping_sub(ZERO);
    if special <= LAST_SPECIAL {
        return f64::from_bits(SPECIALS[special as usize / 4]);
    }
    let first = word >> 63;
    f64::from_bits((word & !FLONUM | (2 - first)).rotate_right(3))
}

/// A double that doesn't fit in a word: magnitudes beyond about 1e±77, and the NaNs not in
/// `SPECIALS`. Every arena registers it first, as type 0.
struct Boxed;

impl Object for Boxed {
    const DESC: Desc = Desc::of::<Boxed>(1).numbered(0);
}

/// Type numbers below this are this crate's own: `Boxed`, `Segment`, the containers, strings,
/// numbers, and the data types. An `objects!` group declared without a base starts here.
#[doc(hidden)]
pub const FIRST_TYPE: u16 = crate::objects::Data::END;
/// A header is the type index, a flag, and the item count in the upper half. A forwarded one
/// has the new index there instead.
const TYPE_BITS: u64 = 0xFFFF;
const FORWARDED: u64 = 1 << 16;
const TYPES: usize = 1 << 16;
static NEXT_ARENA: AtomicU64 = AtomicU64::new(0);

type Brand<'gc> = PhantomData<Cell<&'gc ()>>;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct OutOfMemory;

/// What string and number operations fail with.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Error {
    OutOfMemory,
    Num(ragwort_num::NumError),
    Str(ragwort_string::StrError),
}

impl From<OutOfMemory> for Error {
    fn from(_: OutOfMemory) -> Self {
        Self::OutOfMemory
    }
}

impl From<ragwort_num::NumError> for Error {
    fn from(e: ragwort_num::NumError) -> Self {
        Self::Num(e)
    }
}

impl From<ragwort_string::StrError> for Error {
    fn from(e: ragwort_string::StrError) -> Self {
        Self::Str(e)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Items {
    None,
    Values,
    Words,
    /// Pairs of a key and a value, held like `Desc::ephemerons`. The length counts words.
    Ephemerons,
    /// Object indices, 0 for none, that keep their targets alive.
    Members,
    /// Object indices, 0 for none, cleared once their targets die.
    Weaks,
}

/// How the collector sees a type: its fixed words, which of them hold references, and its items.
pub struct Desc {
    pub type_id: TypeId,
    pub fields: u32,
    /// Fields holding a `Value`.
    pub values: u64,
    /// Fields holding an object index, 0 for none.
    pub members: u64,
    /// Fields holding a host id plus one, 0 for none.
    pub hosts: u64,
    /// Fields holding an object index that doesn't keep the object alive, 0 for none.
    pub weaks: u64,
    /// Fields holding a frozen value's id plus one, 0 for none: write-once values outside the
    /// region.
    pub frozen: u64,
    /// Fields holding an ephemeron's key, with its value in the next field. The value is kept
    /// alive only while the key is reachable some other way; once the key dies, both become
    /// `Value::BROKEN`. A key that isn't an object never dies.
    pub ephemerons: u64,
    pub items: Items,
    /// A fixed type number, which `objects!` gives its types so type checks compare against a
    /// constant. Types without one are numbered by each arena as it first sees them.
    pub number: Option<u16>,
    /// Whether marking an object of the type has anything to trace, kept up to date by every
    /// builder: marking asks for each object, and working it out each time costs 4%.
    traces: bool,
}

impl Desc {
    pub const fn of<T: 'static>(fields: u32) -> Self {
        Self {
            type_id: TypeId::of::<T>(),
            fields,
            values: 0,
            members: 0,
            hosts: 0,
            weaks: 0,
            frozen: 0,
            ephemerons: 0,
            items: Items::None,
            number: None,
            traces: false,
        }
    }

    /// Fields with these roles in order, where an ephemeron takes two words.
    #[doc(hidden)]
    pub const fn layout<T: 'static>(roles: &[Role], items: Items) -> Self {
        let mut desc = Self::of::<T>(0).items(items);
        let mut i = 0;
        while i < roles.len() {
            let bit = if desc.fields < 64 { 1 << desc.fields } else { 0 };
            assert!(bit != 0 || matches!(roles[i], Role::Word), "only the first 64 fields can hold references");
            match roles[i] {
                Role::Word => {}
                Role::Value => desc.values |= bit,
                Role::Member => desc.members |= bit,
                Role::Weak => desc.weaks |= bit,
                Role::Host => desc.hosts |= bit,
                Role::Frozen => desc.frozen |= bit,
                Role::Ephemeron => {
                    desc.ephemerons |= bit;
                    desc.fields += 1;
                }
            }
            desc.fields += 1;
            i += 1;
        }
        desc.settled()
    }

    /// What field `field` holds, or `None` past the fields and for an ephemeron's value.
    pub const fn role(&self, field: usize) -> Option<Role> {
        if field >= self.fields as usize {
            return None;
        }
        let bit = if field < 64 { 1 << field } else { 0 };
        let prev = if field >= 1 && field <= 64 { 1 << (field - 1) } else { 0 };
        Some(if self.values & bit != 0 {
            Role::Value
        } else if self.members & bit != 0 {
            Role::Member
        } else if self.weaks & bit != 0 {
            Role::Weak
        } else if self.hosts & bit != 0 {
            Role::Host
        } else if self.frozen & bit != 0 {
            Role::Frozen
        } else if self.ephemerons & bit != 0 && field + 1 < self.fields as usize {
            Role::Ephemeron
        } else if self.ephemerons & (bit | prev) != 0 {
            return None;
        } else {
            Role::Word
        })
    }

    pub const fn numbered(self, number: u16) -> Self {
        Self { number: Some(number), ..self }
    }

    pub const fn values(self, values: u64) -> Self {
        Self { values, ..self }.settled()
    }

    pub const fn members(self, members: u64) -> Self {
        Self { members, ..self }.settled()
    }

    pub const fn hosts(self, hosts: u64) -> Self {
        Self { hosts, ..self }.settled()
    }

    pub const fn weaks(self, weaks: u64) -> Self {
        Self { weaks, ..self }.settled()
    }

    pub const fn frozen(self, frozen: u64) -> Self {
        Self { frozen, ..self }.settled()
    }

    pub const fn ephemerons(self, ephemerons: u64) -> Self {
        Self { ephemerons, ..self }.settled()
    }

    pub const fn items(self, items: Items) -> Self {
        Self { items, ..self }.settled()
    }

    const fn settled(self) -> Self {
        Self { traces: self.find_traces(), ..self }
    }

    const fn find_traces(&self) -> bool {
        self.values | self.members | self.hosts | self.weaks | self.frozen != 0
            || self.has_ephemerons()
            || matches!(self.items, Items::Values | Items::Members | Items::Weaks)
    }

    const fn has_ephemerons(&self) -> bool {
        self.ephemerons != 0 || matches!(self.items, Items::Ephemerons)
    }

    fn size(&self, header: u64) -> usize {
        1 + self.fields as usize + if self.items == Items::None { 0 } else { (header >> 32) as usize }
    }
}

/// A type that lives in the arena. Implementing it is safe: a wrong `DESC` can only give wrong
/// results.
pub trait Object: 'static {
    const DESC: Desc;
}

/// A value in one word: a fixnum shifted left by one, an object's index and type, a short string,
/// or a constant.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Value<'gc> {
    word: u64,
    _brand: Brand<'gc>,
}

impl<'gc> Value<'gc> {
    pub const FALSE: Self = Self::constant(0);
    pub const TRUE: Self = Self::constant(1);
    pub const NIL: Self = Self::constant(2);
    /// What a stack slot above `top` becomes.
    pub const VOID: Self = Self::constant(3);
    /// What a module's variable holds until it's defined.
    pub const UNDEFINED: Self = Self::constant(4);
    /// What an optional parameter is bound to when its call passes no argument for it.
    pub const UNSUPPLIED: Self = Self::constant(5);
    /// What an ephemeron's key and value become once the key dies.
    pub const BROKEN: Self = Self::constant(7);

    const fn constant(id: u64) -> Self {
        Self::from_bits(id << 32 | CONSTANT)
    }

    /// A character: a constant whose id has its top bit set, the code point below it.
    #[inline]
    pub const fn char(c: char) -> Self {
        Self::constant(CHAR | c as u64)
    }

    #[inline]
    pub fn as_char(self) -> Option<char> {
        let id = self.word >> 32;
        if self.word & 0xFFFF_FFFF != CONSTANT || id & CHAR == 0 {
            return None;
        }
        char::from_u32((id & !CHAR) as u32)
    }

    /// Any word is a valid value. One that names no object reads as some other object or none.
    pub const fn from_bits(word: u64) -> Self {
        Self { word, _brand: PhantomData }
    }

    pub const fn to_bits(self) -> u64 {
        self.word
    }

    #[inline]
    pub fn fixnum(n: i64) -> Option<Self> {
        let word = (n as u64) << 1;
        ((word as i64) >> 1 == n).then_some(Self::from_bits(word))
    }

    #[inline]
    pub fn as_fixnum(self) -> Option<i64> {
        (self.word & 1 == 0).then_some(self.word as i64 >> 1)
    }

    pub const MAX_FIXNUM: i64 = i64::MAX >> 1;
    pub const MIN_FIXNUM: i64 = i64::MIN >> 1;

    #[inline]
    pub fn is_fixnum(self) -> bool {
        self.word & 1 == 0
    }

    #[inline]
    pub fn fixnum_add(self, other: Self) -> Option<Self> {
        if (self.word | other.word) & 1 != 0 {
            return None;
        }
        (self.word as i64).checked_add(other.word as i64).map(|w| Self::from_bits(w as u64))
    }

    #[inline]
    pub fn fixnum_sub(self, other: Self) -> Option<Self> {
        if (self.word | other.word) & 1 != 0 {
            return None;
        }
        (self.word as i64).checked_sub(other.word as i64).map(|w| Self::from_bits(w as u64))
    }

    /// Twice `a` times `b` is twice their product, so one operand stays shifted.
    #[inline]
    pub fn fixnum_mul(self, other: Self) -> Option<Self> {
        if (self.word | other.word) & 1 != 0 {
            return None;
        }
        (self.word as i64).checked_mul(other.word as i64 >> 1).map(|w| Self::from_bits(w as u64))
    }

    /// Stores the double in the word when it fits, and boxes it otherwise.
    #[inline]
    pub fn flonum(mc: &Mutation<'gc>, f: f64) -> Result<Self, OutOfMemory> {
        match encode(f) {
            Some(word) => Ok(Self::from_bits(word)),
            None => Ok(Self::object(mc, mc.alloc::<Boxed, 1>([f.to_bits()])?)),
        }
    }

    /// The double as a value without allocating, if it fits in the word.
    #[inline]
    pub fn inline_flonum(f: f64) -> Option<Self> {
        encode(f).map(Self::from_bits)
    }

    /// Inline, or a reference to a boxed one: type 0 in every arena.
    #[inline]
    pub fn is_flonum(self) -> bool {
        self.word & FLONUM == FLONUM || self.word & (TYPE_BITS << 16 | TAG) == OBJECT
    }

    #[inline]
    pub fn as_flonum(self, mc: &Mutation<'gc>) -> Option<f64> {
        if self.word & FLONUM == FLONUM {
            Some(decode(self.word))
        } else if self.word & (TYPE_BITS << 16 | TAG) == OBJECT {
            let boxed: Gc<'gc, Boxed> = Gc::new((self.word >> 32) as u32);
            Some(f64::from_bits(boxed.word(mc, 0)))
        } else {
            None
        }
    }

    #[inline]
    pub fn object<T: Object>(mc: &Mutation<'gc>, gc: Gc<'gc, T>) -> Self {
        let ty = match T::DESC.number {
            Some(ty) => u64::from(ty),
            None => mc.heap.words[mask(gc.index as usize)].get() & TYPE_BITS,
        };
        Self::from_bits(u64::from(gc.index) << 32 | ty << 16 | OBJECT)
    }

    #[inline]
    pub fn downcast<T: Object>(self, mc: &Mutation<'gc>) -> Option<Gc<'gc, T>> {
        self.downcast_tag(mc.type_tag::<T>()?)
    }

    /// Compares the type the reference carries, without reading the object.
    #[inline]
    pub fn downcast_tag<T: Object>(self, tag: TypeTag<'gc, T>) -> Option<Gc<'gc, T>> {
        (self.word & (TYPE_BITS << 16 | TAG) == u64::from(tag.ty) << 16 | OBJECT).then(|| Gc::new((self.word >> 32) as u32))
    }

    /// The type number and index of the object this refers to, for `objects!` kinds.
    #[doc(hidden)]
    #[inline]
    pub fn object_parts(self) -> Option<(u16, u32)> {
        (self.word & TAG == OBJECT).then_some(((self.word >> 16 & TYPE_BITS) as u16, (self.word >> 32) as u32))
    }

    /// The value, if it refers to no object.
    #[inline]
    pub fn immediate(self) -> Option<Immediate> {
        (self.word & TAG != OBJECT).then_some(Immediate(self.word))
    }
}

/// A value that refers to no object, such as a fixnum, an inline flonum or `#t`. It holds no
/// brand: no collection changes it, so it can be kept outside the arena.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Immediate(u64);

impl Immediate {
    #[inline]
    pub fn value<'gc>(self) -> Value<'gc> {
        Value::from_bits(self.0)
    }

    pub fn to_bits(self) -> u64 {
        self.0
    }
}

pub struct TypeTag<'gc, T> {
    ty: u16,
    _marker: PhantomData<(Brand<'gc>, fn() -> T)>,
}

impl<T> Clone for TypeTag<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for TypeTag<'_, T> {}

/// An object: its header's index in the region.
pub struct Gc<'gc, T> {
    index: u32,
    _marker: PhantomData<(Brand<'gc>, fn() -> T)>,
}

impl<T> Clone for Gc<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Gc<'_, T> {}

impl<T> PartialEq for Gc<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl<T> Eq for Gc<'_, T> {}

impl<T> fmt::Debug for Gc<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Gc").field(&self.index).finish()
    }
}

impl<'gc, T: Object> Gc<'gc, T> {
    const fn new(index: u32) -> Self {
        Self { index, _marker: PhantomData }
    }

    /// The object at `index`, taken to be a `T`: for `objects!` kinds, which have checked the
    /// type the value carries.
    #[doc(hidden)]
    pub const fn forge(index: u32) -> Self {
        Self::new(index)
    }

    #[inline]
    pub fn get<S: Slot>(self, mc: &Mutation<'gc>, field: Field<T, S>) -> S::Out<'gc> {
        S::get(self, mc, field.index)
    }

    /// Takes the barrier the field's kind needs.
    #[inline]
    pub fn set<S: Slot>(self, mc: &Mutation<'gc>, field: Field<T, S>, value: S::In<'gc>) {
        S::set(self, mc, field.index, value);
    }

    pub fn len(self, mc: &Mutation<'gc>) -> usize {
        if T::DESC.items == Items::None { 0 } else { (mc.heap.words[mask(self.index as usize)].get() >> 32) as usize }
    }

    pub fn is_empty(self, mc: &Mutation<'gc>) -> bool {
        self.len(mc) == 0
    }

    /// Entry `i` of `Items::Ephemerons` items, or `None` once its key has died. Panics past
    /// the end.
    #[inline]
    pub fn entry(self, mc: &Mutation<'gc>, i: usize) -> Option<(Value<'gc>, Value<'gc>)> {
        assert!(2 * i + 1 < self.len(mc), "entry {i} out of bounds");
        mc.heap.ephemeron_at(mask(items_start(self) + 2 * i))
    }

    #[inline]
    pub fn set_entry(self, mc: &Mutation<'gc>, i: usize, key: Value<'gc>, value: Value<'gc>) {
        assert!(2 * i + 1 < self.len(mc), "entry {i} out of bounds");
        mc.heap.set_ephemeron_at(mask(items_start(self) + 2 * i), key, value);
    }
}

/// The word of field `field`. Panics past the declared fields, so a write can't reach the next
/// object; constant field numbers fold the check away.
#[inline]
fn field_slot<T: Object>(gc: Gc<'_, T>, field: usize) -> usize {
    assert!(field < T::DESC.fields as usize, "field {field} of {}", T::DESC.fields);
    mask(gc.index as usize) + 1 + field
}

#[inline]
fn items_start<T: Object>(gc: Gc<'_, T>) -> usize {
    mask(gc.index as usize) + 1 + T::DESC.fields as usize
}

/// A member or weak field's target, checked against the type the field declares when that type
/// has a fixed number: one load and compare.
#[inline]
fn target<'gc, U: Object>(region: &RegionWords, index: u32) -> Option<Gc<'gc, U>> {
    if index == 0 {
        return None;
    }
    if let Some(ty) = U::DESC.number
        && region[mask(index as usize)].get() & TYPE_BITS != u64::from(ty)
    {
        wrong_target(index, ty);
    }
    Some(Gc::new(index))
}

#[cold]
#[inline(never)]
fn wrong_target(index: u32, ty: u16) -> ! {
    panic!("object {index} isn't of type {ty}, which the field it was read from declares")
}

/// A typed handle to field `index` of a `T`, which holds an `S`. `objects!` makes them, and
/// one whose kind doesn't match `T`'s description doesn't compile.
pub struct Field<T, S> {
    index: usize,
    _marker: PhantomData<fn() -> (T, S)>,
}

impl<T, S> Clone for Field<T, S> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T, S> Copy for Field<T, S> {}

impl<T: Object, S: Slot> Field<T, S> {
    #[doc(hidden)]
    pub const fn new(index: usize) -> Self {
        match T::DESC.role(index) {
            Some(role) if role as u8 == S::ROLE as u8 => Self { index, _marker: PhantomData },
            _ => panic!("the field's kind doesn't match the type's description"),
        }
    }

    pub const fn index(self) -> usize {
        self.index
    }
}

/// An object's fields as a fixed array, so constant field numbers need no bounds check: the
/// safe counterpart of a `&'gc T`.
#[doc(hidden)]
#[derive(Clone, Copy)]
pub struct Fields<'gc, const N: usize> {
    words: &'gc [Cell<u64>; N],
    at: usize,
    owner: u32,
    _brand: Brand<'gc>,
}

impl<'gc, const N: usize> Fields<'gc, N> {
    #[inline]
    pub fn value(self, field: usize) -> Value<'gc> {
        Value::from_bits(self.words[field].get())
    }

    #[inline]
    pub fn word(self, field: usize) -> u64 {
        self.words[field].get()
    }

    #[inline]
    pub fn set_value(self, mc: &Mutation<'gc>, field: usize, value: Value<'gc>) {
        self.words[field].set(value.word);
        mc.heap.barrier(self.at + field, self.owner, value.word);
    }
}

/// An object's items, each an `S`: values unless the type declares words.
pub struct Slots<'gc, S = slot::Value> {
    words: &'gc [Cell<u64>],
    /// The whole region, for reads that check what an index refers to.
    region: &'gc RegionWords,
    at: usize,
    owner: u32,
    _marker: PhantomData<(Brand<'gc>, fn() -> S)>,
}

impl<S> Clone for Slots<'_, S> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<S> Copy for Slots<'_, S> {}

impl<'gc> Slots<'gc, slot::u64> {
    /// The words themselves: plain words refer to nothing, so writing them takes no barrier.
    #[inline]
    pub fn words(self) -> &'gc [Cell<u64>] {
        self.words
    }
}

impl<'gc, S: Item> Slots<'gc, S> {
    pub fn len(self) -> usize {
        self.words.len()
    }

    pub fn is_empty(self) -> bool {
        self.words.is_empty()
    }

    #[inline]
    pub fn get(self, i: usize) -> S::Out<'gc> {
        S::load(self.region, self.words[i].get())
    }

    #[inline]
    pub fn set(self, mc: &Mutation<'gc>, i: usize, value: S::In<'gc>) {
        let word = S::store(value);
        self.words[i].set(word);
        let slot = self.at + i;
        match S::REFS {
            Refs::None => {}
            Refs::Values => mc.heap.barrier(slot, self.owner, word),
            Refs::Members if word != 0 => mc.heap.barrier_ref(slot, self.owner, word as u32),
            Refs::Members => {}
            Refs::Weaks => mc.heap.dirty(slot),
        }
    }

    /// The items in `range`, or `None` past the end.
    pub fn slice(self, range: Range<usize>) -> Option<Self> {
        let words = self.words.get(range.clone())?;
        Some(Slots { words, at: self.at + range.start, ..self })
    }

    /// Copies `src` in, which may overlap, with one barrier for the whole range. Panics if the
    /// lengths differ.
    pub fn copy_from(self, mc: &Mutation<'gc>, src: Self) {
        assert_eq!(self.len(), src.len(), "copy between slices of different lengths");
        let refs = S::REFS != Refs::None && src.words.iter().any(|s| S::REFS.refers(s.get()));
        if self.at > src.at {
            for (d, s) in self.words.iter().zip(src.words).rev() {
                d.set(s.get());
            }
        } else {
            for (d, s) in self.words.iter().zip(src.words) {
                d.set(s.get());
            }
        }
        if refs {
            mc.heap.barrier_range(self.at, self.words, self.owner, S::REFS);
        }
    }

    pub fn fill(self, mc: &Mutation<'gc>, value: S::In<'gc>) {
        let word = S::store(value);
        for slot in self.words {
            slot.set(word);
        }
        if S::REFS.refers(word) {
            mc.heap.barrier_range(self.at, self.words, self.owner, S::REFS);
        }
    }
}

impl<'gc> Slots<'gc> {
    /// The first `WINDOW` items, indexed by a byte modulo `WINDOW` so no access needs a bounds
    /// check.
    pub fn window(self) -> Option<Window<'gc>> {
        Some(Window { slots: self.words.first_chunk()?, at: self.at, owner: self.owner, _brand: PhantomData })
    }
}

#[derive(Clone, Copy)]
pub struct Window<'gc> {
    slots: &'gc [Cell<u64>; WINDOW],
    at: usize,
    owner: u32,
    _brand: Brand<'gc>,
}

impl<'gc> Window<'gc> {
    #[inline]
    pub fn get(self, r: u8) -> Value<'gc> {
        Value::from_bits(self.slots[usize::from(r) % WINDOW].get())
    }

    #[inline]
    pub fn set(self, mc: &Mutation<'gc>, r: u8, value: Value<'gc>) {
        let r = usize::from(r) % WINDOW;
        self.slots[r].set(value.word);
        mc.heap.barrier(self.at + r, self.owner, value.word);
    }
}

/// Host data, kept outside the region.
pub struct HostRef<'gc, T> {
    id: u32,
    generation: u32,
    _marker: PhantomData<(Brand<'gc>, fn() -> T)>,
}

impl<T> Clone for HostRef<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for HostRef<'_, T> {}

impl<'gc, T: Any> HostRef<'gc, T> {
    /// The value, or `None` once it's been freed: a stale reference never reads the value that
    /// took its slot. While the `Ref` is held, `Mutation::host` fails with `HostError::InUse`.
    #[inline]
    pub fn get(self, mc: &Mutation<'gc>) -> Option<Ref<'gc, T>> {
        self.erase().downcast_ref(mc)
    }

    /// The same reference, with its type left to be checked on each read.
    pub fn erase(self) -> AnyHostRef<'gc> {
        AnyHostRef { id: self.id, generation: self.generation, _brand: PhantomData }
    }

    /// See [`AnyHostRef::set_owned_bytes`].
    pub fn set_owned_bytes(self, mc: &Mutation<'gc>, bytes: usize) -> Result<(), HostError> {
        self.erase().set_owned_bytes(mc, bytes)
    }

    /// The word a field declared in `Desc::hosts` holds: the slot's generation, and its id plus
    /// one so that 0 is none.
    pub fn to_word(self) -> u64 {
        self.erase().to_word()
    }
}

impl<T> fmt::Debug for HostRef<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("HostRef").field("id", &self.id).field("generation", &self.generation).finish()
    }
}

impl<'gc, T: Any> From<HostRef<'gc, T>> for AnyHostRef<'gc> {
    fn from(host: HostRef<'gc, T>) -> Self {
        host.erase()
    }
}

/// A reference to a host value of any type, for a field that can hold several. Each read checks
/// the type, and like [`HostRef`], a stale reference reads nothing.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct AnyHostRef<'gc> {
    id: u32,
    generation: u32,
    _brand: Brand<'gc>,
}

impl<'gc> AnyHostRef<'gc> {
    /// The value, or `None` once it's been freed.
    #[inline]
    fn value(self, mc: &Mutation<'gc>) -> Option<Ref<'gc, dyn Any>> {
        let hosts = mc.heap.m.hosts.try_borrow().ok()?;
        Ref::filter_map(hosts, |hosts| {
            let slot = hosts.get(self.id as usize).filter(|s| s.generation == self.generation)?;
            slot.value.as_deref()
        })
        .ok()
    }

    /// Whether the value is alive and a `T`.
    pub fn is<T: Any>(self, mc: &Mutation<'gc>) -> bool {
        self.value(mc).is_some_and(|v| (*v).is::<T>())
    }

    /// The value, if it's alive and a `T`. While the `Ref` is held, `Mutation::host` fails with
    /// `HostError::InUse`.
    #[inline]
    pub fn downcast_ref<T: Any>(self, mc: &Mutation<'gc>) -> Option<Ref<'gc, T>> {
        Ref::filter_map(self.value(mc)?, |v| v.downcast_ref::<T>()).ok()
    }

    /// Counts `bytes` the value owns outside the arena, such as a `String`'s characters, in place
    /// of what was counted before, until the value is freed. Call it again whenever that memory
    /// grows or shrinks. Growing fails as an allocation would, failing the step, and counts
    /// nothing; shrinking gives the difference back at once. A freed value's reference does
    /// nothing. Fails with `HostError::InUse` while a `Ref` from a read is held.
    pub fn set_owned_bytes(self, mc: &Mutation<'gc>, bytes: usize) -> Result<(), HostError> {
        let m = mc.heap.m;
        let mut hosts = m.hosts.try_borrow_mut().map_err(|_| HostError::InUse)?;
        let Some(slot) = hosts.get_mut(self.id as usize).filter(|s| s.generation == self.generation && s.value.is_some()) else {
            return Ok(());
        };
        if bytes > slot.owned {
            m.budget.charge(bytes - slot.owned)?;
        } else {
            m.budget.refund(slot.owned - bytes);
        }
        m.host_bytes.set(m.host_bytes.get() - slot.owned + bytes);
        slot.cost = slot.cost - slot.owned + bytes;
        slot.owned = bytes;
        Ok(())
    }

    /// A typed reference, if the value is alive and a `T`.
    pub fn downcast<T: Any>(self, mc: &Mutation<'gc>) -> Option<HostRef<'gc, T>> {
        self.is::<T>(mc).then_some(self.assume())
    }

    /// Typed without checking: `HostRef::get` checks on every read.
    fn assume<T>(self) -> HostRef<'gc, T> {
        HostRef { id: self.id, generation: self.generation, _marker: PhantomData }
    }

    /// The word a host field holds: see [`HostRef::to_word`].
    pub fn to_word(self) -> u64 {
        u64::from(self.generation) << 32 | (u64::from(self.id) + 1)
    }
}

fn host_parts(word: u64) -> Option<(u32, u32)> {
    Some(((word as u32).checked_sub(1)?, (word >> 32) as u32))
}

struct HostSlot {
    generation: u32,
    marked: bool,
    /// What the value is charged, refunded when it's freed: its size, `HOST_COST`, and `owned`.
    cost: usize,
    /// Bytes the value owns outside the arena, as `AnyHostRef::set_owned_bytes` last set them.
    owned: usize,
    value: Option<Box<dyn Any>>,
}

/// What a host value is charged beyond its size: its slot, and the box's header.
const HOST_COST: usize = 32;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum HostError {
    /// A `Ref` from `HostRef::get` is still held.
    InUse,
    OutOfMemory,
}

impl From<OutOfMemory> for HostError {
    fn from(_: OutOfMemory) -> Self {
        Self::OutOfMemory
    }
}

/// A table that grows a chunk at a time, so an arena pays only for the entries it uses.
/// `C * N` entries, the first `C` made up front and the rest a chunk at a time. Indexing with
/// a `u16` when that's 65536 needs no bounds check.
struct Chunked<T, const C: usize, const N: usize> {
    first: Box<[T; C]>,
    /// The chunks after the first; the slot for the first is unused.
    chunks: Box<[OnceCell<Box<[T; C]>>; N]>,
}

impl<T: Default, const C: usize, const N: usize> Chunked<T, C, N> {
    fn new() -> Self {
        let chunks: Box<[_]> = (0..N).map(|_| OnceCell::new()).collect();
        Self { first: Self::chunk(), chunks: chunks.try_into().ok().expect("N chunks") }
    }

    fn chunk() -> Box<[T; C]> {
        Box::new(std::array::from_fn(|_| T::default()))
    }

    #[inline]
    fn get(&self, i: usize) -> Option<&T> {
        if i < C {
            return Some(&self.first[i]);
        }
        Some(&self.chunks.get(i / C)?.get()?[i % C])
    }

    fn get_or_grow(&self, i: usize) -> Option<&T> {
        if i < C {
            return Some(&self.first[i]);
        }
        Some(&self.chunks.get(i / C)?.get_or_init(Self::chunk)[i % C])
    }
}

#[derive(Default)]
struct Page {
    starts: [Cell<u64>; PAGE / 64],
    marks: [Cell<u64>; PAGE / 64],
    /// Lines holding marked objects, built while marking.
    lines: Cell<u128>,
    /// Lines the allocator can't use: `lines` as of the last sweep.
    used: Cell<u128>,
    cards: Cell<u32>,
    evacuating: Cell<bool>,
    /// Swept since the last cycle's marking ended.
    swept: Cell<bool>,
    /// Holds part of an object larger than a page, which starts on this page: it isn't
    /// evacuated, and a dirty card finds the object's header without scanning back to it.
    large: Cell<Option<u32>>,
    /// Given back to the system while free.
    released: Cell<bool>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Phase {
    Idle,
    Marking,
    /// Marking is done; pages are swept in later slices, or before the allocator uses them.
    Sweeping,
}

/// A collection's work lists.
#[derive(Default)]
struct Work {
    gray: Vec<u32>,
    /// Slots that refer to objects on pages being evacuated, as (object, word in it).
    fixups: Vec<(u32, u32)>,
    /// Objects with weak fields or items that were traced.
    holders: Vec<u32>,
    /// Runs of weak items on dirty cards, which a minor collection clears without the rest of
    /// their object.
    weak_runs: Vec<(u32, u32)>,
    /// Objects with ephemerons that were traced.
    ephemerons: Vec<u32>,
}

/// Everything but the words.
struct Meta {
    pages: Box<[Page]>,
    /// Pages handed out, from the start of the region. Those not released are charged.
    used: Cell<usize>,
    budget: Budget,
    /// The hole being allocated into. While failures are injected, `end` is kept at `cursor`
    /// so every allocation takes the slow path, which counts it.
    cursor: Cell<usize>,
    end: Cell<usize>,
    hole_end: Cell<usize>,
    /// The next line to look for a hole from, as `page * LINES + line`.
    scan: Cell<usize>,
    /// Where evacuation copies to.
    to_cursor: Cell<usize>,
    to_end: Cell<usize>,
    /// Bytes allocated since the last collection.
    young: Cell<usize>,
    /// Pages holding something as of the last sweep.
    occupied: Cell<usize>,
    /// Pages charged for: handed out and not given back.
    committed: Cell<usize>,
    /// Pages before this are swept.
    sweep_cursor: Cell<usize>,
    /// A collection swept everything since free pages were last given back.
    settle: Cell<bool>,
    nursery: usize,
    /// A major cycle starts once the pages in use reach this many bytes.
    threshold: Cell<usize>,
    phase: Cell<Phase>,
    /// Whether this cycle evacuates the pages flagged at its start.
    evacuating: Cell<bool>,
    evacuate_all: Cell<bool>,
    /// Fixed type numbers count up from 0, and the rest down from the top.
    descs: Chunked<Cell<Option<&'static Desc>>, 256, { TYPES / 256 }>,
    /// One past the highest fixed number in use.
    low: Cell<usize>,
    /// The next number for a type without a fixed one.
    next: Cell<usize>,
    /// Type numbers of descriptors, by [`cache_slot`] of their types.
    cache: [Cell<Option<(TypeId, u16)>>; 64],
    roots: Box<[Cell<u64>]>,
    stacks: RefCell<Vec<Rc<StackRecord>>>,
    handles: RefCell<Vec<Rc<RootRecord>>>,
    /// Tells arenas apart, for handles that live outside them.
    id: u64,
    hosts: RefCell<Vec<HostSlot>>,
    free_hosts: RefCell<Vec<u32>>,
    /// Freed by the last collection, dropped once it has returned.
    dead_hosts: RefCell<Vec<Box<dyn Any>>>,
    frozen: FrozenTable,
    work: RefCell<Work>,
    /// What the work lists and tables outside the region were last charged.
    tables: Cell<usize>,
    /// A cycle slice of this many bytes after every step, for testing barriers.
    stress: Cell<Option<usize>>,
    /// Bytes of work a running cycle does per byte steps allocate.
    pace: Cell<usize>,
    /// Work steps owe the running cycle, done once it reaches `MIN_SLICE`.
    debt: Cell<usize>,
    /// What `made` reaches when the step owes the collector work, as of the step's start.
    step_end: Cell<usize>,
    /// Work done so far in this cycle, and what the last one took in all.
    cycle_work: Cell<usize>,
    last_work: Cell<usize>,
    collections: Cell<u64>,
    minors: Cell<u64>,
    /// Collections that moved objects, which identity tables rehash after.
    evacuations: Cell<u64>,
    /// What live host values are charged.
    host_bytes: Cell<usize>,
    /// The generation new host slots start at: past what any dropped slot reached, so a stale
    /// reference to a dropped slot never reads a value made in its place.
    host_floor: Cell<u32>,
}

#[derive(Clone, Copy)]
struct Heap<'a> {
    words: &'a [Cell<u64>; WORDS + SLACK],
    m: &'a Meta,
}

/// Wraps an index into the region, so indexing it needs no bounds check: a bad index reads
/// some other word, as a forged one would anyway. Small offsets past it land in `SLACK`.
#[inline]
fn mask(i: usize) -> usize {
    i & (WORDS - 1)
}

const MIN_THRESHOLD: usize = 64 << 10;

impl Meta {
    /// The heap's size as pacing sees it: the pages in use, and what live host values and old
    /// frozen values are charged, since only a major collection frees those.
    fn paced_bytes(&self) -> usize {
        self.occupied.get() * PAGE * 8 + self.host_bytes.get() + self.frozen.live()
    }

    /// What a major cycle started now should take: a quarter more than the last one did, or
    /// before there's been one, tracing every occupied page and sweeping every page in use.
    fn cycle_work(&self) -> usize {
        match self.last_work.get() {
            0 => self.occupied.get() * PAGE * 8 + self.used.get() * SWEEP_COST,
            last => last + last / 4,
        }
    }

    /// What steps can allocate before they draw on the reserve. Committed pages nothing is on
    /// don't count against it: they're kept for new objects to fill. Objects made since the
    /// last sweep do, as they fill them.
    fn room(&self) -> usize {
        let pages = (self.committed.get() - self.occupied.get().min(self.committed.get())) * PAGE_COST;
        self.budget.room_past(self.budget.used().saturating_sub(pages) + self.young.get())
    }

    /// Whether a major cycle has to start now to be done, paced at up to `MAX_PACE`, before the
    /// room runs out: past that the reserve forces a full collection, one pause as long as the
    /// whole cycle. Starting as late as that frees as much as a full collection would. A slice's
    /// worth of room is kept for what the steps in between allocate.
    fn short_of_room(&self) -> bool {
        self.room() <= self.cycle_work() / MAX_PACE + MIN_SLICE
    }

    /// What steps have made: bytes of objects and frozen values since the last collection, and
    /// host values.
    fn made(&self) -> usize {
        self.young_bytes() + self.host_bytes.get()
    }

    /// Bytes of objects and frozen values made since the last collection, which a minor one may
    /// free.
    fn young_bytes(&self) -> usize {
        self.young.get() + self.frozen.young_bytes()
    }

    /// What a step can make before it owes the collector work that ending it does, as
    /// [`Arena::step`] paces it: a minor collection once the nursery fills, a major cycle once
    /// one's due, or a slice of the one running.
    fn step_allowance(&self) -> usize {
        if self.phase.get() != Phase::Idle {
            return (MIN_SLICE - self.debt.get().min(MIN_SLICE)).div_ceil(self.pace.get().max(1));
        }
        let nursery = self.nursery.saturating_sub(self.young_bytes());
        let threshold = self.threshold.get().saturating_sub(self.paced_bytes());
        let room = self.room().saturating_sub(self.cycle_work() / MAX_PACE + MIN_SLICE);
        nursery.min(threshold).min(room)
    }
}

/// Gives back most of the room a table no longer needs, keeping some so it doesn't regrow at once.
fn shrink<T>(table: &mut Vec<T>) {
    if table.capacity() > 4 * table.len() + 64 {
        table.shrink_to(2 * table.len() + 16);
    }
}
/// What a committed page is charged: its words and its bookkeeping.
const PAGE_COST: usize = PAGE * 8 + size_of::<Page>();
/// A page's sweep counts as this many bytes of slice work.
const SWEEP_COST: usize = PAGE;
const MIN_SLICE: usize = 64 << 10;
const STEP_MUL: usize = 2;
const MAX_PACE: usize = 16;
/// Dead host values, and dead frozen values, freed after a step at most.
const FREE_BATCH: usize = 1024;

pub struct Arena {
    memory: Region,
    meta: Meta,
}

impl Arena {
    /// An arena allowed `limit` bytes, with `roots` value slots. The table of pages, made up
    /// front for twice the limit, isn't charged; the roots are. Objects in the region take at
    /// most [`REGION`] bytes whatever the limit; frozen and host values can use the rest.
    ///
    /// # Panics
    ///
    /// If the system won't reserve the region's address space. [`Arena::try_new`] fails then
    /// instead.
    pub fn new(limit: usize, roots: usize) -> Self {
        Self::try_new(limit, roots).expect("reserve the arena's memory")
    }

    /// Like [`Arena::new`], failing if the system won't reserve the region's address space.
    pub fn try_new(limit: usize, roots: usize) -> Result<Self, OutOfMemory> {
        let memory = Region::new(WORDS + SLACK).ok_or(OutOfMemory)?;
        // Page 0 holds nothing, so index 0 can mean none. Twice the limit leaves evacuation room
        // to copy everything.
        let pages = (limit / (PAGE * 8)).clamp(1, PAGES / 2 - 1);
        let meta = Meta {
            pages: (0..2 * pages + 2).map(|_| Page::default()).collect(),
            used: Cell::new(1),
            budget: Budget::new(limit),
            cursor: Cell::new(0),
            end: Cell::new(0),
            hole_end: Cell::new(0),
            scan: Cell::new(LINES),
            to_cursor: Cell::new(0),
            to_end: Cell::new(0),
            young: Cell::new(0),
            occupied: Cell::new(0),
            committed: Cell::new(0),
            sweep_cursor: Cell::new(0),
            settle: Cell::new(false),
            nursery: (limit / 8).clamp(64 << 10, 4 << 20),
            threshold: Cell::new(MIN_THRESHOLD.min(pages * PAGE * 8 / 2)),
            phase: Cell::new(Phase::Idle),
            evacuating: Cell::new(false),
            evacuate_all: Cell::new(false),
            descs: Chunked::new(),
            low: Cell::new(1),
            next: Cell::new(TYPES - 1),
            cache: [const { Cell::new(None) }; 64],
            // One more, after the program's, for the arena's intern table.
            roots: vec![Cell::new(Value::NIL.word); roots + 1].into_boxed_slice(),
            stacks: RefCell::new(Vec::new()),
            handles: RefCell::new(Vec::new()),
            id: NEXT_ARENA.fetch_add(1, Ordering::Relaxed),
            hosts: RefCell::new(Vec::new()),
            free_hosts: RefCell::new(Vec::new()),
            dead_hosts: RefCell::new(Vec::new()),
            host_bytes: Cell::new(0),
            host_floor: Cell::new(0),
            frozen: FrozenTable::new(limit),
            work: RefCell::new(Work::default()),
            tables: Cell::new(0),
            stress: Cell::new(None),
            pace: Cell::new(STEP_MUL),
            step_end: Cell::new(0),
            debt: Cell::new(0),
            cycle_work: Cell::new(0),
            last_work: Cell::new(0),
            collections: Cell::new(0),
            minors: Cell::new(0),
            evacuations: Cell::new(0),
        };
        if let Some(boxed) = meta.descs.get_or_grow(0) {
            boxed.set(Some(&Boxed::DESC));
        }
        meta.budget.force((roots + 1) * 8);
        Ok(Self { memory, meta })
    }

    fn heap(&mut self) -> Heap<'_> {
        let words = self.memory.words().first_chunk().expect("the region is WORDS + SLACK long");
        Heap { words, m: &self.meta }
    }

    /// After every collection entry point: gives back free pages, and runs the destructors of
    /// hosts freed, outside the collector.
    ///
    /// Frees at most `free` dead host values and as many dead frozen ones, the rest later: a cycle
    /// can leave a great many, and freeing them all at once would be a pause of its own.
    fn finish(&mut self, free: usize) {
        self.settle();
        let dead = {
            let mut dead = self.meta.dead_hosts.borrow_mut();
            let keep = dead.len().saturating_sub(free);
            dead.split_off(keep)
        };
        drop(dead);
        let m = &mut self.meta;
        m.frozen.free_dead(&m.budget, free);
        self.charge_tables();
    }

    /// Charges the work lists and tables outside the region for what they hold now. They grow
    /// within collections, which can't fail, so they're charged after.
    fn charge_tables(&self) {
        let m = &self.meta;
        let work = m.work.borrow();
        let bytes = (work.gray.capacity() + work.holders.capacity() + work.ephemerons.capacity()) * size_of::<u32>()
            + (work.fixups.capacity() + work.weak_runs.capacity()) * size_of::<(u32, u32)>()
            + m.hosts.borrow().capacity() * size_of::<HostSlot>()
            + m.free_hosts.borrow().capacity() * size_of::<u32>()
            + m.dead_hosts.borrow().capacity() * size_of::<Box<dyn Any>>()
            + m.stacks.borrow().capacity() * size_of::<Rc<StackRecord>>()
            + m.handles.borrow().capacity() * size_of::<Rc<RootRecord>>()
            + m.frozen.table_bytes();
        let before = m.tables.replace(bytes);
        if bytes > before {
            m.budget.force(bytes - before);
        } else {
            m.budget.refund(before - bytes);
        }
    }

    /// Once a collection has swept everything: keeps a nursery's worth of free pages, which
    /// the next steps would fill again, gives the rest back to the system, and trims the pages
    /// handed out to the last one kept.
    fn settle(&mut self) {
        let m = &self.meta;
        if m.phase.get() != Phase::Idle || !m.settle.replace(false) {
            return;
        }
        let used = m.used.get();
        let mut warm = m.nursery / (PAGE * 8);
        let mut run: Option<usize> = None;
        for p in 1..=used {
            let release = m.pages[..used].get(p).is_some_and(|page| {
                if page.used.get() != 0 || page.released.get() {
                    return false;
                }
                if warm > 0 {
                    warm -= 1;
                    return false;
                }
                true
            });
            match (release, run) {
                (true, None) => run = Some(p),
                (false, Some(first)) => {
                    // Only pages the system wholly took back stop being charged; the rest stay
                    // committed.
                    let words = self.memory.release(first * PAGE..p * PAGE);
                    let gone = words.start.div_ceil(PAGE).max(first)..(words.end / PAGE).min(p);
                    for page in m.pages.get(gone).unwrap_or_default() {
                        page.released.set(true);
                        m.budget.refund(PAGE_COST);
                        m.committed.set(m.committed.get() - 1);
                    }
                    run = None;
                }
                _ => {}
            }
        }
        // Pages past the last one still committed are handed out again as fresh ones.
        let used = (1..used).rev().find(|&p| !m.pages[p].released.get()).map_or(1, |p| p + 1);
        m.used.set(used);
        m.occupied.set(m.pages[..used].iter().filter(|p| p.used.get() != 0).count());
    }

    pub fn mutate<R>(&mut self, f: impl for<'gc> FnOnce(&Mutation<'gc>) -> R) -> R {
        let m = &self.meta;
        m.step_end.set(m.made().saturating_add(m.step_allowance()));
        f(&Mutation { heap: self.heap(), _brand: PhantomData })
    }

    /// Like `mutate`, then paces collection: a minor collection once the nursery fills, and a
    /// major cycle once the pages in use, with what live host and frozen values are charged, reach
    /// the threshold, twice what the last cycle left, or sooner if the room left under the reserve
    /// would run out before the cycle is done. Each step owes the cycle twice what it allocated,
    /// or more when room is short, paid in slices of at least `MIN_SLICE`. Dead host and frozen
    /// values are freed a batch after each step.
    ///
    /// If `f` drew on the reserve, a full collection runs instead. If an allocation failed,
    /// even one `f` went on without, the result is dropped, a full collection runs, and the
    /// step fails. Whatever `f` did before the failure stays done, so the caller picks up from
    /// there: an interpreter runs the failed instruction again.
    pub fn step<R>(&mut self, f: impl for<'gc> FnOnce(&Mutation<'gc>) -> R) -> Result<R, OutOfMemory> {
        self.meta.budget.clear_failed();
        let before = self.meta.made();
        let result = self.mutate(f);
        if self.meta.budget.failed() {
            drop(result);
            self.collect();
            return Err(OutOfMemory);
        }
        if self.meta.budget.due() {
            self.collect();
            return Ok(result);
        }
        let allocated = self.meta.made().saturating_sub(before);
        if let Some(work) = self.meta.stress.get() {
            self.heap().minor();
            self.heap().start();
            self.heap().work(work);
            self.finish(FREE_BATCH);
            return Ok(result);
        }
        let m = &self.meta;
        if m.phase.get() == Phase::Idle && m.young_bytes() >= m.nursery {
            self.heap().minor();
        }
        let m = &self.meta;
        if m.phase.get() == Phase::Idle && (m.paced_bytes() >= m.threshold.get() || m.short_of_room()) {
            if m.young_bytes() > 0 {
                self.heap().minor();
            }
            self.heap().start();
            // Fast enough to be done before the room runs out.
            let m = &self.meta;
            m.pace.set(m.cycle_work().div_ceil(m.room().max(1)).max(STEP_MUL));
            m.debt.set(0);
        }
        let m = &self.meta;
        if m.phase.get() != Phase::Idle {
            let debt = m.debt.get().saturating_add(allocated.saturating_mul(m.pace.get()));
            m.debt.set(debt);
            if debt >= MIN_SLICE {
                m.debt.set(0);
                self.heap().work(debt);
            }
        }
        self.finish(FREE_BATCH);
        Ok(result)
    }

    /// Finishes any cycle in progress, then runs a full one.
    pub fn collect(&mut self) {
        self.heap().work(usize::MAX);
        self.heap().start();
        self.heap().work(usize::MAX);
        self.finish(usize::MAX);
        self.meta.budget.clear_due();
    }

    /// Collects young objects only, if no major cycle is running.
    pub fn collect_minor(&mut self) {
        self.heap().minor();
        self.finish(usize::MAX);
    }

    /// Starts a cycle if none is running, then does about `work` bytes of it. Like a step, it
    /// frees only a batch of the dead host and frozen values.
    pub fn collect_slice(&mut self, work: usize) {
        self.heap().start();
        self.heap().work(work);
        self.finish(FREE_BATCH);
    }

    pub fn phase(&self) -> Phase {
        self.meta.phase.get()
    }

    pub fn collections(&self) -> (u64, u64) {
        (self.meta.collections.get(), self.meta.minors.get())
    }

    /// Bytes of pages handed out so far: the most the arena has used at once.
    pub fn pages_bytes(&self) -> usize {
        (self.meta.used.get() - 1) * PAGE * 8
    }

    /// Bytes of pages handed out and not given back: about what the arena holds in memory.
    pub fn committed_bytes(&self) -> usize {
        let m = &self.meta;
        let pages = &m.pages[1..m.used.get()];
        (pages.len() - pages.iter().filter(|p| p.released.get()).count()) * PAGE * 8
    }

    /// Bytes of pages holding something, as of the last sweep.
    pub fn occupied_bytes(&self) -> usize {
        self.meta.occupied.get() * PAGE * 8
    }

    /// Objects marked and not yet swept away: after [`Arena::collect`], the live ones.
    pub fn objects(&self) -> usize {
        let pages = &self.meta.pages[..self.meta.used.get()];
        pages.iter().flat_map(|p| p.starts.iter().zip(&p.marks)).map(|(s, k)| (s.get() & k.get()).count_ones() as usize).sum()
    }

    pub fn hosts(&self) -> usize {
        self.meta.hosts.borrow().len()
    }

    /// Frozen values not yet freed, including any a collection found dead that the next one
    /// frees.
    pub fn frozen_values(&self) -> usize {
        self.meta.frozen.count()
    }

    /// Bytes charged against the limit: committed pages, roots, stacks, host values, the
    /// collector's tables, and `Charge`s.
    pub fn used(&self) -> usize {
        self.meta.budget.used()
    }

    pub fn peak(&self) -> usize {
        self.meta.budget.peak()
    }

    pub fn limit(&self) -> usize {
        self.meta.budget.limit()
    }

    /// Keeps the last `bytes` under the limit for a step to finish in once the rest is used.
    /// Optional allocations don't draw on it. It starts at a sixteenth of the limit.
    pub fn set_reserve(&mut self, bytes: usize) {
        self.meta.budget.set_reserve(bytes);
    }

    /// Testing: lets `allocations` more allocations through, then fails the next one, once.
    /// Objects, host values and stacks count.
    pub fn fail_after(&mut self, allocations: Option<u64>) {
        let m = &self.meta;
        m.budget.fail_after(allocations);
        m.end.set(if m.budget.injecting() { m.cursor.get() } else { m.hole_end.get() });
    }

    /// Testing: a minor collection and a cycle slice of `work` bytes after every step.
    pub fn set_stress(&mut self, work: Option<usize>) {
        self.meta.stress.set(work);
    }

    pub fn set_evacuate_all(&mut self, on: bool) {
        self.meta.evacuate_all.set(on);
    }
}

pub struct Mutation<'gc> {
    heap: Heap<'gc>,
    _brand: Brand<'gc>,
}

impl<'gc> Mutation<'gc> {
    /// Fields by their words, beneath `objects!` constructors.
    #[doc(hidden)]
    #[inline]
    pub fn alloc<T: Object, const N: usize>(&self, fields: [u64; N]) -> Result<Gc<'gc, T>, OutOfMemory> {
        self.heap.alloc_fixed(&T::DESC, &fields).map(Gc::new)
    }

    /// `alloc_items` with zero items, the zero word reading as fixnum 0, none or 0: small
    /// enough to inline, for objects made often with few items.
    #[doc(hidden)]
    #[inline]
    pub fn alloc_zeroed<T: Object, const N: usize>(&self, fields: [u64; N], len: usize) -> Result<Gc<'gc, T>, OutOfMemory> {
        self.heap.alloc_zeroed(&T::DESC, &fields, len).map(Gc::new)
    }

    #[doc(hidden)]
    pub fn alloc_items<T: Object, const N: usize>(
        &self,
        fields: [u64; N],
        len: usize,
        item: Value<'gc>,
    ) -> Result<Gc<'gc, T>, OutOfMemory> {
        self.heap.alloc(&T::DESC, &fields, len, item.word).map(Gc::new)
    }

    #[inline]
    pub fn type_tag<T: Object>(&self) -> Option<TypeTag<'gc, T>> {
        let ty = match T::DESC.number {
            Some(ty) => ty,
            None => self.heap.type_index(&T::DESC)?,
        };
        Some(TypeTag { ty, _marker: PhantomData })
    }

    pub fn root(&self, i: usize) -> Value<'gc> {
        let roots = &self.heap.m.roots;
        Value::from_bits(roots[..roots.len() - 1][i].get())
    }

    pub fn set_root(&self, i: usize, value: Value<'gc>) {
        let roots = &self.heap.m.roots;
        roots[..roots.len() - 1][i].set(value.word);
    }

    /// The root that holds the arena's intern table, once there is one.
    pub(crate) fn interned(&self) -> &Cell<u64> {
        self.heap.m.roots.last().expect("the arena has a root for its intern table")
    }

    /// Charged its size, plus `HOST_COST`. Memory the value owns elsewhere, such as a
    /// `String`'s bytes, can be counted with [`HostRef::set_owned_bytes`].
    pub fn host<T: Any>(&self, value: T) -> Result<HostRef<'gc, T>, HostError> {
        let m = self.heap.m;
        let mut hosts = m.hosts.try_borrow_mut().map_err(|_| HostError::InUse)?;
        m.budget.count_allocation()?;
        let cost = size_of::<T>() + HOST_COST;
        m.budget.ensure(cost)?;
        // Made while marking, it lives through the cycle, as objects do.
        let marked = m.phase.get() == Phase::Marking;
        let value: Box<dyn Any> = Box::new(value);
        let id = match m.free_hosts.borrow_mut().pop() {
            Some(id) => id,
            None => {
                let Some(id) = u32::try_from(hosts.len()).ok().filter(|&id| id < u32::MAX) else {
                    return Err(m.budget.fail().into());
                };
                if hosts.len() == hosts.capacity() {
                    // Charged as it grows, so growing fails as an allocation would.
                    let more = hosts.capacity().max(16);
                    m.budget.ensure(cost + more * size_of::<HostSlot>())?;
                    let before = hosts.capacity();
                    hosts.reserve_exact(more);
                    let grown = (hosts.capacity() - before) * size_of::<HostSlot>();
                    m.budget.force(grown);
                    m.tables.set(m.tables.get() + grown);
                }
                hosts.push(HostSlot { generation: m.host_floor.get(), marked: false, cost: 0, owned: 0, value: None });
                id
            }
        };
        m.budget.force(cost);
        let slot = &mut hosts[id as usize];
        slot.value = Some(value);
        slot.marked = marked;
        slot.cost = cost;
        slot.owned = 0;
        m.host_bytes.set(m.host_bytes.get() + cost);
        Ok(HostRef { id, generation: slot.generation, _marker: PhantomData })
    }

    /// `value` outside the region, readable as `&'gc T` and never changed: what a field of
    /// `Frozen<T>` holds. Store it in an object this step: a value nothing holds is freed by the
    /// next collection.
    pub fn frozen<T: Any>(&self, value: T) -> Result<FrozenRef<'gc, T>, OutOfMemory> {
        self.frozen_owning(value, 0)
    }

    /// Like [`Mutation::frozen`], also charged `bytes` that `value` owns outside the arena, such
    /// as a string's characters, until it's freed.
    pub fn frozen_owning<T: Any>(&self, value: T, bytes: usize) -> Result<FrozenRef<'gc, T>, OutOfMemory> {
        let m = self.heap.m;
        m.frozen.alloc(&m.budget, false, value, bytes).map(FrozenRef::new)
    }

    /// Runs allocations the caller can do without, such as growing a buffer by more than it
    /// needs: failing them doesn't fail the step, and they don't draw on the reserve.
    pub fn optional<R>(&self, f: impl FnOnce() -> Result<R, OutOfMemory>) -> Result<R, OutOfMemory> {
        self.heap.m.budget.optional(f)
    }

    /// Fails the step as a failed allocation would, for a request too large to even size.
    pub fn out_of_memory(&self) -> OutOfMemory {
        self.heap.m.budget.fail()
    }

    /// Whether an allocation has drawn on the reserve, so a full collection is due. An
    /// interpreter checks it between instructions and ends the step, which collects.
    pub fn collection_due(&self) -> bool {
        self.heap.m.budget.due()
    }

    /// Whether the step has made enough that [`Arena::step`] owes the collector work once it
    /// ends, or a full collection is due. An interpreter checks it after it allocates, and ends
    /// the step at the next place it can go on from, so collection keeps up.
    pub fn step_due(&self) -> bool {
        let m = self.heap.m;
        m.made() >= m.step_end.get() || m.budget.due()
    }

    /// A charge of nothing yet against the budget, for memory kept outside the arena.
    pub fn charge(&self) -> Charge<'gc> {
        Charge::new(self)
    }

    /// Whether `bytes` more fit, as an allocation of them would check.
    pub fn ensure(&self, bytes: usize) -> Result<(), OutOfMemory> {
        self.heap.m.budget.ensure(bytes)
    }

    pub fn used(&self) -> usize {
        self.heap.m.budget.used()
    }

    pub fn limit(&self) -> usize {
        self.heap.m.budget.limit()
    }
}

/// Where `t`'s type number is cached: by what its hash writes, which is a hash already.
#[inline]
fn cache_slot(t: TypeId) -> usize {
    struct Bits(u64);
    impl std::hash::Hasher for Bits {
        fn finish(&self) -> u64 {
            self.0
        }
        fn write(&mut self, bytes: &[u8]) {
            for &b in bytes {
                self.0 = self.0.rotate_left(8) ^ u64::from(b);
            }
        }
        fn write_u64(&mut self, n: u64) {
            self.0 ^= n;
        }
    }
    let mut bits = Bits(0);
    std::hash::Hash::hash(&t, &mut bits);
    (bits.0 as usize) % 64
}

impl<'a> Heap<'a> {
    #[inline]
    fn type_index(self, desc: &'static Desc) -> Option<u16> {
        match self.m.cache[cache_slot(desc.type_id)].get() {
            Some((t, ty)) if t == desc.type_id => Some(ty),
            _ => self.type_index_slow(desc),
        }
    }

    #[inline(never)]
    fn type_index_slow(self, desc: &'static Desc) -> Option<u16> {
        let (m, next) = (self.m, self.m.next.get());
        let same = |d: &'static Desc| d.type_id == desc.type_id;
        let ty = if let Some(ty) = desc.number {
            let ty = usize::from(ty);
            if ty > next {
                return None;
            }
            let slot = m.descs.get_or_grow(ty)?;
            match slot.get() {
                None => slot.set(Some(desc)),
                Some(d) if same(d) => {}
                Some(_) => panic!("two types have type number {ty}: declare one objects! group `after` the other"),
            }
            m.low.set(m.low.get().max(ty + 1));
            ty
        } else {
            match (next + 1..TYPES).find(|&i| m.descs.get(i).and_then(Cell::get).is_some_and(same)) {
                Some(ty) => ty,
                None if next < m.low.get() => return None,
                None => {
                    m.descs.get_or_grow(next)?.set(Some(desc));
                    m.next.set(next - 1);
                    next
                }
            }
        };
        self.m.cache[cache_slot(desc.type_id)].set(Some((desc.type_id, ty as u16)));
        Some(ty as u16)
    }

    fn desc(self, header: u64) -> Option<&'static Desc> {
        self.m.descs.get((header & TYPE_BITS) as usize)?.get()
    }

    #[inline]
    fn alloc(self, desc: &'static Desc, fields: &[u64], len: usize, item: u64) -> Result<u32, OutOfMemory> {
        let ty = self.type_index(desc).ok_or_else(|| self.m.budget.fail())?;
        let len = if desc.items == Items::None { 0 } else { len };
        if len > u32::MAX as usize {
            return Err(self.m.budget.fail());
        }
        let size = 1 + desc.fields as usize + len;
        let at = self.reserve(size)?;
        let object = &self.words[at..at + size];
        object[0].set(u64::from(ty) | (len as u64) << 32);
        let (head, items) = object[1..].split_at(desc.fields as usize);
        for (slot, &word) in head.iter().zip(fields.iter().chain(std::iter::repeat(&0))) {
            slot.set(word);
        }
        for slot in items {
            slot.set(item);
        }
        self.m.young.set(self.m.young.get() + size * 8);
        if self.m.phase.get() == Phase::Marking {
            self.color_marked(at);
        }
        Ok(at as u32)
    }

    #[inline(always)]
    fn alloc_zeroed(self, desc: &'static Desc, fields: &[u64], len: usize) -> Result<u32, OutOfMemory> {
        if desc.items == Items::None || len > u32::MAX as usize {
            return self.alloc(desc, fields, len, 0);
        }
        let ty = self.type_index(desc).ok_or_else(|| self.m.budget.fail())?;
        let size = 1 + desc.fields as usize + len;
        let at = self.reserve(size)?;
        let object = &self.words[at..at + size];
        object[0].set(u64::from(ty) | (len as u64) << 32);
        let (head, items) = object[1..].split_at(desc.fields as usize);
        for (slot, &word) in head.iter().zip(fields.iter().chain(std::iter::repeat(&0))) {
            slot.set(word);
        }
        for slot in items {
            slot.set(0);
        }
        self.m.young.set(self.m.young.get() + size * 8);
        if self.m.phase.get() == Phase::Marking {
            self.color_marked(at);
        }
        Ok(at as u32)
    }

    /// `alloc` without items: the common case, small enough to inline at every call site,
    /// which LLVM stops doing for `alloc` once there are a few dozen.
    #[inline(always)]
    fn alloc_fixed(self, desc: &'static Desc, fields: &[u64]) -> Result<u32, OutOfMemory> {
        let ty = self.type_index(desc).ok_or_else(|| self.m.budget.fail())?;
        let size = 1 + desc.fields as usize;
        let at = self.reserve(size)?;
        let object = &self.words[at..at + size];
        object[0].set(u64::from(ty));
        for (slot, &word) in object[1..].iter().zip(fields.iter().chain(std::iter::repeat(&0))) {
            slot.set(word);
        }
        self.m.young.set(self.m.young.get() + size * 8);
        if self.m.phase.get() == Phase::Marking {
            self.color_marked(at);
        }
        Ok(at as u32)
    }

    /// Objects made while marking are marked, and traced in case they were stored somewhere
    /// already traced.
    #[cold]
    fn color_marked(self, at: usize) {
        self.mark(at as u32, &mut self.m.work.borrow_mut());
    }

    #[inline]
    fn reserve(self, size: usize) -> Result<usize, OutOfMemory> {
        let at = self.m.cursor.get();
        let at = if at + size <= self.m.end.get() {
            self.m.cursor.set(at + size);
            at
        } else {
            self.reserve_slow(size)?
        };
        self.set_bit(at, |p| &p.starts);
        Ok(at)
    }

    #[inline(never)]
    fn reserve_slow(self, size: usize) -> Result<usize, OutOfMemory> {
        let m = self.m;
        m.budget.count_allocation()?;
        // The hole still fits it if failures are injected, or just stopped being.
        let at = m.cursor.get();
        if at + size <= m.hole_end.get() {
            m.cursor.set(at + size);
            m.end.set(if m.budget.injecting() { at + size } else { m.hole_end.get() });
            return Ok(at);
        }
        if size > PAGE - LINE {
            // Its own run of free pages, its lines claimed so nothing else is put there.
            let n = size.div_ceil(PAGE);
            let first = match self.free_run(n, false)? {
                Some(first) => first,
                None => self.fresh_pages(n)?,
            };
            self.cover_lines(first * PAGE, size, |p| &p.used);
            self.m.pages[first..first + n].iter().for_each(|p| p.large.set(Some(first as u32)));
            return Ok(first * PAGE);
        }
        loop {
            let (start, end) = match self.next_hole()? {
                Some(hole) => hole,
                None => {
                    let page = self.fresh_pages(1)?;
                    m.pages[page].used.set(u128::MAX);
                    m.scan.set((page + 1) * LINES);
                    (page * PAGE, (page + 1) * PAGE)
                }
            };
            if end - start >= size {
                m.cursor.set(start + size);
                m.hole_end.set(end);
                m.end.set(if m.budget.injecting() { start + size } else { end });
                return Ok(start);
            }
        }
    }

    /// Claims the next run of free lines in the pages handed out.
    fn next_hole(self) -> Result<Option<(usize, usize)>, OutOfMemory> {
        let mut scan = self.m.scan.get();
        while scan < self.m.used.get() * LINES {
            let (page, line) = (scan / LINES, scan % LINES);
            self.sweep_before_use(page);
            let p = &self.m.pages[page];
            let used = p.used.get();
            let free = !used & (u128::MAX << line);
            // Filling pages chosen for evacuation would undo the compaction.
            if free == 0 || p.evacuating.get() {
                scan = (page + 1) * LINES;
                continue;
            }
            self.recommit(page..page + 1)?;
            let start = free.trailing_zeros() as usize;
            let end = (used & (u128::MAX << start)).trailing_zeros() as usize;
            p.used.set(used | (u128::MAX >> (LINES - end)) & (u128::MAX << start));
            self.m.scan.set(page * LINES + end);
            return Ok(Some((page * PAGE + start * LINE, page * PAGE + end * LINE)));
        }
        self.m.scan.set(scan);
        Ok(None)
    }

    /// Charges again for pages given back to the system, before they're used.
    fn recommit(self, pages: Range<usize>) -> Result<(), OutOfMemory> {
        let pages = &self.m.pages[pages];
        let released = pages.iter().filter(|p| p.released.get()).count();
        if released > 0 {
            self.m.budget.charge(released * PAGE_COST)?;
            self.m.committed.set(self.m.committed.get() + released);
            pages.iter().for_each(|p| p.released.set(false));
        }
        Ok(())
    }

    /// The first of `n` free pages in a row among those handed out. Evacuation can't copy
    /// onto pages being evacuated.
    fn free_run(self, n: usize, evacuation: bool) -> Result<Option<usize>, OutOfMemory> {
        let mut run = 0;
        for p in 1..self.m.used.get() {
            self.sweep_before_use(p);
            let page = &self.m.pages[p];
            let free = page.used.get() == 0 && !(evacuation && page.evacuating.get());
            run = if free { run + 1 } else { 0 };
            if run == n {
                let first = p + 1 - n;
                self.recommit(first..p + 1)?;
                return Ok(Some(first));
            }
        }
        Ok(None)
    }

    fn fresh_pages(self, n: usize) -> Result<usize, OutOfMemory> {
        let first = self.m.used.get();
        if first + n > self.m.pages.len() {
            return Err(self.m.budget.fail());
        }
        self.m.budget.charge(n * PAGE_COST)?;
        self.m.committed.set(self.m.committed.get() + n);
        self.m.used.set(first + n);
        // Nothing on them is from before the cycle, so a lazy sweep has nothing to do there.
        for p in &self.m.pages[first..first + n] {
            p.swept.set(true);
            p.released.set(false);
        }
        Ok(first)
    }

    /// Pages are swept before the allocator looks at them, so it never sees stale lines.
    #[inline]
    fn sweep_before_use(self, page: usize) {
        if self.m.phase.get() == Phase::Sweeping && !self.m.pages[page].swept.get() {
            self.sweep_page(page);
        }
    }

    fn reset_allocator(self) {
        self.m.cursor.set(0);
        self.m.end.set(0);
        self.m.hole_end.set(0);
        self.m.scan.set(LINES);
        self.m.young.set(0);
    }

    #[inline]
    fn set_bit(self, i: usize, bits: impl FnOnce(&Page) -> &[Cell<u64>; PAGE / 64]) {
        let word = &bits(&self.m.pages[i / PAGE])[i % PAGE / 64];
        word.set(word.get() | 1 << (i % 64));
    }

    fn has_bit(self, i: usize, bits: impl FnOnce(&Page) -> &[Cell<u64>; PAGE / 64]) -> bool {
        self.m.pages.get(i / PAGE).is_some_and(|p| bits(p)[i % PAGE / 64].get() & 1 << (i % 64) != 0)
    }

    /// Sets the lines under `size` words at `start` in one of a page's line maps.
    fn cover_lines(self, start: usize, size: usize, lines: impl Fn(&Page) -> &Cell<u128>) {
        let (mut at, end) = (start, start + size);
        while at < end {
            let Some(page) = self.m.pages.get(at / PAGE) else { return };
            let to = end.min((at / PAGE + 1) * PAGE);
            let (first, last) = (at % PAGE / LINE, (to - 1) % PAGE / LINE);
            let lines = lines(page);
            lines.set(lines.get() | (u128::MAX >> (127 - last)) & (u128::MAX << first));
            at = to;
        }
    }

    #[inline]
    fn dirty(self, slot: usize) {
        if let Some(page) = self.m.pages.get(slot / PAGE) {
            page.cards.set(page.cards.get() | 1 << (slot % PAGE / CARD));
        }
    }

    /// Marks the host a word names, if its generation still matches.
    fn mark_host(self, word: u64) {
        let Some((id, generation)) = host_parts(word) else { return };
        if let Some(host) = self.m.hosts.borrow_mut().get_mut(id as usize).filter(|h| h.generation == generation) {
            host.marked = true;
        }
    }

    #[inline]
    fn ephemeron_at(self, slot: usize) -> Option<(Value<'a>, Value<'a>)> {
        let key = Value::from_bits(self.words[slot].get());
        (key != Value::BROKEN).then(|| (key, Value::from_bits(self.words[slot + 1].get())))
    }

    /// Neither part is shaded while marking: the value is traced once the key is found live.
    /// The cards are dirtied, so a minor collection sees both.
    #[inline]
    fn set_ephemeron_at(self, slot: usize, key: Value<'_>, value: Value<'_>) {
        self.words[slot].set(key.word);
        self.words[slot + 1].set(value.word);
        self.dirty(slot);
        self.dirty(slot + 1);
    }

    #[inline]
    fn barrier(self, slot: usize, owner: u32, word: u64) {
        if word & TAG == OBJECT {
            self.barrier_ref(slot, owner, (word >> 32) as u32);
        }
    }

    #[inline]
    fn barrier_ref(self, slot: usize, owner: u32, target: u32) {
        self.dirty(slot);
        if self.m.phase.get() == Phase::Marking && self.has_bit(owner as usize, |p| &p.marks) {
            shade(self.words, self.m, slot, owner, target);
        }
    }

    /// While marking, a store into a marked object marks its target, and if the target is to
    /// move, notes the slot to fix.
    fn shade(self, slot: usize, owner: u32, target: u32) {
        if self.has_bit(owner as usize, |p| &p.marks) {
            self.shade_marked(slot, owner, target);
        }
    }

    fn shade_marked(self, slot: usize, owner: u32, target: u32) {
        let mut work = self.m.work.borrow_mut();
        self.mark(target, &mut work);
        if self.m.evacuating.get() && self.in_evacuation(target) {
            work.fixups.push((owner, (slot - owner as usize) as u32));
        }
    }

    /// Dirties the cards under `slots`, and while marking shades what they refer to, as `refs`
    /// reads them.
    fn barrier_range(self, at: usize, slots: &[Cell<u64>], owner: u32, refs: Refs) {
        let (mut i, end) = (at, at + slots.len());
        while i < end {
            let Some(page) = self.m.pages.get(i / PAGE) else { return };
            let to = end.min((i / PAGE + 1) * PAGE);
            let (first, last) = (i % PAGE / CARD, (to - 1) % PAGE / CARD);
            page.cards.set(page.cards.get() | ((u64::MAX >> (63 - last)) & (u64::MAX << first)) as u32);
            i = to;
        }
        if self.m.phase.get() == Phase::Marking && matches!(refs, Refs::Values | Refs::Members) {
            for (k, slot) in slots.iter().enumerate() {
                if let Some(target) = refs.target(slot.get()) {
                    self.shade(at + k, owner, target);
                }
            }
        }
    }

    fn in_evacuation(self, index: u32) -> bool {
        self.m.pages.get(index as usize / PAGE).is_some_and(|p| p.evacuating.get())
    }

    // Collection.

    /// Collects young objects only. Survivors stay marked, which makes them old.
    fn minor(self) {
        if self.m.phase.get() != Phase::Idle {
            return;
        }
        let mut work = std::mem::take(&mut *self.m.work.borrow_mut());
        self.mark_roots(&mut work);
        self.scan_cards(&mut work);
        self.drain(&mut work, usize::MAX);
        self.trace_ephemerons(&mut work);
        self.clear_weaks(&mut work);
        self.m.frozen.sweep_young();
        work.holders.clear();
        work.weak_runs.clear();
        work.ephemerons.clear();
        self.sweep();
        self.reset_allocator();
        self.m.settle.set(true);
        self.m.minors.set(self.m.minors.get() + 1);
        *self.m.work.borrow_mut() = work;
    }

    /// Starts a major cycle: clears the marks and marks the roots.
    fn start(self) {
        let m = self.m;
        if m.phase.get() != Phase::Idle {
            return;
        }
        // Pages at most a quarter in use are evacuated while half the free room covers them.
        // Pages of large objects stay.
        let pages = &m.pages[..m.used.get()];
        let all = m.evacuate_all.get();
        let occupied: usize = pages.iter().map(|p| p.used.get().count_ones() as usize * LINE).sum();
        let mut room = (m.budget.limit() / 8).saturating_sub(occupied) / 2;
        let mut count = 0;
        for page in pages {
            page.marks.iter().for_each(|w| w.set(0));
            page.lines.set(0);
            page.cards.set(0);
            let used = page.used.get().count_ones() as usize * LINE;
            let candidate = page.large.get().is_none() && used > 0 && (all || (used <= PAGE / 4 && used <= room));
            if candidate {
                room = room.saturating_sub(used);
                count += 1;
            }
            page.evacuating.set(candidate);
        }
        let evacuating = count > 1 || all && count > 0;
        if !evacuating {
            pages.iter().for_each(|p| p.evacuating.set(false));
        }
        m.hosts.borrow_mut().iter_mut().for_each(|h| h.marked = false);
        m.frozen.clear_marks();
        m.evacuating.set(evacuating);
        m.to_cursor.set(0);
        m.to_end.set(0);
        m.phase.set(Phase::Marking);
        m.cycle_work.set(0);
        let mut work = std::mem::take(&mut *m.work.borrow_mut());
        work.fixups.clear();
        work.holders.clear();
        work.weak_runs.clear();
        work.ephemerons.clear();
        self.mark_roots(&mut work);
        *m.work.borrow_mut() = work;
    }

    /// Does about `budget` bytes of the cycle: marking, the atomic phase once nothing is left
    /// to mark, then sweeping.
    fn work(self, budget: usize) {
        let mut left = budget;
        if self.m.phase.get() == Phase::Marking {
            let mut work = std::mem::take(&mut *self.m.work.borrow_mut());
            match self.drain(&mut work, left) {
                Some(rest) => {
                    self.atomic(&mut work);
                    left = rest;
                }
                None => left = 0,
            }
            *self.m.work.borrow_mut() = work;
        }
        if self.m.phase.get() == Phase::Sweeping {
            let mut cursor = self.m.sweep_cursor.get();
            while left > 0 && cursor < self.m.used.get() {
                if !self.m.pages[cursor].swept.get() {
                    self.sweep_page(cursor);
                    left = left.saturating_sub(SWEEP_COST);
                }
                cursor += 1;
            }
            self.m.sweep_cursor.set(cursor);
            if cursor >= self.m.used.get() {
                self.count_work(budget - left);
                self.finish_cycle();
                return;
            }
        }
        if self.m.phase.get() != Phase::Idle {
            self.count_work(budget - left);
        }
    }

    fn count_work(self, done: usize) {
        self.m.cycle_work.set(self.m.cycle_work.get().saturating_add(done));
    }

    /// Traces gray objects until `budget` bytes are done. Returns the budget left once none
    /// remain.
    fn drain(self, work: &mut Work, budget: usize) -> Option<usize> {
        let mut left = budget;
        while left > 0 {
            let Some(i) = work.gray.pop() else { return Some(left) };
            left = left.saturating_sub(self.trace(i as usize, work) * 8);
        }
        work.gray.is_empty().then_some(0)
    }

    /// Ends marking: rescans the roots, which take no barrier, clears dead weak references,
    /// moves the objects being evacuated, and frees dead hosts. Sweeping comes after.
    fn atomic(self, work: &mut Work) {
        let m = self.m;
        self.mark_roots(work);
        self.drain(work, usize::MAX);
        self.trace_ephemerons(work);
        self.clear_weaks(work);
        if m.evacuating.get() {
            self.evacuate(work);
            m.evacuations.set(m.evacuations.get() + 1);
        }
        m.frozen.sweep_all();
        self.sweep_hosts();
        for page in &m.pages[..m.used.get()] {
            page.cards.set(0);
            page.evacuating.set(false);
            page.swept.set(false);
        }
        self.reset_allocator();
        m.evacuating.set(false);
        m.sweep_cursor.set(0);
        m.phase.set(Phase::Sweeping);
        work.fixups.clear();
        work.holders.clear();
        work.weak_runs.clear();
        work.ephemerons.clear();
    }

    /// Frees the host values marking didn't reach, drops the free slots at the end of the table,
    /// and gives back room the table no longer needs. The free list hands out the lowest ids
    /// first, so live values gather at the front and the end keeps emptying.
    fn sweep_hosts(self) {
        let m = self.m;
        let mut hosts = m.hosts.borrow_mut();
        let mut dead = m.dead_hosts.borrow_mut();
        for host in hosts.iter_mut() {
            if !host.marked && let Some(value) = host.value.take() {
                dead.push(value);
                m.budget.refund(host.cost);
                m.host_bytes.set(m.host_bytes.get() - std::mem::take(&mut host.cost));
                // A slot whose generation reaches the last one is retired.
                host.generation = host.generation.saturating_add(1);
            }
        }
        let free = |h: &HostSlot| h.value.is_none() && h.generation < u32::MAX;
        let len = hosts.iter().rposition(|h| !free(h)).map_or(0, |i| i + 1);
        let floor = hosts[len..].iter().map(|h| h.generation).max().unwrap_or(0);
        m.host_floor.set(m.host_floor.get().max(floor));
        hosts.truncate(len);
        shrink(&mut hosts);
        let mut ids = m.free_hosts.borrow_mut();
        ids.clear();
        ids.extend((0..len as u32).rev().filter(|&id| free(&hosts[id as usize])));
        shrink(&mut ids);
    }

    fn finish_cycle(self) {
        let m = self.m;
        self.count_occupied();
        let size = m.paced_bytes();
        let limit = m.budget.limit();
        m.threshold.set((size * 2).max(MIN_THRESHOLD).min(size + limit.saturating_sub(size) / 2));
        m.last_work.set(m.cycle_work.get());
        m.phase.set(Phase::Idle);
        m.settle.set(true);
        m.collections.set(m.collections.get() + 1);
    }

    fn count_occupied(self) {
        let pages = &self.m.pages[..self.m.used.get()];
        self.m.occupied.set(pages.iter().filter(|p| p.used.get() != 0).count());
    }

    fn mark_roots(self, work: &mut Work) {
        for root in &self.m.roots {
            self.visit(root, work);
        }
        let mut stacks = self.m.stacks.borrow_mut();
        for stack in stacks.iter() {
            stack.trace(self, work, Rc::strong_count(stack) == 1);
        }
        // A dropped stack, traced once more for what it wrote, is done with.
        let before = stacks.len();
        stacks.retain(|s| Rc::strong_count(s) > 1);
        self.m.budget.refund((before - stacks.len()) * STACK_COST);
        let mut handles = self.m.handles.borrow_mut();
        let before = handles.len();
        handles.retain(|h| Rc::strong_count(h) > 1);
        self.m.budget.refund((before - handles.len()) * ROOT_COST);
        for handle in handles.iter() {
            self.visit(&handle.word, work);
        }
    }

    /// Sweeps every page at once, for a minor collection.
    fn sweep(self) {
        for p in 0..self.m.used.get() {
            self.m.pages[p].cards.set(0);
            self.sweep_page(p);
        }
        self.count_occupied();
    }

    /// Frees what wasn't marked and gives the allocator the lines that were.
    fn sweep_page(self, p: usize) {
        let page = &self.m.pages[p];
        for (s, k) in page.starts.iter().zip(&page.marks) {
            s.set(s.get() & k.get());
        }
        let lines = page.lines.get();
        page.used.set(lines);
        // Its last page can hold small objects that outlive it.
        if lines == 0 || page.large.get().is_some_and(|first| !self.has_bit(first as usize * PAGE, |p| &p.marks)) {
            page.large.set(None);
        }
        page.swept.set(true);
    }

    /// Clears weak fields whose targets weren't marked.
    fn clear_weaks(self, work: &mut Work) {
        for &holder in &work.holders {
            let i = holder as usize;
            let Some(desc) = self.words.get(i).and_then(|h| self.desc(h.get())) else { continue };
            let mut bits = desc.weaks;
            while bits != 0 {
                if let Some(slot) = self.words.get(i + 1 + bits.trailing_zeros() as usize) {
                    self.clear_dead(slot);
                }
                bits &= bits - 1;
            }
            if desc.items == Items::Weaks {
                for slot in self.items_of(i) {
                    self.clear_dead(slot);
                }
            }
        }
        for &(from, to) in &work.weak_runs {
            for slot in self.words.get(from as usize..to as usize).unwrap_or(&[]) {
                self.clear_dead(slot);
            }
        }
        for &holder in &work.ephemerons {
            self.each_ephemeron(holder as usize, |key, value| {
                if !self.key_live(key.get()) {
                    key.set(Value::BROKEN.word);
                    value.set(Value::BROKEN.word);
                }
            });
        }
    }

    /// Clears a weak slot whose target wasn't marked.
    #[inline]
    fn clear_dead(self, slot: &Cell<u64>) {
        let target = slot.get() as u32;
        if target != 0 && !self.has_bit(target as usize, |p| &p.marks) {
            slot.set(0);
        }
    }

    /// The items of the object at `i`.
    fn items_of(self, i: usize) -> &'a [Cell<u64>] {
        let Some(header) = self.words.get(i).map(Cell::get) else { return &[] };
        let Some(desc) = self.desc(header) else { return &[] };
        let start = i + 1 + desc.fields as usize;
        self.words.get(start..start + (header >> 32) as usize).unwrap_or(&[])
    }

    /// Calls `f` with the key and value slots of each ephemeron in the object at `i`.
    fn each_ephemeron(self, i: usize, mut f: impl FnMut(&'a Cell<u64>, &'a Cell<u64>)) {
        let Some(header) = self.words.get(i).map(Cell::get) else { return };
        let Some(desc) = self.desc(header).filter(|d| d.has_ephemerons()) else { return };
        let fields = desc.fields as usize;
        let mut bits = desc.ephemerons;
        while bits != 0 {
            let k = bits.trailing_zeros() as usize;
            if k + 1 < fields
                && let Some([key, value]) = self.words.get(i + 1 + k..i + 3 + k).and_then(|p| p.as_array())
            {
                f(key, value);
            }
            bits &= bits - 1;
        }
        if desc.items == Items::Ephemerons {
            let len = (header >> 32) as usize;
            for [key, value] in self.words.get(i + 1 + fields..i + 1 + fields + len).unwrap_or(&[]).as_chunks().0 {
                f(key, value);
            }
        }
    }

    /// Whether an ephemeron's key is reachable: marked, or not an object.
    fn key_live(self, word: u64) -> bool {
        word & TAG != OBJECT || self.has_bit((word >> 32) as usize, |p| &p.marks)
    }

    /// Marks the values of ephemerons whose keys are marked, and what they reach, until a pass
    /// finds no more.
    fn trace_ephemerons(self, work: &mut Work) {
        loop {
            let mut marked = false;
            let mut h = 0;
            while let Some(&holder) = work.ephemerons.get(h) {
                self.each_ephemeron(holder as usize, |key, value| {
                    let word = value.get();
                    if word & TAG == OBJECT && self.key_live(key.get()) {
                        marked |= self.mark((word >> 32) as u32, work);
                    }
                });
                h += 1;
            }
            if !marked {
                return;
            }
            self.drain(work, usize::MAX);
        }
    }

    #[inline]
    fn visit(self, slot: &Cell<u64>, work: &mut Work) {
        let word = slot.get();
        if word & TAG == OBJECT {
            self.mark((word >> 32) as u32, work);
        }
    }

    /// Marks the object at `index` and queues it to be traced. An index that isn't an
    /// object's is left alone.
    /// Returns whether it wasn't marked before.
    fn mark(self, index: u32, work: &mut Work) -> bool {
        let i = index as usize;
        let Some(page) = self.m.pages.get(i / PAGE) else { return false };
        let (marks, bit) = (&page.marks[i % PAGE / 64], 1 << (i % 64));
        if marks.get() & bit != 0 || page.starts[i % PAGE / 64].get() & bit == 0 {
            return false;
        }
        let Some(desc) = self.desc(self.words[i].get()) else { return false };
        marks.set(marks.get() | bit);
        self.cover_lines(i, desc.size(self.words[i].get()), |p| &p.lines);
        if desc.traces {
            work.gray.push(index);
        }
        true
    }

    /// Marks what the object refers to. Returns its size in words.
    fn trace(self, i: usize, work: &mut Work) -> usize {
        self.trace_parts(i, work, true)
    }

    /// Traces the object's fields, and its items if `items`.
    #[inline(always)]
    fn trace_parts(self, i: usize, work: &mut Work, items: bool) -> usize {
        let Some(header) = self.words.get(i).map(Cell::get) else { return 1 };
        let Some(desc) = self.desc(header) else { return 1 };
        let evacuating = self.m.evacuating.get();
        let fields = self.words.get(i + 1..i + 1 + desc.fields as usize).unwrap_or(&[]);
        let note = |work: &mut Work, at: usize, target: u32| {
            if evacuating && self.in_evacuation(target) {
                work.fixups.push((i as u32, at as u32 + 1));
            }
        };
        let mut bits = desc.values;
        while bits != 0 {
            let k = bits.trailing_zeros() as usize;
            if let Some(slot) = fields.get(k) {
                let word = slot.get();
                if word & TAG == OBJECT {
                    self.mark((word >> 32) as u32, work);
                    note(work, k, (word >> 32) as u32);
                }
            }
            bits &= bits - 1;
        }
        let mut bits = desc.members;
        while bits != 0 {
            let k = bits.trailing_zeros() as usize;
            if let Some(slot) = fields.get(k) {
                let target = slot.get() as u32;
                if target != 0 {
                    self.mark(target, work);
                    note(work, k, target);
                }
            }
            bits &= bits - 1;
        }
        if desc.has_ephemerons() {
            work.ephemerons.push(i as u32);
            // Values whose keys are marked already; the rest wait for `trace_ephemerons`.
            self.each_ephemeron(i, |key, value| {
                if self.key_live(key.get()) {
                    self.visit(value, work);
                }
            });
        }
        if desc.weaks != 0 || items && desc.items == Items::Weaks {
            work.holders.push(i as u32);
            let mut bits = desc.weaks;
            while bits != 0 {
                let k = bits.trailing_zeros() as usize;
                if let Some(target) = fields.get(k).map(|s| s.get() as u32).filter(|&t| t != 0) {
                    note(work, k, target);
                }
                bits &= bits - 1;
            }
        }
        let mut bits = desc.hosts;
        while bits != 0 {
            if let Some(slot) = fields.get(bits.trailing_zeros() as usize) {
                self.mark_host(slot.get());
            }
            bits &= bits - 1;
        }
        let mut bits = desc.frozen;
        while bits != 0 {
            if let Some(slot) = fields.get(bits.trailing_zeros() as usize) {
                self.m.frozen.mark(slot.get());
            }
            bits &= bits - 1;
        }
        let mut size = 1 + desc.fields as usize;
        if desc.items != Items::None {
            let len = (header >> 32) as usize;
            size += len;
            let traced = self.traced_items(i, header, desc);
            let start = desc.fields as usize;
            let slots = || self.words.get(i + 1 + start..i + 1 + start + traced).unwrap_or(&[]).iter().enumerate();
            if items && desc.items == Items::Values {
                for (j, slot) in slots() {
                    let word = slot.get();
                    if word & TAG == OBJECT {
                        self.mark((word >> 32) as u32, work);
                        note(work, start + j, (word >> 32) as u32);
                    }
                }
            } else if items && desc.items == Items::Members {
                for (j, slot) in slots() {
                    let target = slot.get() as u32;
                    if target != 0 {
                        self.mark(target, work);
                        note(work, start + j, target);
                    }
                }
            }
        }
        size
    }

    /// How many items of the object at `i` are ordinary arena memory: for a [`Segment`], those
    /// below the active stack's `base` (or `top` once retired).
    #[inline]
    fn traced_items(self, i: usize, header: u64, desc: &'static Desc) -> usize {
        let len = (header >> 32) as usize;
        if desc.number == Segment::DESC.number {
            self.words.get(i + 1).map_or(0, |w| (w.get() as u32 as usize).min(len))
        } else {
            len
        }
    }

    /// Moves the marked objects off the pages being evacuated, then fixes every reference
    /// to them: the roots, root handles and stacks, which are rescanned, and the slots noted while marking.
    fn evacuate(self, work: &mut Work) {
        let used = self.m.used.get();
        for p in 0..used {
            let page = &self.m.pages[p];
            if !page.evacuating.get() {
                continue;
            }
            for (k, (starts, marks)) in page.starts.iter().zip(&page.marks).enumerate() {
                let mut live = starts.get() & marks.get();
                while live != 0 {
                    self.move_object(p * PAGE + k * 64 + live.trailing_zeros() as usize);
                    live &= live - 1;
                }
            }
        }
        for root in &self.m.roots {
            self.fix_value(root);
        }
        for stack in self.m.stacks.borrow().iter() {
            stack.fix(self);
        }
        for handle in self.m.handles.borrow().iter() {
            self.fix_value(&handle.word);
        }
        for &(owner, at) in &work.fixups {
            let o = self.resolve(owner) as usize;
            let Some(desc) = self.words.get(o).and_then(|h| self.desc(h.get())) else { continue };
            let Some(slot) = self.words.get(o + at as usize) else { continue };
            let field = at as usize - 1;
            let bit = if field < 64 { 1 << field } else { 0 };
            let index = if field >= desc.fields as usize {
                matches!(desc.items, Items::Members | Items::Weaks)
            } else {
                (desc.members | desc.weaks) & bit != 0
            };
            if index {
                self.fix_index(slot);
            } else if field >= desc.fields as usize || desc.values & bit != 0 {
                self.fix_value(slot);
            }
        }
        for &holder in &work.holders {
            let o = self.resolve(holder) as usize;
            let Some(desc) = self.words.get(o).and_then(|h| self.desc(h.get())) else { continue };
            let mut bits = desc.weaks;
            while bits != 0 {
                if let Some(slot) = self.words.get(o + 1 + bits.trailing_zeros() as usize) {
                    self.fix_index(slot);
                }
                bits &= bits - 1;
            }
            if desc.items == Items::Weaks {
                for slot in self.items_of(o) {
                    self.fix_index(slot);
                }
            }
        }
        for &holder in &work.ephemerons {
            self.each_ephemeron(self.resolve(holder) as usize, |key, value| {
                self.fix_value(key);
                self.fix_value(value);
            });
        }
        // Objects that didn't fit in fresh pages stay, so their lines are found again.
        for page in &self.m.pages[..used] {
            if page.evacuating.get() {
                page.lines.set(0);
            }
        }
        for p in 0..used {
            let page = &self.m.pages[p];
            if !page.evacuating.get() {
                continue;
            }
            for (k, (starts, marks)) in page.starts.iter().zip(&page.marks).enumerate() {
                let mut live = starts.get() & marks.get();
                while live != 0 {
                    let i = p * PAGE + k * 64 + live.trailing_zeros() as usize;
                    if let Some(desc) = self.desc(self.words[i].get()) {
                        self.cover_lines(i, desc.size(self.words[i].get()), |p| &p.lines);
                    }
                    live &= live - 1;
                }
            }
        }
    }

    /// Copies a marked object to a fresh page and leaves a forwarding header. The copy is
    /// marked; the original isn't, so the sweep frees it.
    fn move_object(self, i: usize) {
        let header = self.words[i].get();
        let Some(desc) = self.desc(header) else { return };
        let size = desc.size(header);
        let Some(new) = self.to_reserve(size) else { return };
        let (Some(from), Some(to)) = (self.words.get(i..i + size), self.words.get(new..new + size)) else { return };
        for (d, s) in to.iter().zip(from) {
            d.set(s.get());
        }
        self.set_bit(new, |p| &p.starts);
        self.set_bit(new, |p| &p.marks);
        self.cover_lines(new, size, |p| &p.lines);
        self.words[i].set((new as u64) << 32 | FORWARDED | header & TYPE_BITS);
        let marks = &self.m.pages[i / PAGE].marks[i % PAGE / 64];
        marks.set(marks.get() & !(1 << (i % 64)));
    }

    fn to_reserve(self, size: usize) -> Option<usize> {
        let at = self.m.to_cursor.get();
        if at + size <= self.m.to_end.get() {
            self.m.to_cursor.set(at + size);
            return Some(at);
        }
        // An object that finds no room stays where it is.
        let n = size.div_ceil(PAGE);
        let first = self.m.budget.optional(|| self.free_run(n, true)?.map_or_else(|| self.fresh_pages(n), Ok)).ok()?;
        // Claimed until the sweep sets them from what's marked.
        self.m.pages[first..first + n].iter().for_each(|p| p.used.set(u128::MAX));
        let start = first * PAGE;
        self.m.to_cursor.set(start + size);
        self.m.to_end.set(start + n * PAGE);
        Some(start)
    }

    /// Where the object at `index` is now.
    fn resolve(self, index: u32) -> u32 {
        let i = index as usize;
        match self.words.get(i).map(Cell::get) {
            Some(header) if header & FORWARDED != 0 && self.has_bit(i, |p| &p.starts) => (header >> 32) as u32,
            _ => index,
        }
    }

    fn fix_index(self, slot: &Cell<u64>) {
        slot.set(slot.get() & !0xFFFF_FFFF | u64::from(self.resolve(slot.get() as u32)));
    }

    fn fix_value(self, slot: &Cell<u64>) {
        let word = slot.get();
        if word & TAG == OBJECT {
            let new = self.resolve((word >> 32) as u32);
            slot.set(word & 0xFFFF_FFFF | u64::from(new) << 32);
        }
    }

    /// Traces the old objects that overlap dirty cards, for a minor collection.
    fn scan_cards(self, work: &mut Work) {
        let mut last = usize::MAX;
        for page in 0..self.m.used.get() {
            let mut cards = self.m.pages[page].cards.get();
            while cards != 0 {
                let card = cards.trailing_zeros() as usize;
                cards &= cards - 1;
                let (from, to) = (page * PAGE + card * CARD, page * PAGE + (card + 1) * CARD);
                let mut next = self.start_at_or_before(from).or_else(|| self.next_start(from, to));
                while let Some(object) = next.filter(|&o| o < to) {
                    if self.has_bit(object, |p| &p.marks) {
                        self.trace_card(object, from..to, object != last, work);
                        last = object;
                    }
                    // Nothing starts between the object found before the card and the card.
                    next = self.next_start((object + 1).max(from), to);
                }
            }
        }
    }

    /// Traces what an old object on a dirty card refers to: for items of values, only those on
    /// the card, so storing into a large vector doesn't rescan all of it. The rest of the
    /// object is traced once, for its first card.
    fn trace_card(self, i: usize, card: Range<usize>, first: bool, work: &mut Work) {
        let header = self.words[mask(i)].get();
        let Some(desc) = self.desc(header) else { return };
        let Some(refs @ (Refs::Values | Refs::Members | Refs::Weaks)) = Refs::of(desc.items) else {
            if first {
                self.trace(i, work);
            }
            return;
        };
        if first {
            self.trace_parts(i, work, false);
        }
        let items = i + 1 + desc.fields as usize;
        let traced = self.traced_items(i, header, desc);
        let (from, to) = (card.start.max(items), card.end.min(items + traced));
        let slots = self.words.get(from..to).unwrap_or(&[]);
        match refs {
            Refs::Values => slots.iter().for_each(|slot| self.visit(slot, work)),
            Refs::Members => slots.iter().filter(|s| s.get() as u32 != 0).for_each(|s| _ = self.mark(s.get() as u32, work)),
            _ if from < to => work.weak_runs.push((from as u32, to as u32)),
            _ => {}
        }
    }

    fn start_at_or_before(self, i: usize) -> Option<usize> {
        let (mut page, mut word) = (i / PAGE, i % PAGE / 64);
        let mut mask = u64::MAX >> (63 - i % 64);
        loop {
            let starts = self.m.pages[page].starts[word].get() & mask;
            if starts != 0 {
                return Some(page * PAGE + word * 64 + 63 - starts.leading_zeros() as usize);
            }
            mask = u64::MAX;
            if word > 0 {
                word -= 1;
            } else if let Some(first) = self.m.pages[page].large.get().map(|f| f as usize).filter(|&f| f < page) {
                // Nothing starts between the large object's header and its pages' end.
                (page, word) = (first, 0);
            } else if page > 0 {
                (page, word) = (page - 1, PAGE / 64 - 1);
            } else {
                return None;
            }
        }
    }

    fn next_start(self, from: usize, to: usize) -> Option<usize> {
        let mut i = from;
        while i < to {
            let (page, word) = (i / PAGE, i % PAGE / 64);
            let starts = self.m.pages.get(page)?.starts[word].get() & (u64::MAX << (i % 64));
            if starts != 0 {
                return Some(page * PAGE + word * 64 + starts.trailing_zeros() as usize).filter(|&s| s < to);
            }
            i = (i / 64 + 1) * 64;
        }
        None
    }
}

/// The barrier's slow path. It takes the heap's parts rather than a `Heap`, which is too big to
/// pass in registers: the caller would copy it to the stack on every store, slow path or not.
#[cold]
#[inline(never)]
fn shade(words: &[Cell<u64>; WORDS + SLACK], m: &Meta, slot: usize, owner: u32, target: u32) {
    Heap { words, m }.shade_marked(slot, owner, target);
}
