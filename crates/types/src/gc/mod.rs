//! Ragwort's garbage collector. The region is an array of words in `Cell`s, and a reference is a word index.
//! Each type is described by data that the collector reads, not by code that the collector runs. A wrong descriptor
//! or a forged reference gives wrong results or a panic, but never undefined behavior.
//!
//! The collector has 16 KiB pages of 128-byte lines, 512-byte cards, sticky mark bits for minor
//! collections, major cycles marked in incremental slices, weak references and ephemerons,
//! evacuation of fragmented pages through forwarding headers in the atomic phase, and lazy
//! sweeping. Free pages beyond one nursery's worth are returned to the system through
//! `ragwort-gc-region`, which holds the only unsafe code in Ragwort (at least in interpreter mode).
//! Memory is counted against a budget with a reserve. VM stacks have segments, continuation capture and parking.
//!
//! The arena has a fixed number of value roots, set when the arena is created. A [`Root`] keeps an object
//! alive across steps from outside the arena, such as from a task.
//!
//! # Typed objects
//!
//! [`objects!`] declares a group of types. Each field declares the kind of data it holds. The macro
//! derives the collector's descriptor from the declarations, so the two cannot disagree:
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
//!     let p = Pair::new(mc, Value::NULL, Value::TRUE).unwrap();
//!     assert_eq!(p.cdr(mc), Value::TRUE);
//!     p.set_car(mc, Value::fixnum(1).unwrap());
//!     assert_eq!(p.get(mc, Pair::CAR), Value::fixnum(1).unwrap());
//!
//!     let tail = Node::new(mc, 2, None, None).unwrap();
//!     let head = Node::new(mc, 1, Some(tail), None).unwrap();
//!     assert_eq!(head.next(mc).map(|n| n.n(mc)), Some(2));
//!
//!     let v = Vector::new(mc, 3, Value::NULL).unwrap();
//!     v.items(mc).set(mc, 0, Value::object(mc, p));
//!
//!     match Kind::of(v.items(mc).get(0)) {
//!         Some(Kind::Pair(p)) => assert_eq!(p.cdr(mc), Value::TRUE),
//!         _ => unreachable!(),
//!     }
//! });
//! ```
//!
//! For each `struct`, the macro generates:
//! - a unit struct implementing [`Object`];
//! - a [`Field`] constant per field, named in capitals (`Pair::CAR`), for [`Gc::get`] and
//!   [`Gc::set`];
//! - `new(mc, fields…)`, which also takes a length and fill value when the type has items, or
//!   an entry count for `items Ephemeron`;
//! - a trait `PairFields` for `Gc<Pair>`, with a getter and a `set_` setter per field, and
//!   an `items` method for every kind of items except ephemerons. `Gc::entry` reads ephemeron items.
//!
//! A field holds a `Value`, a word (`u64`, `i64`, `u32`, `f64` or `bool`), a `Member<T>`, a
//! `Weak<T>`, a `Host<T>`, an `AnyHost`, a `Frozen<T>` or an `Ephemeron`. Items can be any of
//! these except hosts and frozen values. A `Host<T>` holds a [`HostRef`]. An `AnyHost` holds
//! an [`AnyHostRef`], which refers to a host value of any type and checks the type on each read. Each write applies the write barrier that its kind needs. A member or weak read
//! checks that the target has the type declared by the field or the items.
//!
//! The group's enum, `Kind` here, has a variant per type. `Kind::of(value)` reads the type
//! number stored in the value, so it needs no memory read. Types get fixed numbers from
//! `Kind::BASE`, in declaration order. Groups used in one arena must not overlap: declare the
//! second group as `kind Extra after Kind;`. If two groups overlap, the first allocation of a clashing type
//! panics. `kind Name at N;` starts the group at `N` instead.
//!
//! A field cannot have the name of a `Gc` method or of a constructor parameter. The underlying raw API,
//! which addresses fields by number, is in the hidden `raw` module.
//!
//! # Frozen values
//!
//! A `Frozen<T>` field holds a value stored outside the region. [`Mutation::frozen`] creates the value once, and
//! a read returns `&'gc T`. Use it for data that is too big to copy into items as cells, such as the text of a source file.
//! No frozen value is freed while a step runs, and a collection needs the arena mutably. So the borrow checker
//! stops a reference from outliving its value.
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
//! [`GcVec`] is a growable array. [`Table`] is a hash table of strong, ephemeron or weak entries.
//! [`ScratchVec`] is scratch space for one step, stored outside the arena and counted against the arena's budget.
//! [`crate::string`] and [`crate::num`] hold `ragwort-string`'s strings and `ragwort-num`'s numbers. A flat
//! string's characters are packed into its own items, and a bignum's digits are its items.
//!
//! The following mistakes do not compile. Storing an object of the wrong type:
//!
//! ```compile_fail
//! # use ragwort_types::gc::*;
//! # objects! { kind Kind; struct Pair { car: Value, cdr: Value } struct Node { next: Member<Node> } }
//! # let mut arena = Arena::new(1 << 20, 1);
//! arena.mutate(|mc| {
//!     let pair = Pair::new(mc, Value::NULL, Value::NULL).unwrap();
//!     let node = Node::new(mc, None).unwrap();
//!     node.set_next(mc, Some(pair));
//! });
//! ```
//!
//! Using one type's field on another type:
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
//! Making a field handle whose kind does not match the descriptor:
//!
//! ```compile_fail
//! # use ragwort_types::gc::*;
//! # objects! { kind Kind; struct Pair { car: Value, cdr: Value } }
//! const CAR_AS_WORD: Field<Pair, slot::u64> = Field::new(0);
//! # let mut arena = Arena::new(1 << 20, 1);
//! arena.mutate(|mc| {
//!     let pair = Pair::new(mc, Value::NULL, Value::NULL).unwrap();
//!     pair.get(mc, CAR_AS_WORD);
//! });
//! ```
//!
//! Giving a field the name of a `Gc` method:
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
pub mod image;
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
use root::RootTable;
pub use root::{ForeignRoot, Handle, Root, ValueRoot, WeakHandle};
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

/// The capacity of an arena's object region, in bytes. The default is 64 MiB.
///
/// The capacity is a compile-time constant, so an object access masks its index with a constant and needs no bounds check. To build with another capacity, set the `RAGWORT_REGION_MB` environment variable to a power of two from 16 to 8192, in mebibytes:
///
/// ```text
/// RAGWORT_REGION_MB=128 cargo build --release
/// ```
///
/// - Every arena reserves `2 * REGION` bytes of address space. The system commits memory only for the pages an arena uses.
/// - An arena's own limit, given to [`Arena::new`], still bounds how much of the region it uses.
pub const REGION: usize = region();

const REGION_SETTING: &str = "RAGWORT_REGION_MB must be a power of two from 16 to 8192";

const fn region() -> usize {
    let digits = match option_env!("RAGWORT_REGION_MB") {
        Some(setting) => setting.as_bytes(),
        None => return 64 << 20,
    };
    assert!(!digits.is_empty() && digits.len() <= 4, "{}", REGION_SETTING);
    let mut mebibytes = 0;
    let mut at = 0;
    while at < digits.len() {
        assert!(digits[at].is_ascii_digit(), "{}", REGION_SETTING);
        mebibytes = mebibytes * 10 + (digits[at] - b'0') as usize;
        at += 1;
    }
    assert!(mebibytes.is_power_of_two() && mebibytes >= 16 && mebibytes <= 8192, "{}", REGION_SETTING);
    mebibytes << 20
}

/// The size of the region in words. It is twice `REGION`, so evacuation has fresh pages to copy into.
const WORDS: usize = 2 * REGION / 8;
/// The type of the region's word array. The array has `SLACK` extra words at its end.
type RegionWords = [Cell<u64>; WORDS + SLACK];
/// Page, line and card sizes in words.
const PAGE: usize = 2048;
const LINE: usize = 16;
const CARD: usize = 64;
const PAGES: usize = WORDS / PAGE;
/// The number of unused words past the end of the region. With them, `mask(index) + 1 + field` needs no
/// bounds check when `field` is a constant.
const SLACK: usize = 128;
const LINES: usize = PAGE / LINE;
/// The number of registers in a frame. A [`Frame`] or [`Window`] sees this many slots from its start. Every
/// register limit in the VM and the compiler is derived from it. A register number is a byte and is taken modulo
/// `WINDOW`, so no access needs a bounds check.
pub const WINDOW: usize = 64;
const _: () = assert!(WINDOW.is_power_of_two() && WINDOW >= 32 && WINDOW <= 256);

pub(crate) const TAG: u64 = 0b1111;
pub(crate) const OBJECT: u64 = 0b0001;
const CONSTANT: u64 = 0b1101;
/// The bits of a constant's id in which the false constants differ. See [`Value::is_false`].
const FALSE_IDS: u64 = (8 | 16) << 32;
/// The bit of a constant's id that makes it a character.
const CHAR: u64 = 1 << 31;
/// The tag of an inline string, which holds at most [`crate::string::INLINE_BYTES`] bytes of UTF-8. The next
/// four bits hold the number of bytes. The bytes follow, with the first byte lowest.
pub(crate) const INLINE_STRING: u64 = 0b0101;
/// The tag of a string cursor: a position in a string, as a byte offset. The offset is in bits 4 to 31, and the hash of the string's text is in bits 32 to 63.
const CURSOR: u64 = 0b1001;
/// The low two bits of an inline flonum. An inline flonum is a double with two redundant exponent bits dropped.
const FLONUM: u64 = 0b11;
/// The special doubles: ±0, ±infinity, and the default NaNs of ARM and x86. Their words are the words of the six smallest inline doubles,
/// ±1.7272337110188889e-77 and the two doubles above each. Those six doubles are boxed instead.
const SPECIALS: [u64; 6] = [0, 1 << 63, 0x7FF0 << 48, 0xFFF0 << 48, 0x7FF8 << 48, 0xFFF8 << 48];
/// The word of the first special. The word of each later special is 4 above the word before it.
const ZERO: u64 = 0x8000_0000_0000_0003;
const LAST_SPECIAL: u64 = 4 * (SPECIALS.len() as u64 - 1);

#[inline]
fn encode(double: f64) -> Option<u64> {
    let bits = double.to_bits();
    // A double is stored inline if its exponent starts with 011 or 100. The third exponent bit then determines the first two. The rotation moves those two to the low bits, and the tag replaces them.
    let top = bits >> 60 & 0b111;
    if top == 0b011 || top == 0b100 {
        let word = bits.rotate_left(3) | FLONUM;
        return (word.wrapping_sub(ZERO) > LAST_SPECIAL).then_some(word);
    }
    let index = SPECIALS.iter().position(|&special| special == bits)?;
    Some(ZERO + 4 * index as u64)
}

#[inline]
fn decode(word: u64) -> f64 {
    let special = word.wrapping_sub(ZERO);
    if special <= LAST_SPECIAL {
        return f64::from_bits(SPECIALS[special as usize / 4]);
    }
    // `first` is the exponent bit that was kept, now the top bit of the word. The two dropped exponent bits are its inverse and then a copy of it: `10` if it is 0 and `01` if it is 1. That is `2 - first`.
    let first = word >> 63;
    f64::from_bits((word & !FLONUM | (2 - first)).rotate_right(3))
}

/// A boxed double, for a double that has no inline encoding. These are the magnitudes outside about 1e-77 to 1e77, and the NaNs that are not in
/// `SPECIALS`. Every arena registers `Boxed` first, as type 0.
struct Boxed;

impl Object for Boxed {
    const DESC: Desc = Desc::of::<Boxed>(1).numbered(0);
}

/// The first type number that other crates can use. The numbers below it belong to this crate's types: `Boxed`, `Segment`, the containers, strings,
/// numbers, and the data types. An `objects!` group declared without a base starts here.
#[doc(hidden)]
pub const FIRST_TYPE: u16 = crate::objects::Data::END;
/// A header holds the type index, the `FORWARDED` flag, and the item count in the upper half. A forwarded header
/// holds the object's new index in the upper half instead.
const TYPE_BITS: u64 = 0xFFFF;
const FORWARDED: u64 = 1 << 16;
const TYPES: usize = 1 << 16;
static NEXT_ARENA: AtomicU64 = AtomicU64::new(0);

type Brand<'gc> = PhantomData<Cell<&'gc ()>>;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct OutOfMemory;

/// The error type of string and number operations.
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
    fn from(error: ragwort_num::NumError) -> Self {
        Self::Num(error)
    }
}

impl From<ragwort_string::StrError> for Error {
    fn from(error: ragwort_string::StrError) -> Self {
        Self::Str(error)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Items {
    None,
    Values,
    Words,
    /// Pairs of a key and a value, which behave like the fields in `Desc::ephemerons`. The item count is in words, two per pair.
    Ephemerons,
    /// Object indices that keep their targets alive. Index 0 means no object.
    Members,
    /// Object indices that do not keep their targets alive. An index is set to 0 once its target dies. Index 0 means no object.
    Weaks,
}

/// The collector's descriptor of a type: the number of fixed fields, the fields that hold references, and the kind of items.
pub struct Desc {
    pub type_id: TypeId,
    pub fields: u32,
    /// Bit mask of the fields that hold a `Value`.
    pub values: u64,
    /// Bit mask of the fields that hold an object index. Index 0 means no object.
    pub members: u64,
    /// Bit mask of the fields that hold a host reference, as the word from [`HostRef::to_word`]. Word 0 means no host value.
    pub hosts: u64,
    /// Bit mask of the fields that hold an object index without keeping the object alive. Index 0 means no object.
    pub weaks: u64,
    /// Bit mask of the fields that hold a frozen value's id plus one, where 0 means no value. A frozen value is a write-once value stored outside the
    /// region.
    pub frozen: u64,
    /// Bit mask of the fields that hold an ephemeron's key. The ephemeron's value is in the next field. The value is kept
    /// alive only while the key is reachable in some other way. Once the key dies, both fields become
    /// `Value::BROKEN`. A key that is not an object never dies.
    pub ephemerons: u64,
    pub items: Items,
    /// A fixed type number. `objects!` gives one to each of its types, so that type checks compare against a
    /// constant. Each arena numbers a type that has no fixed number when it first sees the type.
    pub number: Option<u16>,
    /// Whether an object of the type holds anything for marking to trace. Every builder method keeps the flag up to
    /// date. Marking reads it for each object, and computing it each time costs 4%.
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

    /// Returns a descriptor whose fields have the roles in `roles`, in order, and whose items are `items`. An ephemeron role takes two fields.
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

    /// Returns the role of field `field`. Returns `None` if `field` is out of range or is the value field of an ephemeron. An ephemeron key in the last field has no value field, so `role` also returns `None` for it.
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

/// A value in one word: a fixnum shifted left by one, an inline flonum, an object's index and type, a short string,
/// or a constant.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Value<'gc> {
    word: u64,
    _brand: Brand<'gc>,
}

impl<'gc> Value<'gc> {
    pub const FALSE: Self = Self::constant(0);
    pub const TRUE: Self = Self::constant(1);
    /// The empty list.
    pub const NULL: Self = Self::constant(2);
    /// The void value. A stack slot above `top` is reset to it.
    pub const VOID: Self = Self::constant(3);
    /// The value of a module variable that is not defined yet.
    pub const UNDEFINED: Self = Self::constant(4);
    /// The value bound to an optional parameter when the call passes no argument for it.
    pub const UNSUPPLIED: Self = Self::constant(5);
    /// The marker that the VM's accumulator holds when a call returned no value or several values. The values are then in a list beside the accumulator. The marker is never stored in a variable.
    pub const VALUES: Self = Self::constant(6);
    /// The value that replaces an ephemeron's key and value once the key dies.
    pub const BROKEN: Self = Self::constant(7);
    /// `#nil`: the absence of a value. For example, a table read returns it for a key that the table does not
    /// have. It is false in a conditional. See [`Value::is_false`].
    pub const NIL: Self = Self::constant(8);
    /// The default continuation prompt tag. A program can hold it like any other value.
    pub const DEFAULT_TAG: Self = Self::constant(9);
    /// The continuation mark key under which the VM keeps the installed exception handlers. A program never holds it.
    pub const HANDLER_KEY: Self = Self::constant(10);
    /// `#none`: a value that is present and means "none". For example, a host returns it for a `null`. It is false in
    /// a conditional. See [`Value::is_false`].
    pub const NONE: Self = Self::constant(16);

    /// Returns whether a conditional treats the value as false. Three values are false: `#f`, `#nil` and
    /// `#none`. Every other value is true, including the empty list and void.
    ///
    /// The ids of the three constants differ only in two bits, so clearing
    /// those bits and comparing with `#f` tests for all three at once. No constant is made with
    /// both bits set.
    #[inline(always)]
    pub const fn is_false(self) -> bool {
        self.word & !FALSE_IDS == Self::FALSE.word
    }

    /// Returns whether a conditional treats the value as true. That is every value that is not [false](Value::is_false).
    #[inline(always)]
    pub const fn is_true(self) -> bool {
        !self.is_false()
    }

    const fn constant(id: u64) -> Self {
        Self::from_bits(id << 32 | CONSTANT)
    }

    /// Returns `character` as a value. A character is a constant whose id has its top bit set and holds the code point in the bits below.
    #[inline]
    pub const fn char(character: char) -> Self {
        Self::constant(CHAR | character as u64)
    }

    #[inline]
    pub fn as_char(self) -> Option<char> {
        let id = self.word >> 32;
        if self.word & 0xFFFF_FFFF != CONSTANT || id & CHAR == 0 {
            return None;
        }
        char::from_u32((id & !CHAR) as u32)
    }

    /// The largest byte offset that a string cursor can hold.
    pub const MAX_CURSOR: usize = (1 << 28) - 1;

    /// Returns a string cursor at byte offset `offset` of a string whose text has the hash `text`. Returns `None` if `offset` is more than [`Value::MAX_CURSOR`].
    ///
    /// A cursor names a position in a string without a count of the characters before it. It is an immediate value, so making one allocates nothing.
    /// It holds no reference to the string. It holds the hash of the string's text, and a procedure that takes a cursor compares that with the hash of the string that it is given.
    /// So a cursor is good for every string with the same text, and for no other.
    #[inline]
    pub const fn cursor(offset: usize, text: u32) -> Option<Self> {
        if offset > Self::MAX_CURSOR {
            return None;
        }
        Some(Self::from_bits((text as u64) << 32 | (offset as u64) << 4 | CURSOR))
    }

    /// Returns the byte offset of a string cursor and the hash of the text that it was made for, or `None` if the value is not a cursor.
    #[inline]
    pub const fn as_cursor(self) -> Option<(usize, u32)> {
        if self.word & TAG == CURSOR { Some(((self.word as u32 >> 4) as usize, (self.word >> 32) as u32)) } else { None }
    }

    /// Returns the value with the bits `word`. Every word is a valid value. An object reference that matches no object reads as some other object or as no object.
    pub const fn from_bits(word: u64) -> Self {
        Self { word, _brand: PhantomData }
    }

    pub const fn to_bits(self) -> u64 {
        self.word
    }

    #[inline]
    pub fn fixnum(number: i64) -> Option<Self> {
        let word = (number as u64) << 1;
        ((word as i64) >> 1 == number).then_some(Self::from_bits(word))
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
        (self.word as i64).checked_add(other.word as i64).map(|word| Self::from_bits(word as u64))
    }

    #[inline]
    pub fn fixnum_sub(self, other: Self) -> Option<Self> {
        if (self.word | other.word) & 1 != 0 {
            return None;
        }
        (self.word as i64).checked_sub(other.word as i64).map(|word| Self::from_bits(word as u64))
    }

    /// Returns the product of two fixnums, or `None` if it overflows or an operand is not a fixnum. A fixnum's word is twice its number, and `2a * b` is twice the product. So only one operand is shifted back.
    #[inline]
    pub fn fixnum_mul(self, other: Self) -> Option<Self> {
        if (self.word | other.word) & 1 != 0 {
            return None;
        }
        (self.word as i64).checked_mul(other.word as i64 >> 1).map(|word| Self::from_bits(word as u64))
    }

    /// Returns `double` as a value. The double is stored in the word if it has an inline encoding, and boxed otherwise.
    #[inline]
    pub fn flonum(mc: &Mutation<'gc>, double: f64) -> Result<Self, OutOfMemory> {
        match encode(double) {
            Some(word) => Ok(Self::from_bits(word)),
            None => Ok(Self::object(mc, mc.alloc::<Boxed, 1>([double.to_bits()])?)),
        }
    }

    /// Returns `double` as a value without allocating, or `None` if `double` has no inline encoding.
    #[inline]
    pub fn inline_flonum(double: f64) -> Option<Self> {
        encode(double).map(Self::from_bits)
    }

    /// Returns whether the value is a flonum: an inline flonum, or a reference to a boxed one. `Boxed` is type 0 in every arena.
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

    /// Returns the object if the value refers to a `T`. Compares the type number stored in the value with `tag`, without reading the object.
    #[inline]
    pub fn downcast_tag<T: Object>(self, tag: TypeTag<'gc, T>) -> Option<Gc<'gc, T>> {
        (self.word & (TYPE_BITS << 16 | TAG) == u64::from(tag.ty) << 16 | OBJECT).then(|| Gc::new((self.word >> 32) as u32))
    }

    /// Returns the type number and index of the object that the value refers to, or `None` if it refers to no object. For `objects!` kinds.
    #[doc(hidden)]
    #[inline]
    pub fn object_parts(self) -> Option<(u16, u32)> {
        (self.word & TAG == OBJECT).then_some(((self.word >> 16 & TYPE_BITS) as u16, (self.word >> 32) as u32))
    }

    /// Returns the value as an [`Immediate`], or `None` if it refers to an object.
    #[inline]
    pub fn immediate(self) -> Option<Immediate> {
        (self.word & TAG != OBJECT).then_some(Immediate(self.word))
    }
}

/// A value that refers to no object, such as a fixnum, an inline flonum or `#t`. It has no
/// brand, because no collection changes it. So it can be kept outside the arena.
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

/// A reference to an object: the index of the object's header in the region.
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
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.debug_tuple("Gc").field(&self.index).finish()
    }
}

impl<'gc, T: Object> Gc<'gc, T> {
    const fn new(index: u32) -> Self {
        Self { index, _marker: PhantomData }
    }

    /// Returns the object at `index` as a `T`, without a type check. For `objects!` kinds, which have already checked the
    /// type number stored in the value.
    #[doc(hidden)]
    pub const fn forge(index: u32) -> Self {
        Self::new(index)
    }

    /// Returns a reference to the frozen value that `field` holds, or `None` if it holds none. Another object can then hold the same value: store the
    /// reference in it during this step. The value lives while any object that holds it lives.
    pub fn frozen_ref<U: Any>(self, mc: &Mutation<'gc>, field: Field<T, slot::Frozen<U>>) -> Option<FrozenRef<'gc, U>> {
        let id = (self.word(mc, field.index) as u32).checked_sub(1)?;
        Some(FrozenRef::new(id))
    }

    #[inline]
    pub fn get<S: Slot>(self, mc: &Mutation<'gc>, field: Field<T, S>) -> S::Out<'gc> {
        S::get(self, mc, field.index)
    }

    /// Stores `value` in `field` and applies the write barrier that the field's kind needs.
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

    /// Returns entry `index` of `Items::Ephemerons` items, or `None` once the entry's key has died. Panics if
    /// `index` is out of range.
    #[inline]
    pub fn entry(self, mc: &Mutation<'gc>, index: usize) -> Option<(Value<'gc>, Value<'gc>)> {
        assert!(2 * index + 1 < self.len(mc), "entry {index} out of bounds");
        mc.heap.ephemeron_at(mask(items_start(self) + 2 * index))
    }

    #[inline]
    pub fn set_entry(self, mc: &Mutation<'gc>, index: usize, key: Value<'gc>, value: Value<'gc>) {
        assert!(2 * index + 1 < self.len(mc), "entry {index} out of bounds");
        mc.heap.set_ephemeron_at(mask(items_start(self) + 2 * index), key, value);
    }
}

/// Returns the word index of field `field`. Panics if `field` is not a declared field, so a write cannot reach the next
/// object. The check folds away when the field number is a constant.
#[inline]
fn field_slot<T: Object>(gc: Gc<'_, T>, field: usize) -> usize {
    assert!(field < T::DESC.fields as usize, "field {field} of {}", T::DESC.fields);
    mask(gc.index as usize) + 1 + field
}

#[inline]
fn items_start<T: Object>(gc: Gc<'_, T>) -> usize {
    mask(gc.index as usize) + 1 + T::DESC.fields as usize
}

/// Returns the target of a member or weak field, or `None` for index 0. If the field's declared type
/// has a fixed number, the target's type is checked against it with one load and compare. A mismatch panics.
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

/// Returns the value that refers to the object at `index`, or `None` for index 0. The type number of the value is read from the object.
#[inline]
fn object_at<'gc>(region: &RegionWords, index: u32) -> Option<Value<'gc>> {
    if index == 0 {
        return None;
    }
    let ty = region[mask(index as usize)].get() & TYPE_BITS;
    Some(Value::from_bits(u64::from(index) << 32 | ty << 16 | OBJECT))
}

#[cold]
#[inline(never)]
fn wrong_target(index: u32, ty: u16) -> ! {
    panic!("object {index} isn't of type {ty}, which the field it was read from declares")
}

/// A typed handle to field `index` of a `T`, which holds an `S`. `objects!` makes the handles. A handle
/// whose kind does not match `T`'s descriptor does not compile.
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

/// An object's fields as a fixed-size array, so constant field numbers need no bounds check. It is the
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

/// An object's items, each of slot kind `S`. The default kind is `slot::Value`.
pub struct Slots<'gc, S = slot::Value> {
    words: &'gc [Cell<u64>],
    /// The whole region. A read uses it to check the type of the object that an index refers to.
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
    /// Returns the item cells. A plain word refers to no object, so writing one needs no barrier.
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
    pub fn get(self, index: usize) -> S::Out<'gc> {
        S::load(self.region, self.words[index].get())
    }

    #[inline]
    pub fn set(self, mc: &Mutation<'gc>, index: usize, value: S::In<'gc>) {
        let word = S::store(value);
        self.words[index].set(word);
        let slot = self.at + index;
        match S::REFS {
            Refs::None => {}
            Refs::Values => mc.heap.barrier(slot, self.owner, word),
            Refs::Members if word != 0 => mc.heap.barrier_ref(slot, self.owner, word as u32),
            Refs::Members => {}
            Refs::Weaks => mc.heap.dirty(slot),
        }
    }

    /// Returns the items in `range`, or `None` if `range` is out of bounds.
    pub fn slice(self, range: Range<usize>) -> Option<Self> {
        let words = self.words.get(range.clone())?;
        Some(Slots { words, at: self.at + range.start, ..self })
    }

    /// Copies the items of `src` into these items. The two ranges may overlap. One barrier covers the whole range. Panics if the
    /// lengths differ.
    pub fn copy_from(self, mc: &Mutation<'gc>, src: Self) {
        assert_eq!(self.len(), src.len(), "copy between slices of different lengths");
        let refs = S::REFS != Refs::None && src.words.iter().any(|source| S::REFS.refers(source.get()));
        if self.at > src.at {
            for (target, source) in self.words.iter().zip(src.words).rev() {
                target.set(source.get());
            }
        } else {
            for (target, source) in self.words.iter().zip(src.words) {
                target.set(source.get());
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
    /// Returns the first `WINDOW` items, or `None` if there are fewer. A [`Window`] is indexed by a byte modulo `WINDOW`, so no access needs a bounds
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
    pub fn get(self, register: u8) -> Value<'gc> {
        Value::from_bits(self.slots[usize::from(register) % WINDOW].get())
    }

    #[inline]
    pub fn set(self, mc: &Mutation<'gc>, register: u8, value: Value<'gc>) {
        let register = usize::from(register) % WINDOW;
        self.slots[register].set(value.word);
        mc.heap.barrier(self.at + register, self.owner, value.word);
    }
}

/// A reference to a host value of type `T`. Host values are stored outside the region.
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
    /// Returns the value, or `None` once the value has been freed. A stale reference never reads the value that
    /// reused its slot. While the `Ref` is held, `Mutation::host` fails with `HostError::InUse`.
    #[inline]
    pub fn get(self, mc: &Mutation<'gc>) -> Option<Ref<'gc, T>> {
        self.erase().downcast_ref(mc)
    }

    /// Returns the same reference with its type erased. Each read then checks the type.
    pub fn erase(self) -> AnyHostRef<'gc> {
        AnyHostRef { id: self.id, generation: self.generation, _brand: PhantomData }
    }

    /// See [`AnyHostRef::set_owned_bytes`].
    pub fn set_owned_bytes(self, mc: &Mutation<'gc>, bytes: usize) -> Result<(), HostError> {
        self.erase().set_owned_bytes(mc, bytes)
    }

    /// Returns the word that a field declared in `Desc::hosts` holds. The upper half is the slot's generation. The lower half is the slot's id plus
    /// one, so that 0 means no host value.
    pub fn to_word(self) -> u64 {
        self.erase().to_word()
    }
}

impl<T> fmt::Debug for HostRef<'_, T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.debug_struct("HostRef").field("id", &self.id).field("generation", &self.generation).finish()
    }
}

impl<'gc, T: Any> From<HostRef<'gc, T>> for AnyHostRef<'gc> {
    fn from(host: HostRef<'gc, T>) -> Self {
        host.erase()
    }
}

/// A reference to a host value of any type, for a field that can hold several types. Each read checks
/// the type. As with [`HostRef`], a stale reference reads nothing.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct AnyHostRef<'gc> {
    id: u32,
    generation: u32,
    _brand: Brand<'gc>,
}

impl<'gc> AnyHostRef<'gc> {
    /// Returns the value, or `None` once the value has been freed.
    #[inline]
    fn value(self, mc: &Mutation<'gc>) -> Option<Ref<'gc, dyn Any>> {
        let hosts = mc.heap.m.hosts.try_borrow().ok()?;
        Ref::filter_map(hosts, |hosts| {
            let slot = hosts.get(self.id as usize).filter(|slot| slot.generation == self.generation)?;
            slot.value.as_deref()
        })
        .ok()
    }

    /// Returns whether the value is alive and is a `T`.
    pub fn is<T: Any>(self, mc: &Mutation<'gc>) -> bool {
        self.value(mc).is_some_and(|value| (*value).is::<T>())
    }

    /// Returns the value if it is alive and is a `T`. While the `Ref` is held, `Mutation::host` fails with
    /// `HostError::InUse`.
    #[inline]
    pub fn downcast_ref<T: Any>(self, mc: &Mutation<'gc>) -> Option<Ref<'gc, T>> {
        Ref::filter_map(self.value(mc)?, |value| value.downcast_ref::<T>()).ok()
    }

    /// Sets the number of bytes that the value owns outside the arena, such as a `String`'s characters, to `bytes`. The new count replaces
    /// the previous count and stays charged until the value is freed. Call it again whenever that memory
    /// grows or shrinks. Growing can fail as an allocation can: the step fails and the count does not
    /// change. Shrinking refunds the difference at once. A call on a freed value's reference does
    /// nothing. Fails with `HostError::InUse` while a `Ref` from a read is held.
    pub fn set_owned_bytes(self, mc: &Mutation<'gc>, bytes: usize) -> Result<(), HostError> {
        let meta = mc.heap.m;
        let mut hosts = meta.hosts.try_borrow_mut().map_err(|_| HostError::InUse)?;
        let Some(slot) = hosts.get_mut(self.id as usize).filter(|slot| slot.generation == self.generation && slot.value.is_some()) else {
            return Ok(());
        };
        if bytes > slot.owned {
            meta.budget.charge(bytes - slot.owned)?;
        } else {
            meta.budget.refund(slot.owned - bytes);
        }
        meta.host_bytes.set(meta.host_bytes.get() - slot.owned + bytes);
        slot.cost = slot.cost - slot.owned + bytes;
        slot.owned = bytes;
        Ok(())
    }

    /// Returns a typed reference if the value is alive and is a `T`.
    pub fn downcast<T: Any>(self, mc: &Mutation<'gc>) -> Option<HostRef<'gc, T>> {
        self.is::<T>(mc).then_some(self.assume())
    }

    /// Returns a typed reference without checking the type. `HostRef::get` checks the type on every read.
    fn assume<T>(self) -> HostRef<'gc, T> {
        HostRef { id: self.id, generation: self.generation, _marker: PhantomData }
    }

    /// Returns the word that a host field holds. See [`HostRef::to_word`].
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
    /// The bytes charged for the value, which are refunded when it is freed: its size, `HOST_COST`, and `owned`.
    cost: usize,
    /// The bytes that the value owns outside the arena, as last set by `AnyHostRef::set_owned_bytes`.
    owned: usize,
    value: Option<Box<dyn Any>>,
}

/// The bytes charged for a host value beyond its size. They cover its slot and the box's header.
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

/// A table of `C * N` entries that grows one chunk at a time, so an arena pays only for the chunks it uses.
/// The first `C` entries are allocated up front, and each later chunk on first use. Indexing with
/// a `u16` needs no bounds check when `C * N` is 65536.
struct Chunked<T, const C: usize, const N: usize> {
    first: Box<[T; C]>,
    /// The chunks after the first. Slot 0 is unused, because `first` holds the first chunk.
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
    fn get(&self, index: usize) -> Option<&T> {
        if index < C {
            return Some(&self.first[index]);
        }
        Some(&self.chunks.get(index / C)?.get()?[index % C])
    }

    fn get_or_grow(&self, index: usize) -> Option<&T> {
        if index < C {
            return Some(&self.first[index]);
        }
        Some(&self.chunks.get(index / C)?.get_or_init(Self::chunk)[index % C])
    }
}

#[derive(Default)]
struct Page {
    starts: [Cell<u64>; PAGE / 64],
    marks: [Cell<u64>; PAGE / 64],
    /// Bit mask of the lines that hold marked objects. It is built while marking.
    lines: Cell<u128>,
    /// Bit mask of the lines that the allocator cannot use. A sweep sets it to `lines`, and the allocator adds the lines of each hole it claims.
    used: Cell<u128>,
    cards: Cell<u32>,
    evacuating: Cell<bool>,
    /// Whether the page has been swept since the last major cycle finished marking.
    swept: Cell<bool>,
    /// The first page of a large object, if this page holds part of one. A large object has its own run of pages. Such a page is not
    /// evacuated, and a dirty card finds the object's header without scanning back to it.
    large: Cell<Option<u32>>,
    /// Whether the page's memory has been released to the system. Only a free page is released.
    released: Cell<bool>,
    /// Whether the page held any object when it was last swept. `Meta::occupied` counts these pages.
    counted: Cell<bool>,
}

/// Releases the free pages among `pages` to the system, in runs of adjacent pages. `pages` is in ascending order. The first free pages,
/// one nursery's worth, are kept. Only a page that the system released completely is refunded. Every other page stays
/// committed.
fn give_back(memory: &mut Region, meta: &Meta, pages: impl Iterator<Item = usize>) {
    let mut warm = meta.nursery / (PAGE * 8);
    let mut run: Option<Range<usize>> = None;
    for index in pages.map(Some).chain([None]) {
        let free = index.and_then(|index| meta.pages[..meta.used.get()].get(index)).is_some_and(|page| page.used.get() == 0 && !page.released.get());
        let release = if free && warm > 0 {
            warm -= 1;
            false
        } else {
            free
        };
        if let (Some(range), Some(index)) = (&mut run, index)
            && release
            && range.end == index
        {
            range.end += 1;
            continue;
        }
        if let Some(range) = run.take() {
            let words = memory.release(range.start * PAGE..range.end * PAGE);
            let gone = words.start.div_ceil(PAGE).max(range.start)..(words.end / PAGE).min(range.end);
            for page in meta.pages.get(gone).unwrap_or_default() {
                page.released.set(true);
                meta.budget.refund(PAGE_COST);
                meta.committed.set(meta.committed.get() - 1);
            }
        }
        if release {
            run = index.map(|index| index..index + 1);
        }
    }
}

/// A set of pages, stored as a bit set.
struct PageSet(Box<[Cell<u64>]>);

impl PageSet {
    fn new(pages: usize) -> Self {
        Self((0..pages.div_ceil(64)).map(|_| Cell::new(0)).collect())
    }

    #[inline]
    fn insert(&self, page: usize) {
        if let Some(word) = self.0.get(page / 64) {
            word.set(word.get() | 1 << (page % 64));
        }
    }

    fn insert_all(&self, pages: Range<usize>) {
        pages.for_each(|page| self.insert(page));
    }

    /// Returns the pages in the set, in ascending order. If `take` is true, the iterator also removes them from the set.
    fn iter(&self, take: bool) -> impl Iterator<Item = usize> + '_ {
        self.0.iter().enumerate().flat_map(move |(i, word)| {
            let mut bits = if take { word.replace(0) } else { word.get() };
            std::iter::from_fn(move || {
                let bit = (bits != 0).then(|| bits.trailing_zeros() as usize)?;
                bits &= bits - 1;
                Some(i * 64 + bit)
            })
        })
    }

    fn clear(&self) {
        self.0.iter().for_each(|word| word.set(0));
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Phase {
    Idle,
    Marking,
    /// Marking is done. Each page is swept in a later slice, or just before the allocator uses it.
    Sweeping,
}

/// A collection's work lists.
#[derive(Default)]
struct Work {
    gray: Vec<u32>,
    /// Slots that refer to objects on pages being evacuated. Each entry is the object that owns the slot, and the slot's word offset from that object's header. The offset is the field or item number plus one.
    fixups: Vec<(u32, u32)>,
    /// Traced objects that have weak fields or weak items.
    holders: Vec<u32>,
    /// Runs of weak items on dirty cards, as ranges of word indices. A minor collection clears the dead references in a run without visiting the rest of
    /// the object.
    weak_runs: Vec<(u32, u32)>,
    /// Traced objects that have ephemerons.
    ephemerons: Vec<u32>,
}

/// The arena's state, apart from the words of the region.
struct Meta {
    pages: Box<[Page]>,
    /// The number of pages handed out, counted from the start of the region. The pages among them that are not released are charged.
    used: Cell<usize>,
    budget: Budget,
    /// The hole that allocation bumps into. `cursor` is the next free word and `hole_end` is the end of the hole. `end` is the limit that the fast path checks. It equals `hole_end`, except while failures are injected. Then `end` is kept at `cursor`,
    /// so every allocation takes the slow path, which counts the allocation.
    cursor: Cell<usize>,
    end: Cell<usize>,
    hole_end: Cell<usize>,
    /// The line where the search for the next hole starts, as `page * LINES + line`.
    scan: Cell<usize>,
    /// The range that evacuation copies objects into. `to_cursor` is the next free word and `to_end` is the end of the range.
    to_cursor: Cell<usize>,
    to_end: Cell<usize>,
    /// Bytes allocated since the last collection.
    young: Cell<usize>,
    /// The number of pages that held an object when they were last swept.
    occupied: Cell<usize>,
    /// The pages allocated into since the allocator was last reset. Only these pages can hold young objects.
    /// Every other page holds only marked objects, so a minor collection has nothing to sweep there.
    young_pages: PageSet,
    /// Pages with dirty cards.
    dirty_pages: PageSet,
    /// The pages that a minor collection left free. `Arena::settle` releases them to the system, except for one nursery's worth.
    emptied: RefCell<Vec<u32>>,
    /// The number of pages charged to the budget: the pages handed out and not released.
    committed: Cell<usize>,
    /// Every page before this page has been swept.
    sweep_cursor: Cell<usize>,
    /// Whether a major cycle has swept every page since free pages were last released.
    settle: Cell<bool>,
    nursery: usize,
    /// A major cycle starts once `paced_bytes` reaches this many bytes.
    threshold: Cell<usize>,
    phase: Cell<Phase>,
    /// Whether this cycle evacuates the pages flagged at its start.
    evacuating: Cell<bool>,
    evacuate_all: Cell<bool>,
    /// The descriptor of each registered type, by type number. Fixed type numbers count up from 0. The other numbers are assigned downwards from the top.
    descs: Chunked<Cell<Option<&'static Desc>>, 256, { TYPES / 256 }>,
    /// One past the highest fixed number in use.
    low: Cell<usize>,
    /// The next number to assign to a type that has no fixed number.
    next: Cell<usize>,
    /// A cache of the type numbers of types that have no fixed number. The entry of a type is at [`cache_slot`] of its `TypeId`.
    cache: [Cell<Option<(TypeId, u16)>>; 64],
    roots: Box<[Cell<u64>]>,
    stacks: RefCell<Vec<Rc<StackRecord>>>,
    handles: RefCell<Vec<Rc<RootRecord>>>,
    /// The values that [`Handle`]s keep alive. Each handle holds the table too.
    rooted: Rc<RootTable>,
    /// An id that is unique to this arena. A handle that lives outside the arena stores it, to check that it is used with its own arena.
    id: u64,
    hosts: RefCell<Vec<HostSlot>>,
    free_hosts: RefCell<Vec<u32>>,
    /// Host values that a collection found dead. They are dropped after the collection has returned.
    dead_hosts: RefCell<Vec<Box<dyn Any>>>,
    frozen: FrozenTable,
    work: RefCell<Work>,
    /// The bytes last charged for the work lists and for the tables outside the region.
    tables: Cell<usize>,
    /// For testing barriers. If set, every step ends with a minor collection and a cycle slice of this many bytes.
    stress: Cell<Option<usize>>,
    /// The bytes of work that a running cycle does for each byte that steps allocate.
    pace: Cell<usize>,
    /// The bytes of work that steps owe the running cycle. The work is done once the debt reaches `MIN_SLICE`.
    debt: Cell<usize>,
    /// The value of `made` at which the current step owes the collector work. It is computed when the step starts.
    step_end: Cell<usize>,
    /// `cycle_work` is the work done so far in the current cycle, in bytes. `last_work` is the total work of the last finished cycle.
    cycle_work: Cell<usize>,
    last_work: Cell<usize>,
    collections: Cell<u64>,
    minors: Cell<u64>,
    /// The number of collections that moved objects. Identity tables rehash after each one.
    evacuations: Cell<u64>,
    /// The bytes charged for live host values.
    host_bytes: Cell<usize>,
    /// The generation at which a new host slot starts. It is at least the generation of every slot removed from the table, which is already above the generation of every reference to that slot. So a stale
    /// reference to a removed slot never reads a value that later gets the same id.
    host_floor: Cell<u32>,
}

#[derive(Clone, Copy)]
struct Heap<'a> {
    words: &'a [Cell<u64>; WORDS + SLACK],
    m: &'a Meta,
}

/// Wraps `index` into the region, so that indexing the region with the result needs no bounds check. A bad index reads
/// some other word, as a forged index would anyway. A small offset added to the result lands in `SLACK` at worst.
#[inline]
fn mask(index: usize) -> usize {
    index & (WORDS - 1)
}

const MIN_THRESHOLD: usize = 64 << 10;

impl Meta {
    /// Returns the heap size that pacing uses: the bytes of the occupied pages, plus the bytes charged for live host values and for old
    /// frozen values. Host values and old frozen values count because only a major collection frees them.
    fn paced_bytes(&self) -> usize {
        self.occupied.get() * PAGE * 8 + self.host_bytes.get() + self.frozen.live()
    }

    /// Returns an estimate of the work, in bytes, for a major cycle that starts now. The estimate is a quarter more than the work of the last cycle.
    /// Before the first cycle, it is the cost of tracing every occupied page and sweeping every page handed out.
    fn cycle_work(&self) -> usize {
        match self.last_work.get() {
            0 => self.occupied.get() * PAGE * 8 + self.used.get() * SWEEP_COST,
            last => last + last / 4,
        }
    }

    /// Returns the bytes that steps can allocate before they draw on the reserve. Committed pages that hold no object
    /// do not count as used, because they are kept for new objects to fill. The objects allocated since the
    /// last sweep do count, because they fill those pages.
    fn room(&self) -> usize {
        let pages = (self.committed.get() - self.occupied.get().min(self.committed.get())) * PAGE_COST;
        self.budget.room_past(self.budget.used().saturating_sub(pages) + self.young.get())
    }

    /// Returns whether a major cycle must start now to finish before the room runs out, when it is paced at up to `MAX_PACE`.
    /// If the room runs out first, the reserve forces a full collection, which is one pause as long as the
    /// whole cycle. A cycle that starts this late still frees as much as a full collection would. One slice's
    /// worth of room is kept for the allocations of the steps between slices.
    fn short_of_room(&self) -> bool {
        self.room() <= self.cycle_work() / MAX_PACE + MIN_SLICE
    }

    /// Returns the bytes that steps have allocated: the objects and frozen values allocated since the last collection, and
    /// the live host values.
    fn made(&self) -> usize {
        self.young_bytes() + self.host_bytes.get()
    }

    /// Returns the bytes of the objects and frozen values allocated since the last collection. A minor collection can
    /// free these.
    fn young_bytes(&self) -> usize {
        self.young.get() + self.frozen.young_bytes()
    }

    /// Returns the bytes that a step can allocate before it owes the collector work. [`Arena::step`] does that work
    /// when the step ends: a minor collection once the nursery is full, the start of a major cycle once
    /// a cycle is due, or a slice of the running cycle.
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

/// Shrinks the capacity of `table` if most of it is unused. Some spare capacity is kept, so the table does not regrow at once.
fn shrink<T>(table: &mut Vec<T>) {
    if table.capacity() > 4 * table.len() + 64 {
        table.shrink_to(2 * table.len() + 16);
    }
}
/// The bytes charged for a committed page: its words and its `Page` record.
const PAGE_COST: usize = PAGE * 8 + size_of::<Page>();
/// Sweeping one page counts as this many bytes of slice work.
const SWEEP_COST: usize = PAGE;
const MIN_SLICE: usize = 64 << 10;
const STEP_MUL: usize = 2;
const MAX_PACE: usize = 16;
/// The most dead host values, and the most dead frozen values, that are freed after one step.
const FREE_BATCH: usize = 1024;

pub struct Arena {
    memory: Region,
    meta: Meta,
}

impl Arena {
    /// Creates an arena with a limit of `limit` bytes and `roots` value roots. The page table is allocated up
    /// front for twice the limit and is not charged. The roots are charged. Objects in the region take at
    /// most [`REGION`] bytes, whatever the limit is. Frozen and host values can use the rest of the limit.
    ///
    /// # Panics
    ///
    /// Panics if the system cannot reserve the region's address space. [`Arena::try_new`] returns an error
    /// instead.
    pub fn new(limit: usize, roots: usize) -> Self {
        Self::try_new(limit, roots).expect("reserve the arena's memory")
    }

    /// Like [`Arena::new`], but returns `OutOfMemory` if the system cannot reserve the region's address space.
    pub fn try_new(limit: usize, roots: usize) -> Result<Self, OutOfMemory> {
        let memory = Region::new(WORDS + SLACK).ok_or(OutOfMemory)?;
        // Page 0 holds no object, so index 0 can mean no object. The page table covers twice the limit, so evacuation has room
        // to copy every object.
        let pages = (limit / (PAGE * 8)).clamp(1, PAGES / 2 - 1);
        let count = 2 * pages + 2;
        let id = NEXT_ARENA.fetch_add(1, Ordering::Relaxed);
        let meta = Meta {
            pages: (0..count).map(|_| Page::default()).collect(),
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
            young_pages: PageSet::new(count),
            dirty_pages: PageSet::new(count),
            emptied: RefCell::new(Vec::new()),
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
            // One more root, after the program's roots, holds the arena's intern table.
            roots: vec![Cell::new(Value::NULL.word); roots + 1].into_boxed_slice(),
            stacks: RefCell::new(Vec::new()),
            handles: RefCell::new(Vec::new()),
            rooted: Rc::new(RootTable::new(id)),
            id,
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

    /// Runs at the end of every collection entry point. Releases free pages to the system, and drops dead host values, so that
    /// their destructors run outside the collector.
    ///
    /// Drops at most `free` dead host values and at most `free` dead frozen values. The rest are dropped later. A cycle
    /// can leave a great many, and dropping them all at once would be a pause of its own.
    fn finish(&mut self, free: usize) {
        self.settle();
        let dead = {
            let mut dead = self.meta.dead_hosts.borrow_mut();
            let keep = dead.len().saturating_sub(free);
            dead.split_off(keep)
        };
        drop(dead);
        let meta = &mut self.meta;
        meta.frozen.free_dead(&meta.budget, free);
        self.charge_tables();
    }

    /// Charges the budget for the current capacity of the work lists and of the tables outside the region. They grow
    /// during collections, which cannot fail, so they are charged afterwards.
    fn charge_tables(&self) {
        let meta = &self.meta;
        let work = meta.work.borrow();
        let bytes = (work.gray.capacity() + work.holders.capacity() + work.ephemerons.capacity()) * size_of::<u32>()
            + (work.fixups.capacity() + work.weak_runs.capacity()) * size_of::<(u32, u32)>()
            + meta.hosts.borrow().capacity() * size_of::<HostSlot>()
            + meta.free_hosts.borrow().capacity() * size_of::<u32>()
            + meta.dead_hosts.borrow().capacity() * size_of::<Box<dyn Any>>()
            + meta.stacks.borrow().capacity() * size_of::<Rc<StackRecord>>()
            + meta.handles.borrow().capacity() * size_of::<Rc<RootRecord>>()
            + meta.rooted.bytes()
            + meta.frozen.table_bytes();
        let before = meta.tables.replace(bytes);
        if bytes > before {
            meta.budget.force(bytes - before);
        } else {
            meta.budget.refund(before - bytes);
        }
    }

    /// Runs once a collection has swept. Releases the pages that the collection freed, except for one nursery's
    /// worth, which the next steps would fill again. Then lowers the count of pages handed out, so that it ends at the last
    /// page still committed. A major cycle may have freed any page. A minor collection may have freed only the pages in `emptied`.
    fn settle(&mut self) {
        let Self { memory, meta } = self;
        if meta.phase.get() != Phase::Idle {
            return;
        }
        let emptied = std::mem::take(&mut *meta.emptied.borrow_mut());
        if meta.settle.replace(false) {
            give_back(memory, meta, 1..meta.used.get());
        } else if !emptied.is_empty() {
            give_back(memory, meta, emptied.into_iter().map(|page| page as usize));
        } else {
            return;
        }
        // The pages after the last committed page are handed out again as fresh pages.
        let used = meta.used.get();
        meta.used.set((1..used).rev().find(|&page| !meta.pages[page].released.get()).map_or(1, |page| page + 1));
    }

    pub fn mutate<R>(&mut self, body: impl for<'gc> FnOnce(&Mutation<'gc>) -> R) -> R {
        let meta = &self.meta;
        meta.step_end.set(meta.made().saturating_add(meta.step_allowance()));
        body(&Mutation { heap: self.heap(), _brand: PhantomData })
    }

    /// Runs `body` like `mutate`, then paces collection. A minor collection runs once the nursery is full. A
    /// major cycle starts once the occupied pages, plus the bytes charged for live host and frozen values, reach
    /// the threshold. The threshold is twice the size that the last cycle left. A cycle starts sooner if the room under the reserve
    /// would otherwise run out before the cycle finishes. Each step owes the cycle twice the bytes it allocated,
    /// or more when room is short. The debt is paid in slices of at least `MIN_SLICE`. One batch of dead host and frozen
    /// values is freed after each step.
    ///
    /// If `body` drew on the reserve, a full collection runs instead. If an allocation failed,
    /// even one that `body` then did without, the result is dropped, a full collection runs, and the
    /// step fails. Everything `body` did before the failure stays done, so the caller continues from
    /// there. An interpreter, for example, runs the failed instruction again.
    pub fn step<R>(&mut self, body: impl for<'gc> FnOnce(&Mutation<'gc>) -> R) -> Result<R, OutOfMemory> {
        self.meta.budget.clear_failed();
        let before = self.meta.made();
        let result = self.mutate(body);
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
        let meta = &self.meta;
        if meta.phase.get() == Phase::Idle && meta.young_bytes() >= meta.nursery {
            self.heap().minor();
        }
        let meta = &self.meta;
        if meta.phase.get() == Phase::Idle && (meta.paced_bytes() >= meta.threshold.get() || meta.short_of_room()) {
            if meta.young_bytes() > 0 {
                self.heap().minor();
            }
            self.heap().start();
            // Set a pace that finishes the cycle before the room runs out.
            let meta = &self.meta;
            meta.pace.set(meta.cycle_work().div_ceil(meta.room().max(1)).max(STEP_MUL));
            meta.debt.set(0);
        }
        let meta = &self.meta;
        if meta.phase.get() != Phase::Idle {
            let debt = meta.debt.get().saturating_add(allocated.saturating_mul(meta.pace.get()));
            meta.debt.set(debt);
            if debt >= MIN_SLICE {
                meta.debt.set(0);
                self.heap().work(debt);
            }
        }
        self.finish(FREE_BATCH);
        Ok(result)
    }

    /// Finishes any cycle in progress, then runs a full cycle.
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

    /// Starts a cycle if none is running, then does about `work` bytes of work on it. Like a step, it
    /// frees only one batch of the dead host and frozen values.
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

    /// Returns the bytes of the pages handed out, counted from the start of the region. The count drops when the pages at its end are released to the system.
    pub fn pages_bytes(&self) -> usize {
        (self.meta.used.get() - 1) * PAGE * 8
    }

    /// Returns the bytes of the pages handed out and not released. This is about the memory that the arena holds.
    pub fn committed_bytes(&self) -> usize {
        let meta = &self.meta;
        let pages = &meta.pages[1..meta.used.get()];
        (pages.len() - pages.iter().filter(|page| page.released.get()).count()) * PAGE * 8
    }

    /// Returns the bytes of the pages that held an object when they were last swept.
    pub fn occupied_bytes(&self) -> usize {
        self.meta.occupied.get() * PAGE * 8
    }

    /// Returns the number of marked objects. After [`Arena::collect`], these are the live objects.
    pub fn objects(&self) -> usize {
        let pages = &self.meta.pages[..self.meta.used.get()];
        pages.iter().flat_map(|page| page.starts.iter().zip(&page.marks)).map(|(start, mark)| (start.get() & mark.get()).count_ones() as usize).sum()
    }

    pub fn hosts(&self) -> usize {
        self.meta.hosts.borrow().len()
    }

    /// Returns the number of values that [`Handle`]s keep alive in the arena's root table. A value with several handles counts once for each.
    pub fn handles(&self) -> usize {
        self.meta.rooted.held()
    }

    /// Returns the bytes that the root table takes, for tests that check that it does not grow.
    #[cfg(test)]
    pub(crate) fn root_table_bytes(&self) -> usize {
        self.meta.rooted.bytes()
    }

    /// Returns the number of frozen values not yet freed. The count includes values that a collection found dead and
    /// that are still waiting to be freed.
    pub fn frozen_values(&self) -> usize {
        self.meta.frozen.count()
    }

    /// Returns the bytes charged against the limit: committed pages, roots, stacks, host values, frozen values, the
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

    /// Sets the reserve to `bytes`. The reserve is the last part of the limit. It lets a step finish once the rest is used.
    /// Optional allocations do not draw on it. The default is a sixteenth of the limit.
    pub fn set_reserve(&mut self, bytes: usize) {
        self.meta.budget.set_reserve(bytes);
    }

    /// For testing. Lets `allocations` more allocations succeed, then fails the next one, once. `None` turns failure injection off.
    /// Allocations of objects, host values, frozen values, stacks and roots count.
    pub fn fail_after(&mut self, allocations: Option<u64>) {
        let meta = &self.meta;
        meta.budget.fail_after(allocations);
        meta.end.set(if meta.budget.injecting() { meta.cursor.get() } else { meta.hole_end.get() });
    }

    /// For testing. Makes every step end with a minor collection and a cycle slice of `work` bytes. `None` turns this off.
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
    /// Allocates a `T` whose fields hold the words in `fields`. `objects!` constructors call it.
    #[doc(hidden)]
    #[inline]
    pub fn alloc<T: Object, const N: usize>(&self, fields: [u64; N]) -> Result<Gc<'gc, T>, OutOfMemory> {
        self.heap.alloc_fixed(&T::DESC, &fields).map(Gc::new)
    }

    /// Like `alloc_items`, with every item set to the zero word. The zero word reads as fixnum 0, as no object, or as the word 0, depending on the kind of items. The function is small
    /// enough to inline, for objects that are allocated often with few items.
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

    pub fn root(&self, index: usize) -> Value<'gc> {
        let roots = &self.heap.m.roots;
        Value::from_bits(roots[..roots.len() - 1][index].get())
    }

    pub fn set_root(&self, index: usize, value: Value<'gc>) {
        let roots = &self.heap.m.roots;
        roots[..roots.len() - 1][index].set(value.word);
    }

    /// Returns the root that holds the arena's intern table, once the table exists.
    pub(crate) fn interned(&self) -> &Cell<u64> {
        self.heap.m.roots.last().expect("the arena has a root for its intern table")
    }

    /// Returns the number of collections so far that moved objects. A hash of an object's index stays valid only
    /// while this number is unchanged.
    pub(crate) fn moves(&self) -> u64 {
        self.heap.m.evacuations.get()
    }

    /// Stores `value` as a host value and returns a reference to it. The value is charged its size plus `HOST_COST`. Memory that the value owns elsewhere, such as a
    /// `String`'s bytes, can be counted with [`HostRef::set_owned_bytes`].
    pub fn host<T: Any>(&self, value: T) -> Result<HostRef<'gc, T>, HostError> {
        let meta = self.heap.m;
        let mut hosts = meta.hosts.try_borrow_mut().map_err(|_| HostError::InUse)?;
        meta.budget.count_allocation()?;
        let cost = size_of::<T>() + HOST_COST;
        meta.budget.ensure(cost)?;
        // A host value created while marking starts marked, so it survives the cycle, as a new object does.
        let marked = meta.phase.get() == Phase::Marking;
        let value: Box<dyn Any> = Box::new(value);
        let id = match meta.free_hosts.borrow_mut().pop() {
            Some(id) => id,
            None => {
                let Some(id) = u32::try_from(hosts.len()).ok().filter(|&id| id < u32::MAX) else {
                    return Err(meta.budget.fail().into());
                };
                if hosts.len() == hosts.capacity() {
                    // The table is charged as it grows, so growing it can fail as an allocation can.
                    let more = hosts.capacity().max(16);
                    meta.budget.ensure(cost + more * size_of::<HostSlot>())?;
                    let before = hosts.capacity();
                    hosts.reserve_exact(more);
                    let grown = (hosts.capacity() - before) * size_of::<HostSlot>();
                    meta.budget.force(grown);
                    meta.tables.set(meta.tables.get() + grown);
                }
                hosts.push(HostSlot { generation: meta.host_floor.get(), marked: false, cost: 0, owned: 0, value: None });
                id
            }
        };
        meta.budget.force(cost);
        let slot = &mut hosts[id as usize];
        slot.value = Some(value);
        slot.marked = marked;
        slot.cost = cost;
        slot.owned = 0;
        meta.host_bytes.set(meta.host_bytes.get() + cost);
        Ok(HostRef { id, generation: slot.generation, _marker: PhantomData })
    }

    /// Stores `value` outside the region as a frozen value, which is read as `&'gc T` and never changes. A
    /// `Frozen<T>` field holds the returned reference. Store the reference in an object during this step. The
    /// next collection frees a frozen value that no object holds.
    pub fn frozen<T: Any>(&self, value: T) -> Result<FrozenRef<'gc, T>, OutOfMemory> {
        self.frozen_owning(value, 0)
    }

    /// Like [`Mutation::frozen`], and also charges `bytes` for memory that `value` owns outside the arena, such
    /// as a string's characters. The charge lasts until the value is freed.
    pub fn frozen_owning<T: Any>(&self, value: T, bytes: usize) -> Result<FrozenRef<'gc, T>, OutOfMemory> {
        let meta = self.heap.m;
        meta.frozen.alloc(&meta.budget, false, value, bytes).map(FrozenRef::new)
    }

    /// Runs `allocate`, whose allocations the caller can do without, such as growing a buffer by more than it
    /// needs. A failed allocation in `allocate` does not fail the step, and the allocations do not draw on the reserve.
    pub fn optional<R>(&self, allocate: impl FnOnce() -> Result<R, OutOfMemory>) -> Result<R, OutOfMemory> {
        self.heap.m.budget.optional(allocate)
    }

    /// Fails the step as a failed allocation does, and returns the error. Use it for a request so large that its size cannot be computed.
    pub fn out_of_memory(&self) -> OutOfMemory {
        self.heap.m.budget.fail()
    }

    /// Returns whether an allocation has drawn on the reserve, which makes a full collection due. An
    /// interpreter checks it between instructions and ends the step, so that the collection runs.
    pub fn collection_due(&self) -> bool {
        self.heap.m.budget.due()
    }

    /// Returns whether the step has allocated enough that [`Arena::step`] owes the collector work when the step
    /// ends, or whether a full collection is due. An interpreter checks it after it allocates, and ends
    /// the step at the next point where it can resume. That keeps collection up with allocation.
    pub fn step_due(&self) -> bool {
        let meta = self.heap.m;
        meta.made() >= meta.step_end.get() || meta.budget.due()
    }

    /// Returns an empty [`Charge`] against the budget, for memory kept outside the arena.
    pub fn charge(&self) -> Charge<'gc> {
        Charge::new(self)
    }

    /// Checks whether `bytes` more bytes fit in the budget, as an allocation of `bytes` does, without charging them.
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

/// Returns the index in `Meta::cache` for `type_id`. A `TypeId` is already a hash, so the index comes from the bits that the `TypeId`'s `Hash` impl writes, with no further mixing.
#[inline]
fn cache_slot(type_id: TypeId) -> usize {
    struct Bits(u64);
    impl std::hash::Hasher for Bits {
        fn finish(&self) -> u64 {
            self.0
        }
        fn write(&mut self, bytes: &[u8]) {
            for &byte in bytes {
                self.0 = self.0.rotate_left(8) ^ u64::from(byte);
            }
        }
        fn write_u64(&mut self, number: u64) {
            self.0 ^= number;
        }
    }
    let mut bits = Bits(0);
    std::hash::Hash::hash(&type_id, &mut bits);
    (bits.0 as usize) % 64
}

impl<'a> Heap<'a> {
    #[inline]
    fn type_index(self, desc: &'static Desc) -> Option<u16> {
        // A type with a fixed number is registered at that number in `descs`. A type without one is looked up in the cache.
        let found = if let Some(ty) = desc.number {
            self.m.descs.get(usize::from(ty)).and_then(Cell::get).filter(|registered| registered.type_id == desc.type_id).map(|_| ty)
        } else {
            self.m.cache[cache_slot(desc.type_id)].get().filter(|&(type_id, _)| type_id == desc.type_id).map(|(_, ty)| ty)
        };
        found.or_else(|| self.type_index_slow(desc))
    }

    #[inline(never)]
    fn type_index_slow(self, desc: &'static Desc) -> Option<u16> {
        let (meta, next) = (self.m, self.m.next.get());
        let ty = if let Some(ty) = desc.number {
            let ty = usize::from(ty);
            if ty > next {
                return None;
            }
            let slot = meta.descs.get_or_grow(ty)?;
            match slot.get() {
                None => slot.set(Some(desc)),
                Some(registered) if registered.type_id == desc.type_id => {}
                Some(_) => panic!("two types have type number {ty}: declare one objects! group `after` the other"),
            }
            meta.low.set(meta.low.get().max(ty + 1));
            ty
        } else {
            match (next + 1..TYPES).find(|&i| meta.descs.get(i).and_then(Cell::get).is_some_and(|other| other.type_id == desc.type_id)) {
                Some(ty) => ty,
                None if next < meta.low.get() => return None,
                None => {
                    meta.descs.get_or_grow(next)?.set(Some(desc));
                    meta.next.set(next - 1);
                    next
                }
            }
        };
        if desc.number.is_none() {
            self.m.cache[cache_slot(desc.type_id)].set(Some((desc.type_id, ty as u16)));
        }
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

    /// Like `alloc`, for an object without items. This is the common case. It is small enough to inline at every call site.
    /// LLVM stops inlining `alloc` once there are a few dozen call sites.
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

    /// Marks the new object at `at`. An object allocated while marking is marked. It is also queued for tracing, in case it is stored in an object
    /// that has already been traced.
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
        self.set_bit(at, |page| &page.starts);
        Ok(at)
    }

    #[inline(never)]
    fn reserve_slow(self, size: usize) -> Result<usize, OutOfMemory> {
        let meta = self.m;
        meta.budget.count_allocation()?;
        // The object still fits in the hole if failures are being injected, or if injection has just stopped. In both cases `end` was below `hole_end`.
        let at = meta.cursor.get();
        if at + size <= meta.hole_end.get() {
            meta.cursor.set(at + size);
            meta.end.set(if meta.budget.injecting() { at + size } else { meta.hole_end.get() });
            return Ok(at);
        }
        if size > PAGE - LINE {
            // A large object gets its own run of free pages. Its lines are marked used, so nothing else is allocated on them.
            let count = size.div_ceil(PAGE);
            let first = match self.free_run(count, false)? {
                Some(first) => first,
                None => self.fresh_pages(count)?,
            };
            self.cover_lines(first * PAGE, size, |page| &page.used);
            self.m.pages[first..first + count].iter().for_each(|page| page.large.set(Some(first as u32)));
            return Ok(first * PAGE);
        }
        loop {
            let (start, end) = match self.next_hole()? {
                Some(hole) => hole,
                None => {
                    let page = self.fresh_pages(1)?;
                    meta.pages[page].used.set(u128::MAX);
                    meta.scan.set((page + 1) * LINES);
                    (page * PAGE, (page + 1) * PAGE)
                }
            };
            if end - start >= size {
                meta.cursor.set(start + size);
                meta.hole_end.set(end);
                meta.end.set(if meta.budget.injecting() { start + size } else { end });
                return Ok(start);
            }
        }
    }

    /// Claims the next run of free lines in the pages handed out. Returns the run's word range, or `None` if no page from `scan` on has a free line.
    fn next_hole(self) -> Result<Option<(usize, usize)>, OutOfMemory> {
        let mut scan = self.m.scan.get();
        while scan < self.m.used.get() * LINES {
            let (page, line) = (scan / LINES, scan % LINES);
            self.sweep_before_use(page);
            let entry = &self.m.pages[page];
            let used = entry.used.get();
            let free = !used & (u128::MAX << line);
            // Filling pages chosen for evacuation would undo the compaction.
            if free == 0 || entry.evacuating.get() {
                scan = (page + 1) * LINES;
                continue;
            }
            self.recommit(page..page + 1)?;
            self.m.young_pages.insert(page);
            // `free` holds the free lines at or after `line`. The hole runs from the first free line, `start`, to the next used line, `end`. If no used line follows, `end` is `LINES`.
            // The last mask has bits `start..end` set, which marks the hole's lines as used. `end` is above `start`, so the shift by `LINES - end` is at most 127.
            let start = free.trailing_zeros() as usize;
            let end = (used & (u128::MAX << start)).trailing_zeros() as usize;
            entry.used.set(used | (u128::MAX >> (LINES - end)) & (u128::MAX << start));
            self.m.scan.set(page * LINES + end);
            return Ok(Some((page * PAGE + start * LINE, page * PAGE + end * LINE)));
        }
        self.m.scan.set(scan);
        Ok(None)
    }

    /// Charges the budget again for the pages in `pages` that were released to the system, before they are reused.
    fn recommit(self, pages: Range<usize>) -> Result<(), OutOfMemory> {
        let pages = &self.m.pages[pages];
        let released = pages.iter().filter(|page| page.released.get()).count();
        if released > 0 {
            self.m.budget.charge(released * PAGE_COST)?;
            self.m.committed.set(self.m.committed.get() + released);
            pages.iter().for_each(|page| page.released.set(false));
        }
        Ok(())
    }

    /// Returns the first page of a run of `count` adjacent free pages among the pages handed out, or `None` if there is no such run. If `evacuation` is true, pages being evacuated
    /// are skipped, because evacuation cannot copy onto them.
    fn free_run(self, count: usize, evacuation: bool) -> Result<Option<usize>, OutOfMemory> {
        let mut run = 0;
        for index in 1..self.m.used.get() {
            self.sweep_before_use(index);
            let page = &self.m.pages[index];
            let free = page.used.get() == 0 && !(evacuation && page.evacuating.get());
            run = if free { run + 1 } else { 0 };
            if run == count {
                let first = index + 1 - count;
                self.recommit(first..index + 1)?;
                self.m.young_pages.insert_all(first..index + 1);
                return Ok(Some(first));
            }
        }
        Ok(None)
    }

    fn fresh_pages(self, count: usize) -> Result<usize, OutOfMemory> {
        let first = self.m.used.get();
        if first + count > self.m.pages.len() {
            return Err(self.m.budget.fail());
        }
        self.m.budget.charge(count * PAGE_COST)?;
        self.m.committed.set(self.m.committed.get() + count);
        self.m.used.set(first + count);
        self.m.young_pages.insert_all(first..first + count);
        // A fresh page holds no object from before the cycle, so the lazy sweep has nothing to do on it.
        for page in &self.m.pages[first..first + count] {
            page.swept.set(true);
            page.released.set(false);
        }
        Ok(first)
    }

    /// Sweeps `page` if the lazy sweep has not reached it yet. The allocator calls this before it reads the page's lines, so it never sees stale lines.
    #[inline]
    fn sweep_before_use(self, page: usize) {
        if self.m.phase.get() == Phase::Sweeping && !self.m.pages[page].swept.get() {
            self.sweep_page(page);
        }
    }

    /// Abandons the current hole. The search for the next hole starts from line `scan`.
    fn reset_allocator(self, scan: usize) {
        self.m.cursor.set(0);
        self.m.end.set(0);
        self.m.hole_end.set(0);
        self.m.scan.set(scan);
        self.m.young.set(0);
    }

    #[inline]
    fn set_bit(self, index: usize, bits: impl FnOnce(&Page) -> &[Cell<u64>; PAGE / 64]) {
        let word = &bits(&self.m.pages[index / PAGE])[index % PAGE / 64];
        word.set(word.get() | 1 << (index % 64));
    }

    fn has_bit(self, index: usize, bits: impl FnOnce(&Page) -> &[Cell<u64>; PAGE / 64]) -> bool {
        self.m.pages.get(index / PAGE).is_some_and(|page| bits(page)[index % PAGE / 64].get() & 1 << (index % 64) != 0)
    }

    /// Sets the bits of the lines that the `size` words at `start` cover. `lines` selects one of a page's line maps, `Page::lines` or `Page::used`.
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
            let cards = page.cards.get();
            if cards == 0 {
                self.m.dirty_pages.insert(slot / PAGE);
            }
            page.cards.set(cards | 1 << (slot % PAGE / CARD));
        }
    }

    /// Marks the host value that `word` refers to, if the generation of its slot still matches.
    fn mark_host(self, word: u64) {
        let Some((id, generation)) = host_parts(word) else { return };
        if let Some(host) = self.m.hosts.borrow_mut().get_mut(id as usize).filter(|host| host.generation == generation) {
            host.marked = true;
        }
    }

    #[inline]
    fn ephemeron_at(self, slot: usize) -> Option<(Value<'a>, Value<'a>)> {
        let key = Value::from_bits(self.words[slot].get());
        (key != Value::BROKEN).then(|| (key, Value::from_bits(self.words[slot + 1].get())))
    }

    /// Stores an ephemeron's `key` and `value` at `slot`. Neither is shaded while marking, because the value is traced once the key is found live.
    /// Both cards are marked dirty, so a minor collection sees both words.
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
        // A minor collection traces only marked objects from their dirty cards. An unmarked owner is young,
        // and is traced anyway if it is reachable.
        if self.has_bit(owner as usize, |page| &page.marks) {
            self.dirty(slot);
            if self.m.phase.get() == Phase::Marking {
                shade(self.words, self.m, slot, owner, target);
            }
        }
    }

    /// Handles a store of `target` into `slot` of `owner` while marking. If `owner` is marked, marks `target`. If `target` is on a page being
    /// evacuated, also records the slot as a fixup.
    fn shade(self, slot: usize, owner: u32, target: u32) {
        if self.has_bit(owner as usize, |page| &page.marks) {
            self.shade_marked(slot, owner, target);
        }
    }

    fn shade_marked(self, slot: usize, owner: u32, target: u32) {
        let mut work = self.m.work.borrow_mut();
        self.mark(target, &mut work);
        if self.m.evacuating.get() && self.in_evacuation(target) {
            // The fixup position is the slot's word offset from the header: the field or item number plus one.
            work.fixups.push((owner, (slot - owner as usize) as u32));
        }
    }

    /// Marks the cards under `slots` dirty. `at` is the word index of the first slot. While marking, also shades the target of each slot. `refs` tells
    /// how to read the target from a slot's word.
    fn barrier_range(self, at: usize, slots: &[Cell<u64>], owner: u32, refs: Refs) {
        if slots.is_empty() {
            return;
        }
        let (mut i, end) = (at, at + slots.len());
        while i < end {
            let Some(page) = self.m.pages.get(i / PAGE) else { return };
            let to = end.min((i / PAGE + 1) * PAGE);
            let (first, last) = (i % PAGE / CARD, (to - 1) % PAGE / CARD);
            page.cards.set(page.cards.get() | ((u64::MAX >> (63 - last)) & (u64::MAX << first)) as u32);
            self.m.dirty_pages.insert(i / PAGE);
            i = to;
        }
        if self.m.phase.get() == Phase::Marking && matches!(refs, Refs::Values | Refs::Members) {
            for (offset, slot) in slots.iter().enumerate() {
                if let Some(target) = refs.target(slot.get()) {
                    self.shade(at + offset, owner, target);
                }
            }
        }
    }

    fn in_evacuation(self, index: u32) -> bool {
        self.m.pages.get(index as usize / PAGE).is_some_and(|page| page.evacuating.get())
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
        self.sweep_young();
        self.m.minors.set(self.m.minors.get() + 1);
        *self.m.work.borrow_mut() = work;
    }

    /// Starts a major cycle: clears the marks and marks the roots.
    fn start(self) {
        let meta = self.m;
        if meta.phase.get() != Phase::Idle {
            return;
        }
        // A page is a candidate for evacuation if at most a quarter of it is in use. Candidates are taken while half of the free room can hold their objects.
        // Pages of large objects are never evacuated.
        let pages = &meta.pages[..meta.used.get()];
        let all = meta.evacuate_all.get();
        let occupied: usize = pages.iter().map(|page| page.used.get().count_ones() as usize * LINE).sum();
        let mut room = (meta.budget.limit() / 8).saturating_sub(occupied) / 2;
        let mut count = 0;
        for page in pages {
            page.marks.iter().for_each(|word| word.set(0));
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
        meta.dirty_pages.clear();
        let evacuating = count > 1 || all && count > 0;
        if !evacuating {
            pages.iter().for_each(|page| page.evacuating.set(false));
        }
        meta.hosts.borrow_mut().iter_mut().for_each(|host| host.marked = false);
        meta.frozen.clear_marks();
        meta.evacuating.set(evacuating);
        meta.to_cursor.set(0);
        meta.to_end.set(0);
        meta.phase.set(Phase::Marking);
        meta.cycle_work.set(0);
        let mut work = std::mem::take(&mut *meta.work.borrow_mut());
        work.fixups.clear();
        work.holders.clear();
        work.weak_runs.clear();
        work.ephemerons.clear();
        self.mark_roots(&mut work);
        *meta.work.borrow_mut() = work;
    }

    /// Does about `budget` bytes of work on the cycle: marking, then the atomic phase once nothing is left
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

    /// Traces gray objects until `budget` bytes of work are done. Returns the budget that is left if no gray object
    /// remains, and `None` otherwise.
    fn drain(self, work: &mut Work, budget: usize) -> Option<usize> {
        let mut left = budget;
        while left > 0 {
            let Some(index) = work.gray.pop() else { return Some(left) };
            left = left.saturating_sub(self.trace(index as usize, work) * 8);
        }
        work.gray.is_empty().then_some(0)
    }

    /// Ends marking in one atomic phase. Rescans the roots, because a write to a root applies no barrier. Then clears dead weak references,
    /// moves the objects being evacuated, and frees dead host values. Sweeping follows.
    fn atomic(self, work: &mut Work) {
        let meta = self.m;
        self.mark_roots(work);
        self.drain(work, usize::MAX);
        self.trace_ephemerons(work);
        self.clear_weaks(work);
        if meta.evacuating.get() {
            self.evacuate(work);
            meta.evacuations.set(meta.evacuations.get() + 1);
        }
        meta.frozen.sweep_all();
        self.sweep_hosts();
        for page in &meta.pages[..meta.used.get()] {
            page.cards.set(0);
            page.evacuating.set(false);
            page.swept.set(false);
        }
        meta.dirty_pages.clear();
        meta.young_pages.clear();
        self.reset_allocator(LINES);
        meta.evacuating.set(false);
        meta.sweep_cursor.set(0);
        meta.phase.set(Phase::Sweeping);
        work.fixups.clear();
        work.holders.clear();
        work.weak_runs.clear();
        work.ephemerons.clear();
    }

    /// Frees the host values that marking did not reach. Then removes the free slots at the end of the table,
    /// and shrinks the table's capacity. The free list hands out the lowest ids
    /// first, so live values gather at the front and the end of the table keeps emptying.
    fn sweep_hosts(self) {
        #[inline(always)]
        fn free(host: &HostSlot) -> bool {
            host.value.is_none() && host.generation < u32::MAX
        }
        let meta = self.m;
        let mut hosts = meta.hosts.borrow_mut();
        let mut dead = meta.dead_hosts.borrow_mut();
        for host in hosts.iter_mut() {
            if !host.marked && let Some(value) = host.value.take() {
                dead.push(value);
                meta.budget.refund(host.cost);
                meta.host_bytes.set(meta.host_bytes.get() - std::mem::take(&mut host.cost));
                // A slot whose generation reaches `u32::MAX` is retired and is never reused.
                host.generation = host.generation.saturating_add(1);
            }
        }
        let len = hosts.iter().rposition(|host| !free(host)).map_or(0, |index| index + 1);
        let floor = hosts[len..].iter().map(|host| host.generation).max().unwrap_or(0);
        meta.host_floor.set(meta.host_floor.get().max(floor));
        hosts.truncate(len);
        shrink(&mut hosts);
        let mut ids = meta.free_hosts.borrow_mut();
        ids.clear();
        ids.extend((0..len as u32).rev().filter(|&id| free(&hosts[id as usize])));
        shrink(&mut ids);
    }

    fn finish_cycle(self) {
        let meta = self.m;
        // A fresh page handed out during sweeping was never swept, so every page is counted again here.
        let mut occupied = 0;
        for page in &meta.pages[..meta.used.get()] {
            page.counted.set(page.used.get() != 0);
            occupied += usize::from(page.counted.get());
        }
        meta.occupied.set(occupied);
        let size = meta.paced_bytes();
        let limit = meta.budget.limit();
        meta.threshold.set((size * 2).max(MIN_THRESHOLD).min(size + limit.saturating_sub(size) / 2));
        meta.last_work.set(meta.cycle_work.get());
        meta.phase.set(Phase::Idle);
        meta.settle.set(true);
        meta.collections.set(meta.collections.get() + 1);
    }

    fn mark_roots(self, work: &mut Work) {
        for root in &self.m.roots {
            self.visit(root, work);
        }
        let mut stacks = self.m.stacks.borrow_mut();
        for stack in stacks.iter() {
            stack.trace(self, work, Rc::strong_count(stack) == 1);
        }
        // A dropped stack has now been traced one last time, which covers its last writes. Remove its record and refund its cost.
        let before = stacks.len();
        stacks.retain(|stack| Rc::strong_count(stack) > 1);
        self.m.budget.refund((before - stacks.len()) * STACK_COST);
        let mut handles = self.m.handles.borrow_mut();
        let before = handles.len();
        handles.retain(|handle| Rc::strong_count(handle) > 1);
        self.m.budget.refund((before - handles.len()) * ROOT_COST);
        for handle in handles.iter() {
            self.visit(&handle.word, work);
        }
        // A free slot holds 0, which refers to no object.
        for slot in self.m.rooted.slots().iter() {
            self.visit(slot, work);
        }
    }

    /// Sweeps all young pages at once and clears the dirty cards, for a minor collection. The
    /// allocator then searches again from the first young page with a free line, if that page is before `scan`. The pages before it that the allocator
    /// has already passed were full, and they still are.
    fn sweep_young(self) {
        let meta = self.m;
        for page in meta.dirty_pages.iter(true) {
            meta.pages[page].cards.set(0);
        }
        let (mut first, mut emptied) = (None, meta.emptied.borrow_mut());
        for page in meta.young_pages.iter(true) {
            self.sweep_page(page);
            let used = meta.pages[page].used.get();
            if used != u128::MAX {
                first = first.or(Some(page));
            }
            if used == 0 {
                emptied.push(page as u32);
            }
        }
        self.reset_allocator(first.map_or(meta.scan.get(), |page| meta.scan.get().min(page * LINES)));
    }

    /// Sweeps page `index`. Frees the objects that were not marked, and makes every line without a marked object available to the allocator.
    fn sweep_page(self, index: usize) {
        let page = &self.m.pages[index];
        for (start, mark) in page.starts.iter().zip(&page.marks) {
            start.set(start.get() & mark.get());
        }
        let lines = page.lines.get();
        page.used.set(lines);
        if page.counted.replace(lines != 0) != (lines != 0) {
            let occupied = self.m.occupied.get();
            self.m.occupied.set(if lines != 0 { occupied + 1 } else { occupied - 1 });
        }
        // The last page of a large object can also hold small objects, which can outlive the large object. So `large` is cleared once the large object is dead.
        if lines == 0 || page.large.get().is_some_and(|first| !self.has_bit(first as usize * PAGE, |page| &page.marks)) {
            page.large.set(None);
        }
        page.swept.set(true);
    }

    /// Clears the weak fields and weak items whose targets were not marked, and breaks the ephemerons whose keys are dead.
    fn clear_weaks(self, work: &mut Work) {
        for &holder in &work.holders {
            let index = holder as usize;
            let Some(desc) = self.words.get(index).and_then(|header| self.desc(header.get())) else { continue };
            let mut bits = desc.weaks;
            while bits != 0 {
                if let Some(slot) = self.words.get(index + 1 + bits.trailing_zeros() as usize) {
                    self.clear_dead(slot);
                }
                bits &= bits - 1;
            }
            if desc.items == Items::Weaks {
                for slot in self.items_of(index) {
                    self.clear_dead(slot);
                }
            }
        }
        for &(from, to) in &work.weak_runs {
            for slot in self.words.get(from as usize..to as usize).unwrap_or(&[]) {
                self.clear_dead(slot);
            }
        }
        // A weak handle holds a value word. Its slot is emptied if the object was not marked.
        for slot in self.m.rooted.weak_slots().iter() {
            let word = slot.get();
            if word & TAG == OBJECT && !self.has_bit((word >> 32) as usize, |page| &page.marks) {
                slot.set(0);
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

    /// Clears the reference in the weak slot `slot` if its target was not marked. The reference is the lower half of the word. The upper half is left as it is: a [`slot::Tagged`] item keeps a tag there, which marks the slot as used after its object has died.
    #[inline]
    fn clear_dead(self, slot: &Cell<u64>) {
        let word = slot.get();
        let target = word as u32;
        if target != 0 && !self.has_bit(target as usize, |page| &page.marks) {
            slot.set(word & !0xFFFF_FFFF);
        }
    }

    /// Returns the items of the object at `index`.
    fn items_of(self, index: usize) -> &'a [Cell<u64>] {
        let Some(header) = self.words.get(index).map(Cell::get) else { return &[] };
        let Some(desc) = self.desc(header) else { return &[] };
        let start = index + 1 + desc.fields as usize;
        self.words.get(start..start + (header >> 32) as usize).unwrap_or(&[])
    }

    /// Calls `visit` with the key and value slots of each ephemeron in the object at `index`.
    fn each_ephemeron(self, index: usize, mut visit: impl FnMut(&'a Cell<u64>, &'a Cell<u64>)) {
        let Some(header) = self.words.get(index).map(Cell::get) else { return };
        let Some(desc) = self.desc(header).filter(|desc| desc.has_ephemerons()) else { return };
        let fields = desc.fields as usize;
        let mut bits = desc.ephemerons;
        while bits != 0 {
            let field = bits.trailing_zeros() as usize;
            if field + 1 < fields
                && let Some([key, value]) = self.words.get(index + 1 + field..index + 3 + field).and_then(|pair| pair.as_array())
            {
                visit(key, value);
            }
            bits &= bits - 1;
        }
        if desc.items == Items::Ephemerons {
            let len = (header >> 32) as usize;
            for [key, value] in self.words.get(index + 1 + fields..index + 1 + fields + len).unwrap_or(&[]).as_chunks().0 {
                visit(key, value);
            }
        }
    }

    /// Returns whether the ephemeron key `word` is live. A key is live if it is a marked object or is not an object.
    fn key_live(self, word: u64) -> bool {
        word & TAG != OBJECT || self.has_bit((word >> 32) as usize, |page| &page.marks)
    }

    /// Marks the value of each ephemeron whose key is live, and everything reachable from the value. Repeats until a pass
    /// marks nothing new.
    fn trace_ephemerons(self, work: &mut Work) {
        loop {
            let mut marked = false;
            let mut index = 0;
            while let Some(&holder) = work.ephemerons.get(index) {
                self.each_ephemeron(holder as usize, |key, value| {
                    let word = value.get();
                    if word & TAG == OBJECT && self.key_live(key.get()) {
                        marked |= self.mark((word >> 32) as u32, work);
                    }
                });
                index += 1;
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

    /// Marks the object at `index` and queues it for tracing. Does nothing if `index` is not
    /// the start of an object.
    /// Returns whether this call marked the object.
    fn mark(self, index: u32, work: &mut Work) -> bool {
        let at = index as usize;
        let Some(page) = self.m.pages.get(at / PAGE) else { return false };
        let (marks, bit) = (&page.marks[at % PAGE / 64], 1 << (at % 64));
        if marks.get() & bit != 0 || page.starts[at % PAGE / 64].get() & bit == 0 {
            return false;
        }
        let Some(desc) = self.desc(self.words[at].get()) else { return false };
        marks.set(marks.get() | bit);
        self.cover_lines(at, desc.size(self.words[at].get()), |page| &page.lines);
        if desc.traces {
            work.gray.push(index);
        }
        true
    }

    /// Marks every object that the object at `index` refers to. Returns the size of the object at `index` in words.
    fn trace(self, index: usize, work: &mut Work) -> usize {
        self.trace_parts(index, work, true)
    }

    /// Traces the fields of the object at `index`, and also its items if `items` is true. Returns the object's size in words.
    #[inline(always)]
    fn trace_parts(self, index: usize, work: &mut Work, items: bool) -> usize {
        let Some(header) = self.words.get(index).map(Cell::get) else { return 1 };
        let Some(desc) = self.desc(header) else { return 1 };
        let evacuating = self.m.evacuating.get();
        let fields = self.words.get(index + 1..index + 1 + desc.fields as usize).unwrap_or(&[]);
        let mut bits = desc.values;
        while bits != 0 {
            let field = bits.trailing_zeros() as usize;
            if let Some(slot) = fields.get(field) {
                let word = slot.get();
                if word & TAG == OBJECT {
                    self.mark((word >> 32) as u32, work);
                    self.note(work, evacuating, index, field, (word >> 32) as u32);
                }
            }
            bits &= bits - 1;
        }
        let mut bits = desc.members;
        while bits != 0 {
            let field = bits.trailing_zeros() as usize;
            if let Some(slot) = fields.get(field) {
                let target = slot.get() as u32;
                if target != 0 {
                    self.mark(target, work);
                    self.note(work, evacuating, index, field, target);
                }
            }
            bits &= bits - 1;
        }
        if desc.has_ephemerons() {
            work.ephemerons.push(index as u32);
            // Trace the values whose keys are already marked. The other values wait for `trace_ephemerons`.
            self.each_ephemeron(index, |key, value| {
                if self.key_live(key.get()) {
                    self.visit(value, work);
                }
            });
        }
        if desc.weaks != 0 || items && desc.items == Items::Weaks {
            work.holders.push(index as u32);
            let mut bits = desc.weaks;
            while bits != 0 {
                let field = bits.trailing_zeros() as usize;
                if let Some(target) = fields.get(field).map(|slot| slot.get() as u32).filter(|&target| target != 0) {
                    self.note(work, evacuating, index, field, target);
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
            let traced = self.traced_items(index, header, desc);
            let start = desc.fields as usize;
            if items && desc.items == Items::Values {
                for (j, slot) in self.words.get(index + 1 + start..index + 1 + start + traced).unwrap_or(&[]).iter().enumerate() {
                    let word = slot.get();
                    if word & TAG == OBJECT {
                        self.mark((word >> 32) as u32, work);
                        self.note(work, evacuating, index, start + j, (word >> 32) as u32);
                    }
                }
            } else if items && desc.items == Items::Members {
                for (j, slot) in self.words.get(index + 1 + start..index + 1 + start + traced).unwrap_or(&[]).iter().enumerate() {
                    let target = slot.get() as u32;
                    if target != 0 {
                        self.mark(target, work);
                        self.note(work, evacuating, index, start + j, target);
                    }
                }
            }
        }
        size
    }

    /// Records a fixup for field or item `at` of the object at `index`, if `target` is on a page being evacuated. The stored position is `at + 1`, which is the slot's word offset from the object's header.
    #[inline(always)]
    fn note(self, work: &mut Work, evacuating: bool, index: usize, at: usize, target: u32) {
        if evacuating && self.in_evacuation(target) {
            work.fixups.push((index as u32, at as u32 + 1));
        }
    }

    /// Returns the number of items of the object at `index` that are ordinary arena memory. That is every item, except in a [`Segment`]. In a segment, it is the items
    /// below the attached stack's `base` (or below its `top` once the stack is retired).
    #[inline]
    fn traced_items(self, index: usize, header: u64, desc: &'static Desc) -> usize {
        let len = (header >> 32) as usize;
        if desc.number == Segment::DESC.number {
            self.words.get(index + 1).map_or(0, |word| (word.get() as u32 as usize).min(len))
        } else {
            len
        }
    }

    /// Moves the marked objects off the pages being evacuated, then updates every reference
    /// to them. The roots, root handles and stacks are rescanned. Every other reference is in the fixups recorded while marking.
    fn evacuate(self, work: &mut Work) {
        let used = self.m.used.get();
        for index in 0..used {
            let page = &self.m.pages[index];
            if !page.evacuating.get() {
                continue;
            }
            for (word, (starts, marks)) in page.starts.iter().zip(&page.marks).enumerate() {
                let mut live = starts.get() & marks.get();
                while live != 0 {
                    self.move_object(index * PAGE + word * 64 + live.trailing_zeros() as usize);
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
        for slot in self.m.rooted.slots().iter() {
            self.fix_value(slot);
        }
        for slot in self.m.rooted.weak_slots().iter() {
            self.fix_value(slot);
        }
        // `at` is the slot's word offset from the header, so the slot is field or item `at - 1`. A number at or past `desc.fields` is an item.
        // A member or weak slot holds a bare index. Every other recorded slot holds a value.
        for &(owner, at) in &work.fixups {
            let object = self.resolve(owner) as usize;
            let Some(desc) = self.words.get(object).and_then(|header| self.desc(header.get())) else { continue };
            let Some(slot) = self.words.get(object + at as usize) else { continue };
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
            let object = self.resolve(holder) as usize;
            let Some(desc) = self.words.get(object).and_then(|header| self.desc(header.get())) else { continue };
            let mut bits = desc.weaks;
            while bits != 0 {
                if let Some(slot) = self.words.get(object + 1 + bits.trailing_zeros() as usize) {
                    self.fix_index(slot);
                }
                bits &= bits - 1;
            }
            if desc.items == Items::Weaks {
                for slot in self.items_of(object) {
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
        // An object that found no room in the fresh pages stays where it is. So rebuild the line maps of the evacuated pages from the objects that stayed.
        for page in &self.m.pages[..used] {
            if page.evacuating.get() {
                page.lines.set(0);
            }
        }
        for index in 0..used {
            let page = &self.m.pages[index];
            if !page.evacuating.get() {
                continue;
            }
            for (word, (starts, marks)) in page.starts.iter().zip(&page.marks).enumerate() {
                let mut live = starts.get() & marks.get();
                while live != 0 {
                    let object = index * PAGE + word * 64 + live.trailing_zeros() as usize;
                    if let Some(desc) = self.desc(self.words[object].get()) {
                        self.cover_lines(object, desc.size(self.words[object].get()), |page| &page.lines);
                    }
                    live &= live - 1;
                }
            }
        }
    }

    /// Copies the marked object at `index` to a fresh page and leaves a forwarding header in its place. The copy is
    /// marked and the original is unmarked, so the sweep frees the original.
    fn move_object(self, index: usize) {
        let header = self.words[index].get();
        let Some(desc) = self.desc(header) else { return };
        let size = desc.size(header);
        let Some(new) = self.to_reserve(size) else { return };
        let (Some(from), Some(to)) = (self.words.get(index..index + size), self.words.get(new..new + size)) else { return };
        for (target, source) in to.iter().zip(from) {
            target.set(source.get());
        }
        self.set_bit(new, |page| &page.starts);
        self.set_bit(new, |page| &page.marks);
        self.cover_lines(new, size, |page| &page.lines);
        self.words[index].set((new as u64) << 32 | FORWARDED | header & TYPE_BITS);
        let marks = &self.m.pages[index / PAGE].marks[index % PAGE / 64];
        marks.set(marks.get() & !(1 << (index % 64)));
    }

    fn to_reserve(self, size: usize) -> Option<usize> {
        let at = self.m.to_cursor.get();
        if at + size <= self.m.to_end.get() {
            self.m.to_cursor.set(at + size);
            return Some(at);
        }
        // An object that finds no room stays where it is.
        let count = size.div_ceil(PAGE);
        let first = self.m.budget.optional(|| self.free_run(count, true)?.map_or_else(|| self.fresh_pages(count), Ok)).ok()?;
        // Mark every line as used, so the allocator leaves the pages alone. The sweep later sets the lines from the marked objects.
        self.m.pages[first..first + count].iter().for_each(|page| page.used.set(u128::MAX));
        let start = first * PAGE;
        self.m.to_cursor.set(start + size);
        self.m.to_end.set(start + count * PAGE);
        Some(start)
    }

    /// Returns the current index of the object that was at `index`: the forwarding target if the object moved, and `index` otherwise.
    fn resolve(self, index: u32) -> u32 {
        let at = index as usize;
        match self.words.get(at).map(Cell::get) {
            Some(header) if header & FORWARDED != 0 && self.has_bit(at, |page| &page.starts) => (header >> 32) as u32,
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
        for page in self.m.dirty_pages.iter(false) {
            let mut cards = self.m.pages[page].cards.get();
            while cards != 0 {
                let card = cards.trailing_zeros() as usize;
                cards &= cards - 1;
                let (from, to) = (page * PAGE + card * CARD, page * PAGE + (card + 1) * CARD);
                let mut next = self.start_at_or_before(from).or_else(|| self.next_start(from, to));
                while let Some(object) = next.filter(|&object| object < to) {
                    if self.has_bit(object, |page| &page.marks) {
                        self.trace_card(object, from..to, object != last, work);
                        last = object;
                    }
                    // No object starts between an object found before the card and the start of the card.
                    next = self.next_start((object + 1).max(from), to);
                }
            }
        }
    }

    /// Traces the references of an old object that overlaps a dirty card. If the items hold references, only the items on
    /// the card are traced, so a store into a large vector does not rescan the whole vector. The rest of the
    /// object is traced once, for its first dirty card.
    fn trace_card(self, index: usize, card: Range<usize>, first: bool, work: &mut Work) {
        let header = self.words[mask(index)].get();
        let Some(desc) = self.desc(header) else { return };
        let Some(refs @ (Refs::Values | Refs::Members | Refs::Weaks)) = Refs::of(desc.items) else {
            if first {
                self.trace(index, work);
            }
            return;
        };
        if first {
            self.trace_parts(index, work, false);
        }
        let items = index + 1 + desc.fields as usize;
        let traced = self.traced_items(index, header, desc);
        let (from, to) = (card.start.max(items), card.end.min(items + traced));
        let slots = self.words.get(from..to).unwrap_or(&[]);
        match refs {
            Refs::Values => slots.iter().for_each(|slot| self.visit(slot, work)),
            Refs::Members => slots.iter().filter(|slot| slot.get() as u32 != 0).for_each(|slot| _ = self.mark(slot.get() as u32, work)),
            _ if from < to => work.weak_runs.push((from as u32, to as u32)),
            _ => {}
        }
    }

    fn start_at_or_before(self, index: usize) -> Option<usize> {
        let (mut page, mut word) = (index / PAGE, index % PAGE / 64);
        let mut mask = u64::MAX >> (63 - index % 64);
        loop {
            let starts = self.m.pages[page].starts[word].get() & mask;
            if starts != 0 {
                return Some(page * PAGE + word * 64 + 63 - starts.leading_zeros() as usize);
            }
            mask = u64::MAX;
            if word > 0 {
                word -= 1;
            } else if let Some(first) = self.m.pages[page].large.get().map(|first| first as usize).filter(|&first| first < page) {
                // No object starts between a large object's header and this page, so continue from the object's first page.
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
                return Some(page * PAGE + word * 64 + starts.trailing_zeros() as usize).filter(|&start| start < to);
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
fn shade(words: &[Cell<u64>; WORDS + SLACK], meta: &Meta, slot: usize, owner: u32, target: u32) {
    Heap { words, m: meta }.shade_marked(slot, owner, target);
}
