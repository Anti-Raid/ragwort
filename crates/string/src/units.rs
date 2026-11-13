//! The characters of a flat string: one, two or four bytes each, as the widest needs.

use std::cell::Cell;
use std::cmp::Ordering;
use std::ops::Range;

use crate::word::{HIGH, SHORT, fingerprint, low_bytes, read_bytes, write_bytes};

/// Bytes per character of a flat string. A flat string always has the narrowest width that
/// holds all its characters, so strings of different widths are never equal.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(u8)]
pub enum Width {
    /// Up to U+00FF, Latin-1.
    One = 1,
    /// Up to U+FFFF. Surrogates aren't characters, so never appear.
    Two = 2,
    Four = 4,
}

impl Width {
    pub const fn of(character: char) -> Self {
        Self::of_code(character as u32)
    }

    const fn of_code(code: u32) -> Self {
        match code {
            0..=0xFF => Self::One,
            0x100..=0xFFFF => Self::Two,
            _ => Self::Four,
        }
    }

    pub const fn bytes(self) -> usize {
        self as usize
    }

    /// Units that fit in a word.
    pub const fn per_word(self) -> usize {
        1 << self.per_word_log()
    }

    const fn per_word_log(self) -> u32 {
        match self {
            Self::One => 3,
            Self::Two => 2,
            Self::Four => 1,
        }
    }

    const fn bits(self) -> u32 {
        8 * self as u32
    }

    const fn mask(self) -> u64 {
        u64::MAX >> (64 - self.bits())
    }

    pub(crate) fn from_bits(bits: u8) -> Self {
        match bits {
            1 => Self::One,
            2 => Self::Two,
            _ => Self::Four,
        }
    }
}

/// A flat string's characters, as its host stores them.
#[derive(Clone, Copy, Debug)]
pub enum Units<'a> {
    One(&'a [u8]),
    Two(&'a [u16]),
    Four(&'a [u32]),
    Packed(Packed<'a>),
    Inline(Inline),
}

/// Room for a new flat string's characters.
#[derive(Debug)]
pub enum UnitsMut<'a> {
    One(&'a mut [u8]),
    Two(&'a mut [u16]),
    Four(&'a mut [u32]),
    Packed(PackedMut<'a>),
}

/// Units packed into words, [`Width::per_word`] to a word with the first lowest, as a host that
/// stores words holds them. What's past the last unit is ignored.
#[derive(Clone, Copy, Debug)]
pub struct Packed<'a> {
    words: &'a [Cell<u64>],
    len: usize,
    /// Units to pass over in the first word.
    skip: u8,
    width: Width,
}

/// Up to eight one-byte units in one word, the first lowest, which the host keeps in the string's
/// handle rather than in memory. Bytes past the last unit are zero. Reads of single units take
/// it as it is; the word-at-a-time paths it shares with [`Packed`] take it `anchored`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Inline {
    word: u64,
    len: u8,
}

/// Room for a new flat string's characters, packed as [`Packed`] reads them, in words the host
/// zeroed.
#[derive(Debug)]
pub struct PackedMut<'a> {
    words: &'a [Cell<u64>],
    len: usize,
    width: Width,
}

impl<'a> Packed<'a> {
    /// The first `len` units in `words`, or as many as they hold.
    #[inline]
    pub fn new(words: &'a [Cell<u64>], len: usize, width: Width) -> Self {
        Self { words, len: len.min(words.len() << width.per_word_log()), skip: 0, width }
    }

    #[inline]
    pub fn len(self) -> usize {
        self.len
    }

    pub fn is_empty(self) -> bool {
        self.len == 0
    }

    pub fn width(self) -> Width {
        self.width
    }

    #[inline]
    pub(crate) fn code(self, i: usize) -> u32 {
        let j = self.skip as usize + i;
        let log = self.width.per_word_log();
        let shift = (j & ((1 << log) - 1)) as u32 * self.width.bits();
        ((self.words[j >> log].get() >> shift) & self.width.mask()) as u32
    }

    /// Unit `i` of one-byte units.
    #[inline]
    pub(crate) fn byte(self, i: usize) -> u32 {
        debug_assert!(self.width == Width::One);
        let j = self.skip as usize + i;
        u32::from((self.words[j >> 3].get() >> ((j & 7) * 8)) as u8)
    }

    #[inline]
    pub(crate) fn slice(self, range: Range<usize>) -> Self {
        assert!(range.start <= range.end && range.end <= self.len, "range {range:?} out of {}", self.len);
        let log = self.width.per_word_log();
        let start = self.skip as usize + range.start;
        let words = &self.words[(start >> log).min(self.words.len())..];
        Self { words, len: range.len(), skip: (start & ((1 << log) - 1)) as u8, width: self.width }
    }

    /// Calls `visit` with each unit's code, in order.
    #[inline]
    fn each_code(self, mut visit: impl FnMut(u32)) {
        let (log, bits, mask) = (self.width.per_word_log(), self.width.bits(), self.width.mask());
        let (mut i, end) = (self.skip as usize, self.skip as usize + self.len);
        for cell in &self.words[..end.div_ceil(1 << log)] {
            let (word, stop) = (cell.get(), end.min((i | ((1 << log) - 1)) + 1));
            while i < stop {
                visit(((word >> ((i & ((1 << log) - 1)) as u32 * bits)) & mask) as u32);
                i += 1;
            }
        }
    }

    /// Where the units' bytes start in the first word.
    fn byte_start(self) -> usize {
        self.skip as usize * self.width.bytes()
    }

    /// The units' bytes from unit `from`, as many as fill `out`.
    #[inline]
    pub(crate) fn copy_bytes(self, from: usize, out: &mut [u8]) {
        let at = self.byte_start() + from * self.width.bytes();
        let (whole, tail) = out.as_chunks_mut::<8>();
        for (index, chunk) in whole.iter_mut().enumerate() {
            *chunk = read_bytes(self.words, at + 8 * index, 8).to_le_bytes();
        }
        if !tail.is_empty() {
            let value = read_bytes(self.words, at + 8 * whole.len(), tail.len());
            for (i, byte) in tail.iter_mut().enumerate() {
                *byte = (value >> (8 * i)) as u8;
            }
        }
    }

    /// Whether these are one-byte units, all of them ASCII.
    pub(crate) fn is_ascii(self) -> bool {
        self.width == Width::One && self.byte_words().fold(0, |seen, word| seen | word) & HIGH == 0
    }

    /// The units' bytes, eight to a word, the last word holding what's left.
    #[inline]
    pub(crate) fn byte_words(self) -> impl Iterator<Item = u64> + Clone + 'a {
        let n = self.len * self.width.bytes();
        (0..n.div_ceil(8)).map(move |index| self.word_at(index, (n - 8 * index).min(8)))
    }

    /// The `index`th 8 bytes of the units' bytes, or the `n` there are if fewer.
    #[inline]
    pub(crate) fn word_at(self, index: usize, n: usize) -> u64 {
        match self.skip {
            0 if n == 8 => self.words[index].get(),
            _ => read_bytes(self.words, self.byte_start() + 8 * index, n),
        }
    }

    /// Orders two runs of the same length and width by code point, a word at a time, each word
    /// passed through `map` first. Units pack lowest first, so the lowest differing bit is in
    /// the first differing unit.
    #[inline]
    pub(crate) fn compare_by(self, other: Packed<'_>, map: impl Fn(u64) -> u64) -> Ordering {
        let (bytes, bits) = (self.len * self.width.bytes(), self.width.bits());
        for at in (0..bytes).step_by(8) {
            let n = (bytes - at).min(8);
            let (x, y) = (map(self.word_at(at / 8, n)), map(other.word_at(at / 8, n)));
            if x != y {
                let shift = (x ^ y).trailing_zeros() / bits * bits;
                return (x >> shift & self.width.mask()).cmp(&(y >> shift & self.width.mask()));
            }
        }
        Ordering::Equal
    }

    #[inline]
    fn equal(self, other: Packed<'_>) -> bool {
        if self.len != other.len || self.width != other.width {
            return false;
        }
        let bytes = self.len * self.width.bytes();
        if self.skip == 0 && other.skip == 0 {
            let (whole, rest) = (bytes / 8, bytes % 8);
            let (Some(a), Some(b)) = (self.words.get(..bytes.div_ceil(8)), other.words.get(..bytes.div_ceil(8))) else { return false };
            let same = a[..whole].iter().zip(&b[..whole]).all(|(x, y)| x.get() == y.get());
            return same && (rest == 0 || (a[whole].get() ^ b[whole].get()) & low_bytes(rest) == 0);
        }
        let (a, b) = (self.byte_start(), other.byte_start());
        (0..bytes).step_by(8).all(|at| {
            let count = (bytes - at).min(8);
            read_bytes(self.words, a + at, count) == read_bytes(other.words, b + at, count)
        })
    }

    /// Whether these are one-byte units equal to `bytes`, all of them ASCII.
    #[inline]
    pub(crate) fn equal_ascii(self, bytes: &[u8]) -> bool {
        if self.width != Width::One || self.len != bytes.len() {
            return false;
        }
        if self.skip != 0 {
            return self.equal_bytes(bytes) && bytes.is_ascii();
        }
        let (chunks, tail) = bytes.as_chunks::<8>();
        let Some(words) = self.words.get(..chunks.len() + !tail.is_empty() as usize) else { return false };
        // Differences and high bits gather, so there's one branch whatever the length.
        let (mut diff, mut seen) = (0, 0);
        for (cell, chunk) in words.iter().zip(chunks) {
            let chunk = u64::from_le_bytes(*chunk);
            diff |= cell.get() ^ chunk;
            seen |= chunk;
        }
        if let Some(last) = words.get(chunks.len()) {
            let tail_word = match bytes.last_chunk::<8>() {
                Some(end) => u64::from_le_bytes(*end) >> (64 - 8 * tail.len()),
                None => u8::pack(tail),
            };
            diff |= (last.get() ^ tail_word) & low_bytes(tail.len());
            seen |= tail_word;
        }
        diff | seen & HIGH == 0
    }

    /// Whether these are one-byte units equal to `bytes`.
    pub(crate) fn equal_bytes(self, bytes: &[u8]) -> bool {
        let at = self.byte_start();
        self.width == Width::One
            && self.len == bytes.len()
            && bytes.chunks(8).enumerate().all(|(index, chunk)| read_bytes(self.words, at + 8 * index, chunk.len()) == u8::pack(chunk))
    }
}

impl Inline {
    /// The first `len` bytes of `word`, up to eight.
    #[inline]
    pub fn new(word: u64, len: usize) -> Self {
        let len = len.min(8);
        Self { word: word & low_bytes(len), len: len as u8 }
    }

    /// The `len` units, up to eight, that `init` writes, for a host's [`crate::Host::flat`].
    #[inline]
    pub fn filled(len: usize, init: impl FnOnce(UnitsMut<'_>)) -> Self {
        let word = [Cell::new(0)];
        init(UnitsMut::Packed(PackedMut::new(&word, len, Width::One)));
        Self::new(word[0].get(), len)
    }

    #[inline]
    pub fn len(self) -> usize {
        self.len as usize
    }

    pub fn is_empty(self) -> bool {
        self.len == 0
    }

    #[inline]
    pub fn word(self) -> u64 {
        self.word
    }

    /// The units, then zeros.
    #[inline]
    pub(crate) fn bytes(self) -> [u8; 8] {
        self.word.to_le_bytes()
    }

    #[inline]
    fn byte(self, i: usize) -> u8 {
        (self.word >> (8 * i)) as u8
    }

    #[inline]
    fn code(self, i: usize) -> u32 {
        u32::from(self.byte(i))
    }

    /// Whether these are equal to `bytes`, all of them ASCII.
    #[inline]
    pub(crate) fn equal_ascii(self, bytes: &[u8]) -> bool {
        self.len() == bytes.len() && {
            let word = u8::pack(bytes);
            word == self.word && word & HIGH == 0
        }
    }

    #[inline]
    fn slice(self, range: Range<usize>) -> Self {
        assert!(range.start <= range.end && range.end <= self.len(), "range {range:?} out of {}", self.len);
        Self::new(self.word.checked_shr(8 * range.start as u32).unwrap_or(0), range.len())
    }
}

impl<'a> PackedMut<'a> {
    /// Room for `len` units in `words`, or as many as they hold.
    #[inline]
    pub fn new(words: &'a [Cell<u64>], len: usize, width: Width) -> Self {
        Self { words, len: len.min(words.len() << width.per_word_log()), width }
    }

    #[inline]
    fn put(&self, i: usize, code: u32) {
        assert!(i < self.len, "unit {i} past the end");
        let log = self.width.per_word_log();
        let shift = (i & ((1 << log) - 1)) as u32 * self.width.bits();
        let cell = &self.words[i >> log];
        cell.set(cell.get() & !(self.width.mask() << shift) | (code as u64 & self.width.mask()) << shift);
    }

    /// Writes `src` from `at`, each character converted to this width, which must hold them.
    fn write(&self, at: usize, src: Units<'_>) {
        assert!(at + src.len() <= self.len, "writing past the end");
        let wb = self.width.bytes();
        match src {
            Units::Packed(packed) if packed.width == self.width => {
                let from = packed.byte_start();
                self.copy(at * wb, packed.len() * wb, |i, count| read_bytes(packed.words, from + i, count));
            }
            Units::One(bytes) if self.width == Width::One => self.copy(at, bytes.len(), |i, count| u8::pack(&bytes[i..i + count])),
            Units::One(bytes) => self.widen(at, bytes.len(), |i| bytes[i] as u32),
            Units::Two(slice) => self.widen(at, slice.len(), |i| slice[i] as u32),
            Units::Four(slice) => self.widen(at, slice.len(), |i| slice[i]),
            Units::Packed(packed) => self.widen(at, packed.len, |i| packed.code(i)),
            Units::Inline(inline) if self.width == Width::One => self.copy(at, inline.len(), |i, count| inline.word >> (8 * i) & low_bytes(count)),
            Units::Inline(inline) => self.widen(at, inline.len(), |i| inline.code(i)),
        }
    }

    /// Writes `n` units from `at`, the `i`th `unit(i)`, a word at a time.
    #[inline]
    fn widen(&self, at: usize, n: usize, unit: impl Fn(usize) -> u32) {
        let (log, bits, mask) = (self.width.per_word_log(), self.width.bits(), self.width.mask());
        let (end, mut position, mut i) = (at + n, at, 0);
        while position < end {
            let first = position & ((1 << log) - 1);
            let count = ((1 << log) - first).min(end - position);
            let mut word = 0;
            for offset in 0..count {
                word |= (unit(i + offset) as u64 & mask) << ((first + offset) as u32 * bits);
            }
            let used = if count == 1 << log { u64::MAX } else { ((1u64 << (count as u32 * bits)) - 1) << (first as u32 * bits) };
            let cell = &self.words[position >> log];
            cell.set(cell.get() & !used | word);
            (position, i) = (position + count, i + count);
        }
    }

    /// Writes `n` bytes from byte `to`, which `read(i, count)` gives `count` at a time from the `i`th.
    #[inline]
    fn copy(&self, to: usize, n: usize, read: impl Fn(usize, usize) -> u64) {
        let mut i = 0;
        while i < n {
            let count = (8 - (to + i) % 8).min(n - i);
            write_bytes(self.words, to + i, count, read(i, count));
            i += count;
        }
    }
}

/// Takes the variants that are slices to `$e`, and those in words, [`Packed`] and [`Inline`],
/// to `$words`.
macro_rules! each {
    ($units:expr, $s:ident => $e:expr, $w:ident => $words:expr) => {
        match $units {
            Units::One($s) => $e,
            Units::Two($s) => $e,
            Units::Four($s) => $e,
            Units::Packed($w) => $words,
            Units::Inline($w) => $words,
        }
    };
}

macro_rules! each_mut {
    ($units:expr, $s:ident => $e:expr, $w:ident => $words:expr) => {
        match $units {
            UnitsMut::One($s) => $e,
            UnitsMut::Two($s) => $e,
            UnitsMut::Four($s) => $e,
            UnitsMut::Packed($w) => $words,
        }
    };
}

pub(crate) trait Unit: Copy + Ord {
    const BITS: u32;
    fn code(self) -> u32;
    /// `code`, which must fit.
    fn of(code: u32) -> Self;
    /// Up to `64 / BITS` units, the first lowest.
    #[inline]
    fn pack(units: &[Self]) -> u64 {
        units.iter().rev().fold(0, |word, unit| word << Self::BITS | unit.code() as u64)
    }
}

impl Unit for u8 {
    const BITS: u32 = 8;
    fn code(self) -> u32 {
        self as u32
    }
    fn of(code: u32) -> Self {
        code as u8
    }
    /// Reads overlap for a part word, ORing equal bytes into the same places.
    #[inline]
    fn pack(units: &[Self]) -> u64 {
        let n = units.len();
        let four = |i: usize| u32::from_le_bytes(units[i..i + 4].try_into().expect("four bytes")) as u64;
        match n {
            8 => u64::from_le_bytes(units.try_into().expect("eight bytes")),
            4..=7 => four(0) | four(n - 4) << (8 * (n - 4)),
            1..=3 => units[0] as u64 | (units[n / 2] as u64) << (8 * (n / 2)) | (units[n - 1] as u64) << (8 * (n - 1)),
            _ => 0,
        }
    }
}

impl Unit for u16 {
    const BITS: u32 = 16;
    fn code(self) -> u32 {
        self as u32
    }
    fn of(code: u32) -> Self {
        code as u16
    }
}

impl Unit for u32 {
    const BITS: u32 = 32;
    fn code(self) -> u32 {
        self
    }
    fn of(code: u32) -> Self {
        code
    }
}

/// A host can hand back any bits, so a unit that isn't a character reads as U+FFFD.
#[inline]
fn to_char(code: u32) -> char {
    char::from_u32(code).unwrap_or(char::REPLACEMENT_CHARACTER)
}

fn widest<U: Unit>(units: &[U]) -> u32 {
    units.iter().fold(0, |most, unit| most.max(unit.code()))
}

impl<'a> Units<'a> {
    /// The `index`th eight of these one-byte units in a little-endian word, or the ones left.
    #[inline]
    pub(crate) fn byte_chunk(self, index: usize) -> u64 {
        let n = (self.len() - 8 * index).min(8);
        match self {
            Units::Inline(inline) => inline.word,
            Units::Packed(packed) if packed.width == Width::One => packed.word_at(index, n),
            Units::One(bytes) => u8::pack(&bytes[8 * index..8 * index + n]),
            _ => panic!("reading bytes of wider units"),
        }
    }

    #[inline]
    pub fn len(self) -> usize {
        each!(self, slice => slice.len(), packed => packed.len())
    }

    #[inline]
    pub fn is_empty(self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn width(self) -> Width {
        match self {
            Self::One(_) => Width::One,
            Self::Two(_) => Width::Two,
            Self::Four(_) => Width::Four,
            Self::Packed(packed) => packed.width,
            Self::Inline(_) => Width::One,
        }
    }

    #[inline]
    pub fn get(self, i: usize) -> Option<char> {
        match self {
            Self::One(bytes) => bytes.get(i).map(|&byte| char::from(byte)),
            Self::Two(slice) => slice.get(i).map(|&unit| to_char(unit as u32)),
            Self::Four(slice) => slice.get(i).map(|&unit| to_char(unit)),
            Self::Packed(packed) => (i < packed.len()).then(|| to_char(packed.code(i))),
            Self::Inline(inline) => (i < inline.len()).then(|| char::from(inline.byte(i))),
        }
    }

    /// Always inlined: the rope walks slice on their hot path, and LLVM's own choice there flips
    /// with code elsewhere in the program.
    #[inline(always)]
    pub fn slice(self, range: Range<usize>) -> Self {
        match self {
            Self::One(slice) => Self::One(&slice[range]),
            Self::Two(slice) => Self::Two(&slice[range]),
            Self::Four(slice) => Self::Four(&slice[range]),
            Self::Packed(packed) => Self::Packed(packed.slice(range)),
            Self::Inline(inline) => Self::Inline(inline.slice(range)),
        }
    }

    /// These units, inline ones moved into `cell` so they read as packed words, as the host's
    /// stored ones do.
    #[inline]
    pub(crate) fn anchored<'b>(self, cell: &'b Cell<u64>) -> Units<'b>
    where
        'a: 'b,
    {
        match self {
            Self::Inline(inline) => {
                cell.set(inline.word);
                Units::Packed(Packed::new(std::slice::from_ref(cell), inline.len(), Width::One))
            }
            units => units,
        }
    }

    pub fn chars(self) -> impl Iterator<Item = char> + 'a {
        (0..self.len()).map(move |i| self.get(i).expect("in range"))
    }

    /// The characters, read a word at a time if they're packed.
    #[inline]
    pub(crate) fn each_char(self, mut visit: impl FnMut(char)) {
        match self {
            Self::Packed(packed) => packed.each_code(|code| visit(to_char(code))),
            Self::Inline(inline) => (0..inline.len()).for_each(|i| visit(char::from(inline.byte(i)))),
            _ => self.chars().for_each(visit),
        }
    }

    /// The narrowest width that holds these characters.
    pub(crate) fn narrowest(self) -> Width {
        match self.width() {
            Width::One => Width::One,
            _ => Width::of_code(each!(self, slice => widest(slice), packed => (0..packed.len()).map(|i| packed.code(i)).max().unwrap_or(0))),
        }
    }

    #[inline]
    pub(crate) fn code(self, i: usize) -> u32 {
        each!(self, slice => slice[i].code(), packed => packed.code(i))
    }

    /// Orders two runs of the same length by code point.
    pub(crate) fn compare(self, other: Units<'_>) -> Ordering {
        debug_assert_eq!(self.len(), other.len());
        let (this_cell, other_cell) = (Cell::new(0), Cell::new(0));
        let (this, other) = (self.anchored(&this_cell), other.anchored(&other_cell));
        match (this, other) {
            (Units::One(a), Units::One(b)) => a.cmp(b),
            (Units::Two(a), Units::Two(b)) => a.cmp(b),
            (Units::Four(a), Units::Four(b)) => a.cmp(b),
            (Units::Packed(a), Units::Packed(b)) if a.width == b.width => a.compare_by(b, |word| word),
            _ => (0..this.len()).map(|i| this.code(i).cmp(&other.code(i))).find(|order| order.is_ne()).unwrap_or(Ordering::Equal),
        }
    }

    /// Whether these are the same characters, given both are at their narrowest width.
    #[inline]
    pub(crate) fn equal(self, other: Units<'_>) -> bool {
        if let (Self::Inline(a), Units::Inline(b)) = (self, other) {
            return a == b;
        }
        let (this_cell, other_cell) = (Cell::new(0), Cell::new(0));
        match (self.anchored(&this_cell), other.anchored(&other_cell)) {
            (Units::One(a), Units::One(b)) if a.len() <= SHORT => {
                a.len() == b.len() && fingerprint(a) == fingerprint(b)
            }
            (Units::One(a), Units::One(b)) => a == b,
            (Units::Two(a), Units::Two(b)) => a == b,
            (Units::Four(a), Units::Four(b)) => a == b,
            (Units::Packed(a), Units::Packed(b)) => a.equal(b),
            (Units::Packed(a), Units::One(b)) => a.equal_bytes(b),
            (Units::One(a), Units::Packed(b)) => b.equal_bytes(a),
            (a, b) if a.width() == b.width() && a.len() == b.len() => (0..a.len()).all(|i| a.code(i) == b.code(i)),
            _ => false,
        }
    }

    /// UTF-8 bytes these characters take.
    pub(crate) fn utf8_len(self) -> usize {
        match self {
            Self::One(bytes) => bytes.len() + bytes.iter().filter(|&&byte| byte >= 0x80).count(),
            Self::Packed(packed) if packed.width == Width::One => packed.len() + packed.byte_words().map(|word| (word & HIGH).count_ones() as usize).sum::<usize>(),
            Self::Inline(inline) => inline.len() + (inline.word & HIGH).count_ones() as usize,
            _ => self.chars().map(char::len_utf8).sum(),
        }
    }
}

/// Fills units from the start with runs of units, one after another, which are no wider and as
/// long in all. Into one-byte units packed in words, it writes a word at a time.
pub(crate) struct RunWriter<'o, 'a> {
    out: &'o mut UnitsMut<'a>,
    at: usize,
    /// The next word's bytes so far, `filled` bits of them, for one-byte packed units.
    word: u64,
    filled: u32,
}

impl<'o, 'a> RunWriter<'o, 'a> {
    pub(crate) fn new(out: &'o mut UnitsMut<'a>) -> Self {
        Self { out, at: 0, word: 0, filled: 0 }
    }

    #[inline]
    pub(crate) fn push(&mut self, run: Units<'_>) {
        let n = run.len();
        let UnitsMut::Packed(packed) = &*self.out else {
            self.out.write(self.at, run);
            self.at += n;
            return;
        };
        if packed.width != Width::One {
            packed.write(self.at, run);
            self.at += n;
            return;
        }
        for index in 0..n.div_ceil(8) {
            let (chunk, bits) = (run.byte_chunk(index), 8 * (n - 8 * index).min(8) as u32);
            self.word |= chunk << self.filled;
            if self.filled + bits < 64 {
                self.filled += bits;
                continue;
            }
            packed.words[self.at / 8].set(self.word);
            self.at += 8;
            self.word = chunk.checked_shr(64 - self.filled).unwrap_or(0);
            self.filled = self.filled + bits - 64;
        }
    }

    pub(crate) fn finish(self) {
        if let UnitsMut::Packed(packed) = &*self.out
            && packed.width == Width::One
            && self.filled > 0
        {
            packed.words[self.at / 8].set(self.word);
        }
    }
}

impl UnitsMut<'_> {
    pub fn len(&self) -> usize {
        each_mut!(self, slice => slice.len(), packed => packed.len)
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Fills one-byte units from little-endian words, eight to a word, the last word's extra
    /// bytes dropped.
    pub(crate) fn write_words(&mut self, words: impl Iterator<Item = u64>) {
        match self {
            UnitsMut::Packed(packed) if packed.width == Width::One => packed.words.iter().zip(words).for_each(|(cell, word)| cell.set(word)),
            UnitsMut::One(bytes) => bytes.chunks_mut(8).zip(words).for_each(|(chunk, word)| chunk.copy_from_slice(&word.to_le_bytes()[..chunk.len()])),
            _ => panic!("writing bytes to wider units"),
        }
    }

    /// Fills these units from `src`, which is as long and no wider.
    pub fn copy_from(&mut self, src: Units<'_>) {
        assert!(src.len() == self.len() && src.width() <= self.width(), "copying from a longer or wider string");
        self.write(0, src);
    }

    fn width(&self) -> Width {
        match self {
            UnitsMut::One(_) => Width::One,
            UnitsMut::Two(_) => Width::Two,
            UnitsMut::Four(_) => Width::Four,
            UnitsMut::Packed(packed) => packed.width,
        }
    }

    /// Writes `src` from `at`, each character converted to this width, which must hold them.
    pub(crate) fn write(&mut self, at: usize, src: Units<'_>) {
        let end = at + src.len();
        match (self, src) {
            (UnitsMut::One(dest), Units::One(source)) => dest[at..end].copy_from_slice(source),
            (UnitsMut::Two(dest), Units::Two(source)) => dest[at..end].copy_from_slice(source),
            (UnitsMut::Four(dest), Units::Four(source)) => dest[at..end].copy_from_slice(source),
            (UnitsMut::Packed(dest), source) => dest.write(at, source),
            (dest, source) => (0..source.len()).for_each(|i| dest.put(at + i, source.code(i))),
        }
    }

    fn put(&mut self, i: usize, code: u32) {
        each_mut!(self, slice => slice[i] = Unit::of(code), packed => packed.put(i, code));
    }

    pub(crate) fn set(&mut self, i: usize, character: char) {
        self.put(i, character as u32);
    }
}
