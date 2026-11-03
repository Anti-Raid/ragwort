//! The characters of a flat string: one, two or four bytes each, as the widest needs.

use std::cell::Cell;
use std::cmp::Ordering;
use std::ops::Range;

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
    pub const fn of(c: char) -> Self {
        Self::of_code(c as u32)
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

/// Room for a new flat string's characters, packed as [`Packed`] reads them, in words the host
/// zeroed.
#[derive(Debug)]
pub struct PackedMut<'a> {
    words: &'a [Cell<u64>],
    len: usize,
    width: Width,
}

/// Up to 8 bytes of `words`' little-endian bytes from byte `at`, the first lowest.
#[inline]
fn read_bytes(words: &[Cell<u64>], at: usize, n: usize) -> u64 {
    let (i, shift) = (at / 8, (at % 8) as u32 * 8);
    let mut v = words[i].get() >> shift;
    if shift != 0 && shift + 8 * n as u32 > 64 {
        v |= words[i + 1].get() << (64 - shift);
    }
    if n < 8 { v & ((1 << (8 * n)) - 1) } else { v }
}

/// Writes the low `n` bytes of `v` from byte `at`, all in one word.
#[inline]
fn write_bytes(words: &[Cell<u64>], at: usize, n: usize, v: u64) {
    let shift = (at % 8) as u32 * 8;
    let mask = if n == 8 { u64::MAX } else { (1 << (8 * n)) - 1 } << shift;
    let w = &words[at / 8];
    w.set(w.get() & !mask | (v << shift) & mask);
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

    /// Calls `f` with each unit's code, in order.
    #[inline]
    fn each_code(self, mut f: impl FnMut(u32)) {
        let (log, bits, mask) = (self.width.per_word_log(), self.width.bits(), self.width.mask());
        let (mut i, end) = (self.skip as usize, self.skip as usize + self.len);
        for w in &self.words[..end.div_ceil(1 << log)] {
            let (w, stop) = (w.get(), end.min((i | ((1 << log) - 1)) + 1));
            while i < stop {
                f(((w >> ((i & ((1 << log) - 1)) as u32 * bits)) & mask) as u32);
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
        for (k, chunk) in whole.iter_mut().enumerate() {
            *chunk = read_bytes(self.words, at + 8 * k, 8).to_le_bytes();
        }
        if !tail.is_empty() {
            let v = read_bytes(self.words, at + 8 * whole.len(), tail.len());
            for (i, b) in tail.iter_mut().enumerate() {
                *b = (v >> (8 * i)) as u8;
            }
        }
    }

    /// Whether these are one-byte units, all of them ASCII.
    pub(crate) fn is_ascii(self) -> bool {
        let n = self.len;
        self.width == Width::One
            && (0..n.div_ceil(8)).fold(0, |seen, k| seen | self.word_at(k, (n - 8 * k).min(8))) & crate::hash::HIGH == 0
    }

    /// The `k`th 8 bytes of the units' bytes, or the `n` there are if fewer.
    #[inline]
    pub(crate) fn word_at(self, k: usize, n: usize) -> u64 {
        match self.skip {
            0 if n == 8 => self.words[k].get(),
            _ => read_bytes(self.words, self.byte_start() + 8 * k, n),
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
            return same && (rest == 0 || (a[whole].get() ^ b[whole].get()) & ((1 << (8 * rest)) - 1) == 0);
        }
        let (a, b) = (self.byte_start(), other.byte_start());
        (0..bytes).step_by(8).all(|at| {
            let k = (bytes - at).min(8);
            read_bytes(self.words, a + at, k) == read_bytes(other.words, b + at, k)
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
        for (w, c) in words.iter().zip(chunks) {
            let c = u64::from_le_bytes(*c);
            diff |= w.get() ^ c;
            seen |= c;
        }
        if let Some(last) = words.get(chunks.len()) {
            let c = match bytes.last_chunk::<8>() {
                Some(end) => u64::from_le_bytes(*end) >> (64 - 8 * tail.len()),
                None => u8::pack(tail),
            };
            diff |= (last.get() ^ c) & u64::MAX >> (64 - 8 * tail.len());
            seen |= c;
        }
        diff | seen & crate::hash::HIGH == 0
    }

    /// Whether these are one-byte units equal to `bytes`.
    pub(crate) fn equal_bytes(self, bytes: &[u8]) -> bool {
        let at = self.byte_start();
        self.width == Width::One
            && self.len == bytes.len()
            && bytes.chunks(8).enumerate().all(|(k, b)| read_bytes(self.words, at + 8 * k, b.len()) == u8::pack(b))
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
        let w = &self.words[i >> log];
        w.set(w.get() & !(self.width.mask() << shift) | (code as u64 & self.width.mask()) << shift);
    }

    /// Writes `src` from `at`, each character converted to this width, which must hold them.
    fn write(&self, at: usize, src: Units<'_>) {
        assert!(at + src.len() <= self.len, "writing past the end");
        let wb = self.width.bytes();
        match src {
            Units::Packed(s) if s.width == self.width => {
                let from = s.byte_start();
                self.copy(at * wb, s.len() * wb, |i, k| read_bytes(s.words, from + i, k));
            }
            Units::One(s) if self.width == Width::One => self.copy(at, s.len(), |i, k| u8::pack(&s[i..i + k])),
            Units::One(s) => self.widen(at, s.len(), |i| s[i] as u32),
            Units::Two(s) => self.widen(at, s.len(), |i| s[i] as u32),
            Units::Four(s) => self.widen(at, s.len(), |i| s[i]),
            Units::Packed(s) => self.widen(at, s.len, |i| s.code(i)),
        }
    }

    /// Writes `n` units from `at`, the `i`th `unit(i)`, a word at a time.
    #[inline]
    fn widen(&self, at: usize, n: usize, unit: impl Fn(usize) -> u32) {
        let (log, bits, mask) = (self.width.per_word_log(), self.width.bits(), self.width.mask());
        let (end, mut d, mut i) = (at + n, at, 0);
        while d < end {
            let first = d & ((1 << log) - 1);
            let k = ((1 << log) - first).min(end - d);
            let mut word = 0;
            for u in 0..k {
                word |= (unit(i + u) as u64 & mask) << ((first + u) as u32 * bits);
            }
            let used = if k == 1 << log { u64::MAX } else { ((1u64 << (k as u32 * bits)) - 1) << (first as u32 * bits) };
            let w = &self.words[d >> log];
            w.set(w.get() & !used | word);
            (d, i) = (d + k, i + k);
        }
    }

    /// Writes `n` bytes from byte `to`, which `read(i, k)` gives `k` at a time from the `i`th.
    #[inline]
    fn copy(&self, to: usize, n: usize, read: impl Fn(usize, usize) -> u64) {
        let mut i = 0;
        while i < n {
            let k = (8 - (to + i) % 8).min(n - i);
            write_bytes(self.words, to + i, k, read(i, k));
            i += k;
        }
    }
}

/// Matches the variants that are slices.
macro_rules! each {
    ($units:expr, $s:ident => $e:expr, $p:ident => $packed:expr) => {
        match $units {
            Units::One($s) => $e,
            Units::Two($s) => $e,
            Units::Four($s) => $e,
            Units::Packed($p) => $packed,
        }
    };
}

macro_rules! each_mut {
    ($units:expr, $s:ident => $e:expr, $p:ident => $packed:expr) => {
        match $units {
            UnitsMut::One($s) => $e,
            UnitsMut::Two($s) => $e,
            UnitsMut::Four($s) => $e,
            UnitsMut::Packed($p) => $packed,
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
        units.iter().rev().fold(0, |w, u| w << Self::BITS | u.code() as u64)
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

fn convert<S: Unit, D: Unit>(src: &[S], dst: &mut [D]) {
    for (d, &s) in dst.iter_mut().zip(src) {
        *d = D::of(s.code());
    }
}

fn widest<U: Unit>(units: &[U]) -> u32 {
    units.iter().fold(0, |m, u| m.max(u.code()))
}

impl<'a> Units<'a> {
    #[inline]
    pub fn len(self) -> usize {
        each!(self, s => s.len(), p => p.len())
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
            Self::Packed(p) => p.width,
        }
    }

    #[inline]
    pub fn get(self, i: usize) -> Option<char> {
        match self {
            Self::One(s) => s.get(i).map(|&b| char::from(b)),
            Self::Two(s) => s.get(i).map(|&u| to_char(u as u32)),
            Self::Four(s) => s.get(i).map(|&u| to_char(u)),
            Self::Packed(p) => (i < p.len()).then(|| to_char(p.code(i))),
        }
    }

    #[inline]
    pub fn slice(self, range: Range<usize>) -> Self {
        match self {
            Self::One(s) => Self::One(&s[range]),
            Self::Two(s) => Self::Two(&s[range]),
            Self::Four(s) => Self::Four(&s[range]),
            Self::Packed(p) => Self::Packed(p.slice(range)),
        }
    }

    pub fn chars(self) -> impl Iterator<Item = char> + 'a {
        (0..self.len()).map(move |i| self.get(i).expect("in range"))
    }

    /// The characters, read a word at a time if they're packed.
    #[inline]
    pub(crate) fn each_char(self, mut f: impl FnMut(char)) {
        match self {
            Self::Packed(p) => p.each_code(|c| f(to_char(c))),
            _ => self.chars().for_each(f),
        }
    }

    /// The narrowest width that holds these characters.
    pub(crate) fn narrowest(self) -> Width {
        match self.width() {
            Width::One => Width::One,
            _ => Width::of_code(each!(self, s => widest(s), p => (0..p.len()).map(|i| p.code(i)).max().unwrap_or(0))),
        }
    }

    #[inline]
    pub(crate) fn code(self, i: usize) -> u32 {
        each!(self, s => s[i].code(), p => p.code(i))
    }

    /// Orders two runs of the same length by code point.
    pub(crate) fn compare(self, other: Units<'_>) -> Ordering {
        debug_assert_eq!(self.len(), other.len());
        match (self, other) {
            (Self::One(a), Units::One(b)) => a.cmp(b),
            (Self::Two(a), Units::Two(b)) => a.cmp(b),
            (Self::Four(a), Units::Four(b)) => a.cmp(b),
            (Self::Packed(a), Units::Packed(b)) if a.width == b.width => a.compare_by(b, |w| w),
            _ => (0..self.len()).map(|i| self.code(i).cmp(&other.code(i))).find(|o| o.is_ne()).unwrap_or(Ordering::Equal),
        }
    }

    /// Whether these are the same characters, given both are at their narrowest width.
    #[inline]
    pub(crate) fn equal(self, other: Units<'_>) -> bool {
        match (self, other) {
            (Self::One(a), Units::One(b)) if a.len() <= crate::hash::SHORT => {
                a.len() == b.len() && crate::hash::words(a) == crate::hash::words(b)
            }
            (Self::One(a), Units::One(b)) => a == b,
            (Self::Two(a), Units::Two(b)) => a == b,
            (Self::Four(a), Units::Four(b)) => a == b,
            (Self::Packed(a), Units::Packed(b)) => a.equal(b),
            (Self::Packed(a), Units::One(b)) => a.equal_bytes(b),
            (Self::One(a), Units::Packed(b)) => b.equal_bytes(a),
            (a, b) if a.width() == b.width() && a.len() == b.len() => (0..a.len()).all(|i| a.code(i) == b.code(i)),
            _ => false,
        }
    }

    /// UTF-8 bytes these characters take.
    pub(crate) fn utf8_len(self) -> usize {
        match self {
            Self::One(s) => s.len() + s.iter().filter(|&&b| b >= 0x80).count(),
            Self::Packed(p) if p.width == Width::One => {
                let n = p.len();
                n + (0..n.div_ceil(8)).map(|k| (p.word_at(k, (n - 8 * k).min(8)) & crate::hash::HIGH).count_ones() as usize).sum::<usize>()
            }
            _ => self.chars().map(char::len_utf8).sum(),
        }
    }
}

impl UnitsMut<'_> {
    pub fn len(&self) -> usize {
        each_mut!(self, s => s.len(), p => p.len)
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Fills one-byte units from little-endian words, eight to a word, the last word's extra
    /// bytes dropped.
    pub(crate) fn write_words(&mut self, words: impl Iterator<Item = u64>) {
        match self {
            UnitsMut::Packed(p) if p.width == Width::One => p.words.iter().zip(words).for_each(|(w, v)| w.set(v)),
            UnitsMut::One(s) => s.chunks_mut(8).zip(words).for_each(|(chunk, v)| chunk.copy_from_slice(&v.to_le_bytes()[..chunk.len()])),
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
            UnitsMut::Packed(p) => p.width,
        }
    }

    /// Writes `src` from `at`, each character converted to this width, which must hold them.
    pub(crate) fn write(&mut self, at: usize, src: Units<'_>) {
        let end = at + src.len();
        match (self, src) {
            (UnitsMut::One(d), Units::One(s)) => d[at..end].copy_from_slice(s),
            (UnitsMut::Two(d), Units::Two(s)) => d[at..end].copy_from_slice(s),
            (UnitsMut::Four(d), Units::Four(s)) => d[at..end].copy_from_slice(s),
            (UnitsMut::Packed(d), s) => d.write(at, s),
            (d, Units::Packed(s)) => (0..s.len()).for_each(|i| d.put(at + i, s.code(i))),
            (d, s) => each_mut!(d, d => each!(s, s => convert(s, &mut d[at..end]), _p => unreachable!("packed above")), _p => unreachable!("packed above")),
        }
    }

    fn put(&mut self, i: usize, code: u32) {
        each_mut!(self, s => s[i] = Unit::of(code), p => p.put(i, code));
    }

    pub(crate) fn set(&mut self, i: usize, c: char) {
        self.put(i, c as u32);
    }
}
