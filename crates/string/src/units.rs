//! The bytes of a flat string. A string is UTF-8, so a character takes one to four bytes. Every position in this module is a byte offset.
//!
//! The bytes of a string are valid UTF-8. The library relies on that for correct results, never for memory safety:
//! bytes that are not valid UTF-8 read as U+FFFD.

use std::cell::Cell;
use std::cmp::Ordering;
use std::ops::Range;

use crate::word::{HIGH, ONES, SHORT, fingerprint, low_bytes, pack, read_bytes, starts, write_bytes};

/// The bytes of a flat string, in the representation that its host stores.
#[derive(Clone, Copy, Debug)]
pub enum Units<'a> {
    Slice(&'a [u8]),
    Packed(Packed<'a>),
    Inline(Inline),
}

/// The writable bytes of a new flat string.
#[derive(Debug)]
pub enum UnitsMut<'a> {
    Slice(&'a mut [u8]),
    Packed(PackedMut<'a>),
}

/// Bytes packed into 64-bit words, for a host that stores words. Each word holds eight bytes,
/// with the first byte in the lowest bits. Bits past the last byte are ignored.
#[derive(Clone, Copy, Debug)]
pub struct Packed<'a> {
    words: &'a [Cell<u64>],
    len: usize,
    /// The number of bytes to skip in the first word.
    skip: u8,
}

/// Up to eight bytes in one word, with the first byte in the lowest bits. The host keeps the word in the string's
/// handle instead of in memory. Bytes past the last one are zero. Reads of single bytes use the word directly.
/// The word-at-a-time paths shared with [`Packed`] first convert it with `Units::anchored`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Inline {
    word: u64,
    len: u8,
}

/// The writable bytes of a new flat string, in the layout that [`Packed`] reads. The host has
/// zeroed the words.
#[derive(Debug)]
pub struct PackedMut<'a> {
    words: &'a [Cell<u64>],
    len: usize,
}

impl<'a> Packed<'a> {
    /// Returns the first `len` bytes in `words`. If `words` holds fewer bytes, `len` is clamped to that number.
    #[inline]
    pub fn new(words: &'a [Cell<u64>], len: usize) -> Self {
        Self { words, len: len.min(words.len() << 3), skip: 0 }
    }

    #[inline]
    pub fn len(self) -> usize {
        self.len
    }

    pub fn is_empty(self) -> bool {
        self.len == 0
    }

    #[inline]
    pub(crate) fn byte(self, i: usize) -> u8 {
        let j = self.skip as usize + i;
        (self.words[j >> 3].get() >> ((j & 7) * 8)) as u8
    }

    #[inline]
    pub(crate) fn slice(self, range: Range<usize>) -> Self {
        assert!(range.start <= range.end && range.end <= self.len, "range {range:?} out of {}", self.len);
        let start = self.skip as usize + range.start;
        let words = &self.words[(start >> 3).min(self.words.len())..];
        Self { words, len: range.len(), skip: (start & 7) as u8 }
    }

    /// Copies the bytes into `out`, starting at byte `from`, until `out` is full.
    #[inline]
    pub(crate) fn copy_bytes(self, from: usize, out: &mut [u8]) {
        let at = self.skip as usize + from;
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

    /// Returns whether every byte is ASCII.
    pub(crate) fn is_ascii(self) -> bool {
        self.byte_words().fold(0, |seen, word| seen | word) & HIGH == 0
    }

    /// Returns the bytes as little-endian words of eight bytes. The last word holds the remaining bytes, zero-extended.
    #[inline]
    pub(crate) fn byte_words(self) -> impl Iterator<Item = u64> + Clone + 'a {
        let n = self.len;
        (0..n.div_ceil(8)).map(move |index| self.word_at(index, (n - 8 * index).min(8)))
    }

    /// Returns eight of the bytes as a little-endian word, starting at byte `at`. All eight must be bytes of the string.
    #[inline]
    pub(crate) fn bytes_at(self, at: usize) -> u64 {
        read_bytes(self.words, self.skip as usize + at, 8)
    }

    /// Returns `n` of the bytes as a little-endian word, starting at byte `8 * index`. `n` is 8, or the number of bytes left if fewer remain.
    #[inline]
    pub(crate) fn word_at(self, index: usize, n: usize) -> u64 {
        match self.skip {
            0 if n == 8 => self.words[index].get(),
            _ => read_bytes(self.words, self.skip as usize + 8 * index, n),
        }
    }

    /// Compares two runs of the same length byte by byte, a word at a time. Each word is passed through `map` first.
    /// Bytes are packed lowest first, so the lowest differing bit lies in the first differing byte.
    #[inline]
    pub(crate) fn compare_by(self, other: Packed<'_>, map: impl Fn(u64) -> u64) -> Ordering {
        for at in (0..self.len).step_by(8) {
            let n = (self.len - at).min(8);
            let (x, y) = (map(self.word_at(at / 8, n)), map(other.word_at(at / 8, n)));
            if x != y {
                return first_difference(x, y);
            }
        }
        Ordering::Equal
    }

    #[inline]
    fn equal(self, other: Packed<'_>) -> bool {
        if self.len != other.len {
            return false;
        }
        let bytes = self.len;
        if self.skip == 0 && other.skip == 0 {
            let (whole, rest) = (bytes / 8, bytes % 8);
            let (Some(a), Some(b)) = (self.words.get(..bytes.div_ceil(8)), other.words.get(..bytes.div_ceil(8))) else { return false };
            let same = a[..whole].iter().zip(&b[..whole]).all(|(x, y)| x.get() == y.get());
            return same && (rest == 0 || (a[whole].get() ^ b[whole].get()) & low_bytes(rest) == 0);
        }
        let (a, b) = (self.skip as usize, other.skip as usize);
        (0..bytes).step_by(8).all(|at| {
            let count = (bytes - at).min(8);
            read_bytes(self.words, a + at, count) == read_bytes(other.words, b + at, count)
        })
    }

    /// Returns whether the bytes are equal to `bytes`.
    #[inline]
    pub(crate) fn equal_bytes(self, bytes: &[u8]) -> bool {
        if self.len != bytes.len() {
            return false;
        }
        if self.skip != 0 {
            let at = self.skip as usize;
            return bytes.chunks(8).enumerate().all(|(index, chunk)| read_bytes(self.words, at + 8 * index, chunk.len()) == pack(chunk));
        }
        let (chunks, tail) = bytes.as_chunks::<8>();
        let Some(words) = self.words.get(..chunks.len() + !tail.is_empty() as usize) else { return false };
        // OR the differences together across all words. Then a single branch decides the result, whatever the length.
        let mut diff = 0;
        for (cell, chunk) in words.iter().zip(chunks) {
            diff |= cell.get() ^ u64::from_le_bytes(*chunk);
        }
        if let Some(last) = words.get(chunks.len()) {
            let tail_word = match bytes.last_chunk::<8>() {
                Some(end) => u64::from_le_bytes(*end) >> (64 - 8 * tail.len()),
                None => pack(tail),
            };
            diff |= (last.get() ^ tail_word) & low_bytes(tail.len());
        }
        diff == 0
    }
}

/// Orders two words that differ by their first differing byte. The first byte of a word is in its lowest bits.
#[inline]
fn first_difference(x: u64, y: u64) -> Ordering {
    let shift = (x ^ y).trailing_zeros() / 8 * 8;
    (x >> shift & 0xFF).cmp(&(y >> shift & 0xFF))
}

impl Inline {
    /// Returns the first `len` bytes of `word`. `len` is clamped to eight.
    #[inline]
    pub fn new(word: u64, len: usize) -> Self {
        let len = len.min(8);
        Self { word: word & low_bytes(len), len: len as u8 }
    }

    /// Returns the `len` bytes that `init` writes, for use in a host's [`crate::Host::flat`]. `len` is at most eight.
    #[inline]
    pub fn filled(len: usize, init: impl FnOnce(UnitsMut<'_>)) -> Self {
        let word = [Cell::new(0)];
        init(UnitsMut::Packed(PackedMut::new(&word, len)));
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

    /// Returns the number of characters in these bytes.
    #[inline]
    pub fn chars(self) -> usize {
        // In ASCII text every byte is a character.
        if self.word & HIGH == 0 {
            return self.len();
        }
        starts(self.word) as usize - (8 - self.len())
    }

    /// Returns the bytes, followed by zeros.
    #[inline]
    pub(crate) fn bytes(self) -> [u8; 8] {
        self.word.to_le_bytes()
    }

    #[inline]
    fn byte(self, i: usize) -> u8 {
        (self.word >> (8 * i)) as u8
    }

    #[inline]
    fn slice(self, range: Range<usize>) -> Self {
        assert!(range.start <= range.end && range.end <= self.len(), "range {range:?} out of {}", self.len);
        Self::new(self.word.checked_shr(8 * range.start as u32).unwrap_or(0), range.len())
    }
}

impl<'a> PackedMut<'a> {
    /// Returns a writer for `len` bytes in `words`. If `words` holds fewer bytes, `len` is clamped to that number.
    #[inline]
    pub fn new(words: &'a [Cell<u64>], len: usize) -> Self {
        Self { words, len: len.min(words.len() << 3) }
    }

    /// Writes `src` starting at byte `at`.
    fn write(&self, at: usize, src: Units<'_>) {
        assert!(at + src.len() <= self.len, "writing past the end");
        match src {
            Units::Packed(packed) => {
                let from = packed.skip as usize;
                self.copy(at, packed.len(), |i, count| read_bytes(packed.words, from + i, count));
            }
            Units::Slice(bytes) => self.copy(at, bytes.len(), |i, count| pack(&bytes[i..i + count])),
            Units::Inline(inline) => self.copy(at, inline.len(), |i, count| inline.word >> (8 * i) & low_bytes(count)),
        }
    }

    /// Writes `n` bytes starting at byte `to`. `read(i, count)` returns `count` source bytes, starting at source byte `i`, in the low bytes of a word.
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

impl<'a> Units<'a> {
    /// Returns eight bytes as a little-endian word, starting at byte `8 * index`, or the remaining bytes if fewer are left. Bytes past the end are zero.
    #[inline]
    pub(crate) fn byte_chunk(self, index: usize) -> u64 {
        let n = (self.len() - 8 * index).min(8);
        match self {
            Units::Inline(inline) => inline.word,
            Units::Packed(packed) => packed.word_at(index, n),
            Units::Slice(bytes) => pack(&bytes[8 * index..8 * index + n]),
        }
    }

    /// Returns the number of bytes.
    #[inline]
    pub fn len(self) -> usize {
        match self {
            Self::Slice(bytes) => bytes.len(),
            Self::Packed(packed) => packed.len(),
            Self::Inline(inline) => inline.len(),
        }
    }

    #[inline]
    pub fn is_empty(self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub(crate) fn byte(self, i: usize) -> u8 {
        match self {
            Self::Slice(bytes) => bytes[i],
            Self::Packed(packed) => packed.byte(i),
            Self::Inline(inline) => inline.byte(i),
        }
    }

    /// Returns the bytes in `range`. This is always inlined. The rope walks call it on their hot path, and LLVM's own
    /// inlining decision there changes with unrelated code elsewhere in the program.
    #[inline(always)]
    pub fn slice(self, range: Range<usize>) -> Self {
        match self {
            Self::Slice(bytes) => Self::Slice(&bytes[range]),
            Self::Packed(packed) => Self::Packed(packed.slice(range)),
            Self::Inline(inline) => Self::Inline(inline.slice(range)),
        }
    }

    /// Returns these bytes in a form that the word-at-a-time paths can read. Inline bytes are copied into `cell`
    /// and returned as [`Packed`] bytes over it. Other bytes are returned unchanged.
    #[inline]
    pub(crate) fn anchored<'b>(self, cell: &'b Cell<u64>) -> Units<'b>
    where
        'a: 'b,
    {
        match self {
            Self::Inline(inline) => {
                cell.set(inline.word);
                Units::Packed(Packed::new(std::slice::from_ref(cell), inline.len()))
            }
            units => units,
        }
    }

    /// Returns whether every byte is ASCII.
    pub fn is_ascii(self) -> bool {
        match self {
            Self::Slice(bytes) => bytes.is_ascii(),
            Self::Packed(packed) => packed.is_ascii(),
            Self::Inline(inline) => inline.word & HIGH == 0,
        }
    }

    /// Returns the number of characters in these bytes. The bytes are read a word at a time.
    pub fn count_chars(self) -> usize {
        let n = self.len();
        match self {
            // Each representation gets a loop of its own, so that the loop reads its words directly.
            Units::Packed(packed) if packed.skip == 0 => count_in(packed.words.iter().map(Cell::get), n),
            Units::Slice(bytes) => {
                let (whole, tail) = bytes.as_chunks::<8>();
                count_in(whole.iter().map(|chunk| u64::from_le_bytes(*chunk)).chain(std::iter::once(pack(tail))), n)
            }
            _ => count_in((0..n.div_ceil(8)).map(|index| self.byte_chunk(index)), n),
        }
    }

    /// Returns the byte offset at which character `index` starts. Returns the number of bytes if there are only `index` characters or fewer.
    pub(crate) fn offset_of(self, index: usize) -> usize {
        let n = self.len();
        match self {
            Units::Packed(packed) if packed.skip == 0 => offset_in(packed.words.iter().map(Cell::get), n, index),
            Units::Slice(bytes) => {
                let (whole, tail) = bytes.as_chunks::<8>();
                offset_in(whole.iter().map(|chunk| u64::from_le_bytes(*chunk)).chain(std::iter::once(pack(tail))), n, index)
            }
            _ => offset_in((0..n.div_ceil(8)).map(|at| self.byte_chunk(at)), n, index),
        }
    }

    /// Returns the character that starts at byte `at`, and the number of bytes that it takes. `at` must be less than the number of bytes.
    /// Bytes that are no character read as U+FFFD.
    #[inline]
    pub(crate) fn char_at(self, at: usize) -> (char, usize) {
        let first = self.byte(at);
        if first < 0x80 {
            return (char::from(first), 1);
        }
        let size = match first {
            0xC0..=0xDF => 2,
            0xE0..=0xEF => 3,
            0xF0..=0xFF => 4,
            _ => return (char::REPLACEMENT_CHARACTER, 1),
        };
        let size = size.min(self.len() - at);
        let mut code = u32::from(first) & (0x7F >> size);
        for i in 1..size {
            code = code << 6 | u32::from(self.byte(at + i)) & 0x3F;
        }
        (char::from_u32(code).unwrap_or(char::REPLACEMENT_CHARACTER), size)
    }

    /// Returns the byte offset at which the character before byte `at` starts. `at` must be greater than 0.
    #[inline]
    pub(crate) fn before(self, at: usize) -> usize {
        let mut start = at - 1;
        while start > 0 && self.byte(start) & 0xC0 == 0x80 {
            start -= 1;
        }
        start
    }

    pub fn chars(self) -> impl Iterator<Item = char> + Clone + 'a {
        let mut at = 0;
        std::iter::from_fn(move || {
            if at >= self.len() {
                return None;
            }
            let (character, size) = self.char_at(at);
            at += size;
            Some(character)
        })
    }

    /// Copies the bytes into `out`, which must have room for them.
    pub(crate) fn copy_to(self, out: &mut [u8]) {
        let out = &mut out[..self.len()];
        match self {
            Units::Slice(bytes) => out.copy_from_slice(bytes),
            Units::Packed(packed) => packed.copy_bytes(0, out),
            Units::Inline(inline) => out.copy_from_slice(&inline.bytes()[..inline.len()]),
        }
    }

    /// Compares two runs of the same length byte by byte. For whole strings this is the order of their characters by code point.
    pub(crate) fn compare(self, other: Units<'_>) -> Ordering {
        debug_assert_eq!(self.len(), other.len());
        let (this_cell, other_cell) = (Cell::new(0), Cell::new(0));
        let (this, other) = (self.anchored(&this_cell), other.anchored(&other_cell));
        match (this, other) {
            (Units::Slice(a), Units::Slice(b)) => a.cmp(b),
            (Units::Packed(a), Units::Packed(b)) => a.compare_by(b, |word| word),
            _ => {
                for index in 0..this.len().div_ceil(8) {
                    let (x, y) = (this.byte_chunk(index), other.byte_chunk(index));
                    if x != y {
                        return first_difference(x, y);
                    }
                }
                Ordering::Equal
            }
        }
    }

    /// Returns whether the two runs hold the same bytes.
    #[inline]
    pub fn equal(self, other: Units<'_>) -> bool {
        if let (Self::Inline(a), Units::Inline(b)) = (self, other) {
            return a == b;
        }
        let (this_cell, other_cell) = (Cell::new(0), Cell::new(0));
        match (self.anchored(&this_cell), other.anchored(&other_cell)) {
            (Units::Slice(a), Units::Slice(b)) if a.len() <= SHORT => a.len() == b.len() && fingerprint(a) == fingerprint(b),
            (Units::Slice(a), Units::Slice(b)) => a == b,
            (Units::Packed(a), Units::Packed(b)) => a.equal(b),
            (Units::Packed(a), Units::Slice(b)) => a.equal_bytes(b),
            (Units::Slice(a), Units::Packed(b)) => b.equal_bytes(a),
            _ => false,
        }
    }

    /// Returns whether these bytes are `bytes`.
    #[inline]
    pub fn equal_bytes(self, bytes: &[u8]) -> bool {
        match self {
            Units::Inline(inline) => inline.len() == bytes.len() && pack(bytes) == inline.word,
            Units::Slice(own) if own.len() <= SHORT => own.len() == bytes.len() && fingerprint(own) == fingerprint(bytes),
            Units::Slice(own) => own == bytes,
            Units::Packed(packed) => packed.equal_bytes(bytes),
        }
    }
}

/// Returns the number of characters in the first `n` bytes of `words`, which hold eight bytes each. The bytes past `n` can be anything.
#[inline(always)]
fn count_in(mut words: impl Iterator<Item = u64>, n: usize) -> usize {
    let (whole, rest) = (n / 8, n % 8);
    let mut count = 0;
    for word in words.by_ref().take(whole) {
        count += starts(word) as usize;
    }
    if rest > 0
        && let Some(word) = words.next()
    {
        count += starts(word & low_bytes(rest)) as usize - (8 - rest);
    }
    count
}

/// Returns the byte offset at which character `index` starts in the first `n` bytes of `words`, which hold eight bytes each. Returns `n` if there are only `index` characters or fewer. The bytes past `n` can be anything.
#[inline(always)]
fn offset_in(mut words: impl Iterator<Item = u64>, n: usize, index: usize) -> usize {
    /// Returns the offset in `word` of the byte that starts character `index` of the word. The word has more starts than `index`.
    #[inline(always)]
    fn start_in(word: u64, index: usize) -> usize {
        // Drop the marks of the starts before the character. The lowest mark left is its byte.
        let mut marks = (!(word >> 7) | (word >> 6)) & ONES;
        for _ in 0..index {
            marks &= marks - 1;
        }
        marks.trailing_zeros() as usize / 8
    }
    let (whole, rest) = (n / 8, n % 8);
    let mut seen = 0;
    for (at, word) in words.by_ref().take(whole).enumerate() {
        let here = starts(word) as usize;
        if seen + here > index {
            return 8 * at + start_in(word, index - seen);
        }
        seen += here;
    }
    if rest > 0
        && let Some(word) = words.next()
    {
        // A byte past the end is 0 here, and counts as a start. So the count is corrected by the number of such bytes.
        let word = word & low_bytes(rest);
        if seen + starts(word) as usize - (8 - rest) > index {
            return 8 * whole + start_in(word, index - seen);
        }
    }
    n
}

/// Fills `out` from the start with consecutive runs of bytes. The total length of the runs
/// must equal the length of `out`. When `out` is packed in words, the writer stores a word at a time.
pub(crate) struct RunWriter<'o, 'a> {
    out: &'o mut UnitsMut<'a>,
    at: usize,
    /// The bytes collected so far for the next word. `filled` is the number of bits collected. Both are used only for packed bytes.
    word: u64,
    filled: u32,
}

impl<'o, 'a> RunWriter<'o, 'a> {
    pub(crate) fn new(out: &'o mut UnitsMut<'a>) -> Self {
        Self { out, at: 0, word: 0, filled: 0 }
    }

    #[inline(always)]
    pub(crate) fn push(&mut self, run: Units<'_>) {
        let n = run.len();
        let UnitsMut::Packed(packed) = &*self.out else {
            self.out.write(self.at, run);
            self.at += n;
            return;
        };
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
            && self.filled > 0
        {
            packed.words[self.at / 8].set(self.word);
        }
    }
}

impl UnitsMut<'_> {
    /// Returns the number of bytes.
    pub fn len(&self) -> usize {
        match self {
            UnitsMut::Slice(bytes) => bytes.len(),
            UnitsMut::Packed(packed) => packed.len,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Fills the bytes from little-endian `words`, eight bytes to a word. Extra bytes in the
    /// last word are ignored: the bits past the last byte are left 0, so that a host can compare two strings a word at a time.
    pub(crate) fn write_words(&mut self, words: impl Iterator<Item = u64>) {
        match self {
            UnitsMut::Packed(packed) => {
                for (index, (cell, word)) in packed.words.iter().zip(words).enumerate() {
                    cell.set(word & low_bytes(packed.len.saturating_sub(8 * index).min(8)));
                }
            }
            UnitsMut::Slice(bytes) => bytes.chunks_mut(8).zip(words).for_each(|(chunk, word)| chunk.copy_from_slice(&word.to_le_bytes()[..chunk.len()])),
        }
    }

    /// Fills these bytes from `src`, which must have the same length.
    pub fn copy_from(&mut self, src: Units<'_>) {
        assert!(src.len() == self.len(), "copying from a string of another length");
        self.write(0, src);
    }

    /// Writes `src` starting at byte `at`.
    pub(crate) fn write(&mut self, at: usize, src: Units<'_>) {
        match self {
            UnitsMut::Slice(dest) => src.copy_to(&mut dest[at..at + src.len()]),
            UnitsMut::Packed(dest) => dest.write(at, src),
        }
    }

    /// Writes `character` as UTF-8 starting at byte `at`. Returns the number of bytes written.
    pub(crate) fn encode(&mut self, at: usize, character: char) -> usize {
        let mut buf = [0; 4];
        let encoded = character.encode_utf8(&mut buf).as_bytes();
        self.write(at, Units::Slice(encoded));
        encoded.len()
    }
}
