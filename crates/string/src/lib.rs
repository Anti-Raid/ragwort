//! Immutable strings over any heap. A string is either flat or a rope. A flat string stores its
//! characters as UTF-8 in one array of bytes. A rope is a balanced binary tree of strings.
//! [`concat()`] builds a rope when the result is too long to copy cheaply.
//! The heap implements [`Host`], and the library allocates only through it.
//! A flat string's text can also live outside the heap, as an [`External`].
//!
//! # Positions
//!
//! A position that a caller passes or receives is a character index: [`len`] counts characters, [`char_at`] returns character `i`,
//! and [`substring`] and [`find`] take and return character indices. Inside the library a position is a byte offset. A string
//! knows both its number of bytes and its number of characters. Where the two are equal the string is ASCII, and a
//! character index is a byte offset. Otherwise the library counts characters a word at a time to convert one to the other.
//!
//! A caller that keeps a byte offset needs no such count. The procedures for that are [`char_at_byte`], [`byte_before`],
//! [`substring_bytes`], [`find_bytes`] and [`rfind_bytes`]. Each checks that an offset it is given lies between two characters,
//! so none of them can cut a character. [`char_index`] and [`byte_offset_of`] convert between the two kinds of position.

mod case;
mod digit;
mod external;
mod hash;
mod intern;
mod iter;
mod rope;
mod search;
mod units;
mod word;

#[cfg(test)]
#[path = "tests/support.rs"]
mod testing;
#[cfg(test)]
#[path = "tests/string.rs"]
mod tests;

use std::cmp::Ordering;
use std::fmt;

pub use case::{compare_ci, downcase, downcase_char, foldcase, foldcase_char, upcase, upcase_char};
pub use digit::digit_value;
pub use external::{External, ExternalText, check_external};
pub use hash::{hash, hash_str, hash_units};
pub use intern::{Table, intern, intern_str};
pub use iter::{Chars, Chunks};
pub use rope::{concat, concat_all, flatten, substring, substring_bytes};
pub use search::{Split, SplitWhitespace, ends_with, find, find_bytes, rfind, rfind_bytes, split, split_whitespace, splitn, starts_with, trim, trim_end, trim_start};
pub use units::{Inline, Packed, PackedMut, Units, UnitsMut};

/// The maximum length of a string, in bytes. A rope can share the same string many times,
/// so memory does not bound the length.
pub const MAX_LEN: usize = (1 << 48) - 1;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum StrError {
    OutOfRange,
    TooLong,
    /// Bytes that were read as text are not valid UTF-8.
    NotUtf8,
}

/// Summary of a string. The host stores it in each rope node.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Info {
    /// The number of bytes.
    pub bytes: usize,
    /// The number of characters. It equals `bytes` exactly when the string is ASCII.
    pub chars: usize,
    /// The number of edges from this node to its deepest flat string. Ropes stay balanced, so
    /// the depth is at most about `log2` of the number of flat strings.
    pub depth: u8,
}

pub enum StrView<'a, S> {
    /// A flat string: its bytes, and the number of characters in them.
    Flat { units: Units<'a>, chars: usize },
    /// `flat` is the flat copy that [`Host::flattened`] stored for the rope, if any. It holds the same characters as the rope.
    Rope { left: S, right: S, info: Info, flat: Option<S> },
}

/// The heap that stores strings. The library reads strings through [`Host::view`] and creates
/// them with [`Host::flat`] and [`Host::rope`].
pub trait Host {
    /// A handle to a string. Equal handles refer to the same string.
    type Str: Copy + Eq;
    type Error: From<StrError>;

    fn view(&self, string: Self::Str) -> StrView<'_, Self::Str>;

    /// Allocates a flat string of `bytes` bytes, which hold `chars` characters. The bytes start zeroed, and `init` fills them in with UTF-8.
    /// Views of other strings stay valid while `init` runs.
    ///
    /// A host that interns its strings can return a string that it already has with the same characters.
    fn flat(&self, bytes: usize, chars: usize, init: impl FnOnce(UnitsMut<'_>)) -> Result<Self::Str, Self::Error>;

    /// Returns the interned string of `string`, if the host interns its strings and already knows it for this handle. Finding it must take no work that grows with the length of the string.
    ///
    /// Two strings that this returns have the same characters exactly when they are the same handle. The default returns `None`: the host interns nothing.
    fn known(&self, string: Self::Str) -> Option<Self::Str> {
        let _ = string;
        None
    }

    /// Returns the interned string of `string`, and interns `string` if that is needed to find it. Returns `None` if the host does not intern this string. See [`Host::known`].
    fn canonical(&self, string: Self::Str) -> Result<Option<Self::Str>, Self::Error> {
        let _ = string;
        Ok(None)
    }

    /// Returns the bytes of the flat string `string` from byte `start` up to, but not including, byte `end` as a string that shares those bytes with `string`, if the host can share them and chooses to.
    /// Both offsets lie between two characters. `chars` is the number of characters in the part, if the caller knows it. The default returns `None`, and the library then copies the bytes.
    fn slice(&self, string: Self::Str, start: usize, end: usize, chars: Option<usize>) -> Result<Option<Self::Str>, Self::Error> {
        let _ = (string, start, end, chars);
        Ok(None)
    }

    /// Returns the [`Info`] of `string`. The default takes it from [`Host::view`]. A host that can read it with less work than a view takes overrides this.
    /// Building a rope asks for the info of each node on the way many times.
    #[inline]
    fn info(&self, string: Self::Str) -> Info {
        match self.view(string) {
            StrView::Flat { units, chars } => Info { bytes: units.len(), chars, depth: 0 },
            StrView::Rope { info, .. } => info,
        }
    }

    /// Allocates a rope node of `left` followed by `right`. Both are nonempty, and `info` describes the new node.
    fn rope(&self, left: Self::Str, right: Self::Str, info: Info) -> Result<Self::Str, Self::Error>;

    /// Stores `flat`, a flat copy of `rope`'s characters, so that later views of `rope` return it in [`StrView::Rope`].
    /// A host whose ropes cannot be modified keeps the default, which does nothing.
    fn flattened(&self, rope: Self::Str, flat: Self::Str) {
        let _ = (rope, flat);
    }

    /// Records one read of `rope` by character index and returns the total number of such reads. The library flattens a rope
    /// that has been read often enough. With the default, which returns 0, reads never flatten a rope.
    fn count_read(&self, rope: Self::Str) -> u64 {
        let _ = rope;
        0
    }

    /// Called before the library performs about `work` byte operations. Returning an error aborts the operation.
    #[inline]
    fn charge(&self, work: u64) -> Result<(), Self::Error> {
        let _ = work;
        Ok(())
    }
}

pub type Res<H> = Result<<H as Host>::Str, <H as Host>::Error>;

#[inline]
pub(crate) fn info<H: Host>(h: &H, string: H::Str) -> Info {
    h.info(string)
}

/// Returns the byte offset of character `index` in the flat string `units`, which holds `chars` characters. `index` is at most `chars`.
#[inline]
pub(crate) fn offset(units: Units<'_>, chars: usize, index: usize) -> usize {
    if chars == units.len() {
        index
    } else {
        units.offset_of(index)
    }
}

/// Returns the byte offset of character `index` of `string`. `index` is at most the number of characters.
pub(crate) fn byte_offset<H: Host>(h: &H, mut string: H::Str, mut index: usize) -> usize {
    let mut base = 0;
    loop {
        match h.view(string) {
            StrView::Flat { units, chars } => return base + offset(units, chars, index),
            StrView::Rope { info, .. } if info.chars == info.bytes => return base + index,
            StrView::Rope { flat: Some(flat), .. } => string = flat,
            StrView::Rope { left, right, .. } => {
                let left_info = info(h, left);
                if index < left_info.chars {
                    string = left;
                } else {
                    (base, index, string) = (base + left_info.bytes, index - left_info.chars, right);
                }
            }
        }
    }
}

/// Returns the flat string of `string` that holds byte `at`, and the offset of that byte in it. `at` is less than the number of bytes.
fn leaf<H: Host>(h: &H, mut string: H::Str, mut at: usize) -> (Units<'_>, usize) {
    loop {
        match h.view(string) {
            StrView::Flat { units, .. } => return (units, at),
            StrView::Rope { flat: Some(flat), .. } => string = flat,
            StrView::Rope { left, right, .. } => {
                let left_bytes = info(h, left).bytes;
                (string, at) = if at < left_bytes {
                    (left, at)
                } else {
                    (right, at - left_bytes)
                };
            }
        }
    }
}

/// Returns whether byte offset `at` of `string` lies between two characters, or at one of the two ends.
#[inline]
pub fn is_boundary<H: Host>(h: &H, string: H::Str, at: usize) -> bool {
    let (units, offset) = match h.view(string) {
        StrView::Flat { units, .. } => (units, at),
        StrView::Rope { info, .. } if at < info.bytes => leaf(h, string, at),
        StrView::Rope { info, .. } => return at == info.bytes,
    };
    if offset >= units.len() {
        return offset == units.len();
    }
    units.byte(offset) & 0xC0 != 0x80
}

/// Returns the character that starts at byte offset `at` of `string`, and the number of bytes that it takes. Fails if no character starts at `at`.
#[inline]
pub fn char_at_byte<H: Host>(h: &H, string: H::Str, at: usize) -> Result<(char, usize), H::Error> {
    // A flat string is viewed once.
    let (units, offset) = match h.view(string) {
        StrView::Flat { units, .. } => (units, at),
        StrView::Rope { info, .. } if at < info.bytes => leaf(h, string, at),
        StrView::Rope { .. } => return Err(StrError::OutOfRange.into()),
    };
    if offset >= units.len() || units.byte(offset) & 0xC0 == 0x80 {
        return Err(StrError::OutOfRange.into());
    }
    Ok(units.char_at(offset))
}

/// Returns the byte offset at which the character before byte offset `at` starts. Fails if `at` is 0 or does not lie between two characters.
pub fn byte_before<H: Host>(h: &H, string: H::Str, at: usize) -> Result<usize, H::Error> {
    if at == 0 || !is_boundary(h, string, at) {
        return Err(StrError::OutOfRange.into());
    }
    // The character ends at `at`, so its last byte is in the flat string that holds byte `at - 1`. A character never spans two flat strings.
    let (units, offset) = leaf(h, string, at - 1);
    Ok(at - 1 - (offset - units.before(offset + 1)))
}

/// Returns the byte at byte offset `at` of `string`.
pub fn byte_at<H: Host>(h: &H, string: H::Str, at: usize) -> Result<u8, H::Error> {
    if at >= byte_len(h, string) {
        return Err(StrError::OutOfRange.into());
    }
    let (units, offset) = leaf(h, string, at);
    Ok(units.byte(offset))
}

/// Returns the index of the character that starts at byte offset `at` of `string`: the number of characters before it. Fails if `at` does not lie between two characters.
pub fn char_index<H: Host>(h: &H, mut string: H::Str, mut at: usize) -> Result<usize, H::Error> {
    if !is_boundary(h, string, at) {
        return Err(StrError::OutOfRange.into());
    }
    let mut before = 0;
    loop {
        match h.view(string) {
            StrView::Flat { units, chars } => {
                let counted = if chars == units.len() {
                    at
                } else {
                    units.slice(0..at).count_chars()
                };
                return Ok(before + counted);
            }
            StrView::Rope { info, .. } if info.chars == info.bytes => return Ok(before + at),
            StrView::Rope { flat: Some(flat), .. } => string = flat,
            StrView::Rope { left, right, .. } => {
                let left_info = info(h, left);
                if at < left_info.bytes {
                    string = left;
                } else {
                    (before, at, string) = (before + left_info.chars, at - left_info.bytes, right);
                }
            }
        }
    }
}

/// Returns the byte offset at which character `index` of `string` starts. `index` can be the number of characters, which gives the number of bytes.
pub fn byte_offset_of<H: Host>(h: &H, string: H::Str, index: usize) -> Result<usize, H::Error> {
    if index > len(h, string) {
        return Err(StrError::OutOfRange.into());
    }
    Ok(byte_offset(h, string, index))
}

pub fn empty<H: Host>(h: &H) -> Res<H> {
    h.flat(0, 0, |_| {})
}

pub fn from_str<H: Host>(h: &H, string: &str) -> Res<H> {
    if string.len() > MAX_LEN {
        return Err(StrError::TooLong.into());
    }
    h.charge(string.len() as u64)?;
    h.flat(string.len(), string.chars().count(), |mut out| out.write(0, Units::Slice(string.as_bytes())))
}

/// Returns a string of the characters that `chars` yields. `chars` is iterated twice, and both passes must yield the same characters.
pub fn from_chars<H: Host>(h: &H, chars: impl Iterator<Item = char> + Clone) -> Res<H> {
    let (bytes, count) = chars.clone().fold((0usize, 0usize), |(bytes, count), character| (bytes.saturating_add(character.len_utf8()), count + 1));
    if bytes > MAX_LEN {
        return Err(StrError::TooLong.into());
    }
    h.charge(bytes as u64)?;
    h.flat(bytes, count, |mut out| {
        let mut at = 0;
        for character in chars.take(count) {
            // A second pass that yields other characters must not write past the end.
            if at + character.len_utf8() > bytes {
                break;
            }
            at += out.encode(at, character);
        }
    })
}

/// Returns a string of `n` copies of `character`.
pub fn repeat<H: Host>(h: &H, character: char, n: usize) -> Res<H> {
    let size = character.len_utf8();
    let bytes = n.checked_mul(size).filter(|&bytes| bytes <= MAX_LEN).ok_or(StrError::TooLong)?;
    h.charge(bytes as u64)?;
    h.flat(bytes, n, |mut out| {
        if character.is_ascii() {
            out.write_words(std::iter::repeat(word::ONES * character as u64));
            return;
        }
        for i in 0..n {
            out.encode(i * size, character);
        }
    })
}

/// Returns the number of characters in `string`.
pub fn len<H: Host>(h: &H, string: H::Str) -> usize {
    info(h, string).chars
}

/// Returns the number of bytes that `string` takes as UTF-8.
pub fn byte_len<H: Host>(h: &H, string: H::Str) -> usize {
    info(h, string).bytes
}

pub fn is_flat<H: Host>(h: &H, string: H::Str) -> bool {
    matches!(h.view(string), StrView::Flat { .. })
}

/// Returns the character at index `i`. In an ASCII string that is one read. Otherwise the characters before it are counted, a word at a time.
/// On a rope, the read also takes time proportional to the rope's depth.
/// A rope that is read this way often enough is flattened.
#[inline]
pub fn char_at<H: Host>(h: &H, string: H::Str, i: usize) -> Result<char, H::Error> {
    match h.view(string) {
        StrView::Flat { units, chars } => flat_char_at(units, chars, i).ok_or_else(|| StrError::OutOfRange.into()),
        StrView::Rope { .. } => rope_char_at(h, string, i),
    }
}

/// Returns character `i` of the flat string `units`, which holds `chars` characters.
#[inline]
fn flat_char_at(units: Units<'_>, chars: usize, i: usize) -> Option<char> {
    if i >= chars {
        return None;
    }
    if chars == units.len() {
        return Some(char::from(units.byte(i)));
    }
    Some(units.char_at(units.offset_of(i)).0)
}

/// The rope case of [`char_at`]. This and the other rope cases are kept out of line, so that the flat cases stay small when inlined.
#[inline(never)]
fn rope_char_at<H: Host>(h: &H, mut string: H::Str, mut i: usize) -> Result<char, H::Error> {
    match h.view(string) {
        StrView::Rope { flat: Some(flat), .. } => string = flat,
        // Only an ASCII rope is flattened for reads: in its flat copy a character index is a byte offset. For any other text the rope is the
        // faster one to read, because its nodes count the characters of each piece and a flat copy would be counted from its start.
        StrView::Rope { info, .. } if info.chars == info.bytes && h.count_read(string).saturating_mul(rope::CHARS_PER_READ) >= info.chars as u64 => {
            string = flatten(h, string)?;
        }
        _ => {}
    }
    loop {
        match h.view(string) {
            StrView::Flat { units, chars } => return flat_char_at(units, chars, i).ok_or_else(|| StrError::OutOfRange.into()),
            StrView::Rope { flat: Some(flat), .. } => string = flat,
            StrView::Rope { left, right, info, .. } => {
                if i >= info.chars {
                    return Err(StrError::OutOfRange.into());
                }
                let left_chars = len(h, left);
                (string, i) = if i < left_chars {
                    (left, i)
                } else {
                    (right, i - left_chars)
                };
            }
        }
    }
}

pub fn chunks<H: Host>(h: &H, string: H::Str) -> Chunks<'_, H> {
    Chunks::new(h, string, 0, byte_len(h, string))
}

pub fn chars<H: Host>(h: &H, string: H::Str) -> Chars<'_, H> {
    Chars::new(chunks(h, string))
}

/// Compares `a` and `b` lexicographically by code point. If one string is a prefix of the other, the shorter string orders first.
/// In UTF-8 the order of the bytes is the order of the code points, so the bytes are compared.
#[inline]
pub fn compare<H: Host>(h: &H, a: H::Str, b: H::Str) -> Result<Ordering, H::Error> {
    if a == b {
        return Ok(Ordering::Equal);
    }
    if let (Some(units_a), Some(units_b)) = (flat(h, a), flat(h, b)) {
        let n = units_a.len().min(units_b.len());
        h.charge(n as u64)?;
        return Ok(units_a.slice(0..n).compare(units_b.slice(0..n)).then(units_a.len().cmp(&units_b.len())));
    }
    rope_compare(h, a, b)
}

#[inline(never)]
fn rope_compare<H: Host>(h: &H, a: H::Str, b: H::Str) -> Result<Ordering, H::Error> {
    let ((ia, fa), (ib, fb)) = (summary(h, a), summary(h, b));
    let n = ia.bytes.min(ib.bytes);
    h.charge(n as u64)?;
    if let (Some(units_a), Some(units_b)) = (fa, fb) {
        return Ok(units_a.slice(0..n).compare(units_b.slice(0..n)).then(ia.bytes.cmp(&ib.bytes)));
    }
    compare_chunks(h, a, b)
}

#[inline(never)]
fn compare_chunks<H: Host>(h: &H, a: H::Str, b: H::Str) -> Result<Ordering, H::Error> {
    Ok(compare_runs(chunks(h, a), chunks(h, b)).then(byte_len(h, a).cmp(&byte_len(h, b))))
}

/// Compares the bytes of two chunk sequences, up to the length of the shorter sequence. Returns `Equal` if they agree over that length.
pub(crate) fn compare_runs<'a>(mut ca: impl Iterator<Item = Units<'a>>, mut cb: impl Iterator<Item = Units<'a>>) -> Ordering {
    let (mut run_a, mut run_b) = (Units::Slice(&[]), Units::Slice(&[]));
    loop {
        while run_a.is_empty() {
            let Some(next) = ca.next() else { return Ordering::Equal };
            run_a = next;
        }
        while run_b.is_empty() {
            let Some(next) = cb.next() else { return Ordering::Equal };
            run_b = next;
        }
        let n = run_a.len().min(run_b.len());
        match run_a.slice(0..n).compare(run_b.slice(0..n)) {
            Ordering::Equal => (run_a, run_b) = (run_a.slice(n..run_a.len()), run_b.slice(n..run_b.len())),
            order => return order,
        }
    }
}

#[inline]
pub fn equal<H: Host>(h: &H, a: H::Str, b: H::Str) -> Result<bool, H::Error> {
    if a == b {
        return Ok(true);
    }
    // Two interned strings are compared as handles. No character is read.
    if let (Some(first), Some(second)) = (h.known(a), h.known(b)) {
        return Ok(first == second);
    }
    if let (Some(units_a), Some(units_b)) = (flat(h, a), flat(h, b)) {
        if units_a.len() != units_b.len() {
            return Ok(false);
        }
        h.charge(units_a.len() as u64)?;
        // A host that interns its strings interns the two. They are compared as handles, now and from now on.
        if let (Some(first), Some(second)) = (h.canonical(a)?, h.canonical(b)?) {
            return Ok(first == second);
        }
        return Ok(units_a.equal(units_b));
    }
    rope_equal(h, a, b, true)
}

/// Returns whether `a` and `b` have the same characters, by reading the characters. Unlike [`equal`], this interns nothing and leaves a rope as it is. A host that interns its strings uses it to look a string up among them.
pub fn same_chars<H: Host>(h: &H, a: H::Str, b: H::Str) -> Result<bool, H::Error> {
    if a == b {
        return Ok(true);
    }
    rope_equal(h, a, b, false)
}

/// Compares two strings of which at least one is not flat, or which are compared by their characters. If `intern` is true, a host that interns its strings interns the two and compares the interned strings.
#[inline(never)]
fn rope_equal<H: Host>(h: &H, a: H::Str, b: H::Str, intern: bool) -> Result<bool, H::Error> {
    let (ia, fa) = summary(h, a);
    let (ib, fb) = summary(h, b);
    if ia.bytes != ib.bytes || ia.chars != ib.chars {
        return Ok(false);
    }
    h.charge(ia.bytes as u64)?;
    // The two interned strings are compared as handles, now and from now on.
    if intern
        && let (Some(first), Some(second)) = (h.canonical(a)?, h.canonical(b)?)
    {
        return Ok(first == second);
    }
    if let (Some(units_a), Some(units_b)) = (fa, fb) {
        return Ok(units_a.equal(units_b));
    }
    Ok(compare_chunks(h, a, b)? == Ordering::Equal)
}

/// Returns whether `string` has the same characters as `text`.
#[inline]
pub fn equal_str<H: Host>(h: &H, string: H::Str, text: &str) -> Result<bool, H::Error> {
    match flat(h, string) {
        Some(units) => units_equal_str(h, units, text),
        None => rope_equal_str(h, string, text),
    }
}

#[inline(never)]
fn rope_equal_str<H: Host>(h: &H, string: H::Str, text: &str) -> Result<bool, H::Error> {
    let (info, flat) = summary(h, string);
    if let Some(units) = flat {
        return units_equal_str(h, units, text);
    }
    if info.bytes != text.len() {
        return Ok(false);
    }
    h.charge(info.bytes as u64)?;
    let mut rest = text.as_bytes();
    for chunk in chunks(h, string) {
        let (head, tail) = rest.split_at(chunk.len());
        if !chunk.equal_bytes(head) {
            return Ok(false);
        }
        rest = tail;
    }
    Ok(true)
}

#[inline]
fn units_equal_str<H: Host>(h: &H, units: Units<'_>, text: &str) -> Result<bool, H::Error> {
    if units.len() != text.len() {
        return Ok(false);
    }
    h.charge(text.len() as u64)?;
    // Each representation gets its own `if` instead of one `match`.
    // Names mix representations, and the indirect jump of a jump table is predicted worse than these branches.
    if let Units::Inline(inline) = units {
        return Ok(inline.word() == word::pack(text.as_bytes()));
    }
    if let Units::Slice(bytes) = units {
        return Ok(word::equal(bytes, text.as_bytes()));
    }
    if let Units::Packed(packed) = units {
        return Ok(packed.equal_bytes(text.as_bytes()));
    }
    Ok(false)
}

/// Returns the bytes of `string` if it is flat, or `None` if it is a rope.
#[inline]
fn flat<H: Host>(h: &H, string: H::Str) -> Option<Units<'_>> {
    match h.view(string) {
        StrView::Flat { units, .. } => Some(units),
        StrView::Rope { .. } => None,
    }
}

/// Returns the bytes of `string` and its number of characters if it is flat, or `None` if it is a rope.
#[inline]
fn flat_counted<H: Host>(h: &H, string: H::Str) -> Option<(Units<'_>, usize)> {
    match h.view(string) {
        StrView::Flat { units, chars } => Some((units, chars)),
        StrView::Rope { .. } => None,
    }
}

/// Returns the [`Info`] of `string` and, if `string` is flat or is a rope with a flat copy, its bytes.
/// It views `string` only once.
fn summary<H: Host>(h: &H, string: H::Str) -> (Info, Option<Units<'_>>) {
    match h.view(string) {
        StrView::Flat { units, chars } => (Info { bytes: units.len(), chars, depth: 0 }, Some(units)),
        StrView::Rope { info, flat: Some(flat), .. } => match h.view(flat) {
            StrView::Flat { units, .. } => (info, Some(units)),
            StrView::Rope { .. } => (info, None),
        },
        StrView::Rope { info, .. } => (info, None),
    }
}

/// Returns the number of bytes that `string` takes as UTF-8. It is kept in the string, so no character is read.
pub fn utf8_len<H: Host>(h: &H, string: H::Str) -> Result<usize, H::Error> {
    Ok(byte_len(h, string))
}

/// Copies `string` into `out` as UTF-8. Returns the number of bytes written, or `None` if `out` is too short for the whole string.
///
/// This is the cheap way to get a short string as a `&str`: it allocates nothing and uses no formatter.
pub fn copy_utf8<H: Host>(h: &H, string: H::Str, out: &mut [u8]) -> Option<usize> {
    let mut written = 0;
    match flat(h, string) {
        Some(units) => {
            units.copy_to(out.get_mut(..units.len())?);
            written = units.len();
        }
        None => {
            for chunk in chunks(h, string) {
                chunk.copy_to(out.get_mut(written..written + chunk.len())?);
                written += chunk.len();
            }
        }
    }
    Some(written)
}

/// Copies the bytes of `string` from byte offset `start` up to, but not including, byte offset `end` into `out`, which must have room for them.
/// The bytes are valid UTF-8 if both offsets lie between two characters.
pub fn copy_bytes<H: Host>(h: &H, string: H::Str, start: usize, end: usize, out: &mut [u8]) {
    match flat(h, string) {
        Some(units) => units.slice(start..end).copy_to(out),
        None => {
            let mut written = 0;
            for chunk in Chunks::new(h, string, start, end) {
                chunk.copy_to(&mut out[written..]);
                written += chunk.len();
            }
        }
    }
}

/// Appends `string` to `out` as UTF-8. The bytes are copied as they are stored: nothing is encoded and nothing is checked.
/// A host that builds a message in a buffer of its own uses this to write a string straight into it.
pub fn append_utf8<H: Host>(h: &H, string: H::Str, out: &mut Vec<u8>) {
    let (start, bytes) = (out.len(), byte_len(h, string));
    out.resize(start + bytes, 0);
    copy_bytes(h, string, 0, bytes, &mut out[start..]);
}

/// Returns `string` as a Rust `String`. The bytes are copied once and checked once.
pub fn to_string<H: Host>(h: &H, string: H::Str) -> String {
    let mut bytes = Vec::new();
    append_utf8(h, string, &mut bytes);
    // A string is UTF-8, so the check passes. A host whose bytes are no text gets them with U+FFFD in their place.
    String::from_utf8(bytes).unwrap_or_else(|error| String::from_utf8_lossy(error.as_bytes()).into_owned())
}

/// Returns a string with the text that `bytes` hold as UTF-8. Fails with [`StrError::NotUtf8`] if they hold no text. The bytes are checked once and copied once.
pub fn from_utf8<H: Host>(h: &H, bytes: &[u8]) -> Res<H> {
    from_str(h, std::str::from_utf8(bytes).map_err(|_| StrError::NotUtf8)?)
}

/// Returns a value that formats `string`, for use with `write!` or `to_string`.
pub fn display<H: Host>(h: &H, string: H::Str) -> Display<'_, H> {
    Display { h, s: string }
}

pub struct Display<'h, H: Host> {
    h: &'h H,
    s: H::Str,
}

impl<H: Host> fmt::Display for Display<'_, H> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut out = Utf8 { f: formatter, buf: [0; 256], n: 0 };
        match flat(self.h, self.s) {
            Some(units) => out.units(units)?,
            None => {
                for chunk in chunks(self.h, self.s) {
                    out.units(chunk)?;
                }
            }
        }
        out.flush()
    }
}

/// A buffer of UTF-8 bytes in front of a formatter. The bytes of whole characters collect in `buf` and are written a block at a time.
struct Utf8<'a, 'f> {
    f: &'a mut fmt::Formatter<'f>,
    buf: [u8; 256],
    n: usize,
}

/// Writes `bytes` to `formatter` as text. Bytes that are not valid UTF-8 are written as U+FFFD.
fn write_text(formatter: &mut fmt::Formatter<'_>, bytes: &[u8]) -> fmt::Result {
    match std::str::from_utf8(bytes) {
        Ok(text) => formatter.write_str(text),
        Err(_) => formatter.write_str(&String::from_utf8_lossy(bytes)),
    }
}

impl Utf8<'_, '_> {
    fn flush(&mut self) -> fmt::Result {
        let n = std::mem::take(&mut self.n);
        write_text(self.f, &self.buf[..n])
    }

    /// Writes the bytes of `units`, which hold whole characters.
    fn units(&mut self, units: Units<'_>) -> fmt::Result {
        if let Units::Slice(bytes) = units {
            self.flush()?;
            return write_text(self.f, bytes);
        }
        let (len, mut at) = (units.len(), 0);
        while at < len {
            let room = self.buf.len() - self.n;
            // A block ends between two characters. If the buffer ends inside a character, the block stops before that character.
            let mut end = (at + room).min(len);
            while end < len && end > at && units.byte(end) & 0xC0 == 0x80 {
                end -= 1;
            }
            if end == at {
                if self.n > 0 {
                    self.flush()?;
                    continue;
                }
                // The bytes are no characters. They are written as they are, and read as U+FFFD.
                end = (at + room).min(len);
            }
            units.slice(at..end).copy_to(&mut self.buf[self.n..]);
            self.n += end - at;
            at = end;
        }
        Ok(())
    }
}
