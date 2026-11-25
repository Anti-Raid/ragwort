//! Substring search, and the prefix tests, splitting and trimming built on it.
//! Search uses the two-way algorithm of Crochemore and Perrin, as `str::find` does. It takes linear time
//! on any text and needs no memory beyond a few counters. A search or a scan charges the host for
//! the bytes it passed over, after it finishes.
//!
//! The search runs over bytes. UTF-8 is self-synchronizing: the bytes of a text occur in another text only where
//! a character starts. So a match of whole characters is found by matching bytes.

use std::cell::Cell;
use std::cmp::Ordering;
use std::ops::Range;

use crate::rope::sub;
use crate::word::{HIGH, ONES, low_bytes};
use crate::{Chunks, Host, Packed, Res, StrError, StrView, Units, byte_len, chunks, compare_runs, flat, flat_counted, flatten, info, offset};

#[cfg(test)]
#[path = "tests/search.rs"]
mod tests;

/// Returns the index of the first occurrence of `pattern` in `string` that starts at or after character `from`, or `None` if there is none.
#[inline]
pub fn find<H: Host>(h: &H, string: H::Str, pattern: H::Str, from: usize) -> Result<Option<usize>, H::Error> {
    match (flat_counted(h, string), flat(h, pattern)) {
        (Some((text, chars)), Some(pattern)) => find_units::<H, false>(h, text, chars, pattern, from),
        _ => rope_find::<H, false>(h, string, pattern, from),
    }
}

/// Returns the index of the last occurrence of `pattern` in `string` that ends at or before character `to`, or `None` if there is none.
#[inline]
pub fn rfind<H: Host>(h: &H, string: H::Str, pattern: H::Str, to: usize) -> Result<Option<usize>, H::Error> {
    match (flat_counted(h, string), flat(h, pattern)) {
        (Some((text, chars)), Some(pattern)) => find_units::<H, true>(h, text, chars, pattern, to),
        _ => rope_find::<H, true>(h, string, pattern, to),
    }
}

/// Returns the range of a text of `n` bytes to search. A forward search covers `at..n`, and a backward search (`BACK`) covers `0..at`.
fn room<const BACK: bool>(at: usize, n: usize) -> Range<usize> {
    if BACK { 0..at } else { at..n }
}

#[inline(never)]
fn rope_find<H: Host, const BACK: bool>(h: &H, string: H::Str, pattern: H::Str, at: usize) -> Result<Option<usize>, H::Error> {
    let (is, ip) = (info(h, string), info(h, pattern));
    if at > is.chars {
        return Err(StrError::OutOfRange.into());
    }
    if ip.bytes > is.bytes {
        return Ok(None);
    }
    let (text, pattern) = (flatten(h, string)?, flatten(h, pattern)?);
    let (units, chars) = flat_counted(h, text).expect("flattened");
    find_units::<H, BACK>(h, units, chars, flat(h, pattern).expect("flattened"), at)
}

/// Searches the flat string `text`, which holds `chars` characters. `at` and the result are character indices.
fn find_units<H: Host, const BACK: bool>(h: &H, text: Units<'_>, chars: usize, pattern: Units<'_>, at: usize) -> Result<Option<usize>, H::Error> {
    if at > chars {
        return Err(StrError::OutOfRange.into());
    }
    let at_byte = offset(text, chars, at);
    let (room, pattern_len) = (room::<BACK>(at_byte, text.len()), pattern.len());
    if pattern_len > room.len() {
        return Ok(None);
    }
    let found = search::<BACK>(text.slice(room.clone()), pattern);
    let passed = match found {
        Some(i) if BACK => room.len() - i,
        Some(i) => i + pattern_len,
        None => room.len(),
    };
    h.charge(passed as u64)?;
    let Some(found) = found else { return Ok(None) };
    let byte = found + room.start;
    // In an ASCII text a byte offset is a character index. Otherwise the characters before the match are counted.
    Ok(Some(if chars == text.len() {
        byte
    } else if BACK {
        text.slice(0..byte).count_chars()
    } else {
        at + text.slice(at_byte..byte).count_chars()
    }))
}

/// Returns the byte offset of the last occurrence of `pattern` in `string` that ends at or before byte offset `to`. Fails if `to` does not lie between two characters.
pub fn rfind_bytes<H: Host>(h: &H, string: H::Str, pattern: H::Str, to: usize) -> Result<Option<usize>, H::Error> {
    if !crate::is_boundary(h, string, to) {
        return Err(StrError::OutOfRange.into());
    }
    let (text, pattern) = match (flat(h, string), flat(h, pattern)) {
        (Some(text), Some(pattern)) => (text, pattern),
        _ => {
            let (text, pattern) = (flatten(h, string)?, flatten(h, pattern)?);
            (flat(h, text).expect("flattened"), flat(h, pattern).expect("flattened"))
        }
    };
    if pattern.len() > to {
        return Ok(None);
    }
    let found = search::<true>(text.slice(0..to), pattern);
    h.charge(found.map_or(to, |i| to - i) as u64)?;
    Ok(found)
}

/// Returns the byte offset of the first occurrence of `pattern` in `string` that starts at or after byte offset `from`. Fails if `from` does not lie between two characters.
pub fn find_bytes<H: Host>(h: &H, string: H::Str, pattern: H::Str, from: usize) -> Result<Option<usize>, H::Error> {
    if !crate::is_boundary(h, string, from) {
        return Err(StrError::OutOfRange.into());
    }
    let (text, pattern) = match (flat(h, string), flat(h, pattern)) {
        (Some(text), Some(pattern)) => (text, pattern),
        _ => {
            let (text, pattern) = (flatten(h, string)?, flatten(h, pattern)?);
            (flat(h, text).expect("flattened"), flat(h, pattern).expect("flattened"))
        }
    };
    let room = text.len() - from;
    if pattern.len() > room {
        return Ok(None);
    }
    let found = search::<false>(text.slice(from..text.len()), pattern);
    h.charge(found.map_or(room, |i| i + pattern.len()) as u64)?;
    Ok(found.map(|i| i + from))
}

/// Returns the byte offset of the first occurrence of `pattern` in `text`, or of the last occurrence if `BACK`. A backward search
/// reads both `text` and `pattern` from their ends, so the first match it finds is the last occurrence.
#[inline]
fn search<const BACK: bool>(text: Units<'_>, pattern: Units<'_>) -> Option<usize> {
    #[inline(always)]
    fn at<const BACK: bool>(n: usize, i: usize) -> usize {
        if BACK { n - 1 - i } else { i }
    }
    let cell = Cell::new(0);
    let text = text.anchored(&cell);
    let (n, pattern_len) = (text.len(), pattern.len());
    let found = match pattern_len {
        0 => return Some(if BACK { n } else { 0 }),
        1 => return find_byte::<BACK>(text, pattern.byte(0)),
        2..=COPIED_PATTERN => {
            let mut buf = [0; COPIED_PATTERN];
            buf.iter_mut().zip(0..pattern_len).for_each(|(slot, i)| *slot = u32::from(pattern.byte(if BACK { pattern_len - 1 - i } else { i })));
            let copied = &buf[..pattern_len];
            match text {
                Units::Packed(packed) => two_way(|i| u32::from(packed.byte(at::<BACK>(n, i))), n, |i| copied[i], pattern_len),
                _ => two_way(|i| u32::from(text.byte(at::<BACK>(n, i))), n, |i| copied[i], pattern_len),
            }
        }
        _ => two_way(|i| u32::from(text.byte(at::<BACK>(n, i))), n, |i| u32::from(pattern.byte(if BACK { pattern_len - 1 - i } else { i })), pattern_len),
    };
    found.map(|i| if BACK { n - pattern_len - i } else { i })
}

/// Returns the offset of the first byte of `text` equal to `byte`, or of the last such byte if `BACK`.
fn find_byte<const BACK: bool>(text: Units<'_>, byte: u8) -> Option<usize> {
    match text {
        Units::Slice(bytes) if BACK => bytes.iter().rposition(|&other| other == byte),
        Units::Slice(bytes) => bytes.iter().position(|&other| other == byte),
        Units::Packed(packed) => {
            #[inline(always)]
            fn zeros<const BACK: bool>(packed: Packed<'_>, n: usize, pattern: u64, index: usize) -> u64 {
                let bytes = (n - 8 * index).min(8);
                let x = packed.word_at(index, bytes) ^ pattern;
                // A zero byte of `x` is a match. The forward test subtracts one from each byte. The borrow reaches the
                // high bit of the lowest zero byte first, so the lowest marked byte is exact. A backward search needs every
                // mark to be exact. So it adds 0x7F to the low seven bits of each byte, which marks each byte that is not zero.
                let mut zero = if BACK {
                    !(((x & !HIGH) + !HIGH) | x) & HIGH
                } else {
                    x.wrapping_sub(ONES) & !x & HIGH
                };
                if bytes < 8 {
                    zero &= low_bytes(bytes);
                }
                zero
            }
            #[inline(always)]
            fn hit<const BACK: bool>(packed: Packed<'_>, n: usize, pattern: u64, index: usize) -> Option<(usize, u64)> {
                Some((index, zeros::<BACK>(packed, n, pattern, index))).filter(|&(_, z)| z != 0)
            }
            let (n, pattern) = (packed.len(), ONES * u64::from(byte));
            let words = 0..n.div_ceil(8);
            if BACK {
                words.rev().find_map(|index| hit::<BACK>(packed, n, pattern, index)).map(|(index, z)| 8 * index + (63 - z.leading_zeros() as usize) / 8)
            } else {
                words.clone().find_map(|index| hit::<BACK>(packed, n, pattern, index)).map(|(index, z)| 8 * index + z.trailing_zeros() as usize / 8)
            }
        }
        _ if BACK => (0..text.len()).rev().find(|&i| text.byte(i) == byte),
        _ => (0..text.len()).find(|&i| text.byte(i) == byte),
    }
}

/// The maximum length of a pattern that is copied into a local buffer for the search.
const COPIED_PATTERN: usize = 64;

/// Returns the index of the first occurrence of a pattern in a text, by the two-way algorithm. `text(i)` and `pattern(i)` return the byte at index `i`.
/// The text has `n` bytes, and the pattern has `pattern_len`, which is at least two. The pattern is split at a critical factorization,
/// and the right part is matched first. A mismatch in the right part shifts the window by one more than the number of bytes matched there.
/// A mismatch in the left part shifts the window by the period if the pattern is periodic, and by `max(crit, pattern_len - crit) + 1` otherwise.
/// A window whose last byte does not occur in the pattern is skipped entirely. That test uses a 64-bit set of the pattern's bytes modulo 64.
#[inline]
fn two_way(text: impl Fn(usize) -> u32, n: usize, pattern: impl Fn(usize) -> u32 + Copy, pattern_len: usize) -> Option<usize> {
    let (crit, period) = critical_factorization(pattern, pattern_len);
    #[inline(always)]
    fn absent(seen: u64, code: u32) -> bool {
        seen >> (code & 63) & 1 == 0
    }
    let seen = (0..pattern_len).fold(0u64, |seen, i| seen | 1 << (pattern(i) & 63));
    let mut pos = 0;
    if (0..crit).all(|i| pattern(i) == pattern(i + period)) {
        // The pattern is periodic. After a shift by the period, the first `memory` characters of the pattern are known to match.
        let mut memory = 0;
        while pos + pattern_len <= n {
            if absent(seen, text(pos + pattern_len - 1)) {
                (pos, memory) = (pos + pattern_len, 0);
            } else if let Some(i) = (crit.max(memory)..pattern_len).find(|&i| pattern(i) != text(pos + i)) {
                (pos, memory) = (pos + i - crit + 1, 0);
            } else if (memory..crit).rev().any(|i| pattern(i) != text(pos + i)) {
                (pos, memory) = (pos + period, pattern_len - period);
            } else {
                return Some(pos);
            }
        }
    } else {
        let shift = crit.max(pattern_len - crit) + 1;
        while pos + pattern_len <= n {
            if absent(seen, text(pos + pattern_len - 1)) {
                pos += pattern_len;
            } else if let Some(i) = (crit..pattern_len).find(|&i| pattern(i) != text(pos + i)) {
                pos += i - crit + 1;
            } else if (0..crit).rev().any(|i| pattern(i) != text(pos + i)) {
                pos += shift;
            } else {
                return Some(pos);
            }
        }
    }
    None
}

/// Returns the index at which to split the pattern and the period of the part to the right of the split. The split is at the start
/// of the later of the two maximal suffixes, one for each ordering of bytes. That split is a critical factorization.
fn critical_factorization(pattern: impl Fn(usize) -> u32 + Copy, pattern_len: usize) -> (usize, usize) {
    let (a, b) = (maximal_suffix(pattern, pattern_len, Ordering::Less), maximal_suffix(pattern, pattern_len, Ordering::Greater));
    if a.0 > b.0 { a } else { b }
}

/// Returns the start index of the maximal suffix of the pattern and the period of that suffix. `order` selects the ordering
/// of bytes: `Greater` for the usual ascending order, `Less` for the reverse.
fn maximal_suffix(pattern: impl Fn(usize) -> u32, pattern_len: usize, order: Ordering) -> (usize, usize) {
    let (mut left, mut right, mut offset, mut period) = (0, 1, 0, 1);
    while right + offset < pattern_len {
        match pattern(right + offset).cmp(&pattern(left + offset)) {
            Ordering::Equal if offset + 1 == period => (right, offset) = (right + period, 0),
            Ordering::Equal => offset += 1,
            ordering if ordering == order => (left, right, offset, period) = (right, right + 1, 0, 1),
            _ => (right, offset, period) = (right + offset + 1, 0, right + offset + 1 - left),
        }
    }
    (left, period)
}

#[inline]
pub fn starts_with<H: Host>(h: &H, string: H::Str, prefix: H::Str) -> Result<bool, H::Error> {
    match (flat(h, string), flat(h, prefix)) {
        (Some(units), Some(prefix_units)) if prefix_units.len() <= units.len() => units_at(h, units, 0, prefix_units),
        (Some(_), Some(_)) => Ok(false),
        _ => rope_at(h, string, |_, _| 0, prefix),
    }
}

#[inline]
pub fn ends_with<H: Host>(h: &H, string: H::Str, suffix: H::Str) -> Result<bool, H::Error> {
    match (flat(h, string), flat(h, suffix)) {
        (Some(units), Some(suffix_units)) if suffix_units.len() <= units.len() => units_at(h, units, units.len() - suffix_units.len(), suffix_units),
        (Some(_), Some(_)) => Ok(false),
        _ => rope_at(h, string, |n, suffix_len| n - suffix_len, suffix),
    }
}

/// Returns whether `units` contains the bytes of `part` starting at byte `at`. The caller ensures that `part` fits there.
#[inline]
fn units_at<H: Host>(h: &H, units: Units<'_>, at: usize, part: Units<'_>) -> Result<bool, H::Error> {
    h.charge(part.len() as u64)?;
    Ok(units.slice(at..at + part.len()).compare(part).is_eq())
}

/// Returns whether `string` contains the bytes of `part` at the byte offset that `at` returns. `at` is called with the byte lengths of
/// `string` and `part`. Returns `false` if `part` is longer than `string`.
#[inline(never)]
fn rope_at<H: Host>(h: &H, string: H::Str, at: fn(usize, usize) -> usize, part: H::Str) -> Result<bool, H::Error> {
    let (n, part_len) = (byte_len(h, string), byte_len(h, part));
    if part_len > n {
        return Ok(false);
    }
    h.charge(part_len as u64)?;
    let at = at(n, part_len);
    Ok(compare_runs(Chunks::new(h, string, at, at + part_len), chunks(h, part)).is_eq())
}

/// Returns the number of bytes of the character that starts at byte `at` of `string`.
fn char_size_at<H: Host>(h: &H, mut string: H::Str, mut at: usize) -> usize {
    loop {
        match h.view(string) {
            StrView::Flat { units, .. } => return units.char_at(at).1,
            StrView::Rope { flat: Some(flat), .. } => string = flat,
            StrView::Rope { left, right, .. } => {
                let left_bytes = byte_len(h, left);
                (string, at) = if at < left_bytes { (left, at) } else { (right, at - left_bytes) };
            }
        }
    }
}

/// Returns an iterator over the pieces of `string` between occurrences of `separator`, in order. There is one more piece than there are
/// separators, so some pieces can be empty. An empty separator splits between characters, so
/// each character is a piece. An empty `string` gives one empty piece.
pub fn split<H: Host>(h: &H, string: H::Str, separator: H::Str) -> Split<'_, H> {
    splitn(h, string, separator, usize::MAX)
}

/// Like [`split`], but returns at most `limit` pieces. The last piece holds the rest of `string`, including any separators.
pub fn splitn<H: Host>(h: &H, string: H::Str, separator: H::Str, limit: usize) -> Split<'_, H> {
    Split { h, s: string, separator, at: Some(0), limit }
}

pub struct Split<'h, H: Host> {
    h: &'h H,
    s: H::Str,
    separator: H::Str,
    /// The byte offset where the next piece starts, or `None` once the last piece has been returned.
    at: Option<usize>,
    /// The maximum number of pieces still to return.
    limit: usize,
}

impl<H: Host> Iterator for Split<'_, H> {
    type Item = Res<H>;

    fn next(&mut self) -> Option<Res<H>> {
        let (h, at) = (self.h, self.at?);
        self.limit = self.limit.checked_sub(1)?;
        let (n, separator_len) = (byte_len(h, self.s), byte_len(h, self.separator));
        let end = match separator_len {
            _ if self.limit == 0 => None,
            0 if at < n => Some(at + char_size_at(h, self.s, at)).filter(|&next| next < n),
            0 => None,
            _ => match find_bytes(h, self.s, self.separator, at) {
                Ok(end) => end,
                Err(error) => {
                    self.at = None;
                    return Some(Err(error));
                }
            },
        };
        self.at = end.map(|end| end + separator_len);
        Some(sub(h, self.s, at, end.unwrap_or(n), None))
    }
}

/// Returns an iterator over the runs of non-whitespace characters in `string`. No run is empty.
pub fn split_whitespace<H: Host>(h: &H, string: H::Str) -> SplitWhitespace<'_, H> {
    SplitWhitespace { h, s: string, text: None, at: Some(0) }
}

pub struct SplitWhitespace<'h, H: Host> {
    h: &'h H,
    s: H::Str,
    /// The flattened `s` and its bytes. They are set when the first run is requested.
    text: Option<(H::Str, Units<'h>)>,
    /// The byte offset from which to look for the next run, or `None` once there are no more runs.
    at: Option<usize>,
}

impl<H: Host> Iterator for SplitWhitespace<'_, H> {
    type Item = Res<H>;

    fn next(&mut self) -> Option<Res<H>> {
        let (h, from) = (self.h, self.at?);
        let (text, units) = match self.text {
            Some(text) => text,
            None => match flatten(h, self.s) {
                Ok(text) => *self.text.insert((text, flat(h, text).expect("flattened"))),
                Err(error) => {
                    self.at = None;
                    return Some(Err(error));
                }
            },
        };
        let n = units.len();
        let start = spaces_end(units, from);
        if start == n {
            self.at = None;
            return None;
        }
        let mut end = start;
        while end < n {
            let (character, size) = units.char_at(end);
            if character.is_whitespace() {
                break;
            }
            end += size;
        }
        self.at = Some(end);
        Some(h.charge((end - from) as u64).and_then(|()| sub(h, text, start, end, None)))
    }
}

/// Returns the byte offset of the first character of `units` at or after byte `from` that is not whitespace, or the number of bytes if there is none.
fn spaces_end(units: Units<'_>, from: usize) -> usize {
    let mut at = from;
    while at < units.len() {
        let (character, size) = units.char_at(at);
        if !character.is_whitespace() {
            break;
        }
        at += size;
    }
    at
}

/// Returns `string` without the whitespace at either end.
pub fn trim<H: Host>(h: &H, string: H::Str) -> Res<H> {
    trimmed(h, string, true, true)
}

pub fn trim_start<H: Host>(h: &H, string: H::Str) -> Res<H> {
    trimmed(h, string, true, false)
}

pub fn trim_end<H: Host>(h: &H, string: H::Str) -> Res<H> {
    trimmed(h, string, false, true)
}

fn trimmed<H: Host>(h: &H, string: H::Str, start: bool, end: bool) -> Res<H> {
    let text = flatten(h, string)?;
    let units = flat(h, text).expect("flattened");
    let n = units.len();
    let from = if start { spaces_end(units, 0) } else { 0 };
    let mut to = n;
    while end && to > from {
        let before = units.before(to);
        if !units.char_at(before).0.is_whitespace() {
            break;
        }
        to = before;
    }
    h.charge((from + n - to) as u64)?;
    if from == 0 && to == n {
        return Ok(string);
    }
    sub(h, text, from, to, None)
}
