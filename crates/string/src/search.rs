//! Finding strings in strings, and the prefix tests, splitting and trimming built on it.
//! Search is Crochemore and Perrin's two-way algorithm, as `str::find` uses: linear time
//! whatever the text, and no memory beyond a few counters. Searches and scans are charged for
//! the characters they pass over once they're done.

use std::cell::Cell;
use std::cmp::Ordering;
use std::ops::Range;

use crate::word::{HIGH, ONES, low_bytes};
use crate::{Chunks, Host, Res, StrError, Units, Width, chunks, compare_runs, flat, flatten, info, len, substring};

#[cfg(test)]
#[path = "tests/search.rs"]
mod tests;

/// Where `pattern` first occurs in `string` at or after character `from`.
#[inline]
pub fn find<H: Host>(h: &H, string: H::Str, pattern: H::Str, from: usize) -> Result<Option<usize>, H::Error> {
    match (flat(h, string), flat(h, pattern)) {
        (Some(text), Some(pattern)) => find_units::<H, false>(h, text, pattern, from),
        _ => rope_find::<H, false>(h, string, pattern, from),
    }
}

/// Where `pattern` last occurs in `string` before character `to`, all of it.
#[inline]
pub fn rfind<H: Host>(h: &H, string: H::Str, pattern: H::Str, to: usize) -> Result<Option<usize>, H::Error> {
    match (flat(h, string), flat(h, pattern)) {
        (Some(text), Some(pattern)) => find_units::<H, true>(h, text, pattern, to),
        _ => rope_find::<H, true>(h, string, pattern, to),
    }
}

/// Where to search from `at`: back to the start if `BACK`, else on to the end.
fn room<const BACK: bool>(at: usize, n: usize) -> Range<usize> {
    if BACK { 0..at } else { at..n }
}

#[inline(never)]
fn rope_find<H: Host, const BACK: bool>(h: &H, string: H::Str, pattern: H::Str, at: usize) -> Result<Option<usize>, H::Error> {
    let (is, ip) = (info(h, string), info(h, pattern));
    if at > is.len {
        return Err(StrError::OutOfRange.into());
    }
    if ip.len > room::<BACK>(at, is.len).len() || ip.width > is.width {
        return Ok(None);
    }
    let (text, pattern) = (flatten(h, string)?, flatten(h, pattern)?);
    find_units::<H, BACK>(h, flat(h, text).expect("flattened"), flat(h, pattern).expect("flattened"), at)
}

fn find_units<H: Host, const BACK: bool>(h: &H, text: Units<'_>, pattern: Units<'_>, at: usize) -> Result<Option<usize>, H::Error> {
    if at > text.len() {
        return Err(StrError::OutOfRange.into());
    }
    let (room, pattern_len) = (room::<BACK>(at, text.len()), pattern.len());
    // Flat strings are at their narrowest, so a wider pattern has a character the text lacks.
    if pattern_len > room.len() || pattern.width() > text.width() {
        return Ok(None);
    }
    let found = search::<BACK>(text.slice(room.clone()), pattern);
    let passed = match found {
        Some(i) if BACK => room.len() - i,
        Some(i) => i + pattern_len,
        None => room.len(),
    };
    h.charge(passed as u64)?;
    Ok(found.map(|i| i + room.start))
}

/// Where `pattern` first occurs in `text`, or last if `BACK`. Backwards, both are read from
/// their ends, so the first match found is the last.
#[inline]
fn search<const BACK: bool>(text: Units<'_>, pattern: Units<'_>) -> Option<usize> {
    let cell = Cell::new(0);
    let text = text.anchored(&cell);
    let (n, pattern_len) = (text.len(), pattern.len());
    let at = move |i: usize| if BACK { n - 1 - i } else { i };
    let found = match pattern_len {
        0 => return Some(if BACK { n } else { 0 }),
        1 => return find_code::<BACK>(text, pattern.code(0)),
        2..=COPIED_PATTERN => {
            let mut buf = [0; COPIED_PATTERN];
            buf.iter_mut().zip(0..pattern_len).for_each(|(slot, i)| *slot = pattern.code(if BACK { pattern_len - 1 - i } else { i }));
            let copied = &buf[..pattern_len];
            match text {
                Units::Packed(packed) if packed.width() == Width::One => two_way(|i| packed.byte(at(i)), n, |i| copied[i], pattern_len),
                _ => two_way(|i| text.code(at(i)), n, |i| copied[i], pattern_len),
            }
        }
        _ => two_way(|i| text.code(at(i)), n, |i| pattern.code(if BACK { pattern_len - 1 - i } else { i }), pattern_len),
    };
    found.map(|i| if BACK { n - pattern_len - i } else { i })
}

/// Where the code `code` first occurs in `text`, or last if `BACK`.
fn find_code<const BACK: bool>(text: Units<'_>, code: u32) -> Option<usize> {
    match text {
        Units::One(bytes) if BACK => bytes.iter().rposition(|&byte| u32::from(byte) == code),
        Units::One(bytes) => bytes.iter().position(|&byte| u32::from(byte) == code),
        Units::Packed(packed) if packed.width() == Width::One => {
            let (n, pattern) = (packed.len(), ONES * u64::from(code));
            let zeros = |index: usize| {
                let bytes = (n - 8 * index).min(8);
                let x = packed.word_at(index, bytes) ^ pattern;
                // Zero bytes of `x` are matches. Subtracting one from each byte borrows into the
                // high bit of the lowest zero byte first, so that one is exact; backwards, every
                // one has to be, so adding 0x7F to the low bits marks each byte that isn't zero.
                let mut zero = if BACK {
                    !(((x & !HIGH) + !HIGH) | x) & HIGH
                } else {
                    x.wrapping_sub(ONES) & !x & HIGH
                };
                if bytes < 8 {
                    zero &= low_bytes(bytes);
                }
                zero
            };
            let (words, hit) = (0..n.div_ceil(8), |index| Some((index, zeros(index))).filter(|&(_, z)| z != 0));
            if BACK {
                words.rev().find_map(hit).map(|(index, z)| 8 * index + (63 - z.leading_zeros() as usize) / 8)
            } else {
                words.clone().find_map(hit).map(|(index, z)| 8 * index + z.trailing_zeros() as usize / 8)
            }
        }
        _ if BACK => (0..text.len()).rev().find(|&i| text.code(i) == code),
        _ => (0..text.len()).find(|&i| text.code(i) == code),
    }
}

/// Patterns this long or shorter are copied out to search for.
const COPIED_PATTERN: usize = 64;

/// Where the pattern of `pattern_len` characters, two or more, that `pattern` gives first occurs in the `n`
/// characters `text` gives. The pattern is cut where its two halves can't both line up with a
/// shifted copy of it; the right half is matched first, and a mismatch there shifts by how far
/// it got, one in the left half by the period. A window whose last character isn't in the
/// pattern is skipped whole.
#[inline]
fn two_way(text: impl Fn(usize) -> u32, n: usize, pattern: impl Fn(usize) -> u32 + Copy, pattern_len: usize) -> Option<usize> {
    let (crit, period) = critical_factorization(pattern, pattern_len);
    let seen = (0..pattern_len).fold(0u64, |seen, i| seen | 1 << (pattern(i) & 63));
    let absent = |code: u32| seen >> (code & 63) & 1 == 0;
    let mut pos = 0;
    if (0..crit).all(|i| pattern(i) == pattern(i + period)) {
        // Periodic: after a shift by the period, the first `memory` characters still match.
        let mut memory = 0;
        while pos + pattern_len <= n {
            if absent(text(pos + pattern_len - 1)) {
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
            if absent(text(pos + pattern_len - 1)) {
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

/// Where to cut the pattern, and the period of what's right of the cut: the later of its
/// maximal suffixes by either order.
fn critical_factorization(pattern: impl Fn(usize) -> u32 + Copy, pattern_len: usize) -> (usize, usize) {
    let (a, b) = (maximal_suffix(pattern, pattern_len, Ordering::Less), maximal_suffix(pattern, pattern_len, Ordering::Greater));
    if a.0 > b.0 { a } else { b }
}

/// Where the pattern's greatest suffix starts, by code points in the order `order` gives
/// (`Greater` for ascending), and that suffix's period.
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

/// Whether `units` holds the characters of `part` from `at`, where there's room for them.
#[inline]
fn units_at<H: Host>(h: &H, units: Units<'_>, at: usize, part: Units<'_>) -> Result<bool, H::Error> {
    h.charge(part.len() as u64)?;
    Ok(units.slice(at..at + part.len()).compare(part).is_eq())
}

/// Whether `string` holds the characters of `part` from where `at` puts them, given the lengths of
/// both, if there's room.
#[inline(never)]
fn rope_at<H: Host>(h: &H, string: H::Str, at: fn(usize, usize) -> usize, part: H::Str) -> Result<bool, H::Error> {
    let (n, part_len) = (len(h, string), len(h, part));
    if part_len > n {
        return Ok(false);
    }
    h.charge(part_len as u64)?;
    let at = at(n, part_len);
    Ok(compare_runs(Chunks::new(h, string, at, at + part_len), chunks(h, part)).is_eq())
}

/// The pieces of `string` between occurrences of `separator`, in order, one more than there are
/// separators, so some may be empty. An empty separator splits between characters, so then
/// each character is a piece, unless `string` is empty.
pub fn split<H: Host>(h: &H, string: H::Str, separator: H::Str) -> Split<'_, H> {
    splitn(h, string, separator, usize::MAX)
}

/// Like [`split`], in at most `limit` pieces: the last holds the rest of `string`, separators and all.
pub fn splitn<H: Host>(h: &H, string: H::Str, separator: H::Str, limit: usize) -> Split<'_, H> {
    Split { h, s: string, separator, at: Some(0), limit }
}

pub struct Split<'h, H: Host> {
    h: &'h H,
    s: H::Str,
    separator: H::Str,
    /// Where the next piece starts, or `None` once the last is out.
    at: Option<usize>,
    /// How many more pieces there may be.
    limit: usize,
}

impl<H: Host> Iterator for Split<'_, H> {
    type Item = Res<H>;

    fn next(&mut self) -> Option<Res<H>> {
        let (h, at) = (self.h, self.at?);
        self.limit = self.limit.checked_sub(1)?;
        let (n, separator_len) = (len(h, self.s), len(h, self.separator));
        let end = match separator_len {
            _ if self.limit == 0 => None,
            0 => (at + 1 < n).then_some(at + 1),
            _ => match find(h, self.s, self.separator, at) {
                Ok(end) => end,
                Err(error) => {
                    self.at = None;
                    return Some(Err(error));
                }
            },
        };
        self.at = end.map(|end| end + separator_len);
        Some(substring(h, self.s, at, end.unwrap_or(n)))
    }
}

/// The runs of `string` between whitespace, none empty.
pub fn split_whitespace<H: Host>(h: &H, string: H::Str) -> SplitWhitespace<'_, H> {
    SplitWhitespace { h, s: string, text: None, at: Some(0) }
}

pub struct SplitWhitespace<'h, H: Host> {
    h: &'h H,
    s: H::Str,
    /// `s` flattened, and its characters, once the first run is asked for.
    text: Option<(H::Str, Units<'h>)>,
    /// Where to look for the next run, or `None` once there are no more.
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
        let space = |i| units.get(i).is_some_and(char::is_whitespace);
        let Some(start) = (from..n).find(|&i| !space(i)) else {
            self.at = None;
            return None;
        };
        let end = (start..n).find(|&i| space(i)).unwrap_or(n);
        self.at = Some(end);
        Some(h.charge((end - from) as u64).and_then(|()| substring(h, text, start, end)))
    }
}

/// `string` without whitespace at either end.
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
    let space = |i| units.get(i).is_some_and(char::is_whitespace);
    let from = if start { (0..n).find(|&i| !space(i)).unwrap_or(n) } else { 0 };
    let to = if end { (from..n).rev().find(|&i| !space(i)).map_or(from, |i| i + 1) } else { n };
    h.charge((from + n - to) as u64)?;
    if from == 0 && to == n {
        return Ok(string);
    }
    substring(h, text, from, to)
}
