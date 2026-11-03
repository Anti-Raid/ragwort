//! Finding strings in strings, and the prefix tests, splitting and trimming built on it.
//! Search is Crochemore and Perrin's two-way algorithm, as `str::find` uses: linear time
//! whatever the text, and no memory beyond a few counters. Searches and scans are charged for
//! the characters they pass over once they're done.

use std::cmp::Ordering;
use std::ops::Range;

use crate::{Chunks, Host, Res, StrError, Units, Width, chunks, compare_runs, flat, flatten, info, len, substring};

#[cfg(test)]
#[path = "tests/search.rs"]
mod tests;

/// Where `pattern` first occurs in `s` at or after character `from`.
#[inline]
pub fn find<H: Host>(h: &H, s: H::Str, pattern: H::Str, from: usize) -> Result<Option<usize>, H::Error> {
    match (flat(h, s), flat(h, pattern)) {
        (Some(text), Some(pattern)) => find_units::<H, false>(h, text, pattern, from),
        _ => rope_find::<H, false>(h, s, pattern, from),
    }
}

/// Where `pattern` last occurs in `s` before character `to`, all of it.
#[inline]
pub fn rfind<H: Host>(h: &H, s: H::Str, pattern: H::Str, to: usize) -> Result<Option<usize>, H::Error> {
    match (flat(h, s), flat(h, pattern)) {
        (Some(text), Some(pattern)) => find_units::<H, true>(h, text, pattern, to),
        _ => rope_find::<H, true>(h, s, pattern, to),
    }
}

/// Where to search from `at`: back to the start if `BACK`, else on to the end.
fn room<const BACK: bool>(at: usize, n: usize) -> Range<usize> {
    if BACK { 0..at } else { at..n }
}

#[inline(never)]
fn rope_find<H: Host, const BACK: bool>(h: &H, s: H::Str, pattern: H::Str, at: usize) -> Result<Option<usize>, H::Error> {
    let (is, ip) = (info(h, s), info(h, pattern));
    if at > is.len {
        return Err(StrError::OutOfRange.into());
    }
    if ip.len > room::<BACK>(at, is.len).len() || ip.width > is.width {
        return Ok(None);
    }
    let (text, pattern) = (flatten(h, s)?, flatten(h, pattern)?);
    find_units::<H, BACK>(h, flat(h, text).expect("flattened"), flat(h, pattern).expect("flattened"), at)
}

fn find_units<H: Host, const BACK: bool>(h: &H, text: Units<'_>, pattern: Units<'_>, at: usize) -> Result<Option<usize>, H::Error> {
    if at > text.len() {
        return Err(StrError::OutOfRange.into());
    }
    let (room, m) = (room::<BACK>(at, text.len()), pattern.len());
    // Flat strings are at their narrowest, so a wider pattern has a character the text lacks.
    if m > room.len() || pattern.width() > text.width() {
        return Ok(None);
    }
    let found = search::<BACK>(text.slice(room.clone()), pattern);
    let passed = match found {
        Some(i) if BACK => room.len() - i,
        Some(i) => i + m,
        None => room.len(),
    };
    h.charge(passed as u64)?;
    Ok(found.map(|i| i + room.start))
}

/// Where `pattern` first occurs in `text`, or last if `BACK`. Backwards, both are read from
/// their ends, so the first match found is the last.
#[inline]
fn search<const BACK: bool>(text: Units<'_>, pattern: Units<'_>) -> Option<usize> {
    let (n, m) = (text.len(), pattern.len());
    let at = move |i: usize| if BACK { n - 1 - i } else { i };
    let found = match m {
        0 => return Some(if BACK { n } else { 0 }),
        1 => return find_code::<BACK>(text, pattern.code(0)),
        2..=SHORT => {
            let mut buf = [0; SHORT];
            buf.iter_mut().zip(0..m).for_each(|(b, i)| *b = pattern.code(if BACK { m - 1 - i } else { i }));
            let p = &buf[..m];
            match text {
                Units::Packed(t) if t.width() == Width::One => two_way(|i| t.byte(at(i)), n, |i| p[i], m),
                _ => two_way(|i| text.code(at(i)), n, |i| p[i], m),
            }
        }
        _ => two_way(|i| text.code(at(i)), n, |i| pattern.code(if BACK { m - 1 - i } else { i }), m),
    };
    found.map(|i| if BACK { n - m - i } else { i })
}

/// Where the code `c` first occurs in `text`, or last if `BACK`.
fn find_code<const BACK: bool>(text: Units<'_>, c: u32) -> Option<usize> {
    const ONES: u64 = 0x0101_0101_0101_0101;
    match text {
        Units::One(s) if BACK => s.iter().rposition(|&u| u32::from(u) == c),
        Units::One(s) => s.iter().position(|&u| u32::from(u) == c),
        Units::Packed(p) if p.width() == Width::One => {
            let (n, pattern) = (p.len(), ONES * u64::from(c));
            let zeros = |k: usize| {
                let bytes = (n - 8 * k).min(8);
                let x = p.word_at(k, bytes) ^ pattern;
                // Zero bytes of `x` are matches. Subtracting one from each byte borrows into the
                // high bit of the lowest zero byte first, so that one is exact; backwards, every
                // one has to be, so adding 0x7F to the low bits marks each byte that isn't zero.
                let mut zero = if BACK {
                    !(((x & !crate::hash::HIGH) + !crate::hash::HIGH) | x) & crate::hash::HIGH
                } else {
                    x.wrapping_sub(ONES) & !x & crate::hash::HIGH
                };
                if bytes < 8 {
                    zero &= (1 << (8 * bytes)) - 1;
                }
                zero
            };
            let (words, hit) = (0..n.div_ceil(8), |k| Some((k, zeros(k))).filter(|&(_, z)| z != 0));
            if BACK {
                words.rev().find_map(hit).map(|(k, z)| 8 * k + (63 - z.leading_zeros() as usize) / 8)
            } else {
                words.clone().find_map(hit).map(|(k, z)| 8 * k + z.trailing_zeros() as usize / 8)
            }
        }
        _ if BACK => (0..text.len()).rev().find(|&i| text.code(i) == c),
        _ => (0..text.len()).find(|&i| text.code(i) == c),
    }
}

/// Patterns this long or shorter are copied out to search for.
const SHORT: usize = 64;

/// Where the pattern of `m` characters, two or more, that `p` gives first occurs in the `n`
/// characters `t` gives. The pattern is cut where its two halves can't both line up with a
/// shifted copy of it; the right half is matched first, and a mismatch there shifts by how far
/// it got, one in the left half by the period. A window whose last character isn't in the
/// pattern is skipped whole.
#[inline]
fn two_way(t: impl Fn(usize) -> u32, n: usize, p: impl Fn(usize) -> u32 + Copy, m: usize) -> Option<usize> {
    let (crit, period) = critical_factorization(p, m);
    let seen = (0..m).fold(0u64, |seen, i| seen | 1 << (p(i) & 63));
    let absent = |c: u32| seen >> (c & 63) & 1 == 0;
    let mut pos = 0;
    if (0..crit).all(|i| p(i) == p(i + period)) {
        // Periodic: after a shift by the period, the first `memory` characters still match.
        let mut memory = 0;
        while pos + m <= n {
            if absent(t(pos + m - 1)) {
                (pos, memory) = (pos + m, 0);
            } else if let Some(i) = (crit.max(memory)..m).find(|&i| p(i) != t(pos + i)) {
                (pos, memory) = (pos + i - crit + 1, 0);
            } else if (memory..crit).rev().any(|i| p(i) != t(pos + i)) {
                (pos, memory) = (pos + period, m - period);
            } else {
                return Some(pos);
            }
        }
    } else {
        let shift = crit.max(m - crit) + 1;
        while pos + m <= n {
            if absent(t(pos + m - 1)) {
                pos += m;
            } else if let Some(i) = (crit..m).find(|&i| p(i) != t(pos + i)) {
                pos += i - crit + 1;
            } else if (0..crit).rev().any(|i| p(i) != t(pos + i)) {
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
fn critical_factorization(p: impl Fn(usize) -> u32 + Copy, m: usize) -> (usize, usize) {
    let (a, b) = (maximal_suffix(p, m, Ordering::Less), maximal_suffix(p, m, Ordering::Greater));
    if a.0 > b.0 { a } else { b }
}

/// Where the pattern's greatest suffix starts, by code points in the order `order` gives
/// (`Greater` for ascending), and that suffix's period.
fn maximal_suffix(p: impl Fn(usize) -> u32, m: usize, order: Ordering) -> (usize, usize) {
    let (mut left, mut right, mut offset, mut period) = (0, 1, 0, 1);
    while right + offset < m {
        match p(right + offset).cmp(&p(left + offset)) {
            Ordering::Equal if offset + 1 == period => (right, offset) = (right + period, 0),
            Ordering::Equal => offset += 1,
            o if o == order => (left, right, offset, period) = (right, right + 1, 0, 1),
            _ => (right, offset, period) = (right + offset + 1, 0, right + offset + 1 - left),
        }
    }
    (left, period)
}

#[inline]
pub fn starts_with<H: Host>(h: &H, s: H::Str, prefix: H::Str) -> Result<bool, H::Error> {
    match (flat(h, s), flat(h, prefix)) {
        (Some(x), Some(y)) if y.len() <= x.len() => units_at(h, x, 0, y),
        (Some(_), Some(_)) => Ok(false),
        _ => rope_at(h, s, |_, _| 0, prefix),
    }
}

#[inline]
pub fn ends_with<H: Host>(h: &H, s: H::Str, suffix: H::Str) -> Result<bool, H::Error> {
    match (flat(h, s), flat(h, suffix)) {
        (Some(x), Some(y)) if y.len() <= x.len() => units_at(h, x, x.len() - y.len(), y),
        (Some(_), Some(_)) => Ok(false),
        _ => rope_at(h, s, |n, m| n - m, suffix),
    }
}

/// Whether `x` holds the characters of `y` from `at`, where there's room for them.
#[inline]
fn units_at<H: Host>(h: &H, x: Units<'_>, at: usize, y: Units<'_>) -> Result<bool, H::Error> {
    h.charge(y.len() as u64)?;
    Ok(x.slice(at..at + y.len()).compare(y).is_eq())
}

/// Whether `s` holds the characters of `t` from where `at` puts them, given the lengths of
/// both, if there's room.
#[inline(never)]
fn rope_at<H: Host>(h: &H, s: H::Str, at: fn(usize, usize) -> usize, t: H::Str) -> Result<bool, H::Error> {
    let (n, m) = (len(h, s), len(h, t));
    if m > n {
        return Ok(false);
    }
    h.charge(m as u64)?;
    let at = at(n, m);
    Ok(compare_runs(Chunks::new(h, s, at, at + m), chunks(h, t)).is_eq())
}

/// The pieces of `s` between occurrences of `separator`, in order, one more than there are
/// separators, so some may be empty. An empty separator splits between characters, so then
/// each character is a piece, unless `s` is empty.
pub fn split<H: Host>(h: &H, s: H::Str, separator: H::Str) -> Split<'_, H> {
    splitn(h, s, separator, usize::MAX)
}

/// Like [`split`], in at most `limit` pieces: the last holds the rest of `s`, separators and all.
pub fn splitn<H: Host>(h: &H, s: H::Str, separator: H::Str, limit: usize) -> Split<'_, H> {
    Split { h, s, separator, at: Some(0), limit }
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
        let (n, m) = (len(h, self.s), len(h, self.separator));
        let end = match m {
            _ if self.limit == 0 => None,
            0 => (at + 1 < n).then_some(at + 1),
            _ => match find(h, self.s, self.separator, at) {
                Ok(end) => end,
                Err(e) => {
                    self.at = None;
                    return Some(Err(e));
                }
            },
        };
        self.at = end.map(|end| end + m);
        Some(substring(h, self.s, at, end.unwrap_or(n)))
    }
}

/// The runs of `s` between whitespace, none empty.
pub fn split_whitespace<H: Host>(h: &H, s: H::Str) -> SplitWhitespace<'_, H> {
    SplitWhitespace { h, s, text: None, at: Some(0) }
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
                Err(e) => {
                    self.at = None;
                    return Some(Err(e));
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

/// `s` without whitespace at either end.
pub fn trim<H: Host>(h: &H, s: H::Str) -> Res<H> {
    trimmed(h, s, true, true)
}

pub fn trim_start<H: Host>(h: &H, s: H::Str) -> Res<H> {
    trimmed(h, s, true, false)
}

pub fn trim_end<H: Host>(h: &H, s: H::Str) -> Res<H> {
    trimmed(h, s, false, true)
}

fn trimmed<H: Host>(h: &H, s: H::Str, start: bool, end: bool) -> Res<H> {
    let text = flatten(h, s)?;
    let units = flat(h, text).expect("flattened");
    let n = units.len();
    let space = |i| units.get(i).is_some_and(char::is_whitespace);
    let from = if start { (0..n).find(|&i| !space(i)).unwrap_or(n) } else { 0 };
    let to = if end { (from..n).rev().find(|&i| !space(i)).map_or(from, |i| i + 1) } else { n };
    h.charge((from + n - to) as u64)?;
    if from == 0 && to == n {
        return Ok(s);
    }
    substring(h, text, from, to)
}
