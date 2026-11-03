//! Case mapping and caseless comparison, by the full mappings of each character that `char`
//! knows, so a character may become several. There's no context: a final capital sigma
//! lowercases to `σ`, not `ς`. Folding is Unicode's full case folding: the lowercase of the
//! uppercase of the lowercase, except that dotless `ı` stays as it is and Cherokee folds to
//! uppercase.

use std::cmp::Ordering;
use std::char::{ToLowercase, ToUppercase};
use std::iter::FlatMap;

use crate::{Host, Res, Units, Width, chars, flat, from_chars, len};

#[cfg(test)]
#[path = "tests/case.rs"]
mod tests;

pub fn upcase<H: Host>(h: &H, s: H::Str) -> Res<H> {
    map_case(h, s, Case::Upper)
}

pub fn downcase<H: Host>(h: &H, s: H::Str) -> Res<H> {
    map_case(h, s, Case::Lower)
}

/// `s` folded, so strings that differ only in case fold alike.
pub fn foldcase<H: Host>(h: &H, s: H::Str) -> Res<H> {
    map_case(h, s, Case::Fold)
}

/// Orders `a` and `b` as their folds would be.
pub fn compare_ci<H: Host>(h: &H, a: H::Str, b: H::Str) -> Result<Ordering, H::Error> {
    if a == b {
        return Ok(Ordering::Equal);
    }
    h.charge((len(h, a) + len(h, b)) as u64)?;
    if let (Some(Units::Packed(x)), Some(Units::Packed(y))) = (flat(h, a), flat(h, b))
        && x.is_ascii()
        && y.is_ascii()
    {
        let n = x.len().min(y.len());
        let fold = |w| Case::Fold.ascii(w);
        return Ok(x.slice(0..n).compare_by(y.slice(0..n), fold).then(x.len().cmp(&y.len())));
    }
    let fold = |c| Case::Fold.map(c);
    Ok(chars(h, a).flat_map(fold).cmp(chars(h, b).flat_map(fold)))
}

#[derive(Clone, Copy)]
enum Case {
    Upper,
    Lower,
    Fold,
}

type Folded = FlatMap<FlatMap<ToLowercase, ToUppercase, fn(char) -> ToUppercase>, ToLowercase, fn(char) -> ToLowercase>;

/// What a character maps to.
#[derive(Clone)]
enum Mapped {
    Upper(ToUppercase),
    Lower(ToLowercase),
    Fold(Folded),
}

impl Iterator for Mapped {
    type Item = char;

    fn next(&mut self) -> Option<char> {
        match self {
            Self::Upper(m) => m.next(),
            Self::Lower(m) => m.next(),
            Self::Fold(m) => m.next(),
        }
    }
}

impl Case {
    fn map(self, c: char) -> Mapped {
        match self {
            Self::Upper => Mapped::Upper(c.to_uppercase()),
            Self::Lower => Mapped::Lower(c.to_lowercase()),
            Self::Fold => match c {
                'ı' => Mapped::Lower(c.to_lowercase()),
                '\u{13A0}'..='\u{13FD}' | '\u{AB70}'..='\u{ABBF}' => Mapped::Upper(c.to_uppercase()),
                _ => Mapped::Fold(c.to_lowercase().flat_map(char::to_uppercase as fn(char) -> ToUppercase).flat_map(char::to_lowercase as fn(char) -> ToLowercase)),
            },
        }
    }

    /// Maps eight ASCII bytes at once: those from `lo` to `hi` flip their 0x20 bit. The bytes
    /// are all below 0x80, so adding to them never carries from one to the next.
    fn ascii(self, w: u64) -> u64 {
        const ONES: u64 = 0x0101_0101_0101_0101;
        let (lo, hi) = match self {
            Self::Upper => (b'a', b'z'),
            Self::Lower | Self::Fold => (b'A', b'Z'),
        };
        let from_lo = w + ONES * u64::from(0x80 - lo);
        let past_hi = w + ONES * u64::from(0x7F - hi);
        w ^ (from_lo & !past_hi & crate::hash::HIGH) >> 2
    }
}

/// `s` mapped, or `s` itself if that changes nothing.
fn map_case<H: Host>(h: &H, s: H::Str, case: Case) -> Res<H> {
    h.charge(len(h, s) as u64)?;
    if let Some(Units::Packed(p)) = flat(h, s)
        && p.is_ascii()
    {
        let n = p.len();
        let words = (0..n.div_ceil(8)).map(|k| p.word_at(k, (n - 8 * k).min(8)));
        if words.clone().all(|w| case.ascii(w) == w) {
            return Ok(s);
        }
        return h.flat(Width::One, n, |mut out| out.write_words(words.map(|w| case.ascii(w))));
    }
    if chars(h, s).all(|c| case.map(c).eq([c])) {
        return Ok(s);
    }
    from_chars(h, chars(h, s).flat_map(move |c| case.map(c)))
}
