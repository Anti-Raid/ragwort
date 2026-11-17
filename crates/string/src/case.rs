//! Case mapping and case-insensitive comparison. Both use the full Unicode mappings that `char`
//! provides, so one character can map to several. The mappings ignore context: a final capital sigma
//! lowercases to `σ`, not `ς`. Folding is Unicode full case folding. It is computed as the lowercase of the
//! uppercase of the lowercase, with two exceptions: dotless `ı` stays as it is, and Cherokee folds to
//! uppercase.

use std::cell::Cell;
use std::cmp::Ordering;
use std::char::{ToLowercase, ToUppercase};
use std::iter::FlatMap;

use crate::word::{HIGH, ONES};
use crate::{Host, Res, Units, Width, chars, flat, from_chars, len};

#[cfg(test)]
#[path = "tests/case.rs"]
mod tests;

pub fn upcase<H: Host>(h: &H, string: H::Str) -> Res<H> {
    map_case(h, string, Case::Upper)
}

pub fn downcase<H: Host>(h: &H, string: H::Str) -> Res<H> {
    map_case(h, string, Case::Lower)
}

/// Returns `string` case-folded. Strings that differ only in case fold to the same characters.
pub fn foldcase<H: Host>(h: &H, string: H::Str) -> Res<H> {
    map_case(h, string, Case::Fold)
}

/// Returns the uppercase of `character` if the mapping is a single character. Otherwise returns `character` unchanged, as R7RS `char-upcase` does.
pub fn upcase_char(character: char) -> char {
    single(Case::Upper.map(character), character)
}

pub fn downcase_char(character: char) -> char {
    single(Case::Lower.map(character), character)
}

/// Returns `character` folded as [`foldcase`] folds it, if the result is a single character. Otherwise returns `character` unchanged.
pub fn foldcase_char(character: char) -> char {
    single(Case::Fold.map(character), character)
}

fn single(mut mapped: Mapped, character: char) -> char {
    match (mapped.next(), mapped.next()) {
        (Some(one), None) => one,
        _ => character,
    }
}

/// Compares `a` and `b` as [`crate::compare`] would compare their case-folded forms.
pub fn compare_ci<H: Host>(h: &H, a: H::Str, b: H::Str) -> Result<Ordering, H::Error> {
    if a == b {
        return Ok(Ordering::Equal);
    }
    h.charge((len(h, a) + len(h, b)) as u64)?;
    let (cell_a, cell_b) = (Cell::new(0), Cell::new(0));
    let (units_a, units_b) = (flat(h, a).map(|units| units.anchored(&cell_a)), flat(h, b).map(|units| units.anchored(&cell_b)));
    if let (Some(Units::Packed(packed_a)), Some(Units::Packed(packed_b))) = (units_a, units_b)
        && packed_a.is_ascii()
        && packed_b.is_ascii()
    {
        let n = packed_a.len().min(packed_b.len());
        return Ok(packed_a.slice(0..n).compare_by(packed_b.slice(0..n), |word| Case::Fold.ascii(word)).then(packed_a.len().cmp(&packed_b.len())));
    }
    Ok(chars(h, a).flat_map(|character| Case::Fold.map(character)).cmp(chars(h, b).flat_map(|character| Case::Fold.map(character))))
}

#[derive(Clone, Copy)]
enum Case {
    Upper,
    Lower,
    Fold,
}

type Folded = FlatMap<FlatMap<ToLowercase, ToUppercase, fn(char) -> ToUppercase>, ToLowercase, fn(char) -> ToLowercase>;

/// Iterator over the characters that one character maps to.
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
            Self::Upper(mapping) => mapping.next(),
            Self::Lower(mapping) => mapping.next(),
            Self::Fold(mapping) => mapping.next(),
        }
    }
}

impl Case {
    fn map(self, character: char) -> Mapped {
        match self {
            Self::Upper => Mapped::Upper(character.to_uppercase()),
            Self::Lower => Mapped::Lower(character.to_lowercase()),
            Self::Fold => match character {
                'ı' => Mapped::Lower(character.to_lowercase()),
                '\u{13A0}'..='\u{13FD}' | '\u{AB70}'..='\u{ABBF}' => Mapped::Upper(character.to_uppercase()),
                _ => Mapped::Fold(character.to_lowercase().flat_map(char::to_uppercase as fn(char) -> ToUppercase).flat_map(char::to_lowercase as fn(char) -> ToLowercase)),
            },
        }
    }

    /// Maps eight ASCII bytes at once. Each byte in the range `lo` to `hi` has its 0x20 bit flipped. All the bytes
    /// are below 0x80, so the additions never carry from one byte into the next.
    fn ascii(self, word: u64) -> u64 {
        let (lo, hi) = match self {
            Self::Upper => (b'a', b'z'),
            Self::Lower | Self::Fold => (b'A', b'Z'),
        };
        let from_lo = word + ONES * u64::from(0x80 - lo);
        let past_hi = word + ONES * u64::from(0x7F - hi);
        word ^ (from_lo & !past_hi & HIGH) >> 2
    }
}

/// Returns `string` mapped by `case`, or `string` itself if the mapping changes nothing.
fn map_case<H: Host>(h: &H, string: H::Str, case: Case) -> Res<H> {
    h.charge(len(h, string) as u64)?;
    let cell = Cell::new(0);
    if let Some(Units::Packed(packed)) = flat(h, string).map(|units| units.anchored(&cell))
        && packed.is_ascii()
    {
        let words = packed.byte_words();
        if words.clone().all(|word| case.ascii(word) == word) {
            return Ok(string);
        }
        return h.flat(Width::One, packed.len(), |mut out| out.write_words(words.map(|word| case.ascii(word))));
    }
    if chars(h, string).all(|character| case.map(character).eq([character])) {
        return Ok(string);
    }
    from_chars(h, chars(h, string).flat_map(move |character| case.map(character)))
}
