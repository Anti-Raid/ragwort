//! Case mapping and case-insensitive comparison. Both use the full Unicode mappings that `char`
//! provides, so one character can map to several. The mappings ignore context: a final capital sigma
//! lowercases to `σ`, not `ς`. Folding is Unicode full case folding. It is computed as the lowercase of the
//! uppercase of the lowercase, with two exceptions: dotless `ı` stays as it is, and Cherokee folds to
//! uppercase.

use std::cmp::Ordering;
use std::char::{ToLowercase, ToUppercase};
use std::iter::FlatMap;

use crate::word::{HIGH, ONES};
use crate::{Host, Res, byte_len, chars, flat_counted, from_chars};

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
    h.charge((byte_len(h, a) + byte_len(h, b)) as u64)?;
    // A flat string is ASCII exactly when it has as many characters as bytes. Two ASCII strings are folded and compared a word at a time, however they are stored.
    let (ascii_a, ascii_b) = (flat_counted(h, a).filter(|(units, chars)| units.len() == *chars), flat_counted(h, b).filter(|(units, chars)| units.len() == *chars));
    if let (Some((units_a, _)), Some((units_b, _))) = (ascii_a, ascii_b) {
        let n = units_a.len().min(units_b.len());
        let (head_a, head_b) = (units_a.slice(0..n), units_b.slice(0..n));
        for index in 0..n.div_ceil(8) {
            let (x, y) = (Case::Fold.ascii(head_a.byte_chunk(index)), Case::Fold.ascii(head_b.byte_chunk(index)));
            if x != y {
                // The first byte of a word is in its lowest bits, so the lowest differing bit lies in the first differing byte.
                let shift = (x ^ y).trailing_zeros() / 8 * 8;
                return Ok((x >> shift & 0xFF).cmp(&(y >> shift & 0xFF)));
            }
        }
        return Ok(units_a.len().cmp(&units_b.len()));
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
    h.charge(byte_len(h, string) as u64)?;
    // ASCII text is mapped a word at a time, however it is stored.
    if let Some((units, _)) = flat_counted(h, string).filter(|(units, chars)| units.len() == *chars) {
        let n = units.len();
        let words = (0..n.div_ceil(8)).map(move |index| units.byte_chunk(index));
        if words.clone().all(|word| case.ascii(word) == word) {
            return Ok(string);
        }
        return h.flat(n, n, |mut out| out.write_words(words.map(|word| case.ascii(word))));
    }
    if chars(h, string).all(|character| case.map(character).eq([character])) {
        return Ok(string);
    }
    from_chars(h, chars(h, string).flat_map(move |character| case.map(character)))
}
