//! The characters of a flat string: one, two or four bytes each, as the widest needs.

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
}

/// Room for a new flat string's characters.
#[derive(Debug)]
pub enum UnitsMut<'a> {
    One(&'a mut [u8]),
    Two(&'a mut [u16]),
    Four(&'a mut [u32]),
}

macro_rules! each {
    ($units:expr, $s:ident => $e:expr) => {
        match $units {
            Units::One($s) => $e,
            Units::Two($s) => $e,
            Units::Four($s) => $e,
        }
    };
}

macro_rules! each_mut {
    ($units:expr, $s:ident => $e:expr) => {
        match $units {
            UnitsMut::One($s) => $e,
            UnitsMut::Two($s) => $e,
            UnitsMut::Four($s) => $e,
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
    pub fn len(self) -> usize {
        each!(self, s => s.len())
    }

    pub fn is_empty(self) -> bool {
        self.len() == 0
    }

    pub fn width(self) -> Width {
        match self {
            Self::One(_) => Width::One,
            Self::Two(_) => Width::Two,
            Self::Four(_) => Width::Four,
        }
    }

    pub fn get(self, i: usize) -> Option<char> {
        match self {
            Self::One(s) => s.get(i).map(|&b| char::from(b)),
            Self::Two(s) => s.get(i).map(|&u| to_char(u as u32)),
            Self::Four(s) => s.get(i).map(|&u| to_char(u)),
        }
    }

    pub fn slice(self, range: Range<usize>) -> Self {
        match self {
            Self::One(s) => Self::One(&s[range]),
            Self::Two(s) => Self::Two(&s[range]),
            Self::Four(s) => Self::Four(&s[range]),
        }
    }

    pub fn chars(self) -> impl Iterator<Item = char> + 'a {
        (0..self.len()).map(move |i| self.get(i).expect("in range"))
    }

    /// The narrowest width that holds these characters.
    pub(crate) fn narrowest(self) -> Width {
        match self {
            Self::One(_) => Width::One,
            _ => Width::of_code(each!(self, s => widest(s))),
        }
    }

    fn code(self, i: usize) -> u32 {
        each!(self, s => s[i].code())
    }

    /// Orders two runs of the same length by code point.
    pub(crate) fn compare(self, other: Units<'_>) -> Ordering {
        debug_assert_eq!(self.len(), other.len());
        match (self, other) {
            (Self::One(a), Units::One(b)) => a.cmp(b),
            (Self::Two(a), Units::Two(b)) => a.cmp(b),
            (Self::Four(a), Units::Four(b)) => a.cmp(b),
            _ => (0..self.len()).map(|i| self.code(i).cmp(&other.code(i))).find(|o| o.is_ne()).unwrap_or(Ordering::Equal),
        }
    }

    /// Whether these are the same characters, given both are at their narrowest width.
    pub(crate) fn equal(self, other: Units<'_>) -> bool {
        match (self, other) {
            (Self::One(a), Units::One(b)) => a == b,
            (Self::Two(a), Units::Two(b)) => a == b,
            (Self::Four(a), Units::Four(b)) => a == b,
            _ => false,
        }
    }

    /// UTF-8 bytes these characters take.
    pub(crate) fn utf8_len(self) -> usize {
        match self {
            Self::One(s) => s.len() + s.iter().filter(|&&b| b >= 0x80).count(),
            _ => self.chars().map(char::len_utf8).sum(),
        }
    }
}

impl UnitsMut<'_> {
    pub fn len(&self) -> usize {
        each_mut!(self, s => s.len())
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
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
        }
    }

    /// Writes `src` from `at`, each character converted to this width, which must hold them.
    pub(crate) fn write(&mut self, at: usize, src: Units<'_>) {
        let end = at + src.len();
        match (self, src) {
            (UnitsMut::One(d), Units::One(s)) => d[at..end].copy_from_slice(s),
            (UnitsMut::Two(d), Units::Two(s)) => d[at..end].copy_from_slice(s),
            (UnitsMut::Four(d), Units::Four(s)) => d[at..end].copy_from_slice(s),
            (d, s) => each_mut!(d, d => each!(s, s => convert(s, &mut d[at..end]))),
        }
    }

    pub(crate) fn set(&mut self, i: usize, c: char) {
        each_mut!(self, s => s[i] = Unit::of(c as u32));
    }
}
