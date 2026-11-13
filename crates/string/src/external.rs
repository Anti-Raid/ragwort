//! Characters kept outside the heap, by the program that runs it. A host keeps an external
//! string's owner alive while the string is reachable, and the library reads its characters
//! like any flat string's.
//!
//! A string never changes, so its owner promises that the characters don't: there are always as
//! many, with the same values. The library relies on that and can't check it: it keeps what it
//! has read of a string, such as its length and its hash.

use crate::{MAX_LEN, StrError, Units, Width};

/// Characters owned outside the heap, which never change.
pub trait External: 'static {
    /// The same characters on every call, as many and with the same values, at their narrowest
    /// width.
    fn units(&self) -> Units<'_>;
}

/// Checks that `units` can stand as a flat string.
pub fn check_external(units: Units<'_>) -> Result<(), StrError> {
    if units.len() > MAX_LEN {
        return Err(StrError::TooLong);
    }
    if units.narrowest() != units.width() {
        return Err(StrError::NotNarrowest);
    }
    Ok(())
}

/// UTF-8 text as an external string: ASCII stays as it is, and other text is converted once
/// to characters at their narrowest width, kept with the text's owner rather than in the heap.
pub struct ExternalText<T>(Repr<T>);

enum Repr<T> {
    Ascii(T),
    One(Box<[u8]>),
    Two(Box<[u16]>),
    Four(Box<[u32]>),
}

impl<T: AsRef<str>> ExternalText<T> {
    pub fn new(text: T) -> Self {
        let string = text.as_ref();
        if string.is_ascii() {
            return Self(Repr::Ascii(text));
        }
        let repr = match string.chars().map(Width::of).max().unwrap_or(Width::One) {
            Width::One => Repr::One(string.chars().map(|character| character as u8).collect()),
            Width::Two => Repr::Two(string.chars().map(|character| character as u16).collect()),
            Width::Four => Repr::Four(string.chars().map(|character| character as u32).collect()),
        };
        Self(repr)
    }
}

impl<T: AsRef<str> + 'static> External for ExternalText<T> {
    fn units(&self) -> Units<'_> {
        match &self.0 {
            Repr::Ascii(text) => Units::One(text.as_ref().as_bytes()),
            Repr::One(units) => Units::One(units),
            Repr::Two(units) => Units::Two(units),
            Repr::Four(units) => Units::Four(units),
        }
    }
}
