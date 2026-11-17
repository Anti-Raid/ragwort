//! Characters stored outside the heap, by the program that runs the heap. A host keeps the owner of an
//! external string alive while the string is reachable. The library reads the characters
//! like those of any flat string.
//!
//! Strings are immutable, so the owner must never change the characters. Their number and their
//! values stay the same. The library relies on this and cannot check it. It caches values that it
//! has read from a string, such as the length and the hash.

use crate::{MAX_LEN, StrError, Units, Width};

/// Characters that are owned outside the heap and never change.
pub trait External: 'static {
    /// Returns the characters. Every call must return the same number of units with the same values,
    /// at the narrowest width that holds them.
    fn units(&self) -> Units<'_>;
}

/// Checks that `units` are valid as a flat string. They must be no longer than [`MAX_LEN`] and at their narrowest width.
pub fn check_external(units: Units<'_>) -> Result<(), StrError> {
    if units.len() > MAX_LEN {
        return Err(StrError::TooLong);
    }
    if units.narrowest() != units.width() {
        return Err(StrError::NotNarrowest);
    }
    Ok(())
}

/// UTF-8 text as an external string. ASCII text is used as it is. Other text is converted once
/// to units at their narrowest width. The units are stored in this value, not in the heap.
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
