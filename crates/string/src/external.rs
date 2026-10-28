//! Characters kept outside the heap, by the program that runs it. A host keeps an external
//! string's owner alive while the string is reachable, and the library reads its characters
//! like any flat string's.

use crate::{MAX_LEN, StrError, Units, Width};

/// Characters owned outside the heap.
pub trait External: 'static {
    /// The same characters on every call, at their narrowest width.
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
        let s = text.as_ref();
        if s.is_ascii() {
            return Self(Repr::Ascii(text));
        }
        let repr = match s.chars().map(Width::of).max().unwrap_or(Width::One) {
            Width::One => Repr::One(s.chars().map(|c| c as u8).collect()),
            Width::Two => Repr::Two(s.chars().map(|c| c as u16).collect()),
            Width::Four => Repr::Four(s.chars().map(|c| c as u32).collect()),
        };
        Self(repr)
    }
}

impl<T: AsRef<str> + 'static> External for ExternalText<T> {
    fn units(&self) -> Units<'_> {
        match &self.0 {
            Repr::Ascii(text) => Units::One(text.as_ref().as_bytes()),
            Repr::One(u) => Units::One(u),
            Repr::Two(u) => Units::Two(u),
            Repr::Four(u) => Units::Four(u),
        }
    }
}
