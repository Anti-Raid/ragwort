//! Text stored outside the heap, by the program that runs the heap. A host keeps the owner of an
//! external string alive while the string is reachable. The library reads the text
//! like that of any flat string.
//!
//! Strings are immutable, so the owner must never change the text. The library relies on this and cannot check it.
//! It caches values that it has read from a string, such as the number of characters and the hash.

use crate::{MAX_LEN, StrError};

/// Text that is owned outside the heap and never changes.
pub trait External: 'static {
    /// Returns the text. Every call must return the same text.
    fn text(&self) -> &str;
}

/// Checks that `text` is valid as a flat string: it must be no longer than [`MAX_LEN`] bytes.
pub fn check_external(text: &str) -> Result<(), StrError> {
    if text.len() > MAX_LEN {
        return Err(StrError::TooLong);
    }
    Ok(())
}

/// Text of the host as an external string. The text is used as it is: nothing is converted and nothing is copied.
pub struct ExternalText<T>(T);

impl<T: AsRef<str>> ExternalText<T> {
    pub fn new(text: T) -> Self {
        Self(text)
    }
}

impl<T: AsRef<str> + 'static> External for ExternalText<T> {
    fn text(&self) -> &str {
        self.0.as_ref()
    }
}
