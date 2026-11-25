//! Stores: read-only memory outside the arena that strings and bytevectors read from.
//!
//! A store is kept once, as a frozen value, and its bytes are charged to the arena's budget. It never changes.
//! A string or a bytevector that reads from a store is a view: it holds the store, a start and a length. So several
//! values can read from one store, and a part of a long text needs no bytes of its own.
//!
//! # What is in a store
//!
//! - Text that the host handed over, such as the body of a message. It stays where the host has it.
//! - Bytes that the host handed over, for a read-only bytevector.
//! - Bytes that the arena made, for a flat string that is too long to keep in the arena.
//!
//! # Sharing a part
//!
//! A view of a part of a store keeps the whole store alive. So a part is shared only if it is at least half
//! of the store and at least [`SHARE_MIN`] bytes. A smaller part is copied, and the store can be freed
//! once nothing else reads from it.

use std::ops::Range;

use ragwort_string::External;

use crate::bytevector::ExternalBuffer;

/// Read-only bytes outside the arena. See the [module docs](self).
pub enum Store {
    /// Text that the host owns.
    Text(Box<dyn External>),
    /// Bytes that the host owns.
    Bytes(Box<dyn ExternalBuffer>),
    /// Bytes that the arena made. They are UTF-8 if a string made them.
    Owned(Box<[u8]>),
}

impl Store {
    /// Returns the bytes.
    #[inline]
    pub(crate) fn bytes(&self) -> &[u8] {
        match self {
            Self::Text(text) => text.text().as_bytes(),
            Self::Bytes(bytes) => (**bytes).as_ref(),
            Self::Owned(bytes) => bytes,
        }
    }

    /// Returns the bytes in `range` as text, or `None` if they are no text or `range` is not in the store.
    /// Text of the host is returned without a check. Other bytes are checked each time.
    pub(crate) fn text(&self, range: Range<usize>) -> Option<&str> {
        match self {
            Self::Text(text) => text.text().get(range),
            _ => std::str::from_utf8(self.bytes().get(range)?).ok(),
        }
    }
}

/// The most bytes that a store can hold. A view keeps its start and its length in 31 bits each.
pub const STORE_MAX: usize = (1 << 31) - 2;

/// A part of a store that has fewer bytes than this is copied, and not shared.
pub const SHARE_MIN: usize = 64;

/// Returns whether a part of `part` bytes of a store of `store` bytes is shared. See the [module docs](self).
pub(crate) fn shares(part: usize, store: usize) -> bool {
    part >= SHARE_MIN && part.saturating_mul(2) >= store
}

/// Packs the range of a view into a word: the start in the upper half and the length in the lower half.
pub(crate) fn range_word(start: usize, len: usize) -> u64 {
    (start as u64) << 32 | len as u64
}

/// Returns the start and the length that `word` holds. See [`range_word`].
#[inline]
pub(crate) fn range_of(word: u64) -> (usize, usize) {
    ((word >> 32) as usize, (word & 0xFFFF_FFFF) as usize)
}
