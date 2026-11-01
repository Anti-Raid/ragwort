//! String interning over a table the host keeps. Hashing, name comparison and symbol creation
//! live here; the table supplies storage, probing and growth.

use crate::{Host, equal, equal_str, flatten, from_str, hash, hash_str};

#[cfg(test)]
#[path = "tests/intern.rs"]
mod tests;

/// A table of symbols, each named by a flat string.
pub trait Table<H: Host> {
    type Entry: Copy;

    fn seed(&self) -> u64;
    /// A new entry named by a flat string, with the original hash.
    fn make(&self, h: &H, name: H::Str, hash: u64) -> Result<Self::Entry, H::Error>;
    fn name(&self, h: &H, entry: Self::Entry) -> H::Str;

    /// The live entry with this hash that `same` accepts, or one `make` makes and the table
    /// keeps. Neither callback may change the table.
    fn find_or_insert(
        &self,
        h: &H,
        hash: u64,
        same: impl Fn(Self::Entry) -> Result<bool, H::Error>,
        make: impl FnOnce() -> Result<Self::Entry, H::Error>,
    ) -> Result<Self::Entry, H::Error>;
}

/// The symbol named by the characters of `s`, made if there's none.
#[inline]
pub fn intern<H: Host, T: Table<H>>(h: &H, table: &T, s: H::Str) -> Result<T::Entry, H::Error> {
    let hash = hash(h, s, table.seed())?;
    table.find_or_insert(h, probe_hash(hash), |entry| equal(h, table.name(h, entry), s), || table.make(h, flatten(h, s)?, hash))
}

/// The symbol named `s`, made without making a string first unless the name is new.
#[inline]
pub fn intern_str<H: Host, T: Table<H>>(h: &H, table: &T, s: &str) -> Result<T::Entry, H::Error> {
    let hash = hash_str(s, table.seed());
    table.find_or_insert(h, probe_hash(hash), |entry| equal_str(h, table.name(h, entry), s), || table.make(h, from_str(h, s)?, hash))
}

fn probe_hash(hash: u64) -> u64 {
    #[cfg(test)]
    let hash = hash & tests::KEY_BITS.get();
    hash
}
