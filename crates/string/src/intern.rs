//! String interning over a table that the host owns. Hashing, name comparison and symbol creation
//! are implemented here. The table supplies storage, probing and growth.

use crate::{Host, equal, equal_str, flatten, from_str, hash, hash_str};

#[cfg(test)]
#[path = "tests/intern.rs"]
mod tests;

/// A table of symbols, each named by a flat string.
pub trait Table<H: Host> {
    type Entry: Copy;

    fn seed(&self) -> u64;
    /// Creates a new entry named by the flat string `name`. `hash` is the hash of `name` under [`Table::seed`].
    fn make(&self, h: &H, name: H::Str, hash: u64) -> Result<Self::Entry, H::Error>;
    fn name(&self, h: &H, entry: Self::Entry) -> H::Str;

    /// Returns the live entry with hash `hash` that `same` accepts. If there is none, calls `make`, inserts the new entry
    /// into the table and returns it. Neither callback may modify the table.
    fn find_or_insert(
        &self,
        h: &H,
        hash: u64,
        same: impl Fn(Self::Entry) -> Result<bool, H::Error>,
        make: impl FnOnce() -> Result<Self::Entry, H::Error>,
    ) -> Result<Self::Entry, H::Error>;
}

/// Returns the symbol whose name has the characters of `name`. Creates the symbol if it does not exist.
#[inline]
pub fn intern<H: Host, T: Table<H>>(h: &H, table: &T, name: H::Str) -> Result<T::Entry, H::Error> {
    let hash = hash(h, name, table.seed())?;
    table.find_or_insert(h, probe_hash(hash), |entry| equal(h, table.name(h, entry), name), || table.make(h, flatten(h, name)?, hash))
}

/// Returns the symbol named `name`, creating it if it does not exist. A string is allocated only when the symbol is new.
#[inline]
pub fn intern_str<H: Host, T: Table<H>>(h: &H, table: &T, name: &str) -> Result<T::Entry, H::Error> {
    let hash = hash_str(name, table.seed());
    table.find_or_insert(h, probe_hash(hash), |entry| named(h, table, entry, name), || table.make(h, from_str(h, name)?, hash))
}

/// Returns whether `entry` is named `name`. This is kept out of line. If it were inlined into the probe, its setup for `name`
/// would run on every call, before any entry is compared.
#[inline(never)]
fn named<H: Host, T: Table<H>>(h: &H, table: &T, entry: T::Entry, name: &str) -> Result<bool, H::Error> {
    equal_str(h, table.name(h, entry), name)
}

fn probe_hash(hash: u64) -> u64 {
    #[cfg(test)]
    let hash = hash & tests::KEY_BITS.get();
    hash
}
