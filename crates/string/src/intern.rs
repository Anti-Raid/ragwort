//! Intern tables: at most one symbol per name at a time, so symbols are equal exactly when
//! they're the same. The host keeps the table, open addressed with linear probing, in slots
//! that each hold a key and a symbol the slot may lose, such as through a weak reference. This
//! does the rest: hashing, probing, matching names and growing the table.

use crate::{Host, equal, equal_str, flatten, from_str, hash, hash_str};

#[cfg(test)]
mod tests;

/// Where a host keeps an intern table. A slot's key is zero until it's first used, and it
/// keeps its key after its symbol is gone, so probes go on past it until the table is rebuilt.
pub trait Table<H: Host> {
    type Symbol: Copy;
    type Slot;

    /// The seed of the table's hashes, which its symbols keep.
    fn seed(&self) -> u64;

    /// None at first, then a power of two of them.
    fn slots<'a>(&'a self, h: &'a H) -> &'a [Self::Slot];

    /// Puts `len` slots with zero keys in place of the ones [`Table::slots`] gave, and hands
    /// them back. The old ones stay as they were.
    fn replace<'a>(&'a self, h: &'a H, len: usize) -> Result<&'a [Self::Slot], H::Error>;

    fn key(&self, slot: &Self::Slot) -> u64;

    /// The slot's symbol, unless it's gone.
    fn symbol(&self, h: &H, slot: &Self::Slot) -> Option<Self::Symbol>;

    fn set(&self, h: &H, slot: &Self::Slot, key: u64, symbol: Self::Symbol);

    /// Slots with a key, as last set.
    fn used(&self) -> usize;

    fn set_used(&self, h: &H, used: usize);

    /// A new symbol named `name`, a flat string, whose hash is `hash`.
    fn make(&self, h: &H, name: H::Str, hash: u64) -> Result<Self::Symbol, H::Error>;

    fn name(&self, h: &H, symbol: Self::Symbol) -> H::Str;
}

const MIN_SLOTS: usize = 64;

/// The symbol named by the characters of `s`, made if there's none.
#[inline]
pub fn intern<H: Host, T: Table<H>>(h: &H, table: &T, s: H::Str) -> Result<T::Symbol, H::Error> {
    let hash = hash(h, s, table.seed())?;
    find_or_make(h, table, hash, |name| equal(h, name, s), || flatten(h, s))
}

/// The symbol named `s`, made without making a string first unless the name is new.
#[inline]
pub fn intern_str<H: Host, T: Table<H>>(h: &H, table: &T, s: &str) -> Result<T::Symbol, H::Error> {
    let hash = hash_str(s, table.seed());
    find_or_make(h, table, hash, |name| equal_str(h, name, s), || from_str(h, s))
}

#[inline]
fn find_or_make<H: Host, T: Table<H>>(
    h: &H,
    table: &T,
    hash: u64,
    same: impl Fn(H::Str) -> Result<bool, H::Error>,
    name: impl FnOnce() -> Result<H::Str, H::Error>,
) -> Result<T::Symbol, H::Error> {
    let key = key_of(hash);
    let mut slots = table.slots(h);
    let mut free = None;
    if !slots.is_empty() {
        let mask = slots.len() - 1;
        let mut i = home(key, mask);
        loop {
            let slot = &slots[i];
            match table.key(slot) {
                0 => {
                    free = free.or(Some(i));
                    break;
                }
                k if k == key => match table.symbol(h, slot) {
                    Some(symbol) if same(table.name(h, symbol))? => return Ok(symbol),
                    Some(_) => {}
                    None => free = free.or(Some(i)),
                },
                _ => {}
            }
            i = (i + 1) & mask;
        }
    }
    let symbol = table.make(h, name()?, hash)?;
    let i = match free {
        Some(i) if table.key(&slots[i]) != 0 => i,
        Some(i) if (table.used() + 1) * 4 <= slots.len() * 3 => {
            table.set_used(h, table.used() + 1);
            i
        }
        _ => {
            slots = rebuild(h, table)?;
            table.set_used(h, table.used() + 1);
            empty_slot(table, slots, key)
        }
    };
    table.set(h, &slots[i], key, symbol);
    Ok(symbol)
}

/// Moves the live symbols to a table at most half full with one more.
fn rebuild<'a, H: Host, T: Table<H>>(h: &'a H, table: &'a T) -> Result<&'a [T::Slot], H::Error> {
    let old = table.slots(h);
    let live = old.iter().filter(|slot| table.symbol(h, slot).is_some()).count();
    let len = (2 * (live + 1)).next_power_of_two().max(MIN_SLOTS);
    let slots = table.replace(h, len)?;
    for slot in old {
        if let Some(symbol) = table.symbol(h, slot) {
            let key = table.key(slot);
            table.set(h, &slots[empty_slot(table, slots, key)], key, symbol);
        }
    }
    table.set_used(h, live);
    Ok(slots)
}

/// A slot's key for a symbol with this hash. Tests can keep only some of its bits, so that
/// different names share keys.
fn key_of(hash: u64) -> u64 {
    #[cfg(test)]
    let hash = hash & tests::KEY_BITS.get();
    hash | 1
}

/// Where probes for `key` start. Its low bit is always set, so it's left out.
fn home(key: u64, mask: usize) -> usize {
    (key >> 1) as usize & mask
}

fn empty_slot<H: Host, T: Table<H>>(table: &T, slots: &[T::Slot], key: u64) -> usize {
    let mask = slots.len() - 1;
    let mut i = home(key, mask);
    while table.key(&slots[i]) != 0 {
        i = (i + 1) & mask;
    }
    i
}
