//! Linear-probing tables over host-owned storage. The host supplies allocation, entry
//! liveness, and writes; these algorithms do not allocate or hold references into the host.

/// Storage for a table. Slots have power-of-two capacity and zero keys when unused.
/// A dead entry keeps its key until rebuilding, so lookups can probe past it.
/// Implementations must retain old storage while borrowed and preserve at least one
/// unused slot. Use `find_or_insert` to maintain the occupancy and growth rules.
pub trait GcMap<H> {
    type Entry: Copy;
    type Error;
    type Slot;

    /// Empty at first, then a power-of-two number of slots.
    fn slots<'a>(&'a self, h: &'a H) -> &'a [Self::Slot];

    /// Puts `len` slots with zero keys in place of the ones [`GcMap::slots`] gave, and hands
    /// them back. The old ones stay as they were.
    fn replace<'a>(&'a self, h: &'a H, len: usize) -> Result<&'a [Self::Slot], Self::Error>;

    fn key(&self, slot: &Self::Slot) -> u64;

    /// The slot's entry, unless it's gone.
    fn entry(&self, h: &H, slot: &Self::Slot) -> Option<Self::Entry>;

    fn set(&self, h: &H, slot: &Self::Slot, key: u64, entry: Self::Entry);

    /// Slots with a key, as last set.
    fn used(&self) -> usize;

    fn set_used(&self, h: &H, used: usize);

    /// Finds an equal live entry or creates one. Neither callback may modify this table.
    /// Hashes must remain stable when the host moves an entry.
    #[inline]
    fn find_or_insert(
        &self,
        h: &H,
        hash: u64,
        same: impl Fn(Self::Entry) -> Result<bool, Self::Error>,
        make: impl FnOnce() -> Result<Self::Entry, Self::Error>,
    ) -> Result<Self::Entry, Self::Error>
    where
        Self: Sized,
    {
        find_or_insert(h, self, hash, same, make)
    }
}

const MIN_SLOTS: usize = 64;

#[inline]
fn find_or_insert<H, T: GcMap<H>>(
    h: &H,
    table: &T,
    hash: u64,
    same: impl Fn(T::Entry) -> Result<bool, T::Error>,
    make: impl FnOnce() -> Result<T::Entry, T::Error>,
) -> Result<T::Entry, T::Error> {
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
                k if k == key => match table.entry(h, slot) {
                    Some(entry) if same(entry)? => return Ok(entry),
                    Some(_) => {}
                    None => free = free.or(Some(i)),
                },
                _ => {}
            }
            i = (i + 1) & mask;
        }
    }
    let entry = make()?;
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
    table.set(h, &slots[i], key, entry);
    Ok(entry)
}

/// Rebuilds with enough capacity to stay at most half full after insertion.
fn rebuild<'a, H, T: GcMap<H>>(h: &'a H, table: &'a T) -> Result<&'a [T::Slot], T::Error> {
    let old = table.slots(h);
    let live = old.iter().filter(|slot| table.entry(h, slot).is_some()).count();
    let len = (2 * (live + 1)).next_power_of_two().max(MIN_SLOTS);
    let slots = table.replace(h, len)?;
    for slot in old {
        if let Some(entry) = table.entry(h, slot) {
            let key = table.key(slot);
            table.set(h, &slots[empty_slot(table, slots, key)], key, entry);
        }
    }
    table.set_used(h, live);
    Ok(slots)
}

/// Zero denotes an unused slot; leave out the low bit when choosing a bucket.
fn key_of(hash: u64) -> u64 {
    hash | 1
}

/// Where probes for `key` start. Its low bit is always set, so it's left out.
fn home(key: u64, mask: usize) -> usize {
    (key >> 1) as usize & mask
}

fn empty_slot<H, T: GcMap<H>>(table: &T, slots: &[T::Slot], key: u64) -> usize {
    let mask = slots.len() - 1;
    let mut i = home(key, mask);
    while table.key(&slots[i]) != 0 {
        i = (i + 1) & mask;
    }
    i
}

#[cfg(test)]
#[path = "tests/map.rs"]
mod tests;
