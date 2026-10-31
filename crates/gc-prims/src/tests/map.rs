use std::cell::Cell;

use super::GcMap;

struct Slot {
    key: Cell<u64>,
    value: Cell<Option<u32>>,
}

// Separate banks keep previous storage borrowed during rebuilding valid.
struct Storage {
    banks: [[Slot; 256]; 4],
    bank: Cell<usize>,
    len: Cell<usize>,
    used: Cell<usize>,
    fail: Cell<bool>,
}

impl Storage {
    fn new() -> Self {
        Self {
            banks: std::array::from_fn(|_| {
                std::array::from_fn(|_| Slot {
                    key: Cell::new(0),
                    value: Cell::new(None),
                })
            }),
            bank: Cell::new(0),
            len: Cell::new(0),
            used: Cell::new(0),
            fail: Cell::new(false),
        }
    }
}

impl GcMap<()> for Storage {
    type Entry = u32;
    type Error = &'static str;
    type Slot = Slot;

    fn slots<'a>(&'a self, _: &'a ()) -> &'a [Slot] {
        &self.banks[self.bank.get()][..self.len.get()]
    }

    fn replace<'a>(&'a self, _: &'a (), len: usize) -> Result<&'a [Slot], Self::Error> {
        let bank = self.bank.get() + 1;
        if self.fail.get() || bank >= self.banks.len() || len > 256 {
            return Err("storage full");
        }
        self.bank.set(bank);
        self.len.set(len);
        Ok(&self.banks[bank][..len])
    }

    fn key(&self, slot: &Slot) -> u64 {
        slot.key.get()
    }
    fn entry(&self, _: &(), slot: &Slot) -> Option<u32> {
        slot.value.get()
    }
    fn set(&self, _: &(), slot: &Slot, key: u64, entry: u32) {
        slot.key.set(key);
        slot.value.set(Some(entry));
    }
    fn used(&self) -> usize {
        self.used.get()
    }
    fn set_used(&self, _: &(), used: usize) {
        self.used.set(used);
    }
}

#[test]
fn non_string_entries_survive_collisions_growth_and_dead_slots() {
    let table = Storage::new();
    for value in 0..80 {
        assert_eq!(table.find_or_insert(&(), 2, |entry| Ok(entry == value), || Ok(value)), Ok(value));
    }
    assert_eq!(table.len.get(), 128);
    for value in 0..80 {
        assert_eq!(
            table.find_or_insert(&(), 2, |entry| Ok(entry == value), || panic!("duplicate")),
            Ok(value)
        );
    }
    table
        .slots(&())
        .iter()
        .find(|slot| slot.value.get() == Some(0))
        .expect("entry exists")
        .value
        .set(None);
    let used = table.used();
    assert_eq!(table.find_or_insert(&(), 2, |entry| Ok(entry == 99), || Ok(99)), Ok(99));
    assert_eq!(table.used(), used);
    assert_eq!(
        table.find_or_insert(&(), 2, |entry| Ok(entry == 79), || panic!("lost entry")),
        Ok(79)
    );
}

#[test]
fn errors_leave_existing_entries_reachable() {
    let table = Storage::new();
    table.fail.set(true);
    assert_eq!(table.find_or_insert(&(), 2, |_| Ok(false), || Ok(1)), Err("storage full"));
    assert_eq!(table.used(), 0);
    table.fail.set(false);
    assert_eq!(
        table.find_or_insert(&(), 2, |_| Ok(false), || Err("creation failed")),
        Err("creation failed")
    );
    assert_eq!(table.used(), 0);
    assert_eq!(table.find_or_insert(&(), 2, |_| Ok(false), || Ok(1)), Ok(1));
    assert_eq!(
        table.find_or_insert(&(), 2, |_| Err("comparison failed"), || panic!("must not create")),
        Err("comparison failed")
    );
    assert_eq!(table.find_or_insert(&(), 2, |entry| Ok(entry == 1), || panic!("lost entry")), Ok(1));
}
