use std::cell::{Cell, RefCell};
use std::collections::HashSet;

use super::*;
use crate::testing::*;
use crate::{ExternalText, concat, display, is_flat};

thread_local! {
    /// The bits of a hash [`probe_hash`] keeps.
    pub(super) static KEY_BITS: Cell<u64> = const { Cell::new(u64::MAX) };
}

struct Slot {
    key: Cell<u64>,
    symbol: Cell<Option<usize>>,
}

/// Symbols are indexes into `symbols`, and die when killed. Old slots are leaked, so they
/// stay readable.
struct TestTable {
    seed: u64,
    slots: Cell<&'static [Slot]>,
    used: Cell<usize>,
    symbols: RefCell<Vec<(TestStr, u64, bool)>>,
}

impl TestTable {
    fn new(seed: u64) -> Self {
        Self { seed, slots: Cell::new(&[]), used: Cell::new(0), symbols: RefCell::new(Vec::new()) }
    }

    fn kill(&self, symbol: usize) {
        self.symbols.borrow_mut()[symbol].2 = false;
    }

    fn hash_of(&self, symbol: usize) -> u64 {
        self.symbols.borrow()[symbol].1
    }
}

impl GcMap<TestHost> for TestTable {
    type Entry = usize;
    type Error = TestError;
    type Slot = Slot;

    fn slots<'a>(&'a self, _: &'a TestHost) -> &'a [Slot] {
        self.slots.get()
    }

    fn replace<'a>(&'a self, _: &'a TestHost, len: usize) -> Result<&'a [Slot], TestError> {
        let slots = Vec::from_iter((0..len).map(|_| Slot { key: Cell::new(0), symbol: Cell::new(None) })).leak();
        self.slots.set(slots);
        Ok(slots)
    }

    fn key(&self, slot: &Slot) -> u64 {
        slot.key.get()
    }

    fn entry(&self, _: &TestHost, slot: &Slot) -> Option<usize> {
        slot.symbol.get().filter(|&i| self.symbols.borrow()[i].2)
    }

    fn set(&self, _: &TestHost, slot: &Slot, key: u64, symbol: usize) {
        slot.key.set(key);
        slot.symbol.set(Some(symbol));
    }

    fn used(&self) -> usize {
        self.used.get()
    }

    fn set_used(&self, _: &TestHost, used: usize) {
        self.used.set(used);
    }

}

impl Table<TestHost> for TestTable {
    fn seed(&self) -> u64 {
        self.seed
    }

    fn make(&self, h: &TestHost, name: TestStr, hash: u64) -> Result<usize, TestError> {
        assert!(is_flat(h, name), "names are flat");
        let mut symbols = self.symbols.borrow_mut();
        symbols.push((name, hash, true));
        Ok(symbols.len() - 1)
    }

    fn name(&self, _: &TestHost, symbol: usize) -> TestStr {
        self.symbols.borrow()[symbol].0
    }
}

fn names(n: usize) -> Vec<String> {
    (0..n).map(|i| format!("name {i} {}", ["", "é", "日本", "😀"][i % 4])).collect()
}

/// However its name is held, a name has one symbol, made with a flat copy of the name and
/// its hash.
#[test]
fn one_symbol_per_name() {
    let h = TestHost::new();
    let table = TestTable::new(1);
    for text in ["content", "", "café", "日本語", "😀", &"long name ".repeat(300)] {
        let half = (0..=text.len() / 2).rev().find(|&i| text.is_char_boundary(i)).unwrap();
        let rope = concat(&h, from_str(&h, &text[..half]).unwrap(), from_str(&h, &text[half..]).unwrap()).unwrap();
        let external = h.external(ExternalText::new(String::from(text))).unwrap();
        let first = intern(&h, &table, rope).unwrap();
        for s in [from_str(&h, text).unwrap(), rope, external] {
            assert_eq!(intern(&h, &table, s), Ok(first), "{text:?}");
        }
        assert_eq!(intern_str(&h, &table, text), Ok(first));
        assert_eq!(display(&h, table.name(&h, first)).to_string(), text);
        assert_eq!(table.hash_of(first), hash_str(text, table.seed));
    }
    let all: Vec<_> = names(500).iter().map(|n| intern_str(&h, &table, n).unwrap()).collect();
    assert_eq!(all.iter().collect::<HashSet<_>>().len(), all.len());
}

/// Names whose keys are the same are told apart by their characters, a live symbol is found
/// past dead ones with its key, and a dead one's name gets a new symbol.
#[test]
fn names_sharing_a_key_stay_apart() {
    for bits in [0, 0b110, 0xFF, u64::MAX] {
        KEY_BITS.set(bits);
        let h = TestHost::new();
        let table = TestTable::new(1);
        let names = names(400);
        let first: Vec<_> = names.iter().map(|n| intern_str(&h, &table, n).unwrap()).collect();
        for (i, &s) in first.iter().enumerate() {
            if i % 3 != 2 {
                table.kill(s);
            }
        }
        for (i, n) in names.iter().enumerate() {
            let s = intern_str(&h, &table, n).unwrap();
            match i % 3 {
                2 => assert_eq!(s, first[i], "{bits:#x}: {n}"),
                _ => assert!(s > *first.last().unwrap(), "{bits:#x}: {n} kept a dead symbol"),
            }
            assert_eq!(intern(&h, &table, table.name(&h, s)), Ok(s));
        }
        let fresh: HashSet<_> = names.iter().map(|n| intern_str(&h, &table, n).unwrap()).collect();
        assert_eq!(fresh.len(), names.len());
    }
    KEY_BITS.set(u64::MAX);
}

/// Names made and killed over and over don't grow the table past what the live ones need, and
/// dead slots are reused.
#[test]
fn churn_leaves_the_table_small() {
    let h = TestHost::new();
    let table = TestTable::new(2);
    let kept: Vec<_> = names(100).iter().map(|n| intern_str(&h, &table, n).unwrap()).collect();
    for round in 0..30 {
        for i in 0..500 {
            let s = intern_str(&h, &table, &format!("round {round} message {i}")).unwrap();
            table.kill(s);
        }
        assert!(table.slots(&h).len() <= 1024, "{} slots", table.slots(&h).len());
        assert!(table.used() * 4 <= table.slots(&h).len() * 3);
    }
    for (n, s) in names(100).iter().zip(kept) {
        assert_eq!(intern_str(&h, &table, n), Ok(s));
    }
}

/// Every live symbol is found where a probe from its home reaches it, after any growth.
#[test]
fn growth_keeps_every_symbol() {
    let h = TestHost::new();
    let table = TestTable::new(3);
    let names = names(5000);
    let made: Vec<_> = names.iter().map(|n| intern_str(&h, &table, n).unwrap()).collect();
    let slots = table.slots(&h);
    assert!(slots.len().is_power_of_two() && table.used() * 4 <= slots.len() * 3);
    assert_eq!(table.used(), slots.iter().filter(|s| s.key.get() != 0).count());
    for (n, s) in names.iter().zip(made) {
        assert_eq!(intern_str(&h, &table, n), Ok(s));
    }
}

/// A name whose symbol died takes its old slot back, so interning it again and again neither
/// counts new slots nor rebuilds the table.
#[test]
fn a_dead_name_takes_its_slot_back() {
    let h = TestHost::new();
    let table = TestTable::new(4);
    for n in names(40) {
        intern_str(&h, &table, &n).unwrap();
    }
    let (used, slots) = (table.used(), table.slots(&h).as_ptr());
    for _ in 0..1000 {
        let s = intern_str(&h, &table, "comes and goes").unwrap();
        table.kill(s);
    }
    assert_eq!(table.used(), used + 1);
    assert_eq!(table.slots(&h).as_ptr(), slots, "rebuilt");
}
