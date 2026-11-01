use std::cell::{Cell, RefCell};
use std::collections::HashSet;

use super::*;
use crate::testing::*;
use crate::{ExternalText, concat, display, is_flat};

thread_local! {
    /// The bits of a hash [`probe_hash`] keeps.
    pub(super) static KEY_BITS: Cell<u64> = const { Cell::new(u64::MAX) };
}

/// Symbols are indexes into `symbols`, and die when killed. Entries are found by a scan, which
/// is all interning needs of a table: probing is the host's.
struct TestTable {
    seed: u64,
    entries: RefCell<Vec<(u64, usize)>>,
    symbols: RefCell<Vec<(TestStr, u64, bool)>>,
}

impl TestTable {
    fn new(seed: u64) -> Self {
        Self { seed, entries: RefCell::new(Vec::new()), symbols: RefCell::new(Vec::new()) }
    }

    fn kill(&self, symbol: usize) {
        self.symbols.borrow_mut()[symbol].2 = false;
    }

    fn hash_of(&self, symbol: usize) -> u64 {
        self.symbols.borrow()[symbol].1
    }
}

impl Table<TestHost> for TestTable {
    type Entry = usize;

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

    fn find_or_insert(
        &self,
        _: &TestHost,
        hash: u64,
        same: impl Fn(usize) -> Result<bool, TestError>,
        make: impl FnOnce() -> Result<usize, TestError>,
    ) -> Result<usize, TestError> {
        let candidates: Vec<usize> = self.entries.borrow().iter().filter(|e| e.0 == hash).map(|e| e.1).collect();
        for symbol in candidates {
            if self.symbols.borrow()[symbol].2 && same(symbol)? {
                return Ok(symbol);
            }
        }
        let symbol = make()?;
        self.entries.borrow_mut().push((hash, symbol));
        Ok(symbol)
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
