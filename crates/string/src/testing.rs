use std::cell::{Cell, OnceCell};
use std::collections::HashSet;

use crate::*;

pub struct Rng(pub u64);

impl Rng {
    pub fn u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    pub fn below(&mut self, n: usize) -> usize {
        (self.u64() % n as u64) as usize
    }

    pub fn char(&mut self, widest: Width) -> char {
        let (lo, hi) = match (widest, self.below(4)) {
            (_, 0 | 1) => (0x20, 0x7F),
            (Width::One, _) => (0xA0, 0x100),
            (Width::Two, 2) => (0xA0, 0x100),
            (Width::Two, _) => (0x100, 0xD800),
            (Width::Four, 2) => (0x100, 0xD800),
            (Width::Four, _) => (0x1_0000, 0x11_0000),
        };
        char::from_u32(lo + self.below((hi - lo) as usize) as u32).expect("no surrogates")
    }

    /// Mostly short, sometimes long, each mostly ASCII with some characters up to a random width.
    pub fn text(&mut self) -> Vec<char> {
        let len = match self.below(10) {
            0 => 0,
            1..=6 => self.below(40),
            7 | 8 => self.below(600),
            _ => self.below(3000),
        };
        let widest = [Width::One, Width::Two, Width::Four][self.below(3)];
        (0..len).map(|_| self.char(widest)).collect()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct TestStr(usize);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TestError {
    Str(StrError),
}

impl From<StrError> for TestError {
    fn from(e: StrError) -> Self {
        Self::Str(e)
    }
}

enum Node {
    One(Box<[u8]>),
    Two(Box<[u16]>),
    Four(Box<[u32]>),
    Rope { left: TestStr, right: TestStr, info: u64, flat: Cell<Option<TestStr>>, reads: Cell<u64> },
    External(Box<dyn External>),
}

pub struct TestHost {
    nodes: Box<[OnceCell<Node>]>,
    used: Cell<usize>,
}

impl TestHost {
    pub fn new() -> Self {
        Self::with_capacity(1 << 18)
    }

    pub fn with_capacity(strings: usize) -> Self {
        Self { nodes: (0..strings).map(|_| OnceCell::new()).collect(), used: Cell::new(0) }
    }

    fn push(&self, node: Node) -> TestStr {
        let at = self.used.get();
        self.nodes.get(at).expect("test host is full").set(node).ok().expect("set once");
        self.used.set(at + 1);
        TestStr(at)
    }

    pub fn external(&self, chars: impl External) -> Result<TestStr, TestError> {
        check_external(chars.units())?;
        Ok(self.push(Node::External(Box::new(chars))))
    }

    /// Asserts every flat string in `s` has its narrowest width, and every rope node sums up its
    /// children, has no empty one, is balanced, and has the same characters as its flat copy.
    pub fn check(&self, s: TestStr) {
        let mut seen = HashSet::new();
        self.check_node(s, &mut seen);
    }

    fn check_node(&self, s: TestStr, seen: &mut HashSet<TestStr>) {
        if !seen.insert(s) {
            return;
        }
        match self.view(s) {
            StrView::Flat(u) => assert_eq!(u.width(), u.narrowest(), "flat strings are narrowest"),
            StrView::Rope { left, right, info, flat } => {
                if let Some(flat) = flat {
                    let StrView::Flat(units) = self.view(flat) else { panic!("a flat copy that's a rope") };
                    assert_eq!(units.width(), info.width);
                    let mut walk = Chunks::new(self, left, 0, crate::len(self, left)).chain(Chunks::new(self, right, 0, crate::len(self, right)));
                    let chars = walk.by_ref().flat_map(Units::chars);
                    assert!(chars.eq(units.chars()), "a flat copy with other characters");
                }
                let (l, r) = (crate::info(self, left), crate::info(self, right));
                assert!(l.len > 0 && r.len > 0, "empty child");
                assert_eq!(info.len, l.len + r.len);
                assert_eq!(info.width, l.width.max(r.width));
                assert_eq!(info.depth, l.depth.max(r.depth) + 1);
                assert!(l.depth.abs_diff(r.depth) <= 1, "unbalanced: {} and {}", l.depth, r.depth);
                self.check_node(left, seen);
                self.check_node(right, seen);
            }
        }
    }

    pub fn is_flattened(&self, s: TestStr) -> bool {
        matches!(self.nodes[s.0].get(), Some(Node::Rope { flat, .. }) if flat.get().is_some())
    }

    /// Flat strings in `s`, counting shared ones each time.
    pub fn leaves(&self, s: TestStr) -> usize {
        match self.view(s) {
            StrView::Flat(_) => 1,
            StrView::Rope { left, right, .. } => self.leaves(left) + self.leaves(right),
        }
    }
}

impl Host for TestHost {
    type Str = TestStr;
    type Error = TestError;

    fn view(&self, s: TestStr) -> StrView<'_, TestStr> {
        match self.nodes[s.0].get().expect("made by this host") {
            Node::One(u) => StrView::Flat(Units::One(u)),
            Node::Two(u) => StrView::Flat(Units::Two(u)),
            Node::Four(u) => StrView::Flat(Units::Four(u)),
            Node::Rope { left, right, info, flat, .. } => StrView::Rope { left: *left, right: *right, info: Info::from_bits(*info), flat: flat.get() },
            Node::External(chars) => StrView::Flat(chars.units()),
        }
    }

    fn flat(&self, width: Width, len: usize, init: impl FnOnce(UnitsMut<'_>)) -> Result<TestStr, TestError> {
        let node = match width {
            Width::One => {
                let mut u = vec![0; len];
                init(UnitsMut::One(&mut u));
                Node::One(u.into())
            }
            Width::Two => {
                let mut u = vec![0; len];
                init(UnitsMut::Two(&mut u));
                Node::Two(u.into())
            }
            Width::Four => {
                let mut u = vec![0; len];
                init(UnitsMut::Four(&mut u));
                Node::Four(u.into())
            }
        };
        Ok(self.push(node))
    }

    fn rope(&self, left: TestStr, right: TestStr, info: Info) -> Result<TestStr, TestError> {
        Ok(self.push(Node::Rope { left, right, info: info.to_bits(), flat: Cell::new(None), reads: Cell::new(0) }))
    }

    fn flattened(&self, rope: TestStr, flat: TestStr) {
        let Some(Node::Rope { flat: cache, .. }) = self.nodes[rope.0].get() else { panic!("not a rope") };
        assert!(cache.replace(Some(flat)).is_none(), "flattened twice");
    }

    fn count_read(&self, rope: TestStr) -> u64 {
        let Some(Node::Rope { reads, .. }) = self.nodes[rope.0].get() else { panic!("not a rope") };
        reads.set(reads.get() + 1);
        reads.get()
    }
}
