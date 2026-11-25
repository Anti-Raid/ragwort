use std::cell::{Cell, OnceCell};
use std::collections::HashSet;

use crate::*;

/// The range of characters that a random text draws from, named by the number of bytes that its widest characters took in a fixed-width string.
/// `One` is up to U+00FF, `Two` is up to U+FFFF, and `Four` is every character.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Width {
    One,
    Two,
    Four,
}

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

    /// Returns random text. Most texts are short and some are long. About half of the characters are ASCII, and the rest go up to a randomly chosen width.
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
    Slice(Box<[u8]>, usize),
    Packed { words: Box<[Cell<u64>]>, len: usize, chars: usize },
    Inline(Inline),
    Rope { left: TestStr, right: TestStr, info: Info, flat: Cell<Option<TestStr>>, reads: Cell<u64> },
    External(Box<dyn External>, usize),
}

pub struct TestHost {
    nodes: Box<[OnceCell<Node>]>,
    used: Cell<usize>,
    /// The number of flat strings created. It selects the layout: of every three flat strings, one is packed, one is inline if it fits, and one is stored in slices.
    flats: Cell<usize>,
}

impl TestHost {
    pub fn new() -> Self {
        Self::with_capacity(1 << 18)
    }

    pub fn with_capacity(strings: usize) -> Self {
        Self { nodes: (0..strings).map(|_| OnceCell::new()).collect(), used: Cell::new(0), flats: Cell::new(0) }
    }

    fn push(&self, node: Node) -> TestStr {
        let at = self.used.get();
        self.nodes.get(at).expect("test host is full").set(node).ok().expect("set once");
        self.used.set(at + 1);
        TestStr(at)
    }

    pub fn external(&self, text: impl External) -> Result<TestStr, TestError> {
        check_external(text.text())?;
        let chars = text.text().chars().count();
        Ok(self.push(Node::External(Box::new(text), chars)))
    }

    /// Asserts that every flat string in `s` is valid UTF-8 and has the number of characters that it reports. Also asserts that every rope node has an `Info` that matches
    /// its children, has no empty child, is balanced, and has the same bytes as its flat copy.
    pub fn check(&self, s: TestStr) {
        let mut seen = HashSet::new();
        self.check_node(s, &mut seen);
    }

    fn check_node(&self, s: TestStr, seen: &mut HashSet<TestStr>) {
        if !seen.insert(s) {
            return;
        }
        match self.view(s) {
            StrView::Flat { units, chars } => {
                let mut bytes = vec![0; units.len()];
                units.copy_to(&mut bytes);
                assert_eq!(std::str::from_utf8(&bytes).expect("a flat string is UTF-8").chars().count(), chars, "the number of characters");
                assert_eq!(units.count_chars(), chars);
            }
            StrView::Rope { left, right, info, flat } => {
                if let Some(flat) = flat {
                    let StrView::Flat { units, chars } = self.view(flat) else { panic!("a flat copy that's a rope") };
                    assert_eq!((units.len(), chars), (info.bytes, info.chars));
                    let mut walk = Chunks::new(self, left, 0, crate::byte_len(self, left)).chain(Chunks::new(self, right, 0, crate::byte_len(self, right)));
                    let chars = walk.by_ref().flat_map(Units::chars);
                    assert!(chars.eq(units.chars()), "a flat copy with other characters");
                }
                let (l, r) = (crate::info(self, left), crate::info(self, right));
                assert!(l.bytes > 0 && r.bytes > 0, "empty child");
                assert_eq!((info.bytes, info.chars), (l.bytes + r.bytes, l.chars + r.chars));
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

    /// Returns the number of flat strings in `s`. A shared flat string is counted once per occurrence.
    pub fn leaves(&self, s: TestStr) -> usize {
        match self.view(s) {
            StrView::Flat { .. } => 1,
            StrView::Rope { left, right, .. } => self.leaves(left) + self.leaves(right),
        }
    }
}

impl Host for TestHost {
    type Str = TestStr;
    type Error = TestError;

    fn view(&self, s: TestStr) -> StrView<'_, TestStr> {
        match self.nodes[s.0].get().expect("made by this host") {
            Node::Slice(bytes, chars) => StrView::Flat { units: Units::Slice(bytes), chars: *chars },
            Node::Packed { words, len, chars } => StrView::Flat { units: Units::Packed(Packed::new(words, *len)), chars: *chars },
            Node::Inline(inline) => StrView::Flat { units: Units::Inline(*inline), chars: inline.chars() },
            Node::Rope { left, right, info, flat, .. } => StrView::Rope { left: *left, right: *right, info: *info, flat: flat.get() },
            Node::External(text, chars) => StrView::Flat { units: Units::Slice(text.text().as_bytes()), chars: *chars },
        }
    }

    fn flat(&self, bytes: usize, chars: usize, init: impl FnOnce(UnitsMut<'_>)) -> Result<TestStr, TestError> {
        /// Asserts that the library wrote valid UTF-8 with the number of characters that it gave.
        fn checked(written: &[u8], chars: usize) {
            let text = std::str::from_utf8(written).expect("the library writes UTF-8");
            assert_eq!(text.chars().count(), chars, "the number of characters of {text:?}");
        }
        self.flats.set(self.flats.get() + 1);
        if self.flats.get() % 3 == 1 && bytes <= 8 {
            let inline = Inline::filled(bytes, init);
            checked(&inline.word().to_le_bytes()[..bytes], chars);
            return Ok(self.push(Node::Inline(inline)));
        }
        if self.flats.get().is_multiple_of(3) {
            let words: Box<[Cell<u64>]> = (0..bytes.div_ceil(8)).map(|_| Cell::new(0)).collect();
            init(UnitsMut::Packed(PackedMut::new(&words, bytes)));
            let mut written = vec![0; bytes];
            Units::Packed(Packed::new(&words, bytes)).copy_to(&mut written);
            checked(&written, chars);
            // Set the bits past the last byte, to check that readers ignore them.
            let used = bytes % 8 * 8;
            if let Some(last) = words.last().filter(|_| used > 0) {
                last.set(last.get() | u64::MAX << used);
            }
            return Ok(self.push(Node::Packed { words, len: bytes, chars }));
        }
        let mut written = vec![0; bytes];
        init(UnitsMut::Slice(&mut written));
        checked(&written, chars);
        Ok(self.push(Node::Slice(written.into(), chars)))
    }

    fn rope(&self, left: TestStr, right: TestStr, info: Info) -> Result<TestStr, TestError> {
        Ok(self.push(Node::Rope { left, right, info, flat: Cell::new(None), reads: Cell::new(0) }))
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

/// Returns `text` in several representations: flat, external, and, if it has two or more characters, as a rope of two flat strings
/// cut at `cut` and as the same kind of rope with a flat copy.
pub fn shapes(h: &TestHost, text: &[char], cut: usize) -> Vec<TestStr> {
    fn make(h: &TestHost, text: &[char]) -> TestStr {
        from_chars(h, text.iter().copied()).unwrap()
    }
    let mut out = vec![make(h, text), h.external(ExternalText::new(text.iter().collect::<String>())).unwrap()];
    if text.len() >= 2 {
        let cut = cut.clamp(1, text.len() - 1);
        for flattened in [false, true] {
            let (l, r) = (make(h, &text[..cut]), make(h, &text[cut..]));
            let (il, ir) = (crate::info(h, l), crate::info(h, r));
            let rope = h.rope(l, r, Info { bytes: il.bytes + ir.bytes, chars: il.chars + ir.chars, depth: 1 }).unwrap();
            if flattened {
                flatten(h, rope).unwrap();
            }
            out.push(rope);
        }
    }
    out
}
