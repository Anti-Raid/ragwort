//! Tests' check that every counter and bitmap agrees with the pages.

use crate::layout::{GRANULE, LINE, LINES, PAGE, WORDS};
use crate::root::ROOT_COST;
use crate::Phase;
use super::mark::GRAY_BYTES;
use super::pages::{CANDIDATE, Kind, META, OVERFLOW, PENDING, PageIndex, WARM, YOUNG, each_bit};
use super::Heap;

impl Heap {
    /// Checks every counter and bitmap against the pages. Panics on any mismatch.
    pub(crate) fn check(&self) {
        let pages = self.pages();
        let idle = self.phase() == Phase::Idle;
        let (mut objects, mut committed, mut free, mut warm) = (0, 0, 0, 0);
        let mut i = 0;
        while i < pages.len() {
            let (page, p) = (PageIndex::at(i), &pages[i]);
            assert!(!p.has(OVERFLOW | PENDING | CANDIDATE) || self.is_marking(), "page {i} has marking flags");
            assert!(!p.has(CANDIDATE) || self.is_evacuating(), "page {i} is a candidate outside compaction");
            match p.kind.get() {
                Kind::Free => {
                    let empty = p.start.is_empty() && p.mark.is_empty() && p.used.is_empty() && p.marked_lines.is_empty();
                    assert!(p.flags.get() & !WARM == 0 && p.cards.get() == 0 && empty, "free page {i} isn't reset");
                    free += 1;
                    warm += p.has(WARM) as usize;
                }
                Kind::Lines => {
                    committed += 1;
                    let mut end = 0;
                    each_bit(&p.start.load(), |g| {
                        let offset = page.granule(g);
                        let obj = self.object_at(offset).unwrap();
                        let (_, size) = self.size_of(obj).unwrap_or_else(|| panic!("bad object {offset:#x}"));
                        assert!(g * GRANULE >= end, "objects overlap at {offset:#x}");
                        end = g * GRANULE + size;
                        for line in g * GRANULE / LINE..end.div_ceil(LINE) {
                            assert!(p.used.get(line), "object {offset:#x} sits on a free line");
                            if p.mark.get(g) {
                                assert!(p.marked_lines.get(line), "marked object {offset:#x} on an unmarked line");
                            }
                        }
                        objects += 1;
                    });
                    for line in 0..LINES {
                        assert!(!p.marked_lines.get(line) || p.used.get(line), "page {i} line {line} marked but free");
                    }
                    for (m, s) in p.mark.load().iter().zip(p.start.load()) {
                        assert_eq!(m & !s, 0, "page {i} marks a granule with no object");
                    }
                    if idle && !p.has(YOUNG) {
                        assert_eq!(p.start.load(), p.mark.load(), "page {i} has unmarked objects but isn't young");
                    }
                }
                Kind::Large(n) => {
                    let n = n as usize;
                    let mut first = [0; WORDS];
                    first[0] = 1;
                    assert_eq!(p.start.load(), first, "large page {i}");
                    for (j, tail) in self.run(page.plus(1), n - 1).iter().enumerate() {
                        assert_eq!(tail.kind.get(), Kind::tail_of(page), "page {} should be a tail of {i}", i + 1 + j);
                        assert!(tail.start.is_empty(), "tail page {} has object starts", i + 1 + j);
                    }
                    if idle && !p.has(YOUNG) {
                        assert!(p.mark.get(0), "large page {i} is unmarked but isn't young");
                    }
                    objects += 1;
                    committed += n;
                    i += n;
                    continue;
                }
                Kind::Tail(head) => panic!("page {i} is an orphan tail of {head}"),
            }
            i += 1;
        }
        self.check_space(committed, free, warm);
        assert_eq!(objects, self.stats.objects.get(), "object count");
        assert!(self.gray_is_empty() || self.is_marking(), "gray objects outside marking");
        let (roots, stacks) = (self.roots.borrow(), self.stacks.borrow());
        let tables = pages.len() * META + roots.charged() + stacks.charged() + self.hosts.charged();
        let expected = committed * PAGE + (roots.len() + stacks.len()) * ROOT_COST + tables + GRAY_BYTES;
        assert_eq!(self.budget.used(), expected, "budget");
        assert!(self.budget.used() <= self.budget.limit());
    }
}
