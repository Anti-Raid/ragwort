//! Space in the region: free lines for small objects, page runs for large ones, and giving
//! pages back.

use std::cell::Cell;
#[cfg(test)]
use std::cell::RefCell;
use std::ptr::NonNull;

use crate::layout::{GRANULE, LINE, LINES, MAX_PAGES, MAX_SMALL, PAGE};
use crate::region::{self, Region};
use crate::OutOfMemory;
use super::pages::{CANDIDATE, Kind, LINE_WORDS, META, PageIndex, SWEPT, WARM, YOUNG};
use super::Heap;

/// The region, and what the allocator knows of its pages besides the page table.
pub(super) struct Space {
    region: Region,
    /// The current free-line run: next free byte and end, as region offsets.
    bump: Cell<(usize, usize)>,
    /// A separate run, on a fresh page, for objects bigger than a line that don't fit `bump`.
    overflow: Cell<(usize, usize)>,
    /// Where the allocator next looks for a page with free lines.
    scan: Cell<PageIndex>,
    committed: Cell<usize>,
    free_pages: Cell<usize>,
    /// Pages that are [`WARM`], in the table or past its end.
    warm: Cell<usize>,
    #[cfg(test)]
    used_pages: RefCell<Vec<bool>>,
}

impl Space {
    pub(super) fn new() -> Option<Self> {
        Some(Self {
            region: Region::new()?,
            bump: Cell::new((0, 0)),
            overflow: Cell::new((0, 0)),
            scan: Cell::new(PageIndex::FIRST),
            committed: Cell::new(0),
            free_pages: Cell::new(0),
            warm: Cell::new(0),
            #[cfg(test)]
            used_pages: RefCell::new(vec![false; MAX_PAGES]),
        })
    }

    pub(super) fn base(&self) -> NonNull<u8> {
        self.region.base()
    }
}

impl Heap {
    pub(super) fn reset_allocators(&self) {
        self.retire(self.space.bump.replace((0, 0)));
        self.retire(self.space.overflow.replace((0, 0)));
        self.rescan();
    }

    /// Has the allocator look for free lines from the first page again.
    pub(super) fn rescan(&self) {
        self.space.scan.set(PageIndex::FIRST);
    }

    /// Frees the whole lines an allocation run didn't reach. Runs claim all their lines up
    /// front, so otherwise those lines would stay used until the page is swept.
    fn retire(&self, (next, end): (usize, usize)) {
        let first = next.next_multiple_of(LINE);
        if first >= end {
            return;
        }
        let Some(page) = self.page_of(first) else { return };
        let start = page.start();
        self.page(page).used.clear_range((first - start) / LINE, (end - start) / LINE);
    }

    /// Claims the first run of free lines at or after `from` in `page`.
    fn claim_hole(&self, page: PageIndex, from: usize) -> Option<(usize, usize)> {
        let p = self.page(page);
        let first = (from..LINES).find(|&l| !p.used.get(l))?;
        let end = (first..LINES).find(|&l| p.used.get(l)).unwrap_or(LINES);
        p.used.set_range(first, end);
        p.add(YOUNG);
        Some((page.start() + first * LINE, page.start() + end * LINE))
    }

    /// The next page with free lines the allocator may use.
    fn reusable(&self) -> Option<PageIndex> {
        let sweeping = self.is_sweeping();
        while self.in_table(self.space.scan.get()) {
            let page = self.space.scan.get();
            self.space.scan.set(page.plus(1));
            let p = self.page(page);
            let ready = !sweeping || p.has(SWEPT);
            if p.kind.get() == Kind::Lines && ready && !p.has(CANDIDATE) && !p.used.is_full() {
                return Some(page);
            }
        }
        None
    }

    fn fresh_page(&self) -> Result<PageIndex, OutOfMemory> {
        let page = self.new_pages(1)?;
        let p = self.page(page);
        p.kind.set(Kind::Lines);
        p.flags.set(YOUNG | SWEPT);
        p.used.store([!0; LINE_WORDS]);
        Ok(page)
    }

    #[inline(never)]
    fn reserve_slow(&self, size: usize) -> Result<usize, OutOfMemory> {
        if size <= MAX_SMALL { self.reserve_small(size) } else { self.reserve_large(size) }
    }

    fn reserve_small(&self, size: usize) -> Result<usize, OutOfMemory> {
        loop {
            let (next, end) = self.space.bump.get();
            if next + size <= end {
                self.space.bump.set((next + size, end));
                return Ok(next);
            }
            if size > LINE {
                let (next, end) = self.space.overflow.get();
                if next + size <= end {
                    self.space.overflow.set((next + size, end));
                    return Ok(next);
                }
                let page = self.fresh_page()?;
                self.retire(self.space.overflow.replace((page.start(), page.start() + PAGE)));
                continue;
            }
            if end % PAGE != 0
                && let Some(page) = PageIndex::containing(end)
                && let Some(hole) = self.claim_hole(page, end % PAGE / LINE)
            {
                self.retire(self.space.bump.replace(hole));
                continue;
            }
            let hole = match self.reusable() {
                Some(page) => self.claim_hole(page, 0).expect("page has a free line"),
                None => {
                    let page = self.fresh_page()?;
                    (page.start(), page.start() + PAGE)
                }
            };
            self.retire(self.space.bump.replace(hole));
        }
    }

    fn reserve_large(&self, size: usize) -> Result<usize, OutOfMemory> {
        let n = size.div_ceil(PAGE);
        if n > MAX_PAGES {
            return Err(self.budget.fail());
        }
        let page = self.new_pages(n)?;
        let head = self.page(page);
        head.kind.set(Kind::Large(n as u32));
        head.flags.set(YOUNG | SWEPT);
        for p in self.run(page.plus(1), n - 1) {
            p.kind.set(Kind::tail_of(page));
        }
        Ok(page.start())
    }

    /// Reserves `size` bytes and records an object starting there.
    #[inline]
    pub(super) fn reserve(&self, size: usize) -> Result<u32, OutOfMemory> {
        let (next, end) = self.space.bump.get();
        let offset = if size <= MAX_SMALL && next + size <= end {
            self.space.bump.set((next + size, end));
            next
        } else {
            self.reserve_slow(size)?
        };
        let page = self.page_of(offset).expect("reserved outside the page table");
        self.page(page).start.set(offset % PAGE / GRANULE);
        self.stats.objects.set(self.stats.objects.get() + 1);
        Ok(offset as u32)
    }

    /// Finds or appends a run of `n` free pages and charges for it.
    fn new_pages(&self, n: usize) -> Result<PageIndex, OutOfMemory> {
        let pages = self.pages();
        let mut run = 0;
        let mut start = None;
        if n == 1 && self.space.warm.get() > 0 {
            // Trimming can leave warm pages past the end, above pages that were given back.
            // The count says one exists, so the search stops there.
            start = self.pages.table().iter().position(|p| p.has(WARM));
        }
        if start.is_some() {
        } else if self.space.free_pages.get() >= n {
            for (i, p) in pages.iter().enumerate() {
                if p.kind.get() != Kind::Free {
                    run = 0;
                    continue;
                }
                run += 1;
                if run == n {
                    start = Some(i + 1 - n);
                    break;
                }
            }
        } else {
            run = pages.iter().rev().take_while(|p| p.kind.get() == Kind::Free).count();
        }
        let start = start.unwrap_or(pages.len() - run);
        let len = (start + n).max(pages.len());
        if len > MAX_PAGES {
            return Err(self.budget.fail());
        }
        let grow = len - pages.len();
        self.budget.charge(n * PAGE + grow * META)?;
        for p in &self.pages.table()[start..start + n] {
            if p.has(WARM) {
                p.remove(WARM);
                self.space.warm.set(self.space.warm.get() - 1);
            }
        }
        self.pages.set_count(len);
        #[cfg(test)]
        self.space.used_pages.borrow_mut()[start..start + n].fill(true);
        self.space.committed.set(self.space.committed.get() + n);
        // Pages between the old end and a warm page past it join the table free.
        self.space.free_pages.set(self.space.free_pages.get() + grow - n);
        Ok(PageIndex::at(start))
    }

    pub(super) fn free_run(&self, page: PageIndex, n: usize) {
        for run in [&self.space.bump, &self.space.overflow] {
            let (_, end) = run.get();
            if end != 0 && PageIndex::containing(end - 1).is_some_and(|p| (page..page.plus(n)).contains(&p)) {
                run.set((0, 0));
            }
        }
        for p in self.run(page, n) {
            p.reset();
        }
        self.budget.refund(n * PAGE);
        self.space.committed.set(self.space.committed.get() - n);
        self.space.free_pages.set(self.space.free_pages.get() + n);
        // Young pages empty out every minor collection and fill again right after, so about a
        // nursery's worth stays committed. Giving them back would fault on every reuse.
        match region::os_page() {
            Some(os_page) if os_page > PAGE => self.settle_os_pages(page, n, os_page),
            os_page => {
                let keep = n.min(self.warm_limit().saturating_sub(self.space.warm.get()));
                for p in self.run(page, keep) {
                    p.add(WARM);
                }
                self.space.warm.set(self.space.warm.get() + keep);
                if let Some(os_page) = os_page
                    && keep < n
                {
                    let (lo, hi) = (page.plus(keep).start(), page.plus(n).start());
                    self.decommit(lo.next_multiple_of(os_page), hi / os_page * os_page);
                }
            }
        }
        self.trim();
    }

    /// When an OS page holds several of ours, it's warm or given back as a whole once nothing
    /// on it is live. A free page that shares an OS page with live ones isn't warm: its memory
    /// stays committed either way.
    fn settle_os_pages(&self, page: PageIndex, n: usize, os_page: usize) {
        for os in page.start() / os_page..page.plus(n).start().div_ceil(os_page) {
            let (from, to) = PageIndex::overlapping(os * os_page, (os + 1) * os_page);
            let pages = self.table_pages(from, to);
            if pages.iter().any(|p| p.kind.get() != Kind::Free) {
                continue;
            }
            let warm = pages.iter().filter(|p| p.has(WARM)).count();
            if self.space.warm.get() + pages.len() - warm <= self.warm_limit() {
                for p in pages {
                    p.add(WARM);
                }
                self.space.warm.set(self.space.warm.get() + pages.len() - warm);
            } else {
                for p in pages {
                    p.remove(WARM);
                }
                self.space.warm.set(self.space.warm.get() - warm);
                self.decommit(os * os_page, (os + 1) * os_page);
            }
        }
    }

    /// How many free pages stay committed: the memory of one nursery, beyond the budget.
    pub(super) fn warm_limit(&self) -> usize {
        self.nursery() / PAGE
    }

    fn trim(&self) {
        let before = self.page_count();
        let len = before - self.pages().iter().rev().take_while(|p| p.kind.get() == Kind::Free).count();
        self.pages.set_count(len);
        self.budget.refund((before - len) * META);
        self.space.free_pages.set(self.space.free_pages.get() - (before - len));
        self.space.scan.set(self.space.scan.get().min(PageIndex::at(len)));
        self.clamp_cursor(len);
    }

    /// Gives back the OS pages in `lo..hi`, offsets on OS page boundaries.
    fn decommit(&self, lo: usize, hi: usize) {
        if lo >= hi {
            return;
        }
        #[cfg(test)]
        self.check_decommit(lo, hi);
        self.space.region.decommit(lo, hi - lo);
    }

    /// Each OS page given back must be free and must have been used since it was last given back.
    #[cfg(test)]
    fn check_decommit(&self, lo: usize, hi: usize) {
        let os_page = region::os_page().unwrap();
        let pages = self.pages();
        let mut used = self.space.used_pages.borrow_mut();
        for os in (lo..hi).step_by(os_page) {
            let (from, to) = PageIndex::overlapping(os, os + os_page);
            assert!(from.upto(to).any(|p| used[p.slot()]), "OS page at {os:#x} was already decommitted");
            for p in from.upto(to) {
                let free = pages.get(p.slot()).is_none_or(|p| p.kind.get() == Kind::Free);
                assert!(free, "decommitting live page {p:?}");
            }
        }
        let (from, to) = PageIndex::overlapping(lo, hi);
        used[from.slot()..to.slot()].fill(false);
    }

    /// Undoes `reserve` for an object that was never finished.
    pub(super) fn release(&self, offset: u32) {
        let Some(obj) = self.object_at(offset) else { return };
        self.clear_header(offset);
        let p = self.page(obj.page);
        p.start.clear(obj.granule);
        p.mark.clear(obj.granule);
        self.stats.objects.set(self.stats.objects.get() - 1);
        match p.kind.get() {
            Kind::Lines if p.start.is_empty() => self.free_run(obj.page, 1),
            Kind::Large(n) => self.free_run(obj.page, n as usize),
            _ => {}
        }
    }

    /// Checks the allocation runs, and the counts of `committed` pages, `free` ones and `warm`
    /// ones in the table, against the pages.
    #[cfg(test)]
    pub(super) fn check_space(&self, committed: usize, free: usize, warm: usize) {
        let pages = self.pages();
        for (next, end) in [self.space.bump.get(), self.space.overflow.get()] {
            if end != 0 {
                let page = self.page_of(end - 1).expect("allocation run outside the pages");
                let p = self.page(page);
                assert_eq!(p.kind.get(), Kind::Lines, "allocation run on a page that isn't for lines");
                assert!(!p.has(CANDIDATE), "allocation run on a page being compacted");
                for line in next % PAGE / LINE..(end - 1) % PAGE / LINE + 1 {
                    assert!(p.used.get(line), "allocation run on a free line");
                }
            }
        }
        assert_eq!(committed, self.space.committed.get(), "committed pages");
        let warm = warm + self.pages.table()[pages.len()..].iter().filter(|p| p.has(WARM)).count();
        assert_eq!(warm, self.space.warm.get(), "warm pages");
        assert!(warm <= self.warm_limit(), "too many warm pages");
        assert!(pages.iter().all(|p| !p.has(WARM) || p.kind.get() == Kind::Free), "warm pages are free");
        assert_eq!(free, self.space.free_pages.get(), "free pages");
    }

    pub(crate) fn committed(&self) -> usize {
        self.space.committed.get()
    }

    /// How many free pages are kept committed, and how many may be.
    #[cfg(test)]
    pub(crate) fn warm_pages(&self) -> (usize, usize) {
        (self.space.warm.get(), self.warm_limit())
    }

    /// Free pages that aren't warm but are still committed, on OS pages with nothing live,
    /// so they take memory the warm count doesn't know about.
    #[cfg(test)]
    pub(crate) fn stranded_pages(&self) -> usize {
        let Some(os_page) = region::os_page() else { return 0 };
        let used = self.space.used_pages.borrow();
        let free = |p: PageIndex| self.pages.table().get(p.slot()).is_none_or(|p| p.kind.get() == Kind::Free);
        let os_page_free = |p: PageIndex| {
            let at = p.start() / os_page * os_page;
            let (from, to) = PageIndex::overlapping(at, at + os_page);
            from.upto(to).all(free)
        };
        let all = PageIndex::FIRST.upto(PageIndex::at(MAX_PAGES));
        all.filter(|&p| used[p.slot()] && free(p) && !self.page(p).has(WARM) && os_page_free(p)).count()
    }

    #[cfg(test)]
    pub(crate) fn used_lines(&self) -> usize {
        self.pages().iter().filter(|p| p.kind.get() == Kind::Lines).map(|p| p.used.count()).sum()
    }
}
