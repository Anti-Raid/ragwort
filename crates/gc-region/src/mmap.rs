#![allow(unsafe_code)]

use std::cell::Cell;
use std::ops::Range;
use std::sync::OnceLock;

use memmap2::{MmapOptions, MmapRaw};

pub(crate) struct Backing {
    map: MmapRaw,
    len: usize,
}

impl Backing {
    pub(crate) fn new(len: usize) -> Option<Self> {
        let bytes = len.checked_mul(8)?.max(8);
        let map = MmapRaw::from(MmapOptions::new().len(bytes).map_anon().ok()?);
        Some(Self { map, len })
    }

    pub(crate) fn len(&self) -> usize {
        self.len
    }

    #[inline]
    pub(crate) fn words(&mut self) -> &[Cell<u64>] {
        // SAFETY: the mapping is `len` words, aligned to an OS page, zeroed, readable and
        // writable, and lives as long as `self`. Any bits are a `u64`, and `Cell` makes writes
        // through the shared view sound.
        unsafe { std::slice::from_raw_parts(self.map.as_mut_ptr().cast::<Cell<u64>>(), self.len) }
    }

    pub(crate) fn release(&mut self, range: Range<usize>) {
        let Some(page) = os_page() else { return };
        let lo = (range.start.min(self.len) * 8).next_multiple_of(page);
        let hi = range.end.min(self.len) * 8 / page * page;
        if lo >= hi {
            return;
        }
        self.free_pages(lo, hi - lo);
    }

    /// Frees the pages now, leaving zeroed ones in their place.
    #[cfg(not(target_vendor = "apple"))]
    fn free_pages(&mut self, offset: usize, len: usize) {
        // SAFETY: `&mut self` means no view of the words is alive. The pages stay mapped and
        // read back as zero, or as they were if the advice fails; `u64`s either way.
        let _ = unsafe { self.map.unchecked_advise_range(memmap2::UncheckedAdvice::DontNeed, offset, len) };
    }

    /// macOS keeps anonymous pages after `DontNeed`, and pages marked reusable need another
    /// call before they're written again, so fresh zeroed pages are mapped over them instead.
    #[cfg(target_vendor = "apple")]
    fn free_pages(&mut self, offset: usize, len: usize) {
        let at = self.map.as_mut_ptr().wrapping_add(offset);
        let flags = libc::MAP_PRIVATE | libc::MAP_ANON | libc::MAP_FIXED;
        // SAFETY: `&mut self` means no view of the words is alive, and the range is whole OS
        // pages inside the mapping, replaced by zeroed pages with the same access.
        let mapped = unsafe { libc::mmap(at.cast(), len, libc::PROT_READ | libc::PROT_WRITE, flags, -1, 0) };
        if mapped != at.cast() {
            // A failed fixed mapping may have unmapped the range, and the words must stay
            // readable.
            std::process::abort();
        }
    }

    pub(crate) fn releases() -> bool {
        os_page().is_some()
    }
}

fn os_page() -> Option<usize> {
    static PAGE: OnceLock<Option<usize>> = OnceLock::new();
    *PAGE.get_or_init(|| {
        // SAFETY: `sysconf` only reads a system setting.
        let size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
        usize::try_from(size).ok().filter(|s| s.is_power_of_two() && *s >= 8)
    })
}

/// Bytes the process holds as the system counts them: the physical footprint on macOS, which
/// leaves out pages marked reusable, and the resident set elsewhere.
#[cfg(test)]
pub(crate) fn held_bytes() -> usize {
    #[cfg(target_vendor = "apple")]
    {
        let mut info = std::mem::MaybeUninit::<libc::rusage_info_v2>::zeroed();
        // SAFETY: the buffer is a `rusage_info_v2`, the struct this flavor fills in.
        let ok = unsafe {
            libc::proc_pid_rusage(std::process::id() as i32, libc::RUSAGE_INFO_V2, info.as_mut_ptr().cast())
        };
        assert_eq!(ok, 0, "proc_pid_rusage failed");
        // SAFETY: the call succeeded, so it filled the struct in, and it was zeroed before.
        unsafe { info.assume_init() }.ri_phys_footprint as usize
    }
    #[cfg(not(target_vendor = "apple"))]
    {
        let statm = std::fs::read_to_string("/proc/self/statm").expect("read statm");
        let pages: usize = statm.split_whitespace().nth(1).and_then(|n| n.parse().ok()).expect("statm");
        pages * os_page().expect("page size")
    }
}
