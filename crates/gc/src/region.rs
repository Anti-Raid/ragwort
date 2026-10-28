use std::ptr::NonNull;
use std::sync::OnceLock;

use super::layout::RESERVE;

/// The OS page size. Decommits use whole OS pages only; `None` disables them.
pub(crate) fn os_page() -> Option<usize> {
    #[cfg(test)]
    if let Some(size) = test_os_page::get() {
        return size;
    }
    static OS_PAGE: OnceLock<Option<usize>> = OnceLock::new();
    *OS_PAGE.get_or_init(Backing::os_page)
}

pub(crate) struct Region {
    base: NonNull<u8>,
    backing: Backing,
}

impl Region {
    pub(crate) fn new() -> Option<Self> {
        let (backing, base) = Backing::new()?;
        Some(Self { base, backing })
    }

    pub(crate) fn base(&self) -> NonNull<u8> {
        self.base
    }

    /// `offset` and `len` must be whole OS pages holding no live objects.
    pub(crate) fn decommit(&self, offset: usize, len: usize) {
        self.backing.decommit(offset, len);
    }
}

#[cfg(all(feature = "mmap", not(miri)))]
struct Backing(memmap2::MmapRaw);

#[cfg(all(feature = "mmap", not(miri)))]
impl Backing {
    fn new() -> Option<(Self, NonNull<u8>)> {
        let map = memmap2::MmapRaw::from(memmap2::MmapOptions::new().len(RESERVE).map_anon().ok()?);
        let base = NonNull::new(map.as_mut_ptr())?;
        Some((Self(map), base))
    }

    #[cfg(unix)]
    fn os_page() -> Option<usize> {
        // SAFETY: `sysconf` only reads a system setting.
        let size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
        usize::try_from(size).ok().filter(|s| s.is_power_of_two())
    }

    #[cfg(not(unix))]
    fn os_page() -> Option<usize> {
        None
    }

    fn decommit(&self, offset: usize, len: usize) {
        #[cfg(unix)]
        // SAFETY: nothing lives in the range, and nothing relies on what reads back from it.
        unsafe {
            let _ = self.0.unchecked_advise_range(memmap2::UncheckedAdvice::DontNeed, offset, len);
        }
        #[cfg(not(unix))]
        let _ = (offset, len);
    }
}

#[cfg(not(all(feature = "mmap", not(miri))))]
struct Backing(NonNull<u8>);

#[cfg(not(all(feature = "mmap", not(miri))))]
impl Backing {
    const LAYOUT: std::alloc::Layout = match std::alloc::Layout::from_size_align(RESERVE, super::layout::PAGE) {
        Ok(layout) => layout,
        Err(_) => panic!("bad region layout"),
    };

    fn new() -> Option<(Self, NonNull<u8>)> {
        // SAFETY: the layout has a nonzero size.
        let base = NonNull::new(unsafe { std::alloc::alloc_zeroed(Self::LAYOUT) })?;
        Some((Self(base), base))
    }

    // Nothing to give back, but tests still run the page-range logic.
    fn os_page() -> Option<usize> {
        cfg!(test).then_some(super::layout::PAGE)
    }

    fn decommit(&self, _offset: usize, _len: usize) {}
}

#[cfg(not(all(feature = "mmap", not(miri))))]
impl Drop for Backing {
    fn drop(&mut self) {
        // SAFETY: `new` allocated it with this layout, and this is the only free.
        unsafe { std::alloc::dealloc(self.0.as_ptr(), Self::LAYOUT) }
    }
}

/// Lets a test pretend the OS page size is different, on its own thread only.
#[cfg(test)]
pub(crate) mod test_os_page {
    use std::cell::Cell;

    thread_local! {
        static SIZE: Cell<Option<Option<usize>>> = const { Cell::new(None) };
    }

    pub(super) fn get() -> Option<Option<usize>> {
        SIZE.get()
    }

    /// Restores the previous size when dropped.
    pub(crate) struct Override(Option<Option<usize>>);

    impl Override {
        pub(crate) fn new(size: Option<usize>) -> Self {
            Self(SIZE.replace(Some(size)))
        }
    }

    impl Drop for Override {
        fn drop(&mut self) {
            SIZE.set(self.0);
        }
    }
}
