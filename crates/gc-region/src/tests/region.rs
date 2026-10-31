use super::Region;

#[test]
fn words_start_zeroed_and_hold_writes() {
    let mut region = Region::new(1 << 20).unwrap();
    let words = region.words();
    assert_eq!(words.len(), 1 << 20);
    assert!(words.iter().step_by(4096).all(|w| w.get() == 0));
    words[12345].set(7);
    assert_eq!(region.words()[12345].get(), 7);
}

/// Released words stay usable: they read as zero or as before, and take new writes.
#[test]
fn released_words_stay_usable() {
    let mut region = Region::new(1 << 20).unwrap();
    for (i, w) in region.words().iter().enumerate() {
        w.set(i as u64);
    }
    region.release(1000..900_000);
    let words = region.words();
    for (i, w) in words.iter().enumerate() {
        let v = w.get();
        if (1000..900_000).contains(&i) {
            assert!(v == 0 || v == i as u64);
        } else {
            assert_eq!(v, i as u64);
        }
    }
    words[5000].set(1);
    assert_eq!(words[5000].get(), 1);
}

#[test]
fn odd_ranges_are_harmless() {
    let mut region = Region::new(4096).unwrap();
    region.words()[0].set(1);
    #[allow(clippy::reversed_empty_ranges)]
    region.release(10..5);
    region.release(0..1);
    region.release(4000..usize::MAX);
    region.release(usize::MAX - 1..usize::MAX);
    assert_eq!(region.words()[0].get(), 1);
    assert!(Region::new(0).is_some_and(|r| r.is_empty()));
}

/// Memory comes back to the system, so what the process holds drops after a release.
#[cfg(all(feature = "mmap", any(target_os = "linux", target_vendor = "apple")))]
#[test]
fn release_gives_memory_back() {
    use crate::mmap::held_bytes;
    const LEN: usize = 32 << 20;
    let mut region = Region::new(LEN / 8).unwrap();
    region.words().iter().step_by(512).for_each(|w| w.set(1));
    let touched = held_bytes();
    region.release(0..LEN / 8);
    let released = held_bytes();
    assert!(touched.saturating_sub(released) > LEN / 2, "{touched} -> {released} bytes held");
    // Written again, the pages come back.
    region.words().iter().step_by(512).for_each(|w| w.set(2));
    assert!(held_bytes() > released + LEN / 2);
}
