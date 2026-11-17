//! Helpers that read bytes a word at a time, for the fast paths over one-byte units.

use std::cell::Cell;

/// The high bit of each byte in a word. ASCII bytes have this bit clear.
pub(crate) const HIGH: u64 = 0x8080_8080_8080_8080;

/// The low bit of each byte in a word.
pub(crate) const ONES: u64 = 0x0101_0101_0101_0101;

/// The maximum length, in bytes, of a slice that [`fingerprint`] accepts.
pub(crate) const SHORT: usize = 16;

/// Returns a mask with the low `n` bytes set, for `n` up to 8.
#[inline]
pub(crate) fn low_bytes(n: usize) -> u64 {
    u64::MAX.checked_shr(64 - 8 * n as u32).unwrap_or(0)
}

/// Returns two words that together contain every byte of `bytes`, built from overlapping reads. `bytes` holds
/// at most [`SHORT`] bytes. The words do not hold the bytes in order. Two inputs of the same length
/// have equal fingerprints only if the inputs are equal.
#[inline]
pub(crate) fn fingerprint(bytes: &[u8]) -> (u64, u64) {
    #[inline(always)]
    fn r4(bytes: &[u8], i: usize) -> u64 {
        u32::from_le_bytes(bytes[i..i + 4].try_into().expect("four bytes")) as u64
    }
    let n = bytes.len();
    // These are the reads that wyhash uses for inputs of up to 16 bytes. From 4 bytes up, four 4-byte reads cover the slice.
    // Two start from the front, at 0 and `offset`. Two start from the back, at `n - 4` and `n - 4 - offset`.
    // `offset` is 0 for 4 to 7 bytes, 4 for 8 to 15 bytes and 8 for 16 bytes, so the reads overlap but miss no byte.
    // For 1 to 3 bytes, the first, middle and last bytes cover the slice.
    if n >= 4 {
        let offset = (n >> 3) << 2;
        (r4(bytes, 0) << 32 | r4(bytes, offset), r4(bytes, n - 4) << 32 | r4(bytes, n - 4 - offset))
    } else if n > 0 {
        ((bytes[0] as u64) << 16 | (bytes[n >> 1] as u64) << 8 | bytes[n - 1] as u64, 0)
    } else {
        (0, 0)
    }
}

/// Returns whether `a` and `b` hold the same bytes and all of them are ASCII.
#[inline]
pub(crate) fn equal_ascii(a: &[u8], b: &[u8]) -> bool {
    if b.len() <= SHORT {
        let words = fingerprint(b);
        return a.len() == b.len() && fingerprint(a) == words && (words.0 | words.1) & HIGH == 0;
    }
    a == b && b.is_ascii()
}

/// Returns `n` bytes, at most 8, of the little-endian bytes of `words`, starting at byte `at`. The first byte is in the lowest bits of the result.
#[inline]
pub(crate) fn read_bytes(words: &[Cell<u64>], at: usize, n: usize) -> u64 {
    let (i, shift) = (at / 8, (at % 8) as u32 * 8);
    let mut value = words[i].get() >> shift;
    if shift != 0 && shift + 8 * n as u32 > 64 {
        value |= words[i + 1].get() << (64 - shift);
    }
    value & low_bytes(n)
}

/// Writes the low `n` bytes of `value` starting at byte `at`. All `n` bytes must lie in one word.
#[inline]
pub(crate) fn write_bytes(words: &[Cell<u64>], at: usize, n: usize, value: u64) {
    let shift = (at % 8) as u32 * 8;
    let mask = low_bytes(n) << shift;
    let word = &words[at / 8];
    word.set(word.get() & !mask | (value << shift) & mask);
}
