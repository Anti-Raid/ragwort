//! Helpers that read bytes a word at a time.

use std::cell::Cell;

/// The high bit of each byte in a word. ASCII bytes have this bit clear.
pub(crate) const HIGH: u64 = 0x8080_8080_8080_8080;

/// The low bit of each byte in a word.
pub(crate) const ONES: u64 = 0x0101_0101_0101_0101;

/// The maximum length, in bytes, of a slice that [`fingerprint`] accepts.
pub(crate) const SHORT: usize = 16;

/// The maximum length, in bytes, of the units of a string that is hashed from its first 16 and its last 16 bytes. See the hash module.
pub(crate) const MEDIUM: usize = 32;

/// Returns a mask with the low `n` bytes set, for `n` up to 8.
#[inline]
pub(crate) fn low_bytes(n: usize) -> u64 {
    u64::MAX.checked_shr(64 - 8 * n as u32).unwrap_or(0)
}

/// Returns the number of bytes of `word` that start a character. In UTF-8 every byte starts a character except a byte of the form `10xxxxxx`.
/// A zero byte counts as a start, so the caller subtracts the bytes of `word` that are past the end of the text.
#[inline]
pub(crate) fn starts(word: u64) -> u32 {
    // Each byte of `marks` is 1 for a start and 0 otherwise. The multiplication adds the eight bytes into the top byte.
    let marks = (!(word >> 7) | (word >> 6)) & ONES;
    (marks.wrapping_mul(ONES) >> 56) as u32
}

/// Packs up to eight bytes into a word, with the first byte in the lowest bits. For fewer than eight bytes, the reads overlap.
/// Overlapping reads OR the same byte into the same position, so the result is exact.
#[inline]
pub(crate) fn pack(bytes: &[u8]) -> u64 {
    #[inline(always)]
    fn four(bytes: &[u8], i: usize) -> u64 {
        u32::from_le_bytes(bytes[i..i + 4].try_into().expect("four bytes")) as u64
    }
    let n = bytes.len();
    match n {
        8 => u64::from_le_bytes(bytes.try_into().expect("eight bytes")),
        4..=7 => four(bytes, 0) | four(bytes, n - 4) << (8 * (n - 4)),
        1..=3 => bytes[0] as u64 | (bytes[n / 2] as u64) << (8 * (n / 2)) | (bytes[n - 1] as u64) << (8 * (n - 1)),
        _ => 0,
    }
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

/// Returns whether `a` and `b` hold the same bytes.
#[inline]
pub(crate) fn equal(a: &[u8], b: &[u8]) -> bool {
    if b.len() <= SHORT {
        return a.len() == b.len() && fingerprint(a) == fingerprint(b);
    }
    a == b
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
