//! Reading bytes a word at a time, for the fast paths over one-byte units.

use std::cell::Cell;

/// The high bit of each byte in a word: none is set in ASCII.
pub(crate) const HIGH: u64 = 0x8080_8080_8080_8080;

/// The low bit of each byte in a word.
pub(crate) const ONES: u64 = 0x0101_0101_0101_0101;

/// The longest slice a [`fingerprint`] covers.
pub(crate) const SHORT: usize = 16;

/// The low `n` bytes of a word set, for `n` up to 8.
#[inline]
pub(crate) fn low_bytes(n: usize) -> u64 {
    u64::MAX.checked_shr(64 - 8 * n as u32).unwrap_or(0)
}

/// Two words that together hold every byte of `bytes`, at most [`SHORT`] of them, from
/// overlapping reads. They aren't the bytes in place, but with the length they tell any two
/// inputs apart.
#[inline]
pub(crate) fn fingerprint(bytes: &[u8]) -> (u64, u64) {
    let n = bytes.len();
    if n >= 4 {
        let r4 = |i: usize| u32::from_le_bytes(bytes[i..i + 4].try_into().expect("four bytes")) as u64;
        let offset = (n >> 3) << 2;
        (r4(0) << 32 | r4(offset), r4(n - 4) << 32 | r4(n - 4 - offset))
    } else if n > 0 {
        ((bytes[0] as u64) << 16 | (bytes[n >> 1] as u64) << 8 | bytes[n - 1] as u64, 0)
    } else {
        (0, 0)
    }
}

/// Whether `a` and `b` are the same bytes, all of them ASCII.
#[inline]
pub(crate) fn equal_ascii(a: &[u8], b: &[u8]) -> bool {
    if b.len() <= SHORT {
        let words = fingerprint(b);
        return a.len() == b.len() && fingerprint(a) == words && (words.0 | words.1) & HIGH == 0;
    }
    a == b && b.is_ascii()
}

/// Up to 8 bytes of `words`' little-endian bytes from byte `at`, the first lowest.
#[inline]
pub(crate) fn read_bytes(words: &[Cell<u64>], at: usize, n: usize) -> u64 {
    let (i, shift) = (at / 8, (at % 8) as u32 * 8);
    let mut value = words[i].get() >> shift;
    if shift != 0 && shift + 8 * n as u32 > 64 {
        value |= words[i + 1].get() << (64 - shift);
    }
    value & low_bytes(n)
}

/// Writes the low `n` bytes of `value` from byte `at`, all in one word.
#[inline]
pub(crate) fn write_bytes(words: &[Cell<u64>], at: usize, n: usize, value: u64) {
    let shift = (at % 8) as u32 * 8;
    let mask = low_bytes(n) << shift;
    let word = &words[at / 8];
    word.set(word.get() & !mask | (value << shift) & mask);
}
