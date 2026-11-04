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

/// Two words that together hold every byte of `b`, at most [`SHORT`] of them, from
/// overlapping reads. They aren't the bytes in place, but with the length they tell any two
/// inputs apart.
#[inline]
pub(crate) fn fingerprint(b: &[u8]) -> (u64, u64) {
    let n = b.len();
    if n >= 4 {
        let r4 = |i: usize| u32::from_le_bytes(b[i..i + 4].try_into().expect("four bytes")) as u64;
        let q = (n >> 3) << 2;
        (r4(0) << 32 | r4(q), r4(n - 4) << 32 | r4(n - 4 - q))
    } else if n > 0 {
        ((b[0] as u64) << 16 | (b[n >> 1] as u64) << 8 | b[n - 1] as u64, 0)
    } else {
        (0, 0)
    }
}

/// Whether `a` and `b` are the same bytes, all of them ASCII.
#[inline]
pub(crate) fn equal_ascii(a: &[u8], b: &[u8]) -> bool {
    if b.len() <= SHORT {
        let w = fingerprint(b);
        return a.len() == b.len() && fingerprint(a) == w && (w.0 | w.1) & HIGH == 0;
    }
    a == b && b.is_ascii()
}

/// Up to 8 bytes of `words`' little-endian bytes from byte `at`, the first lowest.
#[inline]
pub(crate) fn read_bytes(words: &[Cell<u64>], at: usize, n: usize) -> u64 {
    let (i, shift) = (at / 8, (at % 8) as u32 * 8);
    let mut v = words[i].get() >> shift;
    if shift != 0 && shift + 8 * n as u32 > 64 {
        v |= words[i + 1].get() << (64 - shift);
    }
    v & low_bytes(n)
}

/// Writes the low `n` bytes of `v` from byte `at`, all in one word.
#[inline]
pub(crate) fn write_bytes(words: &[Cell<u64>], at: usize, n: usize, v: u64) {
    let shift = (at % 8) as u32 * 8;
    let mask = low_bytes(n) << shift;
    let w = &words[at / 8];
    w.set(w.get() & !mask | (v << shift) & mask);
}
