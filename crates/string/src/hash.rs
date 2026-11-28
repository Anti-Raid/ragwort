//! A fast seeded hash of a string's bytes. Every representation of the same text has the same hash, and so does a `&str` of the
//! same text.
//!
//! The hash has three forms, chosen by the number of bytes:
//!
//! - Up to [`SHORT`] bytes, such as most names: one multiplication, then the last one.
//! - Up to [`MEDIUM`] bytes: one multiplication over the first 16 bytes, one over the last 16 bytes on the result of the first, then the last one.
//! - Longer: one multiplication for each 16 bytes, each on the result of the one before, then the last one.
//!
//! The first two forms read the bytes as wyhash does, and all three chain their multiplications as wyhash does. One thing differs on purpose.
//! wyhash combines one side of each multiplication with a constant that is public unless the caller makes its own. Here both sides are combined
//! with values that come from the seed, so no input makes a multiplication come out the same under every seed.

use crate::word::{MEDIUM, SHORT, fingerprint, pack};
use crate::{Host, Info, Packed, Units, chunks, flat, summary};

const K0: u64 = 0x243f_6a88_85a3_08d3;
const K1: u64 = 0x1319_8a2e_0370_7344;
const K2: u64 = 0xa409_3822_299f_31d0;

/// Returns the hash of a string of `len` bytes, at most [`SHORT`]. `(a, b)` is the [`fingerprint`] of the bytes.
#[inline]
fn short((a, b): (u64, u64), seed: u64, len: usize) -> u64 {
    let key = seed.rotate_left(29) ^ K1;
    mix(mix(a ^ seed ^ K0, b ^ key) ^ len as u64, K2 ^ key)
}

/// Returns the hash of a string of `len` bytes, more than [`SHORT`] and at most [`MEDIUM`]. `first` is the first 16 bytes and `last` is the last 16, each as two little-endian words. The two overlap in a string of fewer than 32 bytes.
#[inline]
fn medium(first: (u64, u64), last: (u64, u64), seed: u64, len: usize) -> u64 {
    let key = seed.rotate_left(29) ^ K1;
    let chained = mix(first.0 ^ seed ^ K0, first.1 ^ key);
    mix(mix(last.0 ^ chained, last.1 ^ key) ^ len as u64, K2 ^ key)
}

/// Returns the hash of a string whose bytes are `bytes`, which are at most [`MEDIUM`] bytes.
#[inline]
fn compact(bytes: &[u8], seed: u64) -> u64 {
    #[inline(always)]
    fn word(bytes: &[u8], at: usize) -> u64 {
        u64::from_le_bytes(bytes[at..at + 8].try_into().expect("eight bytes"))
    }
    let n = bytes.len();
    if n <= SHORT {
        return short(fingerprint(bytes), seed, n);
    }
    medium((word(bytes, 0), word(bytes, 8)), (word(bytes, n - 16), word(bytes, n - 8)), seed, n)
}

#[inline]
fn mix(a: u64, b: u64) -> u64 {
    let product = a as u128 * b as u128;
    product as u64 ^ (product >> 64) as u64
}

/// The state of the hash over a long string. Words are consumed in pairs, with one multiplication per pair.
/// The key is derived from the seed, so collisions cannot be predicted without the seed.
struct State {
    acc: u64,
    key: u64,
    /// The first word of a pair, held until the second word arrives.
    half: Option<u64>,
    /// The word that is being packed from bytes. `bits` is the number of its bits filled so far.
    packing: u64,
    bits: u32,
}

impl State {
    fn new(seed: u64) -> Self {
        Self { acc: seed ^ K0, key: seed.rotate_left(29) ^ K1, half: None, packing: 0, bits: 0 }
    }

    #[inline]
    fn word(&mut self, word: u64) {
        match self.half.take() {
            Some(a) => self.acc = mix(a ^ self.acc, word ^ self.key),
            None => self.half = Some(word),
        }
    }

    #[inline]
    fn byte(&mut self, byte: u8) {
        self.packing |= u64::from(byte) << self.bits;
        self.bits += 8;
        if self.bits == 64 {
            let word = self.packing;
            (self.packing, self.bits) = (0, 0);
            self.word(word);
        }
    }

    #[inline]
    fn units(&mut self, units: Units<'_>) {
        match units {
            Units::Slice(bytes) => self.run(bytes),
            Units::Packed(packed) => self.packed(packed),
            Units::Inline(inline) => self.run(&inline.bytes()[..inline.len()]),
        }
    }

    /// Hashes packed bytes. Bytes first complete the partly packed word, and then whole words are hashed directly.
    #[inline]
    fn packed(&mut self, packed: Packed<'_>) {
        let mut i = 0;
        while self.bits != 0 && i < packed.len() {
            self.byte(packed.byte(i));
            i += 1;
        }
        let packed = if i == 0 {
            packed
        } else {
            packed.slice(i..packed.len())
        };
        let bytes = packed.len();
        let (whole, rest) = (bytes / 8, bytes % 8);
        let mut word_index = 0;
        if self.half.is_some() && whole > 0 {
            self.word(packed.word_at(0, 8));
            word_index = 1;
        }
        let (mut acc, key) = (self.acc, self.key);
        while word_index + 2 <= whole {
            acc = mix(packed.word_at(word_index, 8) ^ acc, packed.word_at(word_index + 1, 8) ^ key);
            word_index += 2;
        }
        self.acc = acc;
        if word_index < whole {
            self.word(packed.word_at(word_index, 8));
        }
        if rest > 0 {
            (self.packing, self.bits) = (packed.word_at(whole, rest), 8 * rest as u32);
        }
    }

    /// Hashes a slice of bytes. Bytes first complete the partly packed word, and then whole words are hashed directly.
    fn run(&mut self, mut slice: &[u8]) {
        while self.bits != 0
            && let [byte, rest @ ..] = slice
        {
            self.byte(*byte);
            slice = rest;
        }
        if self.half.is_some() && slice.len() >= 8 {
            self.word(pack(&slice[..8]));
            slice = &slice[8..];
        }
        let (pairs, mut rest) = slice.as_chunks::<16>();
        for pair in pairs {
            self.acc = mix(pack(&pair[..8]) ^ self.acc, pack(&pair[8..]) ^ self.key);
        }
        if rest.len() >= 8 {
            self.word(pack(&rest[..8]));
            rest = &rest[8..];
        }
        // The loop above either completed the partly packed word or consumed all of `slice`. So `packing` is empty here, or `rest` is.
        if !rest.is_empty() {
            (self.packing, self.bits) = (pack(rest), rest.len() as u32 * 8);
        }
    }

    /// Returns the hash. The last step mixes in `len`, the number of bytes, which determines how many words were hashed.
    fn finish(mut self, len: usize) -> u64 {
        if self.bits != 0 {
            self.word(self.packing);
        }
        if let Some(a) = self.half {
            self.acc = mix(a ^ self.acc, self.key);
        }
        mix(self.acc ^ len as u64, K2 ^ self.key)
    }
}

/// Hashes the bytes of `string` with `seed`.
#[inline]
pub fn hash<H: Host>(h: &H, string: H::Str, seed: u64) -> Result<u64, H::Error> {
    if let Some(units) = flat(h, string) {
        h.charge(units.len() as u64)?;
        return Ok(hash_flat(units, seed));
    }
    rope_hash(h, string, seed)
}

#[inline(never)]
fn rope_hash<H: Host>(h: &H, string: H::Str, seed: u64) -> Result<u64, H::Error> {
    let (info, flat) = summary(h, string);
    h.charge(info.bytes as u64)?;
    Ok(match flat {
        Some(units) => hash_flat(units, seed),
        None => hash_chunks(h, string, info, seed),
    })
}

/// Returns the hash that [`hash`] gives a flat string with the bytes `units`. A host uses it to hash bytes that are not in a string yet.
#[inline]
pub fn hash_units(units: Units<'_>, seed: u64) -> u64 {
    hash_flat(units, seed)
}

/// Returns the hash of a flat string's bytes.
#[inline]
fn hash_flat(units: Units<'_>, seed: u64) -> u64 {
    let n = units.len();
    if n > MEDIUM {
        let mut state = State::new(seed);
        state.units(units);
        return state.finish(n);
    }
    match units {
        Units::Slice(bytes) => compact(bytes, seed),
        Units::Inline(inline) => short(fingerprint(&inline.bytes()[..n]), seed, n),
        // Packed bytes of more than `SHORT` bytes are read as words where they are.
        Units::Packed(packed) if n > SHORT => medium((packed.bytes_at(0), packed.bytes_at(8)), (packed.bytes_at(n - 16), packed.bytes_at(n - 8)), seed, n),
        Units::Packed(packed) => {
            let mut buf = [0; SHORT];
            packed.copy_bytes(0, &mut buf[..n]);
            compact(&buf[..n], seed)
        }
    }
}

#[inline(never)]
fn hash_chunks<H: Host>(h: &H, string: H::Str, info: Info, seed: u64) -> u64 {
    if info.bytes <= MEDIUM {
        let mut buf = [0; MEDIUM];
        let mut at = 0;
        for units in chunks(h, string) {
            units.copy_to(&mut buf[at..]);
            at += units.len();
        }
        return compact(&buf[..at], seed);
    }
    let mut state = State::new(seed);
    chunks(h, string).for_each(|units| state.units(units));
    state.finish(info.bytes)
}

/// Returns the hash that [`hash`] gives a string with the characters of `string`.
pub fn hash_str(string: &str, seed: u64) -> u64 {
    let bytes = string.as_bytes();
    if bytes.len() <= MEDIUM {
        return compact(bytes, seed);
    }
    let mut state = State::new(seed);
    state.run(bytes);
    state.finish(bytes.len())
}
