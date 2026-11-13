//! A fast seeded hash of a string's characters. It reads them as units of the string's width,
//! packed into words, so every shape of a string hashes the same, and so does a `&str` of the
//! same text. Strings whose units fit in [`SHORT`] bytes, such as most names, hash in one step.

use crate::units::Unit;
use crate::word::{HIGH, SHORT, fingerprint};
use crate::{Host, Info, Packed, Units, Width, chunks, flat, summary};

const K0: u64 = 0x243f_6a88_85a3_08d3;
const K1: u64 = 0x1319_8a2e_0370_7344;
const K2: u64 = 0xa409_3822_299f_31d0;

/// The hash of a short string of `len` characters at `width`, whose units' bytes gave `words`.
#[inline]
fn short((a, b): (u64, u64), seed: u64, len: usize, width: Width) -> u64 {
    let key = seed.rotate_left(29) ^ K1;
    mix(mix(a ^ seed ^ K0, b ^ key) ^ (len as u64 | (width as u64) << 48), K2 ^ key)
}

/// Writes `codes` as `width`-byte little-endian units into `buf` from `at`, and returns the end.
fn gather(buf: &mut [u8; SHORT], mut at: usize, codes: impl Iterator<Item = u32>, width: Width) -> usize {
    let size = width.bytes();
    for code in codes {
        buf[at..at + size].copy_from_slice(&code.to_le_bytes()[..size]);
        at += size;
    }
    at
}

fn codes(units: Units<'_>) -> impl Iterator<Item = u32> + '_ {
    (0..units.len()).map(move |i| units.code(i))
}

#[inline]
fn mix(a: u64, b: u64) -> u64 {
    let product = a as u128 * b as u128;
    product as u64 ^ (product >> 64) as u64
}

/// Words go in pairs, one multiply for each pair. The key comes from the seed, so which
/// texts collide can't be known without it.
struct State {
    acc: u64,
    key: u64,
    width: Width,
    /// A word waiting for its pair.
    half: Option<u64>,
    /// The word being packed, and how many of its bits are filled.
    packing: u64,
    bits: u32,
}

impl State {
    fn new(seed: u64, width: Width) -> Self {
        Self { acc: seed ^ K0, key: seed.rotate_left(29) ^ K1, width, half: None, packing: 0, bits: 0 }
    }

    #[inline]
    fn word(&mut self, word: u64) {
        match self.half.take() {
            Some(a) => self.acc = mix(a ^ self.acc, word ^ self.key),
            None => self.half = Some(word),
        }
    }

    #[inline]
    fn unit(&mut self, code: u32) {
        self.packing |= (code as u64) << self.bits;
        self.bits += 8 * self.width.bytes() as u32;
        if self.bits == 64 {
            let word = self.packing;
            (self.packing, self.bits) = (0, 0);
            self.word(word);
        }
    }

    #[inline]
    fn units(&mut self, units: Units<'_>) {
        match units {
            Units::One(slice) => self.run(slice),
            Units::Two(slice) => self.run(slice),
            Units::Four(slice) => self.run(slice),
            Units::Packed(packed) => self.packed(packed),
            Units::Inline(inline) => self.run(&inline.bytes()[..inline.len()]),
        }
    }

    /// Whole words go straight in once a part-packed word is filled.
    #[inline]
    fn packed(&mut self, packed: Packed<'_>) {
        if packed.width() != self.width {
            (0..packed.len()).for_each(|i| self.unit(packed.code(i)));
            return;
        }
        let mut i = 0;
        while self.bits != 0 && i < packed.len() {
            self.unit(packed.code(i));
            i += 1;
        }
        let packed = if i == 0 { packed } else { packed.slice(i..packed.len()) };
        let bytes = packed.len() * packed.width().bytes();
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

    /// Units narrower than the string's width are widened one at a time; the rest go in
    /// whole words once a part-packed word is filled.
    fn run<U: Unit>(&mut self, mut slice: &[U]) {
        if U::BITS != 8 * self.width.bytes() as u32 {
            slice.iter().for_each(|unit| self.unit(unit.code()));
            return;
        }
        while self.bits != 0
            && let [unit, rest @ ..] = slice
        {
            self.unit(unit.code());
            slice = rest;
        }
        let per = (64 / U::BITS) as usize;
        if self.half.is_some() && slice.len() >= per {
            self.word(U::pack(&slice[..per]));
            slice = &slice[per..];
        }
        let mut pairs = slice.chunks_exact(2 * per);
        for pair in &mut pairs {
            self.acc = mix(U::pack(&pair[..per]) ^ self.acc, U::pack(&pair[per..]) ^ self.key);
        }
        let mut rest = pairs.remainder();
        if rest.len() >= per {
            self.word(U::pack(&rest[..per]));
            rest = &rest[per..];
        }
        // Filling a part-packed word above left it empty or used up `slice`.
        if !rest.is_empty() {
            (self.packing, self.bits) = (U::pack(rest), rest.len() as u32 * U::BITS);
        }
    }

    /// Length and width tell how many words there were and how they were packed.
    fn finish(mut self, len: usize) -> u64 {
        if self.bits != 0 {
            self.word(self.packing);
        }
        if let Some(a) = self.half {
            self.acc = mix(a ^ self.acc, self.key);
        }
        mix(self.acc ^ (len as u64 | (self.width as u64) << 48), K2 ^ self.key)
    }
}

/// Hashes the characters of `string` with `seed`.
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
    h.charge(info.len as u64)?;
    Ok(match flat {
        Some(units) => hash_flat(units, seed),
        None => hash_chunks(h, string, info, seed),
    })
}

/// The hash of a flat string's characters, which are at their narrowest width.
#[inline]
fn hash_flat(units: Units<'_>, seed: u64) -> u64 {
    let (len, width) = (units.len(), units.width());
    if len * width.bytes() > SHORT {
        let mut state = State::new(seed, width);
        state.units(units);
        return state.finish(len);
    }
    let mut buf = [0; SHORT];
    let n = len * width.bytes();
    match units {
        Units::One(bytes) => return short(fingerprint(bytes), seed, len, width),
        Units::Inline(inline) => return short(fingerprint(&inline.bytes()[..len]), seed, len, width),
        Units::Packed(packed) => packed.copy_bytes(0, &mut buf[..n]),
        _ => _ = gather(&mut buf, 0, codes(units), width),
    }
    short(fingerprint(&buf[..n]), seed, len, width)
}

#[inline(never)]
fn hash_chunks<H: Host>(h: &H, string: H::Str, info: Info, seed: u64) -> u64 {
    if info.len * info.width.bytes() <= SHORT {
        let mut buf = [0; SHORT];
        let n = chunks(h, string).fold(0, |at, units| gather(&mut buf, at, codes(units), info.width));
        return short(fingerprint(&buf[..n]), seed, info.len, info.width);
    }
    let mut state = State::new(seed, info.width);
    chunks(h, string).for_each(|units| state.units(units));
    state.finish(info.len)
}

/// What [`hash`] gives a string of these characters.
pub fn hash_str(string: &str, seed: u64) -> u64 {
    let bytes = string.as_bytes();
    if bytes.len() <= SHORT {
        let words = fingerprint(bytes);
        if (words.0 | words.1) & HIGH == 0 {
            return short(words, seed, bytes.len(), Width::One);
        }
    } else if string.is_ascii() {
        let mut state = State::new(seed, Width::One);
        state.run(bytes);
        return state.finish(bytes.len());
    }
    // A character's first byte tells its length, and whether it's past U+00FF or U+FFFF.
    let len = string.bytes().filter(|&byte| byte as i8 >= -0x40).count();
    let width = match string.bytes().max().unwrap_or(0) {
        0xF0.. => Width::Four,
        0xC4.. => Width::Two,
        _ => Width::One,
    };
    if len * width.bytes() <= SHORT {
        let mut buf = [0; SHORT];
        let n = gather(&mut buf, 0, string.chars().map(|character| character as u32), width);
        return short(fingerprint(&buf[..n]), seed, len, width);
    }
    let mut state = State::new(seed, width);
    match width {
        Width::One => state.decoded::<u8>(string),
        Width::Two => state.decoded::<u16>(string),
        Width::Four => state.decoded::<u32>(string),
    }
    state.finish(len)
}

impl State {
    /// Takes the characters of `string`, all of which fit `U`, a buffer at a time.
    fn decoded<U: Unit + Default>(&mut self, string: &str) {
        let mut buf = [U::default(); 64];
        let mut n = 0;
        for character in string.chars() {
            buf[n] = U::of(character as u32);
            n += 1;
            if n == buf.len() {
                self.run(&buf);
                n = 0;
            }
        }
        self.run(&buf[..n]);
    }
}
