//! A fast seeded hash of a string's characters. It reads them as units of the string's width,
//! packed into words, so every shape of a string hashes the same, and so does a `&str` of the
//! same text. Strings whose units fit in [`SHORT`] bytes, such as most names, hash in one step.

use crate::units::Unit;
use crate::{Host, Units, Width, chunks, summary};

const K0: u64 = 0x243f_6a88_85a3_08d3;
const K1: u64 = 0x1319_8a2e_0370_7344;
const K2: u64 = 0xa409_3822_299f_31d0;

/// Strings whose units take at most this many bytes hash in one step.
pub(crate) const SHORT: usize = 16;

/// The high bit of each byte in a word: none is set in ASCII.
pub(crate) const HIGH: u64 = 0x8080_8080_8080_8080;

/// Two words that together hold every byte of `b`, at most [`SHORT`] of them, from
/// overlapping reads. With the length they tell any two inputs apart.
#[inline]
pub(crate) fn words(b: &[u8]) -> (u64, u64) {
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

/// The hash of a short string of `len` characters at `width`, whose units' bytes gave `words`.
#[inline]
fn short((a, b): (u64, u64), seed: u64, len: usize, width: Width) -> u64 {
    let key = seed.rotate_left(29) ^ K1;
    mix(mix(a ^ seed ^ K0, b ^ key) ^ (len as u64 | (width as u64) << 48), K2 ^ key)
}

/// Writes `codes` as `width`-byte little-endian units into `buf` from `at`, and returns the end.
fn gather(buf: &mut [u8; SHORT], mut at: usize, codes: impl Iterator<Item = u32>, width: Width) -> usize {
    let w = width.bytes();
    for code in codes {
        buf[at..at + w].copy_from_slice(&code.to_le_bytes()[..w]);
        at += w;
    }
    at
}

fn codes(u: Units<'_>) -> impl Iterator<Item = u32> + '_ {
    let (one, two, four) = match u {
        Units::One(s) => (s, &[][..], &[][..]),
        Units::Two(s) => (&[][..], s, &[][..]),
        Units::Four(s) => (&[][..], &[][..], s),
    };
    one.iter().map(|&c| c as u32).chain(two.iter().map(|&c| c as u32)).chain(four.iter().copied())
}

#[inline]
fn mix(a: u64, b: u64) -> u64 {
    let p = a as u128 * b as u128;
    p as u64 ^ (p >> 64) as u64
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
    fn word(&mut self, w: u64) {
        match self.half.take() {
            Some(a) => self.acc = mix(a ^ self.acc, w ^ self.key),
            None => self.half = Some(w),
        }
    }

    #[inline]
    fn unit(&mut self, code: u32) {
        self.packing |= (code as u64) << self.bits;
        self.bits += 8 * self.width.bytes() as u32;
        if self.bits == 64 {
            let w = self.packing;
            (self.packing, self.bits) = (0, 0);
            self.word(w);
        }
    }

    fn units(&mut self, u: Units<'_>) {
        match u {
            Units::One(s) => self.run(s),
            Units::Two(s) => self.run(s),
            Units::Four(s) => self.run(s),
        }
    }

    /// Units narrower than the string's width are widened one at a time; the rest go in
    /// whole words once a part-packed word is filled.
    fn run<U: Unit>(&mut self, mut s: &[U]) {
        if U::BITS != 8 * self.width.bytes() as u32 {
            s.iter().for_each(|u| self.unit(u.code()));
            return;
        }
        while self.bits != 0
            && let [u, rest @ ..] = s
        {
            self.unit(u.code());
            s = rest;
        }
        let per = (64 / U::BITS) as usize;
        if self.half.is_some() && s.len() >= per {
            self.word(U::pack(&s[..per]));
            s = &s[per..];
        }
        let mut pairs = s.chunks_exact(2 * per);
        for p in &mut pairs {
            self.acc = mix(U::pack(&p[..per]) ^ self.acc, U::pack(&p[per..]) ^ self.key);
        }
        let mut rest = pairs.remainder();
        if rest.len() >= per {
            self.word(U::pack(&rest[..per]));
            rest = &rest[per..];
        }
        // Filling a part-packed word above left it empty or used up `s`.
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

/// Hashes the characters of `s` with `seed`.
pub fn hash<H: Host>(h: &H, s: H::Str, seed: u64) -> Result<u64, H::Error> {
    let (info, flat) = summary(h, s);
    h.charge(info.len as u64)?;
    if info.len * info.width.bytes() <= SHORT {
        if let Some(Units::One(b)) = flat
            && info.width == Width::One
        {
            return Ok(short(words(b), seed, info.len, info.width));
        }
        let mut buf = [0; SHORT];
        let n = match flat {
            Some(units) => gather(&mut buf, 0, codes(units), info.width),
            None => chunks(h, s).fold(0, |at, units| gather(&mut buf, at, codes(units), info.width)),
        };
        return Ok(short(words(&buf[..n]), seed, info.len, info.width));
    }
    let mut state = State::new(seed, info.width);
    match flat {
        Some(units) => state.units(units),
        None => chunks(h, s).for_each(|units| state.units(units)),
    }
    Ok(state.finish(info.len))
}

/// What [`hash`] gives a string of these characters.
pub fn hash_str(s: &str, seed: u64) -> u64 {
    let b = s.as_bytes();
    if b.len() <= SHORT {
        let w = words(b);
        if (w.0 | w.1) & HIGH == 0 {
            return short(w, seed, b.len(), Width::One);
        }
    } else if s.is_ascii() {
        let mut state = State::new(seed, Width::One);
        state.run(b);
        return state.finish(b.len());
    }
    // A character's first byte tells its length, and whether it's past U+00FF or U+FFFF.
    let len = s.bytes().filter(|&b| b as i8 >= -0x40).count();
    let width = match s.bytes().max().unwrap_or(0) {
        0xF0.. => Width::Four,
        0xC4.. => Width::Two,
        _ => Width::One,
    };
    if len * width.bytes() <= SHORT {
        let mut buf = [0; SHORT];
        let n = gather(&mut buf, 0, s.chars().map(|c| c as u32), width);
        return short(words(&buf[..n]), seed, len, width);
    }
    let mut state = State::new(seed, width);
    match width {
        Width::One => state.decoded::<u8>(s),
        Width::Two => state.decoded::<u16>(s),
        Width::Four => state.decoded::<u32>(s),
    }
    state.finish(len)
}

impl State {
    /// Takes the characters of `s`, all of which fit `U`, a buffer at a time.
    fn decoded<U: Unit + Default>(&mut self, s: &str) {
        let mut buf = [U::default(); 64];
        let mut n = 0;
        for c in s.chars() {
            buf[n] = U::of(c as u32);
            n += 1;
            if n == buf.len() {
                self.run(&buf);
                n = 0;
            }
        }
        self.run(&buf[..n]);
    }
}
