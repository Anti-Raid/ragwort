//! Immutable strings over any heap. A string is flat, its characters in one array at the
//! narrowest width that holds them all, one, two or four bytes each, or a rope: a balanced
//! tree of strings that [`concat()`] builds when copying would cost more than it saves. The heap
//! implements [`Host`] and the library does the rest, without allocating anywhere else. A
//! flat string's characters can also live outside the heap, as an [`External`].

mod case;
mod digit;
mod external;
mod hash;
mod intern;
mod iter;
mod rope;
mod search;
mod units;
mod word;

#[cfg(test)]
#[path = "tests/support.rs"]
mod testing;
#[cfg(test)]
#[path = "tests/string.rs"]
mod tests;

use std::cmp::Ordering;
use std::fmt;

pub use case::{compare_ci, downcase, downcase_char, foldcase, foldcase_char, upcase, upcase_char};
pub use digit::digit_value;
pub use external::{External, ExternalText, check_external};
pub use hash::{hash, hash_str};
pub use intern::{Table, intern, intern_str};
pub use iter::{Chars, Chunks};
pub use rope::{concat, concat_all, flatten, substring};
pub use search::{Split, SplitWhitespace, ends_with, find, rfind, split, split_whitespace, splitn, starts_with, trim, trim_end, trim_start};
pub use units::{Inline, Packed, PackedMut, Units, UnitsMut, Width};

/// The longest string: a rope can share one string many times over, so length isn't bounded
/// by memory.
pub const MAX_LEN: usize = (1 << 48) - 1;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum StrError {
    OutOfRange,
    TooLong,
    /// External characters stored wider than they need.
    NotNarrowest,
    /// Bytes that aren't UTF-8, read as text.
    NotUtf8,
}

/// What a rope node knows of its characters, which its host stores with it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Info {
    pub len: usize,
    /// The widest of its flat strings.
    pub width: Width,
    /// Edges to its deepest flat string. Ropes stay balanced, so this is about `log2` of the
    /// number of flat strings at most.
    pub depth: u8,
}

impl Info {
    /// The length in the low 48 bits, then the width and the depth.
    pub fn to_bits(self) -> u64 {
        self.len as u64 | (self.width as u64) << 48 | (self.depth as u64) << 56
    }

    pub fn from_bits(bits: u64) -> Self {
        let len = (bits & MAX_LEN as u64) as usize;
        Self { len, width: Width::from_bits((bits >> 48) as u8), depth: (bits >> 56) as u8 }
    }
}

pub enum StrView<'a, S> {
    Flat(Units<'a>),
    /// `flat` is the copy [`Host::flattened`] gave the rope, if any: the same characters.
    Rope { left: S, right: S, info: Info, flat: Option<S> },
}

/// Where strings live. The library reads them through [`Host::view`] and makes them with
/// [`Host::flat`] and [`Host::rope`].
pub trait Host {
    /// Equal handles are the same string.
    type Str: Copy + Eq;
    type Error: From<StrError>;

    fn view(&self, s: Self::Str) -> StrView<'_, Self::Str>;

    /// A flat string of `len` characters at `width`, zeroed for `init` to fill in. Views of
    /// other strings stay valid while it runs.
    fn flat(&self, width: Width, len: usize, init: impl FnOnce(UnitsMut<'_>)) -> Result<Self::Str, Self::Error>;

    /// A rope of `left` then `right`, both nonempty, which `info` sums up.
    fn rope(&self, left: Self::Str, right: Self::Str, info: Info) -> Result<Self::Str, Self::Error>;

    /// Keeps `flat`, a flat copy of `rope`'s characters, for [`StrView::Rope`] to hand back.
    /// A host whose ropes can't change leaves this out.
    fn flattened(&self, rope: Self::Str, flat: Self::Str) {
        let _ = (rope, flat);
    }

    /// Counts a read of `rope` by position, and returns how many it has had. Ropes read often
    /// enough get flattened; a host that leaves this out keeps them as they are.
    fn count_read(&self, rope: Self::Str) -> u64 {
        let _ = rope;
        0
    }

    /// Called before about `work` character operations.
    #[inline]
    fn charge(&self, work: u64) -> Result<(), Self::Error> {
        let _ = work;
        Ok(())
    }
}

pub type Res<H> = Result<<H as Host>::Str, <H as Host>::Error>;

pub(crate) fn info<H: Host>(h: &H, s: H::Str) -> Info {
    match h.view(s) {
        StrView::Flat(u) => Info { len: u.len(), width: u.width(), depth: 0 },
        StrView::Rope { info, .. } => info,
    }
}

pub fn empty<H: Host>(h: &H) -> Res<H> {
    h.flat(Width::One, 0, |_| {})
}

pub fn from_str<H: Host>(h: &H, s: &str) -> Res<H> {
    if s.is_ascii() {
        h.charge(s.len() as u64)?;
        return h.flat(Width::One, s.len(), |mut u| u.write(0, Units::One(s.as_bytes())));
    }
    from_chars(h, s.chars())
}

/// A string of the characters `chars` yields, which it must yield the same each time.
pub fn from_chars<H: Host>(h: &H, chars: impl Iterator<Item = char> + Clone) -> Res<H> {
    let (len, width) = chars.clone().fold((0, Width::One), |(n, w), c| (n + 1, w.max(Width::of(c))));
    if len > MAX_LEN {
        return Err(StrError::TooLong.into());
    }
    h.charge(len as u64)?;
    h.flat(width, len, |mut u| {
        for (i, c) in chars.take(len).enumerate() {
            u.set(i, c);
        }
    })
}

/// `n` copies of `c`.
pub fn repeat<H: Host>(h: &H, c: char, n: usize) -> Res<H> {
    if n > MAX_LEN {
        return Err(StrError::TooLong.into());
    }
    h.charge(n as u64)?;
    h.flat(Width::of(c), n, |mut u| {
        for i in 0..n {
            u.set(i, c);
        }
    })
}

pub fn len<H: Host>(h: &H, s: H::Str) -> usize {
    info(h, s).len
}

pub fn width<H: Host>(h: &H, s: H::Str) -> Width {
    info(h, s).width
}

pub fn is_flat<H: Host>(h: &H, s: H::Str) -> bool {
    matches!(h.view(s), StrView::Flat(_))
}

/// The character at `i`, in time proportional to the rope's depth. A rope read this way often
/// enough is flattened, after which reads take constant time.
#[inline]
pub fn char_at<H: Host>(h: &H, s: H::Str, i: usize) -> Result<char, H::Error> {
    match flat(h, s) {
        Some(u) => u.get(i).ok_or_else(|| StrError::OutOfRange.into()),
        None => rope_char_at(h, s, i),
    }
}

/// Kept out of line, as are the other rope cases, so the flat ones inline small.
#[inline(never)]
fn rope_char_at<H: Host>(h: &H, mut s: H::Str, mut i: usize) -> Result<char, H::Error> {
    match h.view(s) {
        StrView::Rope { flat: Some(flat), .. } => s = flat,
        StrView::Rope { info, .. } if h.count_read(s).saturating_mul(rope::CHARS_PER_READ) >= info.len as u64 => {
            s = flatten(h, s)?;
        }
        _ => {}
    }
    loop {
        match h.view(s) {
            StrView::Flat(u) => return u.get(i).ok_or_else(|| StrError::OutOfRange.into()),
            StrView::Rope { flat: Some(flat), .. } => s = flat,
            StrView::Rope { left, right, info, .. } => {
                if i >= info.len {
                    return Err(StrError::OutOfRange.into());
                }
                let l = len(h, left);
                (s, i) = if i < l { (left, i) } else { (right, i - l) };
            }
        }
    }
}

pub fn chunks<H: Host>(h: &H, s: H::Str) -> Chunks<'_, H> {
    Chunks::new(h, s, 0, len(h, s))
}

pub fn chars<H: Host>(h: &H, s: H::Str) -> Chars<'_, H> {
    Chars::new(chunks(h, s))
}

/// Orders by code point, then by length.
#[inline]
pub fn compare<H: Host>(h: &H, a: H::Str, b: H::Str) -> Result<Ordering, H::Error> {
    if a == b {
        return Ok(Ordering::Equal);
    }
    if let (Some(x), Some(y)) = (flat(h, a), flat(h, b)) {
        let n = x.len().min(y.len());
        h.charge(n as u64)?;
        return Ok(x.slice(0..n).compare(y.slice(0..n)).then(x.len().cmp(&y.len())));
    }
    rope_compare(h, a, b)
}

#[inline(never)]
fn rope_compare<H: Host>(h: &H, a: H::Str, b: H::Str) -> Result<Ordering, H::Error> {
    let ((ia, fa), (ib, fb)) = (summary(h, a), summary(h, b));
    let n = ia.len.min(ib.len);
    h.charge(n as u64)?;
    if let (Some(x), Some(y)) = (fa, fb) {
        return Ok(x.slice(0..n).compare(y.slice(0..n)).then(ia.len.cmp(&ib.len)));
    }
    compare_chunks(h, a, b)
}

#[inline(never)]
fn compare_chunks<H: Host>(h: &H, a: H::Str, b: H::Str) -> Result<Ordering, H::Error> {
    Ok(compare_runs(chunks(h, a), chunks(h, b)).then(len(h, a).cmp(&len(h, b))))
}

/// Orders the characters of two runs of chunks by code point, as far as the shorter goes.
pub(crate) fn compare_runs<'a>(mut ca: impl Iterator<Item = Units<'a>>, mut cb: impl Iterator<Item = Units<'a>>) -> Ordering {
    let (mut x, mut y) = (Units::One(&[]), Units::One(&[]));
    loop {
        while x.is_empty() {
            let Some(next) = ca.next() else { return Ordering::Equal };
            x = next;
        }
        while y.is_empty() {
            let Some(next) = cb.next() else { return Ordering::Equal };
            y = next;
        }
        let n = x.len().min(y.len());
        match x.slice(0..n).compare(y.slice(0..n)) {
            Ordering::Equal => (x, y) = (x.slice(n..x.len()), y.slice(n..y.len())),
            order => return order,
        }
    }
}

#[inline]
pub fn equal<H: Host>(h: &H, a: H::Str, b: H::Str) -> Result<bool, H::Error> {
    if a == b {
        return Ok(true);
    }
    if let (Some(x), Some(y)) = (flat(h, a), flat(h, b)) {
        if x.len() != y.len() || x.width() != y.width() {
            return Ok(false);
        }
        h.charge(x.len() as u64)?;
        return Ok(x.equal(y));
    }
    rope_equal(h, a, b)
}

#[inline(never)]
fn rope_equal<H: Host>(h: &H, a: H::Str, b: H::Str) -> Result<bool, H::Error> {
    let (ia, fa) = summary(h, a);
    let (ib, fb) = summary(h, b);
    if ia.len != ib.len || ia.width != ib.width {
        return Ok(false);
    }
    h.charge(ia.len as u64)?;
    if let (Some(x), Some(y)) = (fa, fb) {
        return Ok(x.equal(y));
    }
    Ok(compare_chunks(h, a, b)? == Ordering::Equal)
}

/// Whether `s` holds the characters of `t`.
#[inline]
pub fn equal_str<H: Host>(h: &H, s: H::Str, t: &str) -> Result<bool, H::Error> {
    match flat(h, s) {
        Some(units) => units_equal_str(h, units, t),
        None => rope_equal_str(h, s, t),
    }
}

#[inline(never)]
fn rope_equal_str<H: Host>(h: &H, s: H::Str, t: &str) -> Result<bool, H::Error> {
    let (info, flat) = summary(h, s);
    if let Some(units) = flat {
        return units_equal_str(h, units, t);
    }
    if info.len > t.len() || info.len < t.len().div_ceil(4) {
        return Ok(false);
    }
    h.charge(info.len as u64)?;
    Ok(chars(h, s).eq(t.chars()))
}

#[inline]
fn units_equal_str<H: Host>(h: &H, units: Units<'_>, t: &str) -> Result<bool, H::Error> {
    // As many characters as `t` has bytes match only if `t` is ASCII: Latin-1 isn't UTF-8 past
    // it. A test for each kind rather than a match: names mix kinds, and a jump table guesses
    // worse.
    if let Units::Inline(p) = units
        && p.len() == t.len()
    {
        h.charge(t.len() as u64)?;
        return Ok(p.equal_ascii(t.as_bytes()));
    }
    if let Units::One(bytes) = units
        && bytes.len() == t.len()
    {
        h.charge(t.len() as u64)?;
        return Ok(word::equal_ascii(bytes, t.as_bytes()));
    }
    if let Units::Packed(p) = units
        && p.len() == t.len()
    {
        h.charge(t.len() as u64)?;
        return Ok(p.equal_ascii(t.as_bytes()));
    }
    if units.len() > t.len() || units.len() < t.len().div_ceil(4) {
        return Ok(false);
    }
    h.charge(units.len() as u64)?;
    Ok(units.chars().eq(t.chars()))
}

/// The characters of `s`, if it's flat.
#[inline]
fn flat<H: Host>(h: &H, s: H::Str) -> Option<Units<'_>> {
    match h.view(s) {
        StrView::Flat(u) => Some(u),
        StrView::Rope { .. } => None,
    }
}

/// What [`info`] says of `s`, and the characters of a flat string or of a rope's flat copy,
/// from one view.
fn summary<H: Host>(h: &H, s: H::Str) -> (Info, Option<Units<'_>>) {
    match h.view(s) {
        StrView::Flat(u) => (Info { len: u.len(), width: u.width(), depth: 0 }, Some(u)),
        StrView::Rope { info, flat: Some(flat), .. } => match h.view(flat) {
            StrView::Flat(u) => (info, Some(u)),
            StrView::Rope { .. } => (info, None),
        },
        StrView::Rope { info, .. } => (info, None),
    }
}

pub fn utf8_len<H: Host>(h: &H, s: H::Str) -> Result<usize, H::Error> {
    if let Some(units) = flat(h, s) {
        h.charge(units.len() as u64)?;
        return Ok(units.utf8_len());
    }
    h.charge(len(h, s) as u64)?;
    Ok(chunks(h, s).map(Units::utf8_len).sum())
}

/// Writes `s` as UTF-8, with `write!` or `to_string`.
pub fn display<H: Host>(h: &H, s: H::Str) -> Display<'_, H> {
    Display { h, s }
}

pub struct Display<'h, H: Host> {
    h: &'h H,
    s: H::Str,
}

impl<H: Host> fmt::Display for Display<'_, H> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut out = Utf8 { f, buf: [0; 256], n: 0 };
        match flat(self.h, self.s) {
            Some(units) => out.units(units)?,
            None => {
                for chunk in chunks(self.h, self.s) {
                    out.units(chunk)?;
                }
            }
        }
        out.flush()
    }
}

/// Characters encoded for a formatter, gathered so they're written a block at a time.
struct Utf8<'a, 'f> {
    f: &'a mut fmt::Formatter<'f>,
    buf: [u8; 256],
    n: usize,
}

impl Utf8<'_, '_> {
    fn flush(&mut self) -> fmt::Result {
        let n = std::mem::take(&mut self.n);
        self.f.write_str(std::str::from_utf8(&self.buf[..n]).expect("whole characters"))
    }

    /// Latin-1 bytes encoded into the buffer, which has room for them.
    #[inline]
    fn latin1(&mut self, bytes: &[u8]) {
        for &b in bytes {
            if b < 0x80 {
                self.buf[self.n] = b;
                self.n += 1;
            } else {
                self.buf[self.n..self.n + 2].copy_from_slice(&[0xC0 | b >> 6, 0x80 | b & 0x3F]);
                self.n += 2;
            }
        }
    }

    fn units(&mut self, units: Units<'_>) -> fmt::Result {
        match units {
            Units::One(bytes) if bytes.is_ascii() => {
                self.flush()?;
                self.f.write_str(std::str::from_utf8(bytes).expect("ASCII"))
            }
            // A block at a time: ASCII straight into the buffer, the rest encoded.
            Units::Packed(p) if p.width() == Width::One => {
                let ascii = p.is_ascii();
                for from in (0..p.len()).step_by(64) {
                    let k = (p.len() - from).min(64);
                    if self.n + 2 * k > self.buf.len() {
                        self.flush()?;
                    }
                    if ascii {
                        p.copy_bytes(from, &mut self.buf[self.n..self.n + k]);
                        self.n += k;
                        continue;
                    }
                    let mut block = [0; 64];
                    p.copy_bytes(from, &mut block[..k]);
                    self.latin1(&block[..k]);
                }
                Ok(())
            }
            Units::Inline(p) => {
                if self.n + 2 * p.len() > self.buf.len() {
                    self.flush()?;
                }
                self.latin1(&p.bytes()[..p.len()]);
                Ok(())
            }
            _ => {
                let mut written = Ok(());
                units.each_char(|c| {
                    if self.n + 4 > self.buf.len() {
                        written = written.and(self.flush());
                    }
                    self.n += c.encode_utf8(&mut self.buf[self.n..]).len();
                });
                written
            }
        }
    }
}
