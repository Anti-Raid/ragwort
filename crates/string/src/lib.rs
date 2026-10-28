//! Immutable strings over any heap. A string is flat, its characters in one array at the
//! narrowest width that holds them all, one, two or four bytes each, or a rope: a balanced
//! tree of strings that [`concat`] builds when copying would cost more than it saves. The heap
//! implements [`Host`] and the library does the rest, without allocating anywhere else. A
//! flat string's characters can also live outside the heap, as an [`External`].

mod external;
mod hash;
mod intern;
mod iter;
mod rope;
mod units;

#[cfg(test)]
mod testing;
#[cfg(test)]
mod tests;

use std::cmp::Ordering;
use std::fmt;

pub use external::{External, ExternalText, check_external};
pub use hash::{hash, hash_str};
pub use intern::{Table, intern, intern_str};
pub use iter::{Chars, Chunks};
pub use rope::{concat, concat_all, flatten, substring};
pub use units::{Units, UnitsMut, Width};

/// The longest string: a rope can share one string many times over, so length isn't bounded
/// by memory.
pub const MAX_LEN: usize = (1 << 48) - 1;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum StrError {
    OutOfRange,
    TooLong,
    /// External characters stored wider than they need.
    NotNarrowest,
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
        return h.flat(Width::One, s.len(), |u| {
            let UnitsMut::One(u) = u else { unreachable!("asked for width one") };
            u.copy_from_slice(s.as_bytes());
        });
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
pub fn char_at<H: Host>(h: &H, mut s: H::Str, mut i: usize) -> Result<char, H::Error> {
    if let StrView::Rope { info, flat: None, .. } = h.view(s)
        && h.count_read(s).saturating_mul(rope::CHARS_PER_READ) >= info.len as u64
    {
        s = flatten(h, s)?;
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
pub fn compare<H: Host>(h: &H, a: H::Str, b: H::Str) -> Result<Ordering, H::Error> {
    if a == b {
        return Ok(Ordering::Equal);
    }
    let ((ia, fa), (ib, fb)) = (summary(h, a), summary(h, b));
    let (la, lb) = (ia.len, ib.len);
    h.charge(la.min(lb) as u64)?;
    if let (Some(x), Some(y)) = (fa, fb) {
        let n = la.min(lb);
        return Ok(x.slice(0..n).compare(y.slice(0..n)).then(la.cmp(&lb)));
    }
    let (mut ca, mut cb) = (chunks(h, a), chunks(h, b));
    let (mut x, mut y) = (Units::One(&[]), Units::One(&[]));
    loop {
        while x.is_empty() {
            let Some(next) = ca.next() else { return Ok(la.cmp(&lb)) };
            x = next;
        }
        while y.is_empty() {
            let Some(next) = cb.next() else { return Ok(la.cmp(&lb)) };
            y = next;
        }
        let n = x.len().min(y.len());
        match x.slice(0..n).compare(y.slice(0..n)) {
            Ordering::Equal => (x, y) = (x.slice(n..x.len()), y.slice(n..y.len())),
            order => return Ok(order),
        }
    }
}

pub fn equal<H: Host>(h: &H, a: H::Str, b: H::Str) -> Result<bool, H::Error> {
    if a == b {
        return Ok(true);
    }
    let (ia, fa) = summary(h, a);
    let (ib, fb) = summary(h, b);
    if ia.len != ib.len || ia.width != ib.width {
        return Ok(false);
    }
    if let (Some(x), Some(y)) = (fa, fb) {
        h.charge(ia.len as u64)?;
        return Ok(x.equal(y));
    }
    Ok(compare(h, a, b)? == Ordering::Equal)
}

/// Whether `s` holds the characters of `t`.
pub fn equal_str<H: Host>(h: &H, s: H::Str, t: &str) -> Result<bool, H::Error> {
    let (info, flat) = summary(h, s);
    if let Some(Units::One(bytes)) = flat
        && bytes.len() == t.len()
    {
        h.charge(t.len() as u64)?;
        // Equal bytes are equal characters only if they're ASCII: Latin-1 isn't UTF-8 past it.
        return Ok(bytes == t.as_bytes() && t.is_ascii());
    }
    if info.len > t.len() || info.len < t.len().div_ceil(4) {
        return Ok(false);
    }
    h.charge(info.len as u64)?;
    Ok(match flat {
        Some(units) => units.chars().eq(t.chars()),
        None => chars(h, s).eq(t.chars()),
    })
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
        let mut buf = [0; 256];
        let mut n = 0;
        for chunk in chunks(self.h, self.s) {
            if let Units::One(bytes) = chunk
                && bytes.is_ascii()
            {
                f.write_str(flush(&buf[..n]))?;
                n = 0;
                f.write_str(std::str::from_utf8(bytes).expect("ASCII"))?;
                continue;
            }
            for c in chunk.chars() {
                if n + 4 > buf.len() {
                    f.write_str(flush(&buf[..n]))?;
                    n = 0;
                }
                n += c.encode_utf8(&mut buf[n..]).len();
            }
        }
        f.write_str(flush(&buf[..n]))
    }
}

fn flush(encoded: &[u8]) -> &str {
    std::str::from_utf8(encoded).expect("whole characters")
}
