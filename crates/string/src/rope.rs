//! Building strings. Concatenation copies when the result is small, and otherwise joins the
//! two into a rope that stays balanced like an AVL tree: no node's sides differ in depth by
//! more than one. Where a short string meets a short flat string at the edge of a rope, they
//! merge into one, so building a string a piece at a time gives flat strings of about
//! [`LEAF`] bytes instead of a node per piece.

use crate::iter::MAX_DEPTH;
use crate::{Chunks, Host, Info, MAX_LEN, Res, StrError, StrView, Units, Width, info, len};

/// The most bytes concatenation copies rather than sharing.
const LEAF: usize = 512;

/// A rope is flattened once it's been read by position once for every this many of its
/// characters: by then the walks down to a leaf, about 100ns each, have cost about what
/// copying it does, about 0.4ns a character.
pub(crate) const CHARS_PER_READ: u64 = 256;

fn fits(len: usize, width: Width) -> bool {
    len * width.bytes() <= LEAF
}

/// `a` then `b`.
pub fn concat<H: Host>(h: &H, a: H::Str, b: H::Str) -> Res<H> {
    let (ia, ib) = (info(h, a), info(h, b));
    if ia.len == 0 {
        return Ok(b);
    }
    if ib.len == 0 {
        return Ok(a);
    }
    let len = ia.len + ib.len;
    if len > MAX_LEN {
        return Err(StrError::TooLong.into());
    }
    if fits(len, ia.width.max(ib.width)) {
        return copy(h, &[a, b]);
    }
    join(h, a, b)
}

/// All of `parts` in order.
pub fn concat_all<H: Host>(h: &H, parts: &[H::Str]) -> Res<H> {
    if let [s] = parts {
        return Ok(*s);
    }
    let (mut len, mut width) = (0usize, Width::One);
    for &s in parts {
        let i = info(h, s);
        len = len.saturating_add(i.len);
        width = width.max(i.width);
    }
    if len > MAX_LEN {
        return Err(StrError::TooLong.into());
    }
    if fits(len, width) {
        return copy(h, parts);
    }
    let (left, right) = parts.split_at(parts.len() / 2);
    let left = concat_all(h, left)?;
    concat(h, left, concat_all(h, right)?)
}

/// The characters from `start` up to `end`. Shares what it can of a rope, and copies the rest.
pub fn substring<H: Host>(h: &H, s: H::Str, start: usize, end: usize) -> Res<H> {
    if start > end || end > len(h, s) {
        return Err(StrError::OutOfRange.into());
    }
    sub(h, s, start, end)
}

fn sub<H: Host>(h: &H, s: H::Str, start: usize, end: usize) -> Res<H> {
    let i = info(h, s);
    if start == 0 && end == i.len {
        return Ok(s);
    }
    let StrView::Rope { left, right, .. } = h.view(s) else { return copy_range(h, s, start, end) };
    if fits(end - start, i.width) {
        return copy_range(h, s, start, end);
    }
    let l = len(h, left);
    if end <= l {
        sub(h, left, start, end)
    } else if start >= l {
        sub(h, right, start - l, end - l)
    } else {
        let left = sub(h, left, start, l)?;
        concat(h, left, sub(h, right, 0, end - l)?)
    }
}

/// `s` as one flat string, which a rope then keeps for reading from.
pub fn flatten<H: Host>(h: &H, s: H::Str) -> Res<H> {
    match h.view(s) {
        StrView::Flat(_) => Ok(s),
        StrView::Rope { flat: Some(flat), .. } => Ok(flat),
        StrView::Rope { info, .. } => {
            let flat = copy_range(h, s, 0, info.len)?;
            h.flattened(s, flat);
            Ok(flat)
        }
    }
}

/// A flat copy of part of `s`, at the narrowest width that holds it.
fn copy_range<H: Host>(h: &H, s: H::Str, start: usize, end: usize) -> Res<H> {
    let n = end - start;
    h.charge(n as u64)?;
    let whole = info(h, s);
    let width = if n == whole.len {
        whole.width
    } else {
        Chunks::new(h, s, start, end).map(Units::narrowest).max().unwrap_or(Width::One)
    };
    h.flat(width, n, |mut out| {
        let mut at = 0;
        for run in Chunks::new(h, s, start, end) {
            out.write(at, run);
            at += run.len();
        }
    })
}

/// `parts` in one flat string.
fn copy<H: Host>(h: &H, parts: &[H::Str]) -> Res<H> {
    let (mut n, mut width) = (0, Width::One);
    for &s in parts {
        let i = info(h, s);
        n += i.len;
        width = width.max(i.width);
    }
    h.charge(n as u64)?;
    h.flat(width, n, |mut out| {
        let mut at = 0;
        for &s in parts {
            for run in Chunks::new(h, s, 0, len(h, s)) {
                out.write(at, run);
                at += run.len();
            }
        }
    })
}

fn children<H: Host>(h: &H, s: H::Str) -> (H::Str, H::Str) {
    match h.view(s) {
        StrView::Rope { left, right, .. } => (left, right),
        StrView::Flat(_) => unreachable!("a node deeper than its sibling is a rope"),
    }
}

fn depth<H: Host>(h: &H, s: H::Str) -> u8 {
    info(h, s).depth
}

fn node<H: Host>(h: &H, left: H::Str, right: H::Str) -> Res<H> {
    let (l, r) = (info(h, left), info(h, right));
    let depth = l.depth.max(r.depth) + 1;
    debug_assert!((depth as usize) < MAX_DEPTH && l.depth.abs_diff(r.depth) <= 1, "unbalanced");
    h.rope(left, right, Info { len: l.len + r.len, width: l.width.max(r.width), depth })
}

/// `a` then `b`, both nonempty and balanced, as a balanced rope. Its depth is at most one
/// more than the deeper of the two.
fn join<H: Host>(h: &H, a: H::Str, b: H::Str) -> Res<H> {
    let (da, db) = (depth(h, a), depth(h, b));
    if da > db + 1 {
        let (l, r) = children(h, a);
        let t = join(h, r, b)?;
        if depth(h, t) <= depth(h, l) + 1 {
            return node(h, l, t);
        }
        // `t` is two deeper than `l`, so rotate.
        let (tl, tr) = children(h, t);
        if depth(h, tl) <= depth(h, tr) {
            let left = node(h, l, tl)?;
            return node(h, left, tr);
        }
        let (tll, tlr) = children(h, tl);
        let (left, right) = (node(h, l, tll)?, node(h, tlr, tr)?);
        return node(h, left, right);
    }
    if db > da + 1 {
        let (l, r) = children(h, b);
        let t = join(h, a, l)?;
        if depth(h, t) <= depth(h, r) + 1 {
            return node(h, t, r);
        }
        let (tl, tr) = children(h, t);
        if depth(h, tr) <= depth(h, tl) {
            let right = node(h, tr, r)?;
            return node(h, tl, right);
        }
        let (trl, trr) = children(h, tr);
        let (left, right) = (node(h, tl, trl)?, node(h, trr, r)?);
        return node(h, left, right);
    }
    pair(h, a, b)
}

/// `a` then `b`, whose depths differ by one at most, merging flat strings that meet where
/// both are short.
fn pair<H: Host>(h: &H, a: H::Str, b: H::Str) -> Res<H> {
    let (ia, ib) = (info(h, a), info(h, b));
    let merge = |x: Info, y: Info| fits(x.len + y.len, x.width.max(y.width));
    if ia.depth == 0 && ib.depth == 0 && merge(ia, ib) {
        return copy(h, &[a, b]);
    }
    // A flat string beside a flat child sits next to a node at most two deep, whose other
    // child is at most one deep, so merging keeps the node's depth.
    if ib.depth == 0
        && let StrView::Rope { left, right, .. } = h.view(a)
        && depth(h, right) == 0
        && merge(info(h, right), ib)
    {
        let right = copy(h, &[right, b])?;
        return node(h, left, right);
    }
    if ia.depth == 0
        && let StrView::Rope { left, right, .. } = h.view(b)
        && depth(h, left) == 0
        && merge(ia, info(h, left))
    {
        let left = copy(h, &[a, left])?;
        return node(h, left, right);
    }
    node(h, a, b)
}
