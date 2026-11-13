//! Building strings. Concatenation copies when the result is small, and otherwise joins the
//! two into a rope that stays balanced like an AVL tree: no node's sides differ in depth by
//! more than one. Where a short string meets a short flat string at the edge of a rope, they
//! merge into one, so building a string a piece at a time gives flat strings of about
//! [`LEAF`] bytes instead of a node per piece.

use crate::iter::MAX_DEPTH;
use crate::units::RunWriter;
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
    if let [string] = parts {
        return Ok(*string);
    }
    let (mut len, mut width) = (0usize, Width::One);
    for &part in parts {
        let part_info = info(h, part);
        len = len.saturating_add(part_info.len);
        width = width.max(part_info.width);
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
pub fn substring<H: Host>(h: &H, string: H::Str, start: usize, end: usize) -> Res<H> {
    if start > end || end > len(h, string) {
        return Err(StrError::OutOfRange.into());
    }
    sub(h, string, start, end)
}

fn sub<H: Host>(h: &H, string: H::Str, start: usize, end: usize) -> Res<H> {
    let whole = info(h, string);
    if start == 0 && end == whole.len {
        return Ok(string);
    }
    let (left, right) = match h.view(string) {
        StrView::Flat(units) => return copy_units(h, units.slice(start..end)),
        StrView::Rope { left, right, .. } => (left, right),
    };
    if fits(end - start, whole.width) {
        return copy_range(h, string, start, end);
    }
    let left_len = len(h, left);
    if end <= left_len {
        sub(h, left, start, end)
    } else if start >= left_len {
        sub(h, right, start - left_len, end - left_len)
    } else {
        let left = sub(h, left, start, left_len)?;
        concat(h, left, sub(h, right, 0, end - left_len)?)
    }
}

/// `string` as one flat string, which a rope then keeps for reading from.
pub fn flatten<H: Host>(h: &H, string: H::Str) -> Res<H> {
    match h.view(string) {
        StrView::Flat(_) => Ok(string),
        StrView::Rope { flat: Some(flat), .. } => Ok(flat),
        StrView::Rope { info, .. } => {
            let flat = copy_range(h, string, 0, info.len)?;
            h.flattened(string, flat);
            Ok(flat)
        }
    }
}

/// A flat copy of part of `string`, at the narrowest width that holds it.
fn copy_range<H: Host>(h: &H, string: H::Str, start: usize, end: usize) -> Res<H> {
    let n = end - start;
    h.charge(n as u64)?;
    let whole = info(h, string);
    let width = if n == whole.len {
        whole.width
    } else {
        Chunks::new(h, string, start, end).map(Units::narrowest).max().unwrap_or(Width::One)
    };
    h.flat(width, n, |mut out| {
        let mut at = 0;
        for run in Chunks::new(h, string, start, end) {
            out.write(at, run);
            at += run.len();
        }
    })
}

/// A flat copy of `units`, at the narrowest width that holds them.
fn copy_units<H: Host>(h: &H, units: Units<'_>) -> Res<H> {
    h.charge(units.len() as u64)?;
    h.flat(units.narrowest(), units.len(), |mut out| out.write(0, units))
}

/// `parts` in one flat string.
fn copy<H: Host>(h: &H, parts: &[H::Str]) -> Res<H> {
    let (mut n, mut width) = (0, Width::One);
    for &part in parts {
        let part_info = info(h, part);
        n += part_info.len;
        width = width.max(part_info.width);
    }
    h.charge(n as u64)?;
    if width == Width::One && n <= 8 {
        // Short and narrow, as much text is: the parts shift into one word.
        let (mut word, mut at) = (0, 0);
        for &part in parts {
            let StrView::Flat(units) = h.view(part) else { break };
            if !units.is_empty() {
                word |= units.byte_chunk(0).checked_shl(8 * at as u32).unwrap_or(0);
                at += units.len();
            }
        }
        if at == n {
            return h.flat(width, n, |mut out| out.write_words(std::iter::once(word)));
        }
    }
    h.flat(width, n, |mut out| {
        let mut writer = RunWriter::new(&mut out);
        for &part in parts {
            match h.view(part) {
                StrView::Flat(units) => writer.push(units),
                StrView::Rope { .. } => Chunks::new(h, part, 0, len(h, part)).for_each(|run| writer.push(run)),
            }
        }
        writer.finish();
    })
}

fn children<H: Host>(h: &H, string: H::Str) -> (H::Str, H::Str) {
    match h.view(string) {
        StrView::Rope { left, right, .. } => (left, right),
        StrView::Flat(_) => unreachable!("a node deeper than its sibling is a rope"),
    }
}

fn depth<H: Host>(h: &H, string: H::Str) -> u8 {
    info(h, string).depth
}

fn node<H: Host>(h: &H, left: H::Str, right: H::Str) -> Res<H> {
    let (left_info, right_info) = (info(h, left), info(h, right));
    let depth = left_info.depth.max(right_info.depth) + 1;
    debug_assert!((depth as usize) < MAX_DEPTH && left_info.depth.abs_diff(right_info.depth) <= 1, "unbalanced");
    h.rope(left, right, Info { len: left_info.len + right_info.len, width: left_info.width.max(right_info.width), depth })
}

/// `a` then `b`, both nonempty and balanced, as a balanced rope. Its depth is at most one
/// more than the deeper of the two.
fn join<H: Host>(h: &H, a: H::Str, b: H::Str) -> Res<H> {
    let (da, db) = (depth(h, a), depth(h, b));
    if da > db + 1 {
        let (a_left, a_right) = children(h, a);
        let joined = join(h, a_right, b)?;
        if depth(h, joined) <= depth(h, a_left) + 1 {
            return node(h, a_left, joined);
        }
        // `joined` is two deeper than `a_left`, so rotate.
        let (tl, tr) = children(h, joined);
        if depth(h, tl) <= depth(h, tr) {
            let left = node(h, a_left, tl)?;
            return node(h, left, tr);
        }
        let (tll, tlr) = children(h, tl);
        let (left, right) = (node(h, a_left, tll)?, node(h, tlr, tr)?);
        return node(h, left, right);
    }
    if db > da + 1 {
        let (b_left, b_right) = children(h, b);
        let joined = join(h, a, b_left)?;
        if depth(h, joined) <= depth(h, b_right) + 1 {
            return node(h, joined, b_right);
        }
        let (tl, tr) = children(h, joined);
        if depth(h, tr) <= depth(h, tl) {
            let right = node(h, tr, b_right)?;
            return node(h, tl, right);
        }
        let (trl, trr) = children(h, tr);
        let (left, right) = (node(h, tl, trl)?, node(h, trr, b_right)?);
        return node(h, left, right);
    }
    pair(h, a, b)
}

/// `a` then `b`, whose depths differ by one at most, merging flat strings that meet where
/// both are short.
fn pair<H: Host>(h: &H, a: H::Str, b: H::Str) -> Res<H> {
    let (ia, ib) = (info(h, a), info(h, b));
    let merge = |first: Info, second: Info| fits(first.len + second.len, first.width.max(second.width));
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
