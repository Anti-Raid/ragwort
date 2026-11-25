//! Building strings. Concatenation copies both strings when the result is small. Otherwise it joins
//! them into a rope, which stays balanced like an AVL tree: the depths of a node's two children differ by
//! at most one. When a short string is joined next to a short flat string at the edge of a rope, the two
//! are merged into one flat string. So building a string a piece at a time gives flat strings of about
//! [`LEAF`] bytes instead of one node per piece.

use crate::iter::MAX_DEPTH;
use crate::units::RunWriter;
use crate::{Chunks, Host, Info, MAX_LEN, Res, StrError, StrView, Units, byte_offset, info};

/// The maximum size, in bytes, of a result that concatenation copies instead of sharing its parts.
const LEAF: usize = 512;

/// A rope is flattened once it has been read by index once per `CHARS_PER_READ` of its
/// characters. By then the walks down to a leaf, at about 100ns each, have cost about as much as
/// copying the rope, at about 0.4ns per character.
pub(crate) const CHARS_PER_READ: u64 = 256;

fn fits(bytes: usize) -> bool {
    bytes <= LEAF
}

/// Returns `a` followed by `b`.
pub fn concat<H: Host>(h: &H, a: H::Str, b: H::Str) -> Res<H> {
    let (ia, ib) = (info(h, a), info(h, b));
    if ia.bytes == 0 {
        return Ok(b);
    }
    if ib.bytes == 0 {
        return Ok(a);
    }
    let bytes = ia.bytes + ib.bytes;
    if bytes > MAX_LEN {
        return Err(StrError::TooLong.into());
    }
    if fits(bytes) {
        return copy(h, &[a, b], bytes, ia.chars + ib.chars);
    }
    join(h, a, b)
}

/// Returns all of `parts` joined in order.
pub fn concat_all<H: Host>(h: &H, parts: &[H::Str]) -> Res<H> {
    if let [string] = parts {
        return Ok(*string);
    }
    let (mut bytes, mut chars) = (0usize, 0usize);
    for &part in parts {
        let part_info = info(h, part);
        bytes = bytes.saturating_add(part_info.bytes);
        chars += part_info.chars;
    }
    if bytes > MAX_LEN {
        return Err(StrError::TooLong.into());
    }
    if fits(bytes) {
        return copy(h, parts, bytes, chars);
    }
    let (left, right) = parts.split_at(parts.len() / 2);
    let left = concat_all(h, left)?;
    concat(h, left, concat_all(h, right)?)
}

/// Returns the characters of `string` from index `start` up to, but not including, `end`. Shares the parts of a rope that it can and copies the rest.
pub fn substring<H: Host>(h: &H, string: H::Str, start: usize, end: usize) -> Res<H> {
    let (from, to) = match h.view(string) {
        StrView::Flat { units, chars } => {
            if start > end || end > chars {
                return Err(StrError::OutOfRange.into());
            }
            if start == 0 && end == chars {
                return Ok(string);
            }
            if chars == units.len() {
                (start, end)
            } else {
                // The end is found from the start, so the characters before the start are counted once.
                let from = units.offset_of(start);
                (from, from + units.slice(from..units.len()).offset_of(end - start))
            }
        }
        StrView::Rope { info, .. } => {
            if start > end || end > info.chars {
                return Err(StrError::OutOfRange.into());
            }
            if start == 0 && end == info.chars {
                return Ok(string);
            }
            (byte_offset(h, string, start), byte_offset(h, string, end))
        }
    };
    sub(h, string, from, to, Some(end - start))
}

/// Returns the characters of `string` from byte offset `start` up to, but not including, byte offset `end`. Fails if either offset does not lie between two characters.
pub fn substring_bytes<H: Host>(h: &H, string: H::Str, start: usize, end: usize) -> Res<H> {
    if start > end || !crate::is_boundary(h, string, start) || !crate::is_boundary(h, string, end) {
        return Err(StrError::OutOfRange.into());
    }
    sub(h, string, start, end, None)
}

/// Returns the bytes of `string` from byte `start` up to, but not including, byte `end`, as a string. Both offsets are between characters.
/// `chars` is the number of characters in the range, if the caller knows it.
pub(crate) fn sub<H: Host>(h: &H, string: H::Str, start: usize, end: usize, chars: Option<usize>) -> Res<H> {
    let (whole, left, right) = match h.view(string) {
        StrView::Flat { units, .. } if start == 0 && end == units.len() => return Ok(string),
        StrView::Flat { units, chars: all } => {
            // In an ASCII string every byte is a character.
            let known = chars.or((all == units.len()).then_some(end - start));
            // A host that keeps long strings outside its heap can let the part share the bytes.
            if let Some(shared) = h.slice(string, start, end, known)? {
                return Ok(shared);
            }
            let part = units.slice(start..end);
            return copy_units(h, part, known.unwrap_or_else(|| part.count_chars()));
        }
        StrView::Rope { info, .. } if start == 0 && end == info.bytes => return Ok(string),
        StrView::Rope { left, right, info, .. } => (info, left, right),
    };
    if fits(end - start) {
        return copy_range(h, string, start, end, chars.or((whole.chars == whole.bytes).then_some(end - start)));
    }
    let left_bytes = info(h, left).bytes;
    if end <= left_bytes {
        sub(h, left, start, end, chars)
    } else if start >= left_bytes {
        sub(h, right, start - left_bytes, end - left_bytes, chars)
    } else {
        let left = sub(h, left, start, left_bytes, None)?;
        concat(h, left, sub(h, right, 0, end - left_bytes, None)?)
    }
}

/// Returns `string` as one flat string. A new flat copy of a rope is passed to [`Host::flattened`], so that the rope can keep it for later reads.
pub fn flatten<H: Host>(h: &H, string: H::Str) -> Res<H> {
    match h.view(string) {
        // A host can read a flattened rope as a flat string. The flat copy is then the string that it knows for the rope.
        StrView::Flat { .. } => Ok(h.known(string).unwrap_or(string)),
        StrView::Rope { flat: Some(flat), .. } => Ok(flat),
        StrView::Rope { info, .. } => {
            let flat = copy_range(h, string, 0, info.bytes, Some(info.chars))?;
            h.flattened(string, flat);
            Ok(flat)
        }
    }
}

/// Returns a flat copy of the bytes of `string` from byte `start` to byte `end`. `chars` is the number of characters in the range, if the caller knows it.
fn copy_range<H: Host>(h: &H, string: H::Str, start: usize, end: usize, chars: Option<usize>) -> Res<H> {
    let n = end - start;
    h.charge(n as u64)?;
    let chars = match chars {
        Some(chars) => chars,
        None => Chunks::new(h, string, start, end).map(Units::count_chars).sum(),
    };
    h.flat(n, chars, |mut out| {
        let mut at = 0;
        for run in Chunks::new(h, string, start, end) {
            out.write(at, run);
            at += run.len();
        }
    })
}

/// Returns a flat copy of `units`, which hold `chars` characters.
fn copy_units<H: Host>(h: &H, units: Units<'_>, chars: usize) -> Res<H> {
    h.charge(units.len() as u64)?;
    h.flat(units.len(), chars, |mut out| out.write(0, units))
}

/// Returns `parts` joined into one flat string. `bytes` is the number of bytes of the parts together, and `chars` is their number of characters.
fn copy<H: Host>(h: &H, parts: &[H::Str], bytes: usize, chars: usize) -> Res<H> {
    h.charge(bytes as u64)?;
    if bytes <= 8 {
        // The result is at most eight bytes, which is common. Shift the parts into one word.
        let (mut word, mut at) = (0, 0);
        for &part in parts {
            let StrView::Flat { units, .. } = h.view(part) else { break };
            if !units.is_empty() {
                word |= units.byte_chunk(0).checked_shl(8 * at as u32).unwrap_or(0);
                at += units.len();
            }
        }
        if at == bytes {
            return h.flat(bytes, chars, |mut out| out.write_words(std::iter::once(word)));
        }
    }
    h.flat(bytes, chars, |mut out| {
        let mut writer = RunWriter::new(&mut out);
        for &part in parts {
            match h.view(part) {
                StrView::Flat { units, .. } => writer.push(units),
                StrView::Rope { info, .. } => Chunks::new(h, part, 0, info.bytes).for_each(|run| writer.push(run)),
            }
        }
        writer.finish();
    })
}

fn children<H: Host>(h: &H, string: H::Str) -> (H::Str, H::Str) {
    match h.view(string) {
        StrView::Rope { left, right, .. } => (left, right),
        StrView::Flat { .. } => unreachable!("a node deeper than its sibling is a rope"),
    }
}

fn depth<H: Host>(h: &H, string: H::Str) -> u8 {
    info(h, string).depth
}

fn node<H: Host>(h: &H, left: H::Str, right: H::Str) -> Res<H> {
    let (left_info, right_info) = (info(h, left), info(h, right));
    let depth = left_info.depth.max(right_info.depth) + 1;
    debug_assert!((depth as usize) < MAX_DEPTH && left_info.depth.abs_diff(right_info.depth) <= 1, "unbalanced");
    h.rope(left, right, Info { bytes: left_info.bytes + right_info.bytes, chars: left_info.chars + right_info.chars, depth })
}

/// Returns `a` followed by `b` as a balanced rope. `a` and `b` must be nonempty and balanced. The depth of the result
/// is at most one more than the depth of the deeper of the two.
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

/// Returns `a` followed by `b`, whose depths differ by at most one. Where a flat string of `a` and a flat string of `b`
/// are adjacent and both are short, they are merged into one flat string.
fn pair<H: Host>(h: &H, a: H::Str, b: H::Str) -> Res<H> {
    #[inline(always)]
    fn merge(first: Info, second: Info) -> bool {
        fits(first.bytes + second.bytes)
    }
    let (ia, ib) = (info(h, a), info(h, b));
    if ia.depth == 0 && ib.depth == 0 && merge(ia, ib) {
        return copy(h, &[a, b], ia.bytes + ib.bytes, ia.chars + ib.chars);
    }
    // Here one side is a flat string and the other side is a rope whose adjacent child is flat. The merged string is flat,
    // like the child that it replaces, so the depth of the node does not change.
    if ib.depth == 0
        && let StrView::Rope { left, right, .. } = h.view(a)
        && depth(h, right) == 0
        && merge(info(h, right), ib)
    {
        let right_info = info(h, right);
        let right = copy(h, &[right, b], right_info.bytes + ib.bytes, right_info.chars + ib.chars)?;
        return node(h, left, right);
    }
    if ia.depth == 0
        && let StrView::Rope { left, right, .. } = h.view(b)
        && depth(h, left) == 0
        && merge(ia, info(h, left))
    {
        let left_info = info(h, left);
        let left = copy(h, &[a, left], ia.bytes + left_info.bytes, ia.chars + left_info.chars)?;
        return node(h, left, right);
    }
    node(h, a, b)
}
