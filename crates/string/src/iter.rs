use crate::{Host, StrView, Units};

/// An upper bound on the depth of a balanced rope. A rope of [`crate::MAX_LEN`] bytes is at most about 69 deep.
pub(crate) const MAX_DEPTH: usize = 72;

/// Iterator over the flat runs in a range of a string's bytes, in order. No run is empty. If the range starts and ends between characters, every run holds whole characters.
pub struct Chunks<'h, H: Host> {
    h: &'h H,
    /// The strings still to visit. The entries below index `top` are live, and the next string to visit is at `top - 1`.
    stack: [H::Str; MAX_DEPTH],
    top: usize,
    /// `skip` is the number of bytes to skip before the range starts. `left` is the number of bytes remaining in the range.
    skip: usize,
    left: usize,
}

impl<'h, H: Host> Chunks<'h, H> {
    /// Returns the runs of `string` from byte `start` up to, but not including, byte `end`.
    pub(crate) fn new(h: &'h H, string: H::Str, start: usize, end: usize) -> Self {
        Self { h, stack: [string; MAX_DEPTH], top: 1, skip: start, left: end - start }
    }

    fn push(&mut self, string: H::Str) {
        self.stack[self.top] = string;
        self.top += 1;
    }
}

impl<H: Host> Clone for Chunks<'_, H> {
    fn clone(&self) -> Self {
        Self { stack: self.stack, ..*self }
    }
}

impl<'h, H: Host> Iterator for Chunks<'h, H> {
    type Item = Units<'h>;

    fn next(&mut self) -> Option<Units<'h>> {
        while self.left > 0 && self.top > 0 {
            self.top -= 1;
            let string = self.stack[self.top];
            match self.h.view(string) {
                StrView::Rope { info, .. } if self.skip >= info.bytes => self.skip -= info.bytes,
                StrView::Rope { flat: Some(flat), .. } => self.push(flat),
                StrView::Rope { left, right, .. } => {
                    self.push(right);
                    let left_bytes = crate::info(self.h, left).bytes;
                    if self.skip >= left_bytes {
                        self.skip -= left_bytes;
                    } else {
                        self.push(left);
                    }
                }
                StrView::Flat { units, .. } => {
                    if self.skip >= units.len() {
                        self.skip -= units.len();
                        continue;
                    }
                    let end = units.len().min(self.skip + self.left);
                    let run = units.slice(self.skip..end);
                    self.skip = 0;
                    self.left -= run.len();
                    return Some(run);
                }
            }
        }
        None
    }
}

/// Iterator over the characters of a string.
pub struct Chars<'h, H: Host> {
    chunks: Chunks<'h, H>,
    run: Units<'h>,
    /// The byte offset of the next character in `run`.
    at: usize,
}

impl<'h, H: Host> Chars<'h, H> {
    pub(crate) fn new(chunks: Chunks<'h, H>) -> Self {
        Self { chunks, run: Units::Slice(&[]), at: 0 }
    }
}

impl<H: Host> Clone for Chars<'_, H> {
    fn clone(&self) -> Self {
        Self { chunks: self.chunks.clone(), ..*self }
    }
}

impl<H: Host> Iterator for Chars<'_, H> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<char> {
        if self.at >= self.run.len() {
            self.run = self.chunks.next()?;
            self.at = 0;
        }
        let (character, size) = self.run.char_at(self.at);
        self.at += size;
        Some(character)
    }
}
