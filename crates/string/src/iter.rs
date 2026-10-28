use crate::{Host, StrView, Units, len};

/// Deeper than any balanced rope of [`crate::MAX_LEN`] characters gets, about 69.
pub(crate) const MAX_DEPTH: usize = 72;

/// The flat runs of a range of a string, in order, none empty.
pub struct Chunks<'h, H: Host> {
    h: &'h H,
    /// What's left to visit, the next on top, below `top`.
    stack: [H::Str; MAX_DEPTH],
    top: usize,
    /// Characters to pass over before the range starts, and then how many it has left.
    skip: usize,
    left: usize,
}

impl<'h, H: Host> Chunks<'h, H> {
    pub(crate) fn new(h: &'h H, s: H::Str, start: usize, end: usize) -> Self {
        Self { h, stack: [s; MAX_DEPTH], top: 1, skip: start, left: end - start }
    }

    fn push(&mut self, s: H::Str) {
        self.stack[self.top] = s;
        self.top += 1;
    }
}

impl<'h, H: Host> Iterator for Chunks<'h, H> {
    type Item = Units<'h>;

    fn next(&mut self) -> Option<Units<'h>> {
        while self.left > 0 && self.top > 0 {
            self.top -= 1;
            let s = self.stack[self.top];
            match self.h.view(s) {
                StrView::Rope { info, .. } if self.skip >= info.len => self.skip -= info.len,
                StrView::Rope { flat: Some(flat), .. } => self.push(flat),
                StrView::Rope { left, right, .. } => {
                    self.push(right);
                    let l = len(self.h, left);
                    if self.skip >= l {
                        self.skip -= l;
                    } else {
                        self.push(left);
                    }
                }
                StrView::Flat(units) => {
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

/// The characters of a string.
pub struct Chars<'h, H: Host> {
    chunks: Chunks<'h, H>,
    run: Units<'h>,
    at: usize,
}

impl<'h, H: Host> Chars<'h, H> {
    pub(crate) fn new(chunks: Chunks<'h, H>) -> Self {
        Self { chunks, run: Units::One(&[]), at: 0 }
    }
}

impl<H: Host> Iterator for Chars<'_, H> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<char> {
        if self.at == self.run.len() {
            self.run = self.chunks.next()?;
            self.at = 0;
        }
        self.at += 1;
        self.run.get(self.at - 1)
    }
}
