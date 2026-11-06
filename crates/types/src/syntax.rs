//! Syntax, lexical context, and source locations, in the arena.
//!
//! Syntax spans keep their source's metadata. A [`SyntaxSession`] separately keeps the source
//! bytes alive; dropping its last clone allows the text to be collected.

use crate::gc::{ForeignRoot, FrozenRef, Gc, Mutation, OutOfMemory, Root, Value};
use crate::objects::{
    self, Data, SessionFields, SyntaxContextFields, SyntaxFields, SyntaxMetaFields, SyntaxOriginFields, SyntaxSourceFields,
    SyntaxTextFields,
};

#[cfg(test)]
#[path = "tests/syntax.rs"]
mod tests;

/// Source bytes, without an encoding requirement.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct SyntaxText<'gc>(Gc<'gc, objects::SyntaxText>);

impl<'gc> SyntaxText<'gc> {
    pub fn new(mc: &Mutation<'gc>, bytes: impl AsRef<[u8]>) -> Result<Self, OutOfMemory> {
        let bytes = bytes.as_ref();
        let copy = frozen_slice(mc, bytes.len(), |out| out.copy_from_slice(bytes))?;
        Ok(Self(objects::SyntaxText::new(mc, copy)?))
    }

    pub fn bytes(self, mc: &Mutation<'gc>) -> &'gc [u8] {
        self.0.bytes(mc).map_or(&[], |b| b)
    }
}

/// Source metadata: a name, the text while a session keeps it, and where lines start.
/// Sessions keep the text; spans keep only this.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct SyntaxSource<'gc>(Gc<'gc, objects::SyntaxSource>);

impl<'gc> SyntaxSource<'gc> {
    pub fn name(self, mc: &Mutation<'gc>) -> Option<SyntaxText<'gc>> {
        self.0.name(mc).map(SyntaxText)
    }

    /// Returns `None` once the text has been collected.
    pub fn text(self, mc: &Mutation<'gc>) -> Option<SyntaxText<'gc>> {
        self.0.text(mc).map(SyntaxText)
    }

    #[inline]
    pub fn byte_len(self, mc: &Mutation<'gc>) -> usize {
        self.0.size(mc) as usize
    }

    /// Each line's first byte offset, from zero.
    pub fn line_starts(self, mc: &Mutation<'gc>) -> &'gc [u32] {
        self.0.lines(mc).map_or(&[], |l| l)
    }

    /// Looks up a byte offset, including EOF. Works after the text is collected.
    pub fn location(self, mc: &Mutation<'gc>, offset: u32) -> Option<SyntaxLocation> {
        if offset as usize > self.byte_len(mc) {
            return None;
        }
        let starts = self.line_starts(mc);
        let line = starts.partition_point(|&start| start <= offset);
        let start = *starts.get(line.checked_sub(1)?)?;
        Some(SyntaxLocation { line: line as u32, column: offset - start + 1 })
    }
}

/// One-based line and column. Columns count bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SyntaxLocation {
    pub line: u32,
    pub column: u32,
}

/// Keeps one source and its text alive across steps. Dropping the last clone releases the
/// text for collection, while surviving spans keep the source metadata.
#[derive(Clone)]
pub struct SyntaxSession {
    root: Root<objects::Session>,
}

impl SyntaxSession {
    pub fn new(mc: &Mutation<'_>, bytes: impl AsRef<[u8]>) -> Result<Self, OutOfMemory> {
        Self::create(mc, None, bytes.as_ref())
    }

    pub fn named(mc: &Mutation<'_>, name: &str, bytes: impl AsRef<[u8]>) -> Result<Self, OutOfMemory> {
        Self::create(mc, Some(name), bytes.as_ref())
    }

    fn create(mc: &Mutation<'_>, name: Option<&str>, bytes: &[u8]) -> Result<Self, OutOfMemory> {
        let len = u32::try_from(bytes.len()).map_err(|_| mc.out_of_memory())?;
        let text = SyntaxText::new(mc, bytes)?;
        let name = name.map(|name| SyntaxText::new(mc, name)).transpose()?;
        let lines = frozen_slice(mc, line_starts(bytes).count(), |out| out.iter_mut().zip(line_starts(bytes)).for_each(|(o, start)| *o = start))?;
        let source = objects::SyntaxSource::new(mc, name.map(|n| n.0), Some(text.0), u64::from(len), lines)?;
        let session = objects::Session::new(mc, Some(source), Some(text.0))?;
        Ok(Self { root: Root::new(mc, session)? })
    }

    pub fn source<'gc>(&self, mc: &Mutation<'gc>) -> Result<SyntaxSource<'gc>, ForeignRoot> {
        Ok(SyntaxSource(self.root.get(mc)?.source(mc).expect("a session has its source")))
    }

    pub fn text<'gc>(&self, mc: &Mutation<'gc>) -> Result<SyntaxText<'gc>, ForeignRoot> {
        Ok(SyntaxText(self.root.get(mc)?.text(mc).expect("a session has its text")))
    }
}

/// `len` zeroed items that `fill` sets, frozen and charged their size, failing as an allocation
/// would rather than aborting when the system has no room for them.
fn frozen_slice<'gc, T: Copy + Default + 'static>(
    mc: &Mutation<'gc>,
    len: usize,
    fill: impl FnOnce(&mut [T]),
) -> Result<FrozenRef<'gc, Box<[T]>>, OutOfMemory> {
    let mut items = Vec::new();
    items.try_reserve_exact(len).map_err(|_| mc.out_of_memory())?;
    items.resize(len, T::default());
    fill(&mut items);
    mc.frozen_owning(items.into_boxed_slice(), len * size_of::<T>())
}

fn line_starts(bytes: &[u8]) -> impl Iterator<Item = u32> + '_ {
    std::iter::once(0).chain(bytes.iter().enumerate().filter_map(|(i, &byte)| {
        // CRLF is one newline; a lone CR also starts a line.
        (byte == b'\n' || byte == b'\r' && bytes.get(i + 1) != Some(&b'\n')).then_some((i + 1) as u32)
    }))
}

/// A source range `start..end`, measured in bytes. Keeps the metadata alive, not the text.
/// A default span has no source.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SyntaxSpan<'gc> {
    source: Option<SyntaxSource<'gc>>,
    start: u32,
    end: u32,
}

impl<'gc> SyntaxSpan<'gc> {
    /// Checks `start <= end <= source.byte_len()`.
    #[inline]
    pub fn new(mc: &Mutation<'gc>, source: SyntaxSource<'gc>, start: u32, end: u32) -> Option<Self> {
        (start <= end && end as usize <= source.byte_len(mc)).then_some(Self { source: Some(source), start, end })
    }

    fn of(source: Option<Gc<'gc, objects::SyntaxSource>>, word: u64) -> Self {
        Self { source: source.map(SyntaxSource), start: word as u32, end: (word >> 32) as u32 }
    }

    fn source_gc(self) -> Option<Gc<'gc, objects::SyntaxSource>> {
        self.source.map(|s| s.0)
    }

    fn word(self) -> u64 {
        u64::from(self.start) | u64::from(self.end) << 32
    }

    pub fn source(self) -> Option<SyntaxSource<'gc>> {
        self.source
    }

    pub fn location(self, mc: &Mutation<'gc>) -> Option<SyntaxLocation> {
        self.source?.location(mc, self.start)
    }

    pub fn start(self) -> u32 {
        self.start
    }

    pub fn end(self) -> u32 {
        self.end
    }
}

/// A scope ID. Identifiers with the same name can belong to different scopes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SyntaxScope(pub u64);

/// An identifier's scopes.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct SyntaxContext<'gc>(Gc<'gc, objects::SyntaxContext>);

impl<'gc> SyntaxContext<'gc> {
    pub fn new(mc: &Mutation<'gc>, scopes: &[SyntaxScope]) -> Result<Self, OutOfMemory> {
        let context = objects::SyntaxContext::new(mc, scopes.len(), 0)?;
        let items = context.items(mc);
        for (i, scope) in scopes.iter().enumerate() {
            items.set(mc, i, scope.0);
        }
        Ok(Self(context))
    }

    pub fn scopes(self, mc: &Mutation<'gc>) -> impl ExactSizeIterator<Item = SyntaxScope> + use<'gc> {
        let items = self.0.items(mc);
        (0..items.len()).map(move |i| SyntaxScope(items.get(i)))
    }
}

/// A source location in an expansion's history. `parent` links to the preceding origin.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct SyntaxOrigin<'gc>(Gc<'gc, objects::SyntaxOrigin>);

impl<'gc> SyntaxOrigin<'gc> {
    pub fn new(mc: &Mutation<'gc>, span: SyntaxSpan<'gc>, parent: Option<Self>) -> Result<Self, OutOfMemory> {
        Ok(Self(objects::SyntaxOrigin::new(mc, span.source_gc(), span.word(), parent.map(|p| p.0))?))
    }

    pub fn span(self, mc: &Mutation<'gc>) -> SyntaxSpan<'gc> {
        SyntaxSpan::of(self.0.source(mc), self.0.span(mc))
    }

    pub fn parent(self, mc: &Mutation<'gc>) -> Option<Self> {
        self.0.parent(mc).map(Self)
    }
}

crate::named! {
    /// Reader shorthand for quotation and unquotation, of data and of syntax, named for the form
    /// each stands for.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum Abbreviation {
        /// `'`
        Quote = "quote",
        /// `` ` ``
        Quasiquote = "quasiquote",
        /// `,`
        Unquote = "unquote",
        /// `,@`
        UnquoteSplicing = "unquote-splicing",
        /// `#'`
        Syntax = "syntax",
        /// `` #` ``
        Quasisyntax = "quasisyntax",
        /// `#,`
        Unsyntax = "unsyntax",
        /// `#,@`
        UnsyntaxSplicing = "unsyntax-splicing",
    }
}

/// The shape of a reader datum.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SyntaxKind {
    /// A number, string, boolean, or character.
    Literal,
    /// An interned symbol, resolved in the node's lexical context.
    Identifier,
    /// `()` or pairs whose heads are syntax nodes. A dotted tail is another syntax node;
    /// a proper list ends in `()`.
    List,
    /// An immutable vector of syntax nodes.
    Vector,
    /// The datum is the prefix's operand, wrapped in a syntax node.
    Abbreviation(Abbreviation),
}

impl SyntaxKind {
    fn tag(self) -> u32 {
        match self {
            Self::Literal => 0,
            Self::Identifier => 1,
            Self::List => 2,
            Self::Vector => 3,
            Self::Abbreviation(Abbreviation::Quote) => 4,
            Self::Abbreviation(Abbreviation::Quasiquote) => 5,
            Self::Abbreviation(Abbreviation::Unquote) => 6,
            Self::Abbreviation(Abbreviation::UnquoteSplicing) => 7,
            Self::Abbreviation(Abbreviation::Syntax) => 8,
            Self::Abbreviation(Abbreviation::Quasisyntax) => 9,
            Self::Abbreviation(Abbreviation::Unsyntax) => 10,
            Self::Abbreviation(Abbreviation::UnsyntaxSplicing) => 11,
        }
    }

    fn from_tag(tag: u32) -> Option<Self> {
        Some(match tag {
            0 => Self::Literal,
            1 => Self::Identifier,
            2 => Self::List,
            3 => Self::Vector,
            4 => Self::Abbreviation(Abbreviation::Quote),
            5 => Self::Abbreviation(Abbreviation::Quasiquote),
            6 => Self::Abbreviation(Abbreviation::Unquote),
            7 => Self::Abbreviation(Abbreviation::UnquoteSplicing),
            8 => Self::Abbreviation(Abbreviation::Syntax),
            9 => Self::Abbreviation(Abbreviation::Quasisyntax),
            10 => Self::Abbreviation(Abbreviation::Unsyntax),
            11 => Self::Abbreviation(Abbreviation::UnsyntaxSplicing),
            _ => return None,
        })
    }
}

/// Kind, lexical context and expansion origin, shared by syntax nodes.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct SyntaxMeta<'gc>(Gc<'gc, objects::SyntaxMeta>);

impl<'gc> SyntaxMeta<'gc> {
    pub fn new(
        mc: &Mutation<'gc>,
        kind: SyntaxKind,
        context: Option<SyntaxContext<'gc>>,
        origin: Option<SyntaxOrigin<'gc>>,
    ) -> Result<Self, OutOfMemory> {
        Ok(Self(objects::SyntaxMeta::new(mc, kind.tag(), context.map(|c| c.0), origin.map(|o| o.0))?))
    }

    /// Returns `None` if the stored tag is invalid.
    pub fn kind(self, mc: &Mutation<'gc>) -> Option<SyntaxKind> {
        SyntaxKind::from_tag(self.0.kind(mc))
    }

    pub fn context(self, mc: &Mutation<'gc>) -> Option<SyntaxContext<'gc>> {
        self.0.context(mc).map(SyntaxContext)
    }

    pub fn origin(self, mc: &Mutation<'gc>) -> Option<SyntaxOrigin<'gc>> {
        self.0.origin(mc).map(SyntaxOrigin)
    }
}

/// A datum and its span. Absent metadata means a literal without context or origin.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Syntax<'gc>(Gc<'gc, objects::Syntax>);

impl<'gc> Syntax<'gc> {
    /// Metadata describes the datum's shape; this does not check that they agree.
    #[inline]
    pub fn new(mc: &Mutation<'gc>, datum: Value<'gc>, span: SyntaxSpan<'gc>, meta: Option<SyntaxMeta<'gc>>) -> Result<Self, OutOfMemory> {
        Ok(Self(objects::Syntax::new(mc, datum, span.source_gc(), span.word(), meta.map(|m| m.0))?))
    }

    #[inline]
    pub fn of(v: Value<'gc>) -> Option<Self> {
        match Data::of(v) {
            Some(Data::Syntax(s)) => Some(Self(s)),
            _ => None,
        }
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        Value::object(mc, self.0)
    }

    pub fn metadata(self, mc: &Mutation<'gc>) -> Option<SyntaxMeta<'gc>> {
        self.0.meta(mc).map(SyntaxMeta)
    }

    /// Returns `None` if the stored tag is invalid.
    pub fn kind(self, mc: &Mutation<'gc>) -> Option<SyntaxKind> {
        self.metadata(mc).map_or(Some(SyntaxKind::Literal), |meta| meta.kind(mc))
    }

    pub fn datum(self, mc: &Mutation<'gc>) -> Value<'gc> {
        self.0.datum(mc)
    }

    pub fn span(self, mc: &Mutation<'gc>) -> SyntaxSpan<'gc> {
        SyntaxSpan::of(self.0.source(mc), self.0.span(mc))
    }

    pub fn context(self, mc: &Mutation<'gc>) -> Option<SyntaxContext<'gc>> {
        self.metadata(mc)?.context(mc)
    }

    pub fn origin(self, mc: &Mutation<'gc>) -> Option<SyntaxOrigin<'gc>> {
        self.metadata(mc)?.origin(mc)
    }
}
