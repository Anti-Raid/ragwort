//! GC-managed syntax, lexical context, and source locations.
//!
//! Syntax spans retain source metadata. A `SyntaxSession` separately keeps the source bytes
//! alive; dropping its last clone allows the text to be collected.

use ragwort_gc::{ForeignRoot, Gc, Member, Mutation, OutOfMemory, Plain, Root, Rooted, Trace, Value, Weak};

/// Source bytes, stored inline without an encoding requirement.
#[derive(Trace, Plain)]
#[gc(items = u8)]
pub struct SyntaxText;

impl SyntaxText {
    pub fn new<'gc>(mc: &Mutation<'gc>, bytes: impl AsRef<[u8]>) -> Result<Gc<'gc, Self>, OutOfMemory> {
        mc.alloc_inline_from(Self, bytes.as_ref())
    }
}

/// Source metadata. Inline items are line-start byte offsets, beginning with zero.
/// Sessions retain the text; spans retain only this record.
#[derive(Trace, Plain)]
#[gc(items = u32)]
pub struct SyntaxSource<'gc> {
    name: Option<Member<'gc, SyntaxText>>,
    text: Weak<'gc, SyntaxText>,
    len: u32,
}

impl<'gc> SyntaxSource<'gc> {
    pub fn name(&self, mc: &Mutation<'gc>) -> Option<Gc<'gc, SyntaxText>> {
        self.name.map(|name| name.get(mc))
    }

    /// Returns `None` once the text has been collected.
    pub fn text(&self, mc: &Mutation<'gc>) -> Option<Gc<'gc, SyntaxText>> {
        self.text.get(mc)
    }

    pub fn byte_len(&self) -> usize {
        self.len as usize
    }

    /// Looks up a byte offset, including EOF. Works after the text is collected.
    pub fn location(this: Gc<'gc, Self>, offset: u32) -> Option<SyntaxLocation> {
        if offset > this.len {
            return None;
        }
        let starts = this.items();
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

#[derive(Clone, Copy, Trace)]
struct SessionData<'gc> {
    source: Member<'gc, SyntaxSource<'gc>>,
    text: Member<'gc, SyntaxText>,
}

struct SessionRoot;
impl Rooted for SessionRoot {
    type Of<'gc> = SessionData<'gc>;
}

/// Keeps one source and its text alive across steps. Dropping the last clone releases the
/// text for collection, while surviving spans retain the source metadata.
#[derive(Clone)]
pub struct SyntaxSession {
    root: Root<SessionRoot>,
}

impl SyntaxSession {
    pub fn new(mc: &Mutation<'_>, bytes: impl AsRef<[u8]>) -> Result<Self, OutOfMemory> {
        Self::create(mc, None, bytes.as_ref())
    }

    pub fn named(mc: &Mutation<'_>, name: &str, bytes: impl AsRef<[u8]>) -> Result<Self, OutOfMemory> {
        Self::create(mc, Some(name), bytes.as_ref())
    }

    fn create(mc: &Mutation<'_>, name: Option<&str>, text: &[u8]) -> Result<Self, OutOfMemory> {
        let bytes = SyntaxText::new(mc, text)?;
        let name = name.map(|name| SyntaxText::new(mc, name).map(|name| Member::new(mc, name))).transpose()?;
        let source = SyntaxSource { name, text: Weak::new(mc, bytes), len: bytes.len() as u32 };
        let mut starts = line_starts(text);
        let source = mc.alloc_inline(source, line_starts(text).count(), |_| starts.next().expect("counted line starts"))?;
        let root = mc.root::<SessionRoot>(SessionData { source: Member::new(mc, source), text: Member::new(mc, bytes) })?;
        Ok(Self { root })
    }

    pub fn source<'gc>(&self, mc: &Mutation<'gc>) -> Result<Gc<'gc, SyntaxSource<'gc>>, ForeignRoot> {
        Ok(mc.fetch(&self.root)?.source.get(mc))
    }

    pub fn text<'gc>(&self, mc: &Mutation<'gc>) -> Result<Gc<'gc, SyntaxText>, ForeignRoot> {
        Ok(mc.fetch(&self.root)?.text.get(mc))
    }
}

fn line_starts(bytes: &[u8]) -> impl Iterator<Item = u32> + '_ {
    std::iter::once(0).chain(bytes.iter().enumerate().filter_map(|(i, &byte)| {
        // CRLF is one newline; a lone CR also starts a line.
        (byte == b'\n' || byte == b'\r' && bytes.get(i + 1) != Some(&b'\n')).then_some((i + 1) as u32)
    }))
}

/// A source range `start..end`, measured in bytes. Keeps the metadata alive, not the text.
/// A default span has no source.
#[derive(Clone, Copy, Debug, Default, Trace, Plain)]
pub struct SyntaxSpan<'gc> {
    source: Option<Member<'gc, SyntaxSource<'gc>>>,
    start: u32,
    end: u32,
}

impl<'gc> SyntaxSpan<'gc> {
    /// Checks `start <= end <= source.byte_len()`.
    pub fn new(mc: &Mutation<'gc>, source: Gc<'gc, SyntaxSource<'gc>>, start: u32, end: u32) -> Option<Self> {
        (start <= end && end as usize <= source.byte_len()).then(|| Self { source: Some(Member::new(mc, source)), start, end })
    }

    pub fn source(self, mc: &Mutation<'gc>) -> Option<Gc<'gc, SyntaxSource<'gc>>> {
        self.source.map(|source| source.get(mc))
    }

    pub fn location(self, mc: &Mutation<'gc>) -> Option<SyntaxLocation> {
        SyntaxSource::location(self.source(mc)?, self.start)
    }

    pub fn start(self) -> u32 {
        self.start
    }

    pub fn end(self) -> u32 {
        self.end
    }
}

/// A scope ID. Identifiers with the same name can belong to different scopes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Trace, Plain)]
pub struct SyntaxScope(pub u64);

/// An identifier's scopes, stored inline.
#[derive(Trace, Plain)]
#[gc(items = SyntaxScope)]
pub struct SyntaxContext;

/// A source location in an expansion's history. `parent` links to the preceding origin.
#[derive(Trace, Plain)]
pub struct SyntaxOrigin<'gc> {
    span: SyntaxSpan<'gc>,
    parent: Option<Member<'gc, SyntaxOrigin<'gc>>>,
}

impl<'gc> SyntaxOrigin<'gc> {
    pub fn new(span: SyntaxSpan<'gc>, parent: Option<Member<'gc, Self>>) -> Self {
        Self { span, parent }
    }

    pub fn span(&self) -> SyntaxSpan<'gc> {
        self.span
    }

    pub fn parent(&self) -> Option<Member<'gc, Self>> {
        self.parent
    }
}

/// Reader shorthand for quotation and unquotation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Abbreviation {
    Quote,
    Quasiquote,
    Unquote,
    UnquoteSplicing,
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
    pub(crate) fn tag(self) -> u32 {
        match self {
            Self::Literal => 0,
            Self::Identifier => 1,
            Self::List => 2,
            Self::Vector => 3,
            Self::Abbreviation(Abbreviation::Quote) => 4,
            Self::Abbreviation(Abbreviation::Quasiquote) => 5,
            Self::Abbreviation(Abbreviation::Unquote) => 6,
            Self::Abbreviation(Abbreviation::UnquoteSplicing) => 7,
        }
    }

    pub(crate) fn from_tag(tag: u32) -> Option<Self> {
        Some(match tag {
            0 => Self::Literal,
            1 => Self::Identifier,
            2 => Self::List,
            3 => Self::Vector,
            4 => Self::Abbreviation(Abbreviation::Quote),
            5 => Self::Abbreviation(Abbreviation::Quasiquote),
            6 => Self::Abbreviation(Abbreviation::Unquote),
            7 => Self::Abbreviation(Abbreviation::UnquoteSplicing),
            _ => return None,
        })
    }
}

/// Kind, lexical context and expansion origin, shared by syntax nodes.
#[derive(Trace, Plain)]
pub struct SyntaxMeta<'gc> {
    kind: u32,
    context: Option<Member<'gc, SyntaxContext>>,
    origin: Option<Member<'gc, SyntaxOrigin<'gc>>>,
}

impl<'gc> SyntaxMeta<'gc> {
    pub fn new(kind: SyntaxKind) -> Self {
        Self { kind: kind.tag(), context: None, origin: None }
    }

    pub fn with_context(mut self, context: Member<'gc, SyntaxContext>) -> Self {
        self.context = Some(context);
        self
    }

    pub fn with_origin(mut self, origin: Member<'gc, SyntaxOrigin<'gc>>) -> Self {
        self.origin = Some(origin);
        self
    }

    /// Returns `None` if the stored tag is invalid.
    pub fn kind(&self) -> Option<SyntaxKind> {
        SyntaxKind::from_tag(self.kind)
    }

    pub fn context(&self) -> Option<Member<'gc, SyntaxContext>> {
        self.context
    }

    pub fn origin(&self) -> Option<Member<'gc, SyntaxOrigin<'gc>>> {
        self.origin
    }
}

/// A datum and its span. Absent metadata means a literal without context or origin.
#[derive(Trace, Plain)]
pub struct Syntax<'gc> {
    datum: Value<'gc>,
    span: SyntaxSpan<'gc>,
    meta: Option<Member<'gc, SyntaxMeta<'gc>>>,
}

impl<'gc> Syntax<'gc> {
    pub fn new(datum: Value<'gc>, span: SyntaxSpan<'gc>) -> Self {
        Self { datum, span, meta: None }
    }

    /// Metadata describes the datum's shape; this does not check that they agree.
    pub fn with_metadata(mut self, meta: Option<Member<'gc, SyntaxMeta<'gc>>>) -> Self {
        self.meta = meta;
        self
    }

    pub fn metadata(&self) -> Option<Member<'gc, SyntaxMeta<'gc>>> {
        self.meta
    }

    /// Returns `None` if the stored tag is invalid.
    pub fn kind(&self, mc: &Mutation<'gc>) -> Option<SyntaxKind> {
        self.meta.map_or(Some(SyntaxKind::Literal), |meta| meta.get(mc).kind())
    }

    pub fn datum(&self) -> Value<'gc> {
        self.datum
    }

    pub fn span(&self) -> SyntaxSpan<'gc> {
        self.span
    }

    pub fn context(&self, mc: &Mutation<'gc>) -> Option<Member<'gc, SyntaxContext>> {
        self.meta.and_then(|meta| meta.get(mc).context())
    }

    pub fn origin(&self, mc: &Mutation<'gc>) -> Option<Member<'gc, SyntaxOrigin<'gc>>> {
        self.meta.and_then(|meta| meta.get(mc).origin())
    }
}

#[cfg(test)]
#[path = "tests/syntax.rs"]
mod tests;
