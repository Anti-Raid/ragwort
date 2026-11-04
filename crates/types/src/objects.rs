//! The objects behind the views the other modules give out. They're private to the crate, so
//! only those views change them: pairs and literal vectors stay as they were made.

use crate::gc::table::TableHead;

crate::gc::objects! {
    /// Every object this crate makes. Strings and numbers are in their own groups.
    pub(crate) kind Data after crate::num::Numbers;

    /// A symbol: its name, a flat string, and the name's hash.
    pub(crate) struct Sym { name: Value, hash: u64 }
    /// The intern table: the seed of its hashes, and the symbols, held weakly.
    pub(crate) struct Interned { seed: u64, table: Member<TableHead> }
    /// `length` is that of the list the pair starts, or 0 if its pairs don't end in `()`.
    pub(crate) struct Pair { head: Value, tail: Value, length: u64 }
    pub(crate) struct Vector {} items Value
    pub(crate) struct ImmutableVector {} items Value
    /// Source bytes, in no particular encoding.
    pub(crate) struct SyntaxText { bytes: Frozen<Box<[u8]>> }
    /// A source's name, its text while a session keeps it, its length, and the byte offset of
    /// each line's start, from zero.
    pub(crate) struct SyntaxSource { name: Member<SyntaxText>, text: Weak<SyntaxText>, size: u64, lines: Frozen<Box<[u32]>> }
    /// What a session keeps alive: the source, and its text.
    pub(crate) struct Session { source: Member<SyntaxSource>, text: Member<SyntaxText> }
    /// An identifier's scopes.
    pub(crate) struct SyntaxContext {} items u64
    /// Spans are the start byte in the low half, the end in the high.
    pub(crate) struct SyntaxOrigin { source: Member<SyntaxSource>, span: u64, parent: Member<SyntaxOrigin> }
    pub(crate) struct SyntaxMeta { kind: u32, context: Member<SyntaxContext>, origin: Member<SyntaxOrigin> }
    pub(crate) struct Syntax { datum: Value, source: Member<SyntaxSource>, span: u64, meta: Member<SyntaxMeta> }
}
