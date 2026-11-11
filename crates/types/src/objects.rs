//! The objects behind the views the other modules give out. They're private to the crate, so
//! only those views change them: pairs and literal vectors stay as they were made.

use std::cell::RefCell;

use crate::bytevector::{ExternalBuffer, ExternalBufferMut};
use crate::gc::table::TableHead;

crate::gc::objects! {
    /// Every object this crate makes. Strings and numbers are in their own groups.
    pub(crate) kind Data after crate::num::Numbers;

    /// A symbol: its name, a flat string, and the name's hash.
    pub(crate) struct Sym { name: Value, hash: u64 }
    /// The intern table: the seed of its hashes, and the symbols and keywords, held weakly.
    pub(crate) struct Interned { seed: u64, table: Member<TableHead>, keywords: Member<TableHead> }
    /// A keyword, `#:name`, by its name's symbol.
    pub(crate) struct Keyword { symbol: Member<Sym> }
    /// `length` is that of the list the pair starts, or 0 if its pairs don't end in `()`.
    pub(crate) struct Pair { head: Value, tail: Value, length: u64 }
    pub(crate) struct Vector {} items Value
    pub(crate) struct ImmutableVector {} items Value
    /// `bytes` bytes, eight to a word, the first lowest.
    pub(crate) struct Bytevector { bytes: u64 } items u64
    pub(crate) struct ImmutableBytevector { bytes: u64 } items u64
    /// A bytevector whose `bytes` bytes live outside the arena, dropped once nothing reaches it.
    /// They never change, in number or in value.
    pub(crate) struct ExternBytevector { bytes: u64, owner: Frozen<Box<dyn ExternalBuffer>> }
    /// One that can be written to, in the buffer it was made of, which stays `bytes` long.
    pub(crate) struct ExternMutBytevector { bytes: u64, buffer: Frozen<RefCell<Box<dyn ExternalBufferMut>>> }
    /// Source bytes, in no particular encoding.
    pub(crate) struct SyntaxText { bytes: Frozen<Box<[u8]>> }
    /// A source's name, its text while a session keeps it, its length, and the byte offset of
    /// each line's start, from zero.
    pub(crate) struct SyntaxSource { name: Member<SyntaxText>, text: Weak<SyntaxText>, size: u64, lines: Frozen<Box<[u32]>> }
    /// What a session keeps alive: the source, and its text.
    pub(crate) struct Session { source: Member<SyntaxSource>, text: Member<SyntaxText> }
    /// A scope made to be apart from every other.
    pub(crate) struct SyntaxScope {}
    /// An identifier's scopes.
    pub(crate) struct SyntaxContext {} items Value
    /// Spans are the start byte in the low half, the end in the high.
    pub(crate) struct SyntaxOrigin { source: Member<SyntaxSource>, span: u64, parent: Member<SyntaxOrigin> }
    pub(crate) struct SyntaxMeta { kind: u32, context: Member<SyntaxContext>, origin: Member<SyntaxOrigin> }
    /// `binding` is `#f` for none.
    pub(crate) struct Syntax { datum: Value, source: Member<SyntaxSource>, span: u64, meta: Member<SyntaxMeta>, binding: Value }
}
