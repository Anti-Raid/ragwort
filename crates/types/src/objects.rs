//! The objects behind the views the other modules give out. They're private to the crate, so
//! only those views change them: pairs and literal vectors stay as they were made.

use std::cell::RefCell;

use crate::bytevector::{ExternalBuffer, ExternalBufferMut};
use crate::external::Held;
use crate::table::Hosted;
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
    /// A reference to a value of a host type, which lives outside the arena with its kind and is
    /// dropped once nothing reaches the reference. `kept` is a value that lives as long as it does.
    pub(crate) struct External { kept: Value, payload: Frozen<Held> }
    /// A table: its entries in the order they were added, and the index that finds them by key.
    /// `live` counts the entries. `used` counts the places of `pairs` taken, dead ones included.
    /// `seed` seeds the hashes. `epoch` is the count of moving collections the index was made
    /// at, or `u64::MAX` while no key is hashed by where it is.
    pub(crate) struct Table { index: Member<TableIndex>, pairs: Member<TableEntries>, live: u64, used: u64, seed: u64, epoch: u64 }
    /// A table whose entries the host holds, in `host`. `memo` is a table of the values read from
    /// the host so far, made at the first read. `walk` is the keys and values in the host's order,
    /// made when the table is first walked and dropped when it is next written. `writable` says
    /// whether programs can change the table.
    pub(crate) struct ExternTable { memo: Member<Table>, walk: Member<TableEntries>, writable: bool, host: Frozen<RefCell<Box<dyn Hosted>>> }
    /// A table's index, probed linearly. A slot is 0 if it was never used. Otherwise its low half
    /// is an entry's number plus one, and its high half is the high half of the key's hash.
    pub(crate) struct TableIndex {} items u64
    /// A table's entries, a key and a value each. Both are `Value::BROKEN` in an entry that was
    /// removed and in the places not used yet.
    pub(crate) struct TableEntries {} items Value
}
