//! The object types behind the views that the other modules export. The types are private to the
//! crate, so only those views can modify the objects. Pairs and literal vectors therefore never
//! change after they are created.

use std::cell::RefCell;

use crate::bytevector::{ExternalBuffer, ExternalBufferMut};
use crate::external::Held;
use crate::table::Hosted;
use crate::vector::HostedVector;
use crate::gc::table::TableHead;

crate::gc::objects! {
    /// Every object type defined in this module. Strings and numbers are in their own groups.
    pub(crate) kind Data after crate::num::Numbers;

    /// A symbol. `name` is a flat string, and `hash` is the hash of the name.
    pub(crate) struct Sym { name: Value, hash: u64 }
    /// The intern table. `seed` seeds its hashes. `table` holds the symbols and `keywords` holds the keywords, both weakly.
    pub(crate) struct Interned { seed: u64, table: Member<TableHead>, keywords: Member<TableHead> }
    /// A keyword, `#:name`. `symbol` is the symbol with the same name.
    pub(crate) struct Keyword { symbol: Member<Sym> }
    /// `length` is the length of the list that starts at this pair, or 0 if the chain of pairs does not end in `()`.
    pub(crate) struct Pair { head: Value, tail: Value, length: u64 }
    pub(crate) struct Vector {} items Value
    pub(crate) struct ImmutableVector {} items Value
    /// A bytevector of `bytes` bytes. The items pack eight bytes to a word, with the first byte in the lowest bits.
    pub(crate) struct Bytevector { bytes: u64 } items u64
    pub(crate) struct ImmutableBytevector { bytes: u64 } items u64
    /// A bytevector whose `bytes` bytes are stored outside the arena, in `owner`. `owner` is dropped
    /// once the bytevector is unreachable. The bytes never change in number or in value.
    pub(crate) struct ExternBytevector { bytes: u64, owner: Frozen<Box<dyn ExternalBuffer>> }
    /// A writable bytevector whose bytes are stored outside the arena, in `buffer`. The buffer stays `bytes` bytes long.
    pub(crate) struct ExternMutBytevector { bytes: u64, buffer: Frozen<RefCell<Box<dyn ExternalBufferMut>>> }
    /// Source bytes, in no particular encoding.
    pub(crate) struct SyntaxText { bytes: Frozen<Box<[u8]>> }
    /// A source's metadata: its name, its text, its length and its line starts. `text` is present
    /// only while a session keeps it alive. `size` is the length of the text in bytes. `lines`
    /// holds the byte offset of the start of each line, counted from zero.
    pub(crate) struct SyntaxSource { name: Member<SyntaxText>, text: Weak<SyntaxText>, size: u64, lines: Frozen<Box<[u32]>> }
    /// The objects that a session keeps alive: the source and its text.
    pub(crate) struct Session { source: Member<SyntaxSource>, text: Member<SyntaxText> }
    /// A scope that is distinct from every other scope.
    pub(crate) struct SyntaxScope {}
    /// An identifier's scopes.
    pub(crate) struct SyntaxContext {} items Value
    /// `span` holds the start byte offset in its low half and the end byte offset in its high half.
    pub(crate) struct SyntaxOrigin { source: Member<SyntaxSource>, span: u64, parent: Member<SyntaxOrigin> }
    pub(crate) struct SyntaxMeta { kind: u32, context: Member<SyntaxContext>, origin: Member<SyntaxOrigin> }
    /// `binding` is `#f` if there is no binding.
    pub(crate) struct Syntax { datum: Value, source: Member<SyntaxSource>, span: u64, meta: Member<SyntaxMeta>, binding: Value }
    /// A reference to a value of a host type. The value and its kind are stored outside the arena,
    /// in `payload`, and dropped once the reference is unreachable. `kept` is an arena value that
    /// stays alive as long as the reference does.
    pub(crate) struct External { kept: Value, payload: Frozen<Held> }
    /// A table. `pairs` holds the entries in the order they were added, and `index` finds them by
    /// key. `live` is the number of live entries. `used` is the number of entries of `pairs` in
    /// use, tombstones included. `seed` seeds the hashes. `epoch` is the number of moving
    /// collections that had run when the index was built, or `u64::MAX` while no key is hashed by
    /// its object word.
    pub(crate) struct Table { index: Member<TableIndex>, pairs: Member<TableEntries>, live: u64, used: u64, seed: u64, epoch: u64 }
    /// A vector whose `count` elements are owned by the host, in `host`. `memo` caches the elements
    /// read from the host so far, and is created on the first read. It is one vector for a short
    /// external vector, and a vector of chunks for a long one (see `ExternVector::remembered`).
    /// `writable` is whether programs can modify the vector.
    pub(crate) struct ExternVector { count: u64, writable: bool, memo: Member<Vector>, host: Frozen<RefCell<Box<dyn HostedVector>>> }
    /// A table whose entries are owned by the host, in `host`. `memo` is a table that caches the
    /// values read from the host so far, created on the first read. `walk` holds the keys and
    /// values in the host's order. It is created when the table is first iterated and dropped on
    /// the next write. `shape` is the shape that the host declared for the table's keys, if any.
    /// The values read from the host are then cached in `fields`, a record of that shape, and
    /// `memo` stays unused. `writable` is whether programs can modify the table.
    pub(crate) struct ExternTable { memo: Member<Table>, fields: Member<TableRecord>, walk: Member<TableEntries>, shape: Member<TableShape>, writable: bool, host: Frozen<RefCell<Box<dyn Hosted>>> }
    /// A table that has the keys of `shape` and holds only its values, as its items: one value for
    /// each key of the shape, in the order of the keys. An item is `Value::BROKEN` for a key that
    /// the table does not have. `live` is the number of keys that the table has.
    ///
    /// A record cannot hold a key outside its shape. When a program adds one, the entries move to
    /// an ordinary table in `own`, `shape` is cleared, and every operation goes to `own` from then on.
    pub(crate) struct TableRecord { shape: Member<TableShape>, own: Member<Table>, live: u64 } items Value
    /// The keys that a group of tables has in common. `pairs` holds the keys in entry order, each
    /// followed by an unused value slot. `index` is the hash index over those keys. Every table
    /// made from the shape shares `index` and copies the keys. `seed` is the hash seed of the index.
    pub(crate) struct TableShape { index: Member<TableIndex>, pairs: Member<TableEntries>, seed: u64 }
    /// A table's index, a hash table with linear probing. A slot is 0 if it was never used.
    /// Otherwise its low half is an entry number plus one, and its high half is the high half of
    /// the key's hash.
    pub(crate) struct TableIndex {} items u64
    /// A table's entries, a key slot and a value slot each. Both slots hold `Value::BROKEN` in a
    /// removed entry and in the entries not used yet.
    pub(crate) struct TableEntries {} items Value
}
