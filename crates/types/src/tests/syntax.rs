use ragwort_gc::{Arena, Lock, Member, Rootable, Value};
use crate::pair::Pairs;
use crate::string::Strings;
use crate::symbol::Symbols;
use crate::vector::Vectors;

use super::*;

struct SyntaxRoot;
impl Rootable for SyntaxRoot {
    type Root<'gc> = Lock<Value<'gc>>;
}

// Syntax retains its children and metadata; the session retains the source text.
#[test]
fn syntax_graph_survives_collection_and_compaction() {
    let mut arena = Arena::<SyntaxRoot>::new(1 << 20, |_| Ok(Lock::new(Value::NIL))).unwrap();
    let session = arena
        .mutate(|mc, root| {
            let session = SyntaxSession::new(mc, "'(a . 42)").unwrap();
            let source = session.source(mc).unwrap();
            let span = SyntaxSpan::new(mc, source, 0, source.byte_len() as u32).unwrap();
            let strings = Strings::new(mc).unwrap();
            let symbols = Symbols::new();
            let symbol = symbols.intern_str(&strings, "a").unwrap();
            let node = |kind, datum| {
                let meta = mc.alloc(SyntaxMeta::new(kind)).unwrap();
                mc.alloc(Syntax::new(datum, span).with_metadata(Some(Member::new(mc, meta)))).unwrap()
            };
            let a = node(SyntaxKind::Identifier, symbol.value());
            let b = mc.alloc(Syntax::new(Value::fixnum(42).unwrap(), span)).unwrap();
            let pairs = Pairs::new(mc).unwrap();
            let pair = pairs.cons(Value::object(mc, a), Value::object(mc, b)).unwrap();
            let context = mc.alloc_inline_from(SyntaxContext, &[SyntaxScope(7), SyntaxScope(9)]).unwrap();
            let parent = mc.alloc(SyntaxOrigin::new(span, None)).unwrap();
            let origin = mc.alloc(SyntaxOrigin::new(span, Some(Member::new(mc, parent)))).unwrap();
            let meta = mc
                .alloc(SyntaxMeta::new(SyntaxKind::List).with_context(Member::new(mc, context)).with_origin(Member::new(mc, origin)))
                .unwrap();
            let list = mc.alloc(Syntax::new(Value::object(mc, pair), span).with_metadata(Some(Member::new(mc, meta)))).unwrap();
            let vectors = Vectors::new(mc).unwrap();
            let vector = vectors.immutable_from_slice(&[Value::object(mc, list)]).unwrap();
            let vector = node(SyntaxKind::Vector, Value::object(mc, vector));
            let quote = node(SyntaxKind::Abbreviation(Abbreviation::Quote), Value::object(mc, vector));
            root.set(mc, Value::object(mc, quote));
            session
        })
        .unwrap();
    arena.collect_minor();
    arena.set_evacuate_all(true);
    arena.collect();
    arena.collect();
    arena
        .mutate(|mc, root| {
            let quote = root.get().downcast::<Syntax>(mc).unwrap();
            assert_eq!(quote.kind(mc), Some(SyntaxKind::Abbreviation(Abbreviation::Quote)));
            let vector_node = quote.datum().downcast::<Syntax>(mc).unwrap();
            assert_eq!(vector_node.kind(mc), Some(SyntaxKind::Vector));
            let vectors = Vectors::new(mc).unwrap();
            let vector = vectors.vector(vector_node.datum()).unwrap();
            assert!(!vector.is_mutable());
            let list = vector.get(0).unwrap().downcast::<Syntax>(mc).unwrap();
            let pairs = Pairs::new(mc).unwrap();
            let pair = pairs.pair(list.datum()).unwrap();
            assert_eq!(pair.list_len(), None);
            let a = pair.head().downcast::<Syntax>(mc).unwrap();
            let b = pair.tail().downcast::<Syntax>(mc).unwrap();
            assert_eq!(a.kind(mc), Some(SyntaxKind::Identifier));
            assert!(Strings::new(mc).unwrap().symbol(a.datum()).is_some());
            assert_eq!(b.datum().as_fixnum(), Some(42));
            assert_eq!(list.context(mc).unwrap().get(mc).items(), &[SyntaxScope(7), SyntaxScope(9)]);
            let origin = list.origin(mc).unwrap().get(mc);
            assert!(origin.parent().is_some());
            let span = origin.parent().unwrap().get(mc).span();
            assert_eq!((span.start(), span.end()), (0, 9));
            assert_eq!(span.source(mc).unwrap().text(mc).unwrap().items(), b"'(a . 42)");
            assert_eq!(session.text(mc).unwrap().items(), b"'(a . 42)");
        })
        .unwrap();
}

#[test]
fn syntax_payloads_are_compact() {
    assert_eq!(std::mem::size_of::<Syntax<'_>>(), 24);
    assert_eq!(std::mem::size_of::<SyntaxMeta<'_>>(), 12);
}

#[test]
fn spans_use_source_bytes_and_check_bounds() {
    let mut arena = Arena::<SyntaxRoot>::new(1 << 20, |_| Ok(Lock::new(Value::NIL))).unwrap();
    arena
        .mutate(|mc, _| {
            let session = SyntaxSession::new(mc, "λx").unwrap();
            let source = session.source(mc).unwrap();
            assert_eq!(source.byte_len(), 3);
            let span = SyntaxSpan::new(mc, source, 0, 2).unwrap();
            assert_eq!(&session.text(mc).unwrap().items()[span.start() as usize..span.end() as usize], "λ".as_bytes());
            assert!(SyntaxSpan::new(mc, source, 2, 1).is_none());
            assert!(SyntaxSpan::new(mc, source, 0, 4).is_none());
            assert!(SyntaxSpan::new(mc, source, 3, 3).is_some());
            assert!(SyntaxSpan::default().source(mc).is_none());
        })
        .unwrap();
}

#[test]
fn source_storage_obeys_the_arena_limit() {
    let mut arena = Arena::<SyntaxRoot>::new(64 << 10, |_| Ok(Lock::new(Value::NIL))).unwrap();
    arena
        .mutate(|mc, _| {
            let before = mc.used();
            assert!(SyntaxSession::new(mc, "x".repeat(128 << 10)).is_err());
            assert_eq!(mc.used(), before);
        })
        .unwrap();
}

#[test]
fn dropping_the_session_releases_text_but_preserves_locations() {
    for minor in [false, true] {
        let mut arena = Arena::<SyntaxRoot>::new(1 << 20, |_| Ok(Lock::new(Value::NIL))).unwrap();
        let text = format!("{}\nλz", "x".repeat(128 << 10));
        let offset = (text.len() - 1) as u32;
        let session = arena
            .mutate(|mc, root| {
                let session = SyntaxSession::named(mc, "bot.scm", &text).unwrap();
                let span = SyntaxSpan::new(mc, session.source(mc).unwrap(), offset, offset + 1).unwrap();
                let syntax = mc.alloc(Syntax::new(Value::NIL, span)).unwrap();
                root.set(mc, Value::object(mc, syntax));
                session
            })
            .unwrap();
        let clone = session.clone();
        drop(session);
        arena.set_evacuate_all(true);
        if !minor {
            arena.collect();
        }
        arena
            .mutate(|mc, _| {
                assert_eq!(clone.text(mc).unwrap().items(), text.as_bytes());
                assert!(clone.source(mc).unwrap().text(mc).is_some());
            })
            .unwrap();
        let before = arena.metrics().used;
        drop(clone);
        if minor {
            arena.collect_minor();
        } else {
            arena.collect();
        }
        assert!(arena.metrics().used + (64 << 10) < before);
        arena
            .mutate(|mc, root| {
                let span = root.get().downcast::<Syntax>(mc).unwrap().span();
                let source = span.source(mc).unwrap();
                assert!(source.text(mc).is_none());
                assert_eq!(source.byte_len(), text.len());
                assert_eq!(source.name(mc).unwrap().items(), b"bot.scm");
                assert_eq!(span.location(mc), Some(SyntaxLocation { line: 2, column: 3 }));
            })
            .unwrap();
    }
}

#[test]
fn locations_handle_line_endings_empty_sources_and_eof() {
    let mut arena = Arena::<SyntaxRoot>::new(1 << 20, |_| Ok(Lock::new(Value::NIL))).unwrap();
    arena
        .mutate(|mc, _| {
            let session = SyntaxSession::new(mc, "a\r\nb\rc\n").unwrap();
            let source = session.source(mc).unwrap();
            assert_eq!(source.items(), &[0, 3, 5, 7]);
            for (offset, line, column) in [(0, 1, 1), (2, 1, 3), (3, 2, 1), (5, 3, 1), (7, 4, 1)] {
                assert_eq!(SyntaxSource::location(source, offset), Some(SyntaxLocation { line, column }));
            }
            assert!(SyntaxSource::location(source, 8).is_none());
            let empty = SyntaxSession::new(mc, "").unwrap();
            let source = empty.source(mc).unwrap();
            assert_eq!(source.byte_len(), 0);
            assert_eq!(source.items(), &[0]);
            assert!(source.name(mc).is_none());
            assert_eq!(SyntaxSource::location(source, 0), Some(SyntaxLocation { line: 1, column: 1 }));
            assert!(SyntaxSource::location(source, 1).is_none());
        })
        .unwrap();
}

#[test]
fn sessions_reject_other_arenas() {
    let mut a = Arena::<SyntaxRoot>::new(1 << 20, |_| Ok(Lock::new(Value::NIL))).unwrap();
    let mut b = Arena::<SyntaxRoot>::new(1 << 20, |_| Ok(Lock::new(Value::NIL))).unwrap();
    let session = a.mutate(|mc, _| SyntaxSession::new(mc, "hello").unwrap()).unwrap();
    b.mutate(|mc, _| {
        assert!(session.source(mc).is_err());
        assert!(session.text(mc).is_err());
    })
    .unwrap();
}

#[test]
fn line_metadata_obeys_the_arena_limit() {
    let mut arena = Arena::<SyntaxRoot>::new(128 << 10, |_| Ok(Lock::new(Value::NIL))).unwrap();
    arena
        .mutate(|mc, _| {
            // The bytes fit, but one line-start offset per newline does not.
            assert!(SyntaxSession::new(mc, "\n".repeat(32 << 10)).is_err());
        })
        .unwrap();
    arena.collect();
    assert_eq!(arena.metrics().objects, 0);
}
