use crate::gc::Arena;
use crate::pair::Pairs;
use crate::string::Strings;
use crate::symbol::{Symbol, Symbols};
use crate::vector::Vectors;

use super::*;

fn arena(limit: usize) -> Arena {
    Arena::new(limit, 2)
}

// Syntax keeps its children and metadata; the session keeps the source text.
#[test]
fn syntax_graph_survives_collection_and_compaction() {
    let mut arena = arena(1 << 20);
    let session = arena.mutate(|mc| {
        let session = SyntaxSession::new(mc, "'(a . 42)").unwrap();
        let source = session.source(mc).unwrap();
        let span = SyntaxSpan::new(mc, source, 0, source.byte_len(mc) as u32).unwrap();
        let symbol = Symbols::of_arena(mc).unwrap().intern_str(&Strings::new(mc), "a").unwrap();
        let node = |kind, datum| {
            let meta = SyntaxMeta::new(mc, kind, None, None).unwrap();
            Syntax::new(mc, datum, span, Some(meta)).unwrap()
        };
        let a = node(SyntaxKind::Identifier, symbol.value(mc));
        let b = Syntax::new(mc, Value::fixnum(42).unwrap(), span, None).unwrap();
        let pair = Pairs::new(mc).cons(a.value(mc), b.value(mc)).unwrap();
        let (seven, nine) = (SyntaxScope::new(mc).unwrap(), SyntaxScope::of(Value::fixnum(9).unwrap()));
        mc.set_root(1, seven.value());
        let context = SyntaxContext::new(mc, &[seven, nine]).unwrap();
        let parent = SyntaxOrigin::new(mc, span, None).unwrap();
        let origin = SyntaxOrigin::new(mc, span, Some(parent)).unwrap();
        let meta = SyntaxMeta::new(mc, SyntaxKind::List, Some(context), Some(origin)).unwrap();
        let list = Syntax::new(mc, pair.value(mc), span, Some(meta)).unwrap();
        let vector = Vectors::new(mc).immutable_from_slice(&[list.value(mc)]).unwrap();
        let vector = node(SyntaxKind::Vector, vector.value(mc));
        let quote = node(SyntaxKind::Abbreviation(Abbreviation::Quote), vector.value(mc));
        mc.set_root(0, quote.value(mc));
        session
    });
    arena.collect_minor();
    arena.set_evacuate_all(true);
    arena.collect();
    arena.collect();
    arena.mutate(|mc| {
        let quote = Syntax::of(mc.root(0)).unwrap();
        assert_eq!(quote.kind(mc), Some(SyntaxKind::Abbreviation(Abbreviation::Quote)));
        let vector_node = Syntax::of(quote.datum(mc)).unwrap();
        assert_eq!(vector_node.kind(mc), Some(SyntaxKind::Vector));
        let vector = Vectors::new(mc).vector(vector_node.datum(mc)).unwrap();
        assert!(!vector.is_mutable());
        let list = Syntax::of(vector.get(mc, 0).unwrap()).unwrap();
        let pair = Pairs::new(mc).pair(list.datum(mc)).unwrap();
        assert_eq!(pair.list_len(mc), None);
        let a = Syntax::of(pair.head(mc)).unwrap();
        let b = Syntax::of(pair.tail(mc)).unwrap();
        assert_eq!(a.kind(mc), Some(SyntaxKind::Identifier));
        assert!(Symbol::of(a.datum(mc)).is_some());
        assert_eq!((b.datum(mc).as_fixnum(), b.kind(mc)), (Some(42), Some(SyntaxKind::Literal)));
        let scopes: Vec<_> = list.context(mc).unwrap().scopes(mc).collect();
        assert_eq!(scopes, [SyntaxScope::of(mc.root(1)), SyntaxScope::of(Value::fixnum(9).unwrap())]);
        let origin = list.origin(mc).unwrap();
        let span = origin.parent(mc).unwrap().span(mc);
        assert!(origin.parent(mc).unwrap().parent(mc).is_none());
        assert_eq!((span.start(), span.end()), (0, 9));
        assert_eq!(span.source().unwrap().text(mc).unwrap().bytes(mc), b"'(a . 42)");
        assert_eq!(session.text(mc).unwrap().bytes(mc), b"'(a . 42)");
    });
}

#[test]
fn spans_use_source_bytes_and_check_bounds() {
    arena(1 << 20).mutate(|mc| {
        let session = SyntaxSession::new(mc, "λx").unwrap();
        let source = session.source(mc).unwrap();
        assert_eq!(source.byte_len(mc), 3);
        let span = SyntaxSpan::new(mc, source, 0, 2).unwrap();
        assert_eq!(&session.text(mc).unwrap().bytes(mc)[span.start() as usize..span.end() as usize], "λ".as_bytes());
        assert!(SyntaxSpan::new(mc, source, 2, 1).is_none());
        assert!(SyntaxSpan::new(mc, source, 0, 4).is_none());
        assert!(SyntaxSpan::new(mc, source, 3, 3).is_some());
        assert!(SyntaxSpan::default().source().is_none());
    });
}

#[test]
fn source_storage_obeys_the_arena_limit() {
    arena(64 << 10).mutate(|mc| {
        let before = mc.used();
        assert!(SyntaxSession::new(mc, "x".repeat(128 << 10)).is_err());
        assert_eq!(mc.used(), before);
    });
}

#[test]
fn dropping_the_session_releases_text_but_preserves_locations() {
    for minor in [false, true] {
        let mut arena = arena(1 << 20);
        let text = format!("{}\nλz", "x".repeat(128 << 10));
        let offset = (text.len() - 1) as u32;
        let session = arena.mutate(|mc| {
            let session = SyntaxSession::named(mc, "bot.scm", &text).unwrap();
            let span = SyntaxSpan::new(mc, session.source(mc).unwrap(), offset, offset + 1).unwrap();
            mc.set_root(0, Syntax::new(mc, Value::NIL, span, None).unwrap().value(mc));
            session
        });
        let clone = session.clone();
        drop(session);
        arena.set_evacuate_all(true);
        if !minor {
            arena.collect();
        }
        arena.mutate(|mc| {
            assert_eq!(clone.text(mc).unwrap().bytes(mc), text.as_bytes());
            assert!(clone.source(mc).unwrap().text(mc).is_some());
        });
        let before = arena.used();
        drop(clone);
        if minor {
            arena.collect_minor();
        } else {
            arena.collect();
        }
        assert!(arena.used() + (64 << 10) < before, "{} then {}", before, arena.used());
        arena.mutate(|mc| {
            let span = Syntax::of(mc.root(0)).unwrap().span(mc);
            let source = span.source().unwrap();
            assert!(source.text(mc).is_none());
            assert_eq!(source.byte_len(mc), text.len());
            assert_eq!(source.name(mc).unwrap().bytes(mc), b"bot.scm");
            assert_eq!(span.location(mc), Some(SyntaxLocation { line: 2, column: 3 }));
        });
    }
}

#[test]
fn locations_handle_line_endings_empty_sources_and_eof() {
    arena(1 << 20).mutate(|mc| {
        let session = SyntaxSession::new(mc, "a\r\nb\rc\n").unwrap();
        let source = session.source(mc).unwrap();
        assert_eq!(source.line_starts(mc), &[0, 3, 5, 7]);
        for (offset, line, column) in [(0, 1, 1), (2, 1, 3), (3, 2, 1), (5, 3, 1), (7, 4, 1)] {
            assert_eq!(source.location(mc, offset), Some(SyntaxLocation { line, column }));
        }
        assert!(source.location(mc, 8).is_none());
        let empty = SyntaxSession::new(mc, "").unwrap();
        let source = empty.source(mc).unwrap();
        assert_eq!(source.byte_len(mc), 0);
        assert_eq!(source.line_starts(mc), &[0]);
        assert!(source.name(mc).is_none());
        assert_eq!(source.location(mc, 0), Some(SyntaxLocation { line: 1, column: 1 }));
        assert!(source.location(mc, 1).is_none());
    });
}

#[test]
fn sessions_reject_other_arenas() {
    let mut a = arena(1 << 20);
    let mut b = arena(1 << 20);
    let session = a.mutate(|mc| SyntaxSession::new(mc, "hello").unwrap());
    b.mutate(|mc| {
        assert!(session.source(mc).is_err());
        assert!(session.text(mc).is_err());
    });
}

#[test]
fn line_metadata_obeys_the_arena_limit() {
    let mut arena = arena(128 << 10);
    arena.mutate(|mc| {
        // The bytes fit, but one line-start offset per newline does not.
        assert!(SyntaxSession::new(mc, "\n".repeat(32 << 10)).is_err());
    });
    arena.collect();
    assert_eq!((arena.objects(), arena.frozen_values()), (0, 0));
}
