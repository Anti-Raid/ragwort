use ragwort_types::gc::Arena;
use ragwort_types::string::display;
use ragwort_types::symbol::Symbol;
use ragwort_types::syntax::SyntaxLocation;

use super::*;

/// Root 0 holds the symbol table, and root 1 is free for a test.
fn arena() -> Arena {
    let mut arena = Arena::new(64 << 20, 2);
    arena.mutate(|mc| mc.set_root(0, Symbols::with_seed(mc, 1).unwrap().value(mc)));
    arena
}

fn symbols<'gc>(mc: &Mutation<'gc>) -> Symbols<'gc> {
    Symbols::of(mc.root(0)).unwrap()
}

/// The datum a node reads as, written back out.
fn show<'gc>(mc: &Mutation<'gc>, node: Syntax<'gc>) -> String {
    let strings = Strings::new(mc);
    let pairs = Pairs::new(mc);
    match node.kind(mc).unwrap() {
        SyntaxKind::Identifier => display(&strings, Symbol::of(node.datum(mc)).unwrap().name(mc)).to_string(),
        SyntaxKind::Abbreviation(Abbreviation::Quote) => format!("'{}", show(mc, Syntax::of(node.datum(mc)).unwrap())),
        SyntaxKind::List => {
            let mut out = Vec::new();
            let mut rest = node.datum(mc);
            while let Some(pair) = pairs.pair(rest) {
                out.push(show(mc, Syntax::of(pair.head(mc)).unwrap()));
                rest = pair.tail(mc);
            }
            if rest != Value::NIL {
                out.push(format!(". {}", show(mc, Syntax::of(rest).unwrap())));
            }
            format!("({})", out.join(" "))
        }
        kind => panic!("the reader made a {kind:?} node"),
    }
}

/// Every datum in `text`, written back out, or the error reading it.
fn read(text: &str) -> Result<Vec<String>, ReadError> {
    let mut arena = arena();
    arena.mutate(|mc| {
        let session = SyntaxSession::new(mc, text).unwrap();
        Ok(read_all(mc, symbols(mc), &session)?.into_iter().map(|node| show(mc, node)).collect())
    })
}

fn error(text: &str) -> (ErrorKind, u32, u32) {
    let e = read(text).unwrap_err();
    (e.kind, e.start, e.end)
}

#[test]
fn reads_lists_quotes_and_dotted_tails() {
    assert_eq!(read("(a b . c)").unwrap(), ["(a b . c)"]);
    assert_eq!(read("[a (b) ()]").unwrap(), ["(a (b) ())"]);
    assert_eq!(read("'(a 'b) 'c ''d").unwrap(), ["'(a 'b)", "'c", "''d"]);
    assert_eq!(read("(lambda (x . rest) [f x . rest])").unwrap(), ["(lambda (x . rest) (f x . rest))"]);
    assert_eq!(read("(a . 'b) (a . (b c))").unwrap(), ["(a . 'b)", "(a . (b c))"]);
    assert_eq!(read("  ; nothing\n").unwrap(), Vec::<String>::new());
    assert_eq!(read("a;comment\nb\t(c)d").unwrap(), ["a", "b", "(c)", "d"]);
}

#[test]
fn identifiers_take_everything_up_to_a_delimiter() {
    let names = ["+", "-", "...", "->", "set!", "a.b", "λx", "list->vector", "a#b"];
    assert_eq!(read(&names.join(" ")).unwrap(), names);
    assert_eq!(read("a'b(c)d[e]").unwrap(), ["a", "'b", "(c)", "d", "(e)"]);
}

#[test]
fn identifiers_are_interned() {
    let mut arena = arena();
    arena
        .mutate(|mc| {
            let session = SyntaxSession::new(mc, "(a a b) a").unwrap();
            let nodes = read_all(mc, symbols(mc), &session).unwrap();
            let pairs = Pairs::new(mc);
            let heads: Vec<Value> = pairs.elements(nodes[0].datum(mc)).map(|v| Syntax::of(v).unwrap().datum(mc)).collect();
            assert_eq!(heads[0], heads[1]);
            assert_ne!(heads[0], heads[2]);
            assert_eq!(nodes[1].datum(mc), heads[0]);
            let strings = Strings::new(mc);
            assert_eq!(nodes[1].datum(mc), symbols(mc).intern_str(&strings, "a").unwrap().value(mc));
        });
}

#[test]
fn spans_cover_each_datum() {
    let mut arena = arena();
    arena
        .mutate(|mc| {
            let session = SyntaxSession::new(mc, "foo\n  '(a [b] . c)").unwrap();
            let nodes = read_all(mc, symbols(mc), &session).unwrap();
            let span = |node| (Syntax::span(node, mc).start(), Syntax::span(node, mc).end());
            assert_eq!(span(nodes[0]), (0, 3));
            assert_eq!(span(nodes[1]), (6, 18));
            assert_eq!(nodes[1].span(mc).location(mc), Some(SyntaxLocation { line: 2, column: 3 }));
            let list = Syntax::of(nodes[1].datum(mc)).unwrap();
            assert_eq!(span(list), (7, 18));
            let pairs = Pairs::new(mc);
            let items: Vec<_> = pairs.elements(list.datum(mc)).map(|v| span(Syntax::of(v).unwrap())).collect();
            assert_eq!(items, [(8, 9), (10, 13)]);
            let mut elements = pairs.elements(list.datum(mc));
            elements.by_ref().for_each(drop);
            let tail = elements.rest();
            assert_eq!(span(Syntax::of(tail).unwrap()), (16, 17));
        });
}

#[test]
fn malformed_text_is_an_error_where_it_goes_wrong() {
    assert_eq!(error(")"), (ErrorKind::UnexpectedClose, 0, 1));
    assert_eq!(error("(a]"), (ErrorKind::Mismatched { open: 0 }, 2, 3));
    assert_eq!(error("[a)"), (ErrorKind::Mismatched { open: 0 }, 2, 3));
    assert_eq!(error("(a (b)"), (ErrorKind::Unclosed, 0, 1));
    assert_eq!(error("((a)"), (ErrorKind::Unclosed, 0, 1));
    assert_eq!(error("'"), (ErrorKind::EmptyQuote, 0, 1));
    assert_eq!(error("(a ')"), (ErrorKind::EmptyQuote, 3, 4));
    assert_eq!(error("."), (ErrorKind::BadDot, 0, 1));
    assert_eq!(error("(. a)"), (ErrorKind::BadDot, 1, 2));
    assert_eq!(error("(a .)"), (ErrorKind::BadDot, 3, 4));
    assert_eq!(error("(a . b c)"), (ErrorKind::BadDot, 7, 8));
    assert_eq!(error("(a . b . c)"), (ErrorKind::BadDot, 7, 8));
    assert_eq!(error("'. a"), (ErrorKind::BadDot, 1, 2));
    let unsupported = [("42", 0, 2), ("(a -5)", 3, 5), (".5", 0, 2), ("\"s\"", 0, 1), ("#t", 0, 1), ("`a", 0, 1)];
    for (text, start, end) in unsupported.into_iter().chain([(",a", 0, 1), ("{a}", 0, 1), ("|a|", 0, 1)]) {
        assert_eq!(error(text), (ErrorKind::Unsupported, start, end), "{text}");
    }
}

#[test]
fn an_error_ends_the_text() {
    let mut arena = arena();
    arena
        .mutate(|mc| {
            let session = SyntaxSession::new(mc, "a ) b").unwrap();
            let mut reader = Reader::new(mc, symbols(mc), &session).unwrap();
            assert!(reader.next().unwrap().is_ok());
            assert_eq!(reader.next().unwrap().unwrap_err().kind, ErrorKind::UnexpectedClose);
            assert!(reader.next().is_none());
        });
}

#[test]
fn text_that_isnt_utf8_is_an_error() {
    let mut arena = arena();
    arena
        .mutate(|mc| {
            let session = SyntaxSession::new(mc, b"(a \xff)").unwrap();
            let e = Reader::new(mc, symbols(mc), &session).err().unwrap();
            assert_eq!((e.kind, e.start, e.end), (ErrorKind::InvalidUtf8, 3, 4));
        });
}

/// Nesting far deeper than a recursive reader's stack would allow.
#[test]
fn deep_nesting_reads_without_recursion() {
    const DEPTH: usize = 200_000;
    let text = format!("{}x{}", "(".repeat(DEPTH), ")".repeat(DEPTH));
    let mut arena = arena();
    arena
        .mutate(|mc| {
            let session = SyntaxSession::new(mc, &text).unwrap();
            let nodes = read_all(mc, symbols(mc), &session).unwrap();
            let pairs = Pairs::new(mc);
            let mut node = nodes[0];
            for _ in 0..DEPTH {
                assert_eq!(node.kind(mc), Some(SyntaxKind::List));
                node = Syntax::of(pairs.pair(node.datum(mc)).unwrap().head(mc)).unwrap();
            }
            assert_eq!(node.kind(mc), Some(SyntaxKind::Identifier));
        });
}

/// The datum of a list node's first item.
fn first<'gc>(mc: &Mutation<'gc>, list: Syntax<'gc>) -> Value<'gc> {
    let pairs = Pairs::new(mc);
    Syntax::of(pairs.pair(list.datum(mc)).unwrap().head(mc)).unwrap().datum(mc)
}

/// Nodes keep what they read alive and correct through collections that move them.
#[test]
fn read_syntax_survives_collection() {
    let mut arena = arena();
    let session = arena
        .mutate(|mc| {
            let session = SyntaxSession::new(mc, "(define (f x . rest) '[x rest])").unwrap();
            let node = read_all(mc, symbols(mc), &session).unwrap()[0];
            mc.set_root(1, node.value(mc));
            session
        });
    arena.set_evacuate_all(true);
    arena.collect();
    arena.collect();
    arena
        .mutate(|mc| {
            let node = Syntax::of(mc.root(1)).unwrap();
            assert_eq!(show(mc, node), "(define (f x . rest) '(x rest))");
            let strings = Strings::new(mc);
            let again = read_all(mc, symbols(mc), &session).unwrap()[0];
            assert_eq!(first(mc, node), first(mc, again));
            assert_eq!(first(mc, node), symbols(mc).intern_str(&strings, "define").unwrap().value(mc));
        });
}
