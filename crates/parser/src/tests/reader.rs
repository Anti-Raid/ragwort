use ragwort_types::gc::{Arena, Lock, Mutation, Rootable};
use ragwort_types::string::display;
use ragwort_types::syntax::SyntaxLocation;

use super::*;

struct Root;
impl Rootable for Root {
    type Root<'gc> = (Symbols<'gc>, Lock<Value<'gc>>);
}

fn arena() -> Arena<Root> {
    Arena::new(64 << 20, |_| Ok((Symbols::with_seed(1), Lock::new(Value::NIL)))).unwrap()
}

/// The datum a node reads as, written back out.
fn show<'gc>(mc: &Mutation<'gc>, node: Gc<'gc, Syntax<'gc>>) -> String {
    let strings = Strings::new(mc).unwrap();
    let pairs = Pairs::new(mc).unwrap();
    match node.kind(mc).unwrap() {
        SyntaxKind::Identifier => display(&strings, strings.name(strings.symbol(node.datum()).unwrap())).to_string(),
        SyntaxKind::Abbreviation(Abbreviation::Quote) => format!("'{}", show(mc, node.datum().downcast(mc).unwrap())),
        SyntaxKind::List => {
            let mut out = Vec::new();
            let mut rest = node.datum();
            while let Some(pair) = pairs.pair(rest) {
                out.push(show(mc, pair.head().downcast(mc).unwrap()));
                rest = pair.tail();
            }
            if rest != Value::NIL {
                out.push(format!(". {}", show(mc, rest.downcast(mc).unwrap())));
            }
            format!("({})", out.join(" "))
        }
        kind => panic!("the reader made a {kind:?} node"),
    }
}

/// Every datum in `text`, written back out, or the error reading it.
fn read(text: &str) -> Result<Vec<String>, ReadError> {
    let mut arena = arena();
    arena
        .mutate(|mc, root| {
            let session = SyntaxSession::new(mc, text).unwrap();
            Ok(read_all(mc, &root.0, &session)?.into_iter().map(|node| show(mc, node)).collect())
        })
        .unwrap()
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
        .mutate(|mc, root| {
            let session = SyntaxSession::new(mc, "(a a b) a").unwrap();
            let nodes = read_all(mc, &root.0, &session).unwrap();
            let pairs = Pairs::new(mc).unwrap();
            let heads: Vec<Value> = pairs.elements(nodes[0].datum()).map(|v| v.downcast::<Syntax>(mc).unwrap().datum()).collect();
            assert_eq!(heads[0], heads[1]);
            assert_ne!(heads[0], heads[2]);
            assert_eq!(nodes[1].datum(), heads[0]);
            let strings = Strings::new(mc).unwrap();
            assert_eq!(nodes[1].datum(), root.0.intern_str(&strings, "a").unwrap().value());
        })
        .unwrap();
}

#[test]
fn spans_cover_each_datum() {
    let mut arena = arena();
    arena
        .mutate(|mc, root| {
            let session = SyntaxSession::new(mc, "foo\n  '(a [b] . c)").unwrap();
            let nodes = read_all(mc, &root.0, &session).unwrap();
            let span = |node: Gc<Syntax>| (node.span().start(), node.span().end());
            assert_eq!(span(nodes[0]), (0, 3));
            assert_eq!(span(nodes[1]), (6, 18));
            assert_eq!(nodes[1].span().location(mc), Some(SyntaxLocation { line: 2, column: 3 }));
            let list = nodes[1].datum().downcast::<Syntax>(mc).unwrap();
            assert_eq!(span(list), (7, 18));
            let pairs = Pairs::new(mc).unwrap();
            let items: Vec<_> = pairs.elements(list.datum()).map(|v| span(v.downcast(mc).unwrap())).collect();
            assert_eq!(items, [(8, 9), (10, 13)]);
            let mut elements = pairs.elements(list.datum());
            elements.by_ref().for_each(drop);
            let tail = elements.rest();
            assert_eq!(span(tail.downcast(mc).unwrap()), (16, 17));
        })
        .unwrap();
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
        .mutate(|mc, root| {
            let session = SyntaxSession::new(mc, "a ) b").unwrap();
            let mut reader = Reader::new(mc, &root.0, &session).unwrap();
            assert!(reader.next().unwrap().is_ok());
            assert_eq!(reader.next().unwrap().unwrap_err().kind, ErrorKind::UnexpectedClose);
            assert!(reader.next().is_none());
        })
        .unwrap();
}

#[test]
fn text_that_isnt_utf8_is_an_error() {
    let mut arena = arena();
    arena
        .mutate(|mc, root| {
            let session = SyntaxSession::new(mc, b"(a \xff)").unwrap();
            let e = Reader::new(mc, &root.0, &session).err().unwrap();
            assert_eq!((e.kind, e.start, e.end), (ErrorKind::InvalidUtf8, 3, 4));
        })
        .unwrap();
}

/// Nesting far deeper than a recursive reader's stack would allow.
#[test]
fn deep_nesting_reads_without_recursion() {
    const DEPTH: usize = 200_000;
    let text = format!("{}x{}", "(".repeat(DEPTH), ")".repeat(DEPTH));
    let mut arena = arena();
    arena
        .mutate(|mc, root| {
            let session = SyntaxSession::new(mc, &text).unwrap();
            let nodes = read_all(mc, &root.0, &session).unwrap();
            let pairs = Pairs::new(mc).unwrap();
            let mut node = nodes[0];
            for _ in 0..DEPTH {
                assert_eq!(node.kind(mc), Some(SyntaxKind::List));
                node = pairs.pair(node.datum()).unwrap().head().downcast(mc).unwrap();
            }
            assert_eq!(node.kind(mc), Some(SyntaxKind::Identifier));
        })
        .unwrap();
}

/// The datum of a list node's first item.
fn first<'gc>(mc: &Mutation<'gc>, list: Gc<'gc, Syntax<'gc>>) -> Value<'gc> {
    let pairs = Pairs::new(mc).unwrap();
    pairs.pair(list.datum()).unwrap().head().downcast::<Syntax>(mc).unwrap().datum()
}

/// Nodes keep what they read alive and correct through collections that move them.
#[test]
fn read_syntax_survives_collection() {
    let mut arena = arena();
    let session = arena
        .mutate(|mc, root| {
            let session = SyntaxSession::new(mc, "(define (f x . rest) '[x rest])").unwrap();
            let node = read_all(mc, &root.0, &session).unwrap()[0];
            root.1.set(mc, Value::object(mc, node));
            session
        })
        .unwrap();
    arena.set_evacuate_all(true);
    arena.collect();
    arena.collect();
    arena
        .mutate(|mc, root| {
            let node = root.1.get().downcast::<Syntax>(mc).unwrap();
            assert_eq!(show(mc, node), "(define (f x . rest) '(x rest))");
            let strings = Strings::new(mc).unwrap();
            let again = read_all(mc, &root.0, &session).unwrap()[0];
            assert_eq!(first(mc, node), first(mc, again));
            assert_eq!(first(mc, node), root.0.intern_str(&strings, "define").unwrap().value());
        })
        .unwrap();
}
