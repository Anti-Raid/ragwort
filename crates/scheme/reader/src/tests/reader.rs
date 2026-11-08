use ragwort_types::gc::Arena;
use ragwort_types::bytevector::Bytevectors;
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
    let written = ragwort_printer_scheme::to_string(mc, node.value(mc), ragwort_printer_scheme::Mode::Write, usize::MAX).unwrap();
    written.strip_prefix("#<syntax ").and_then(|s| s.strip_suffix('>')).unwrap().to_string()
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
    for (text, start, end) in [("{a}", 0, 1), ("#&a", 0, 3), ("#!eof", 0, 5)] {
        assert_eq!(error(text), (ErrorKind::Unsupported, start, end), "{text}");
    }
    assert_eq!(error("#(a . b)"), (ErrorKind::BadDot, 4, 5));
    assert_eq!(error("#;"), (ErrorKind::EmptyQuote, 0, 2));
    assert_eq!(error("`"), (ErrorKind::EmptyQuote, 0, 1));
    assert_eq!(error("#| a |# #| b"), (ErrorKind::Unclosed, 8, 10));
    for (text, start, end) in [("1x", 0, 2), ("(a 1/0)", 3, 6), ("#xZZ", 0, 4), ("-1.5.2", 0, 6), ("1e", 0, 2), ("#e#e1", 0, 5)] {
        assert_eq!(error(text), (ErrorKind::BadNumber, start, end), "{text}");
    }
    assert_eq!(error(r"#\foo"), (ErrorKind::BadChar, 0, 5));
    assert_eq!(error(r"#\xZZ"), (ErrorKind::BadChar, 0, 5));
    assert_eq!(error("\"abc"), (ErrorKind::Unclosed, 0, 1));
    assert_eq!(error(r#""a\qb""#), (ErrorKind::BadEscape, 2, 4));
    assert_eq!(error(r#""\x41""#), (ErrorKind::BadEscape, 1, 5));
}

#[test]
fn reads_booleans_numbers_strings_and_characters() {
    assert_eq!(read("#t #f #true #false").unwrap(), ["#t", "#f", "#t", "#f"]);
    let numbers = "42 -5 +7 0 1/2 -6/4 #x-ff #XFF #b101 #o17 #d10 1.5 -.5 .5 1e3 1.5E-1 #e1.5 #e1e2 #i1/2 #x#e10 +inf.0 -inf.0";
    let read_as = [
        "42", "-5", "7", "0", "1/2", "-3/2", "-255", "255", "5", "15", "10", "1.5", "-0.5", "0.5", "1000.0", "0.15", "3/2",
        "100", "0.5", "16", "+inf.0", "-inf.0",
    ];
    assert_eq!(read(numbers).unwrap(), read_as);
    let big = "123456789012345678901234567890 -1/123456789012345678901";
    assert_eq!(read(big).unwrap(), ["123456789012345678901234567890", "-1/123456789012345678901"]);
    assert_eq!(read("+nan.0").unwrap(), ["+nan.0"]);
    assert_eq!(read("+ - ... +a -> a1 1+").unwrap_err().kind, ErrorKind::BadNumber);
    assert_eq!(read("+ - ... +a -> a1").unwrap(), ["+", "-", "...", "+a", "->", "a1"]);
    let strings = "\"a\\nb\" \"\\x41;\\t\" \"q\\\"\\\\\" \"λ\" \"line \\   \n       continued\" \"\"";
    assert_eq!(read(strings).unwrap(), [r#""a\nb""#, r#""A\t""#, r#""q\"\\""#, r#""λ""#, r#""line continued""#, r#""""#]);
    let chars = r"#\a #\space #\newline #\x41 #\λ #\( #\) #\x #\nul";
    assert_eq!(read(chars).unwrap(), ["#\\a", "#\\space", "#\\newline", "#\\A", "#\\λ", "#\\(", "#\\)", "#\\x", "#\\null"]);
}

#[test]
fn reads_vectors_quasiquotes_and_comments() {
    assert_eq!(read("#(a 1 (b #(c))) #()").unwrap(), ["#(a 1 (b #(c)))", "#()"]);
    assert_eq!(read("`(a ,b ,@c) ,,d").unwrap(), ["`(a ,b ,@c)", ",,d"]);
    assert_eq!(read("#'x #'(a b) #`(a #,b #,@c) #,#'d").unwrap(), ["#'x", "#'(a b)", "#`(a #,b #,@c)", "#,#'d"]);
    assert_eq!(read("a #| x #| nested |# y |# b").unwrap(), ["a", "b"]);
    assert_eq!(read("(a #;b c) #;(d e) f '#;g h #; #;i j k").unwrap(), ["(a c)", "f", "'h", "k"]);
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

/// R7RS lets case differ in everything but identifiers and character names.
#[test]
fn booleans_prefixes_and_infinities_ignore_case() {
    assert_eq!(read("#T #TRUE #False #X1A #E1.5 1E2").unwrap(), ["#t", "#t", "#f", "26", "3/2", "100.0"]);
    assert_eq!(read("+INF.0 -Inf.0 +NaN.0").unwrap(), ["+inf.0", "-inf.0", "+nan.0"]);
    assert_eq!(error(r"#\SPACE"), (ErrorKind::BadChar, 0, 7));
}

/// `\` then spaces or tabs, one line ending of any kind, and more spaces or tabs.
#[test]
fn line_continuations_take_one_line_ending() {
    for ending in ["\n", "\r\n", "\r"] {
        let text = format!("\"a\\  {ending}\t  b\"");
        assert_eq!(read(&text).unwrap(), [r#""ab""#], "{ending:?}");
    }
    assert_eq!(read("\"a\\\n\nb\"").unwrap(), [r#""a\nb""#]);
    assert_eq!(read("\"a\\\r\n\r\nb\"").unwrap(), [r#""a\r\nb""#]);
    // The first `\r` ends the line, so the rest stays.
    assert_eq!(read("\"a\\ \r \r\nb\"").unwrap(), [r#""a\r\nb""#]);
    assert_eq!(error("\"a\\  b\""), (ErrorKind::BadEscape, 2, 4));
    assert_eq!(error("\"a\\  "), (ErrorKind::Unclosed, 0, 1));
}

#[test]
fn a_dangling_prefix_is_an_error_across_all_of_it() {
    assert_eq!(error("(a ,@)"), (ErrorKind::EmptyQuote, 3, 5));
    assert_eq!(error("(a #,@)"), (ErrorKind::EmptyQuote, 3, 6));
    assert_eq!(error("#'"), (ErrorKind::EmptyQuote, 0, 2));
    assert_eq!(error("(a #;)"), (ErrorKind::EmptyQuote, 3, 5));
    assert_eq!(error(",@"), (ErrorKind::EmptyQuote, 0, 2));
    assert_eq!(error("(a . #;b)"), (ErrorKind::BadDot, 3, 4));
}

#[test]
fn reads_complex_numbers() {
    let numbers = "1+2i 1-2i +i -i 1+i 3/4-1/2i +2i -2.5i #e1.5+2i #x10+ai 1e2+1e1i #i1+2i 1@0 +inf.0i -nan.0+i";
    let read_as = [
        "1+2i", "1-2i", "+1i", "-1i", "1+1i", "3/4-1/2i", "+2i", "-2.5i", "3/2+2i", "16+10i", "100.0+10.0i", "1.0+2.0i",
        // Polar goes through floats, and an inexact part makes the other inexact, as in Racket.
        "1.0", "+inf.0i", "+nan.0+1.0i",
    ];
    assert_eq!(read(numbers).unwrap(), read_as);
    // Starting as a number does but not ending as one is an error; `+inf.0x` and `+in` are names.
    assert_eq!(read("+inf.0x +in +ix").unwrap(), ["+inf.0x", "+in", "+ix"]);
    for (text, end) in [("1+2", 3), ("2i", 2), ("1+2j", 4), ("1@", 2), ("1e+2i", 5), ("1+2i+3i", 7)] {
        assert_eq!(error(text), (ErrorKind::BadNumber, 0, end), "{text}");
    }
}

#[test]
fn reads_quoted_identifiers() {
    assert_eq!(read(r"|foo bar| || |a\x41;\|\\| |(x)| a|b|c").unwrap(), ["|foo bar|", "||", r"|aA\|\\|", "|(x)|", "a", "b", "c"]);
    assert_eq!(error("|abc"), (ErrorKind::Unclosed, 0, 1));
    assert_eq!(error(r"|a\qb|"), (ErrorKind::BadEscape, 2, 4));
    // Line continuations are only for strings.
    assert_eq!(error("|a\\\nb|"), (ErrorKind::BadEscape, 2, 4));
    let mut arena = arena();
    arena.mutate(|mc| {
        let session = SyntaxSession::new(mc, "|abc| abc").unwrap();
        let nodes = read_all(mc, symbols(mc), &session).unwrap();
        assert_eq!(nodes[0].datum(mc), nodes[1].datum(mc));
        assert_eq!(nodes[0].kind(mc), Some(SyntaxKind::Identifier));
    });
}

#[test]
fn reads_bytevectors() {
    assert_eq!(read("#u8(1 2 255) #U8() #u8(#xff 0)").unwrap(), ["#u8(1 2 255)", "#u8()", "#u8(255 0)"]);
    assert_eq!(error("#u8(1 256)"), (ErrorKind::BadByte, 6, 9));
    assert_eq!(error("#u8(1 -1)"), (ErrorKind::BadByte, 6, 8));
    assert_eq!(error("#u8(a)"), (ErrorKind::BadByte, 4, 5));
    assert_eq!(error("#u8(1.0)"), (ErrorKind::BadByte, 4, 7));
    assert_eq!(error("#u8((1))"), (ErrorKind::BadByte, 4, 7));
    assert_eq!(error("#u8(1 . 2)"), (ErrorKind::BadDot, 6, 7));
    assert_eq!(error("#u8(1 2"), (ErrorKind::Unclosed, 0, 1));
    let mut arena = arena();
    arena.mutate(|mc| {
        let session = SyntaxSession::new(mc, "#u8(7)").unwrap();
        let node = read_all(mc, symbols(mc), &session).unwrap()[0];
        assert_eq!(node.kind(mc), Some(SyntaxKind::Literal));
        assert!(!Bytevectors::new(mc).bytevector(node.datum(mc)).unwrap().is_mutable());
    });
}

#[test]
fn datum_labels_share_what_they_label() {
    assert_eq!(read("(#0=(a b) #0# #1=c . #1#)").unwrap(), ["((a b) (a b) c . c)"]);
    assert_eq!(read("#0='x").unwrap(), ["'x"]);
    let mut arena = arena();
    arena.mutate(|mc| {
        let session = SyntaxSession::new(mc, "(#7=(a) #7#)").unwrap();
        let node = read_all(mc, symbols(mc), &session).unwrap()[0];
        let items: Vec<_> = Pairs::new(mc).elements(node.datum(mc)).collect();
        assert_eq!(items[0], items[1]);
    });
    assert_eq!(error("#0=(a . #0#)"), (ErrorKind::CyclicLabel, 8, 11));
    assert_eq!(error("(#1#)"), (ErrorKind::UnknownLabel, 1, 4));
    assert_eq!(error("(#0=a #0=b)"), (ErrorKind::DuplicateLabel, 6, 9));
    // A label is only in its top-level datum.
    assert_eq!(error("#0=a #0#"), (ErrorKind::UnknownLabel, 5, 8));
    assert_eq!(error("(#0=)"), (ErrorKind::EmptyQuote, 1, 4));
    assert_eq!(error("#0="), (ErrorKind::EmptyQuote, 0, 3));
    assert_eq!(error("#99999999999999999999999#"), (ErrorKind::BadLabel, 0, 25));
}

#[test]
fn fold_case_lowers_identifiers_and_character_names() {
    let text = r"#!fold-case ABC Straße |XyZ| #\SPACE #\A #T #!no-fold-case ABC";
    assert_eq!(read(text).unwrap(), ["abc", "straße", "XyZ", "#\\space", "#\\A", "#t", "ABC"]);
    assert_eq!(read("#!FOLD-CASE A").unwrap(), ["a"]);
}
