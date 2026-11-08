use super::*;

fn tokens(text: &str) -> Result<Vec<Token<'_>>, LexError> {
    Lexer::new(text).map(|l| l.map(|l| l.token)).collect()
}

fn error(text: &str) -> (ErrorKind, usize, usize) {
    let e = tokens(text).unwrap_err();
    (e.kind, e.start, e.end)
}

#[test]
fn brackets_prefixes_and_atoms_are_tokens() {
    use Token::*;
    let id = |s| Identifier(Cow::Borrowed(s));
    assert_eq!(
        tokens("(a [b] . c) 'x `y ,z ,@w #'s #`t #,u #,@v #(1) #u8(2) #;q #1=#1# #t #false #\\a #\\space").unwrap(),
        [
            Open(Bracket::Round), id("a"), Open(Bracket::Square), id("b"), Close(Bracket::Square), Dot, id("c"), Close(Bracket::Round),
            Prefix(super::Prefix::Quote), id("x"), Prefix(super::Prefix::Quasiquote), id("y"), Prefix(super::Prefix::Unquote), id("z"),
            Prefix(super::Prefix::UnquoteSplicing), id("w"), Prefix(super::Prefix::Syntax), id("s"), Prefix(super::Prefix::Quasisyntax), id("t"),
            Prefix(super::Prefix::Unsyntax), id("u"), Prefix(super::Prefix::UnsyntaxSplicing), id("v"),
            OpenVector, Number("1"), Close(Bracket::Round), OpenBytevector, Number("2"), Close(Bracket::Round),
            DatumComment, id("q"), Label(1), LabelRef(1), Boolean(true), Boolean(false), Char('a'), Char(' '),
        ]
    );
}

#[test]
fn spans_cover_each_token() {
    let spans: Vec<_> = Lexer::new(" (ab \"c d\" ; x\n #| y |# #\\x41)").map(|l| l.map(|l| (l.start, l.end)).unwrap()).collect();
    assert_eq!(spans, [(1, 2), (2, 4), (5, 10), (24, 29), (29, 30)]);
}

#[test]
fn numbers_and_what_might_be_are_told_apart() {
    assert_eq!(tokens("12 -3.5 .5 #x1F #e1.2").unwrap(), [Token::Number("12"), Token::Number("-3.5"), Token::Number(".5"), Token::Number("#x1F"), Token::Number("#e1.2")]);
    let or = |s| Token::NumberOr { text: s, name: Cow::Borrowed(s) };
    assert_eq!(tokens("+i -inf.0 +nan.0x + - ...").unwrap(), [or("+i"), or("-inf.0"), or("+nan.0x"), Token::Identifier("+".into()), Token::Identifier("-".into()), Token::Identifier("...".into())]);
}

#[test]
fn strings_and_quoted_names_borrow_unless_escaped() {
    let [Token::String(Cow::Borrowed("plain")), Token::String(Cow::Owned(escaped)), Token::Identifier(Cow::Borrowed("a b"))] = &tokens(r#""plain" "x\ty\x41;" |a b|"#).unwrap()[..] else {
        panic!("tokens")
    };
    assert_eq!(escaped, "x\tyA");
    assert_eq!(tokens("\"a\\\n   b\"").unwrap(), [Token::String("ab".into())]);
}

#[test]
fn fold_case_lowers_names_till_it_ends() {
    let names: Vec<_> = tokens("Ab #!fold-case Cd #\\SPACE |Ef| +INF.0 #!no-fold-case Gh").unwrap();
    assert_eq!(
        names,
        [
            Token::Identifier("Ab".into()),
            Token::Identifier("cd".into()),
            Token::Char(' '),
            Token::Identifier("Ef".into()),
            Token::NumberOr { text: "+INF.0", name: "+inf.0".into() },
            Token::Identifier("Gh".into()),
        ]
    );
}

#[test]
fn malformed_tokens_are_errors_where_they_go_wrong() {
    assert_eq!(error("\"abc"), (ErrorKind::Unclosed, 0, 1));
    assert_eq!(error("x #| a #| b |#"), (ErrorKind::Unclosed, 2, 4));
    assert_eq!(error("{"), (ErrorKind::Unsupported, 0, 1));
    assert_eq!(error("#!other"), (ErrorKind::Unsupported, 0, 7));
    assert_eq!(error("#\\nope"), (ErrorKind::BadChar, 0, 6));
    assert_eq!(error(r#""\q""#), (ErrorKind::BadEscape, 1, 3));
    assert_eq!(error("#99999999999999999999="), (ErrorKind::BadLabel, 0, 22));
}
