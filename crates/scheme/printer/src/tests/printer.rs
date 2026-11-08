use ragwort_types::bytevector::Bytevectors;
use ragwort_types::gc::Arena;
use ragwort_types::pair::Pairs;
use ragwort_types::symbol::Symbols;
use ragwort_types::syntax::{SyntaxMeta, SyntaxSpan};
use ragwort_types::vector::Vectors;

use super::*;

fn with<R>(f: impl for<'gc> FnOnce(&Mutation<'gc>) -> R) -> R {
    let mut arena = Arena::new(1 << 24, 0);
    arena.mutate(|mc| f(mc))
}

fn number<'gc>(mc: &Mutation<'gc>, text: &str) -> Value<'gc> {
    number::parse(&Nums::new(mc), text).unwrap().unwrap().value()
}

fn symbol<'gc>(mc: &Mutation<'gc>, name: &str) -> Value<'gc> {
    let symbols = Symbols::new(mc).unwrap();
    symbols.intern_str(&Strings::new(mc), name).unwrap().value(mc)
}

fn text<'gc>(mc: &Mutation<'gc>, s: &str) -> Value<'gc> {
    string::from_str(&Strings::new(mc), s).unwrap().value()
}

fn write<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> String {
    to_string(mc, v, Mode::Write, usize::MAX).unwrap()
}

fn display<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> String {
    to_string(mc, v, Mode::Display, usize::MAX).unwrap()
}

#[test]
fn numbers_are_written_as_they_read() {
    with(|mc| {
        for n in ["0", "-7", "123456789012345678901234567890", "1/3", "-5/2", "1.0", "-0.0", "0.1", "1e300", "1e-7", "+inf.0", "-inf.0", "+nan.0", "1+2i", "1/2-3/4i", "+2.0i", "1.5-inf.0i"] {
            assert_eq!(write(mc, number(mc, n)), n);
        }
        assert_eq!(write(mc, number(mc, "#x1F")), "31");
    });
}

#[test]
fn strings_and_characters_are_escaped_only_by_write() {
    with(|mc| {
        let s = text(mc, "say \"hi\"\\\n\t\x01é");
        assert_eq!(write(mc, s), r#""say \"hi\"\\\n\t\x1;é""#);
        assert_eq!(display(mc, s), "say \"hi\"\\\n\t\x01é");
        let chars: Vec<_> = ['a', ' ', '\n', '\0', 'λ', '\u{85}'].iter().map(|&c| write(mc, Value::char(c))).collect();
        assert_eq!(chars, ["#\\a", "#\\space", "#\\newline", "#\\null", "#\\λ", "#\\x85"]);
        assert_eq!(display(mc, Value::char('λ')), "λ");
    });
}

#[test]
fn symbols_that_would_read_otherwise_are_quoted() {
    with(|mc| {
        let names = ["hello", "Hello", "+", "...", "->x", "+inf.0x", "a\\b", "", "a b", "1+", "+i", "-inf.0", "#foo", ".", "a|b", "(x)", "tab\t"];
        let written: Vec<_> = names.iter().map(|name| write(mc, symbol(mc, name))).collect();
        assert_eq!(
            written,
            ["hello", "Hello", "+", "...", "->x", "+inf.0x", "a\\b", "||", "|a b|", "|1+|", "|+i|", "|-inf.0|", "|#foo|", "|.|", "|a\\|b|", "|(x)|", "|tab\\t|"]
        );
        assert_eq!(display(mc, symbol(mc, "a b")), "a b");
    });
}

#[test]
fn lists_vectors_and_bytevectors_nest() {
    with(|mc| {
        let pairs = Pairs::new(mc);
        let vector = Vectors::new(mc).immutable_from_slice(&[number(mc, "4"), text(mc, "x")]).unwrap().value(mc);
        let dotted = pairs.cons(number(mc, "2"), number(mc, "3")).unwrap().value(mc);
        let bytes = Bytevectors::new(mc).immutable_from_slice(&[1, 255]).unwrap().value(mc);
        let empty = Vectors::new(mc).immutable_from_slice(&[]).unwrap().value(mc);
        let list = pairs.list(&[number(mc, "1"), dotted, vector, bytes, empty, Value::NIL, Value::TRUE, Value::FALSE, Value::VOID]).unwrap();
        assert_eq!(write(mc, list), r#"(1 (2 . 3) #(4 "x") #u8(1 255) #() () #t #f #<void>)"#);
        assert_eq!(display(mc, list), "(1 (2 . 3) #(4 x) #u8(1 255) #() () #t #f #<void>)");
    });
}

#[test]
fn deep_nesting_prints_without_recursion() {
    with(|mc| {
        let pairs = Pairs::new(mc);
        let mut v = Value::NIL;
        for _ in 0..100_000 {
            v = pairs.cons(v, Value::NIL).unwrap().value(mc);
        }
        assert_eq!(write(mc, v), format!("{}(){}", "(".repeat(100_000), ")".repeat(100_000)));
    });
}

#[test]
fn cycles_are_labelled_and_shared_data_only_if_asked() {
    with(|mc| {
        let (pairs, vectors) = (Pairs::new(mc), Vectors::new(mc));
        let cyclic = vectors.make(2, number(mc, "1")).unwrap();
        cyclic.items(mc).set(mc, 1, cyclic.value(mc));
        assert_eq!(write(mc, cyclic.value(mc)), "#0=#(1 #0#)");
        assert_eq!(display(mc, cyclic.value(mc)), "#0=#(1 #0#)");
        // A list that comes back to itself through a vector: the vector is labelled, the only
        // part of the cycle that could change to make it.
        let inner = vectors.make(1, Value::NIL).unwrap();
        let list = pairs.list(&[number(mc, "1"), inner.value(mc)]).unwrap();
        inner.items(mc).set(mc, 0, list);
        assert_eq!(write(mc, list), "(1 #0=#((1 #0#)))");
        // A labelled vector reached again is its label, however many ways it's reached.
        let twice_cyclic = pairs.list(&[cyclic.value(mc), cyclic.value(mc)]).unwrap();
        assert_eq!(write(mc, twice_cyclic), "(#0=#(1 #0#) #0#)");
        let shared = pairs.list(&[number(mc, "1")]).unwrap();
        let twice = pairs.list(&[shared, shared, cyclic.value(mc)]).unwrap();
        assert_eq!(write(mc, twice), "((1) (1) #0=#(1 #0#))");
        assert_eq!(to_string(mc, twice, Mode::Shared, usize::MAX).unwrap(), "(#0=(1) #0# #1=#(1 #1#))");
        // The tail of a list that's labelled is written after a dot.
        let tail = pairs.list(&[number(mc, "2")]).unwrap();
        let both = pairs.list(&[pairs.cons(number(mc, "1"), tail).unwrap().value(mc), tail]).unwrap();
        assert_eq!(to_string(mc, both, Mode::Shared, usize::MAX).unwrap(), "((1 . #0=(2)) #0#)");
    });
}

#[test]
fn output_stops_at_the_limit() {
    with(|mc| {
        let pairs = Pairs::new(mc);
        // Shared without a cycle, so written out each time: 2^64 leaves.
        let mut v = number(mc, "1");
        for _ in 0..64 {
            v = pairs.list(&[v, v]).unwrap();
        }
        let mut out = String::from("> ");
        assert_eq!(print(mc, v, Mode::Write, 1000, &mut out), Err(PrintError::TooLong));
        assert_eq!(out, "> ");
        let shared = to_string(mc, v, Mode::Shared, 1000).unwrap();
        assert!(shared.starts_with("(#0=(#1=(#2=(") && shared.contains("#62=(1 1) #62#) #61#)") && shared.ends_with("#1#) #0#)"), "{shared}");
        // A labelled vector is walked once, however many ways it's reached.
        let big = Vectors::new(mc).make(100, pairs.list(&[number(mc, "7")]).unwrap()).unwrap();
        big.items(mc).set(mc, 0, big.value(mc));
        let mut many = big.value(mc);
        for _ in 0..10 {
            many = pairs.list(&[many, many]).unwrap();
        }
        assert!(to_string(mc, many, Mode::Write, 20_000).unwrap().ends_with("#0#) (#0# #0#))))))))))"));
        // Past the walk, the text itself can be too long.
        let long = text(mc, &"x".repeat(2000));
        assert_eq!(to_string(mc, pairs.list(&[long]).unwrap(), Mode::Display, 1000), Err(PrintError::TooLong));
        assert_eq!(to_string(mc, number(mc, "12345"), Mode::Write, 4), Err(PrintError::TooLong));
        assert_eq!(to_string(mc, number(mc, "12345"), Mode::Write, 5).unwrap(), "12345");
    });
}

#[test]
fn syntax_is_written_as_its_datum_once() {
    with(|mc| {
        let meta = |kind| Some(SyntaxMeta::new(mc, kind, None, None).unwrap());
        let node = |datum, kind| Syntax::new(mc, datum, SyntaxSpan::default(), meta(kind)).unwrap().value(mc);
        let a = node(symbol(mc, "a"), SyntaxKind::Identifier);
        let quoted = node(node(symbol(mc, "b"), SyntaxKind::Identifier), SyntaxKind::Abbreviation(Abbreviation::Quote));
        let list = node(Pairs::new(mc).list(&[a, quoted, node(number(mc, "1"), SyntaxKind::Literal)]).unwrap(), SyntaxKind::List);
        assert_eq!(write(mc, list), "#<syntax (a 'b 1)>");
        assert_eq!(write(mc, Pairs::new(mc).list(&[a, a]).unwrap()), "(#<syntax a> #<syntax a>)");
    });
}

#[test]
fn external_refs_and_undefined_print_as_what_they_are() {
    with(|mc| {
        let external = Value::object(mc, ragwort_vm::module::external(mc, 5_u8, 0, Value::NIL).unwrap());
        let list = Pairs::new(mc).list(&[external, Value::UNDEFINED]).unwrap();
        assert_eq!(write(mc, list), "(#<external> #<undefined>)");
    });
}
