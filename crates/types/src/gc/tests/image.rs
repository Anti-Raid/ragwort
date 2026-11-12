use super::*;
use crate::gc::table::{Strong, Table, TableHead};
use crate::gc::{Arena, HostRef, objects};
use crate::num::{Nums, int};
use crate::pair::{Pair, Pairs};
use crate::string;
use crate::syntax::{Syntax, SyntaxSession, SyntaxSpan};
use crate::vector::Vectors;

objects! {
    kind Test at 900;

    struct Holder { host: Host<u32>, next: Value }
}

const STAMP: u64 = 7;

fn fix<'gc>(n: i64) -> Value<'gc> {
    Value::fixnum(n).unwrap()
}

fn text<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> String {
    let strings = Strings::new(mc);
    chars(&strings, strings.string(value).unwrap()).collect()
}

/// A list of one of each kind of thing, some of it shared and some of it in a cycle, and a
/// table keyed by what objects are.
fn sample<'gc>(mc: &Mutation<'gc>) -> Value<'gc> {
    let (symbols, strings, pairs, vectors, nums) = (Symbols::of_arena(mc).unwrap(), Strings::new(mc), Pairs::new(mc), Vectors::new(mc), Nums::new(mc));
    let name = symbols.intern_str(&strings, "a-name").unwrap();
    let keyword = symbols.keyword(mc, name).unwrap().value(mc);
    let long = string::from_str(&strings, &"a string too long to be a word. ".repeat(4)).unwrap().value();
    let big = int::expt(&nums, nums.integer(fix(2)).unwrap(), 100).unwrap().value();
    let float = Value::flonum(mc, 1e300).unwrap();
    let shared = pairs.cons(fix(1), fix(2)).unwrap().value(mc);
    let vector = vectors.from_slice(&[shared, shared, Value::NIL]).unwrap();
    vector.items(mc).set(mc, 2, vector.value(mc));
    let table = Table::<Strong>::new_eq(mc).unwrap();
    table.insert_eq(mc, shared, fix(10)).unwrap();
    table.insert_eq(mc, name.value(mc), fix(20)).unwrap();
    table.insert_eq(mc, fix(5), fix(30)).unwrap();
    let session = SyntaxSession::named(mc, "file.rg", "one\ntwo\nthree").unwrap();
    let span = SyntaxSpan::new(mc, session.source(mc).unwrap(), 4, 7).unwrap();
    let syntax = Syntax::new(mc, fix(2), span, None).unwrap().value(mc);
    let items = [name.value(mc), keyword, long, big, float, vector.value(mc), Value::object(mc, table.head()), syntax, Value::TRUE, fix(-3)];
    pairs.list(&items).unwrap()
}

fn kinds() -> Vec<Kind> {
    KINDS.to_vec()
}

fn saved() -> Vec<u8> {
    let mut arena = Arena::new(1 << 22, 0);
    arena.mutate(|mc| save(mc, STAMP, &[sample(mc), fix(9)], &kinds())).unwrap()
}

#[test]
fn what_is_saved_is_there_when_loaded() {
    let bytes = saved();
    let mut arena = Arena::new(1 << 22, 0);
    arena.mutate(|mc| {
        let roots = load(mc, STAMP, &bytes, &descs(), &kinds(), &()).unwrap();
        assert_eq!(roots.len(), 2);
        assert_eq!(roots[1], fix(9));
        let (symbols, strings, pairs, vectors, nums) = (Symbols::of_arena(mc).unwrap(), Strings::new(mc), Pairs::new(mc), Vectors::new(mc), Nums::new(mc));
        let items: Vec<Value> = pairs.elements(roots[0]).collect();
        assert_eq!(items.len(), 10);
        // A symbol is the arena's of its name, and a keyword that symbol's.
        let name = symbols.intern_str(&strings, "a-name").unwrap();
        assert_eq!(items[0], name.value(mc));
        assert_eq!(items[1], symbols.keyword(mc, name).unwrap().value(mc));
        assert_eq!(text(mc, items[2]), "a string too long to be a word. ".repeat(4));
        let big = int::expt(&nums, nums.integer(fix(2)).unwrap(), 100).unwrap();
        assert_eq!(int::compare(&nums, nums.integer(items[3]).unwrap(), big), std::cmp::Ordering::Equal);
        assert_eq!(items[4].as_flonum(mc), Some(1e300));
        // What was shared is shared, and what held itself holds itself.
        let vector = vectors.vector(items[5]).unwrap();
        let shared = vector.get(mc, 0).unwrap();
        assert_eq!(vector.get(mc, 1), Some(shared));
        assert_eq!(vector.get(mc, 2), Some(items[5]));
        let pair = Pair::of(shared).unwrap();
        assert_eq!((pair.head(mc), pair.tail(mc)), (fix(1), fix(2)));
        // A table keyed by what objects are finds them where they are now.
        let table = Table::<Strong>::of(items[6].downcast::<TableHead>(mc).unwrap());
        assert_eq!(table.get_eq(mc, shared).unwrap(), Some(fix(10)));
        assert_eq!(table.get_eq(mc, name.value(mc)).unwrap(), Some(fix(20)));
        assert_eq!(table.get_eq(mc, fix(5)).unwrap(), Some(fix(30)));
        assert_eq!(table.get_eq(mc, pairs.cons(fix(1), fix(2)).unwrap().value(mc)).unwrap(), None);
        // A frozen value is a copy.
        let span = Syntax::of(items[7]).unwrap().span(mc);
        assert_eq!((span.start(), span.end()), (4, 7));
        let source = span.source().unwrap();
        assert_eq!(source.name(mc).unwrap().bytes(mc), b"file.rg");
        assert_eq!(source.line_starts(mc), &[0, 4, 8]);
        assert_eq!((items[8], items[9]), (Value::TRUE, fix(-3)));
    });
    // It lives through collections, and can be saved again.
    arena.collect();
    let again = arena.mutate(|mc| {
        let roots = load(mc, STAMP, &bytes, &descs(), &kinds(), &()).unwrap();
        save(mc, STAMP, &roots, &kinds()).unwrap()
    });
    assert_eq!(again.len(), bytes.len());
}

#[test]
fn bytes_that_are_not_an_image_do_not_load() {
    let bytes = saved();
    let loaded = |bytes: &[u8], stamp: u64| Arena::new(1 << 22, 0).mutate(|mc| load(mc, stamp, bytes, &descs(), &kinds(), &()).map(|roots| roots.len()));
    assert_eq!(loaded(&bytes, STAMP), Ok(2));
    assert_eq!(loaded(&bytes, STAMP + 1), Err(LoadError::Stamp));
    for len in 0..bytes.len() {
        assert_eq!(loaded(&bytes[..len], STAMP), Err(LoadError::Malformed), "cut to {len}");
    }
    for at in (0..bytes.len()).step_by(7) {
        let mut changed = bytes.clone();
        changed[at] ^= 0x40;
        let expected = if (8..16).contains(&at) { LoadError::Stamp } else { LoadError::Malformed };
        assert_eq!(loaded(&changed, STAMP), Err(expected), "changed at {at}");
    }
    // An arena whose symbols are hashed another way can't take the image's.
    let mut arena = Arena::new(1 << 22, 0);
    let other = arena.mutate(|mc| {
        Symbols::with_seed(mc, 12345).unwrap();
        load(mc, STAMP, &bytes, &descs(), &kinds(), &()).map(|roots| roots.len())
    });
    assert_eq!(other, Err(LoadError::Symbols));
    // One that's too small says so.
    let small = Arena::new(1 << 12, 0).mutate(|mc| load(mc, STAMP, &bytes, &descs(), &kinds(), &()).map(|roots| roots.len()));
    assert_eq!(small, Err(LoadError::OutOfMemory));
}

#[test]
fn what_the_host_owns_is_not_saved() {
    let mut arena = Arena::new(1 << 22, 0);
    arena.mutate(|mc| {
        let host: HostRef<u32> = mc.host(5u32).unwrap();
        let holder = Holder::new(mc, Some(host), Value::NIL).unwrap();
        let number = Holder::DESC.number.unwrap();
        assert_eq!(save(mc, STAMP, &[Value::object(mc, holder)], &kinds()), Err(SaveError::Host(number)));
        // A frozen value of a kind that isn't given is the host's too.
        let session = SyntaxSession::new(mc, "text").unwrap();
        let span = SyntaxSpan::new(mc, session.source(mc).unwrap(), 0, 4).unwrap();
        let source = Syntax::new(mc, Value::NIL, span, None).unwrap().value(mc);
        assert!(matches!(save(mc, STAMP, &[source], &[]), Err(SaveError::Frozen(_))));
        assert!(save(mc, STAMP, &[source], &kinds()).is_ok());
        // A field that holds none of the host's is saved.
        let empty = Holder::new(mc, None, fix(1)).unwrap();
        assert!(save(mc, STAMP, &[Value::object(mc, empty)], &kinds()).is_ok());
    });
    assert_eq!(shape(&descs(), &kinds()), shape(&descs(), &kinds()));
    assert_ne!(shape(&descs(), &kinds()), shape(&descs(), &[]));
}
