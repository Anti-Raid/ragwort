use super::*;
use crate::gc::table::{Strong, Table, TableHead};
use crate::gc::{Arena, HostRef, objects};
use crate::num::{Nums, int};
use crate::pair::{Pair, Pairs};
use crate::string::{self, Str};
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

/// Returns a list with one value of each kind. Some of the values are shared, and one is in a cycle. The list also holds an
/// identity table.
fn sample<'gc>(mc: &Mutation<'gc>) -> Value<'gc> {
    let (symbols, strings, pairs, vectors, nums) = (Symbols::of_arena(mc).unwrap(), Strings::new(mc), Pairs::new(mc), Vectors::new(mc), Nums::new(mc));
    let name = symbols.intern_str(&strings, "a-name").unwrap();
    let keyword = symbols.keyword(mc, name).unwrap().value(mc);
    let long = string::from_str(&strings, &"a string too long to be a word. ".repeat(4)).unwrap().value();
    let big = int::expt(&nums, nums.integer(fix(2)).unwrap(), 100).unwrap().value();
    let float = Value::flonum(mc, 1e300).unwrap();
    let shared = pairs.cons(fix(1), fix(2)).unwrap().value(mc);
    let vector = vectors.from_slice(&[shared, shared, Value::NULL]).unwrap();
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
        // A loaded symbol is the arena's interned symbol with that name, and a loaded keyword is the keyword of that symbol.
        let name = symbols.intern_str(&strings, "a-name").unwrap();
        assert_eq!(items[0], name.value(mc));
        assert_eq!(items[1], symbols.keyword(mc, name).unwrap().value(mc));
        assert_eq!(text(mc, items[2]), "a string too long to be a word. ".repeat(4));
        let big = int::expt(&nums, nums.integer(fix(2)).unwrap(), 100).unwrap();
        assert_eq!(int::compare(&nums, nums.integer(items[3]).unwrap(), big), std::cmp::Ordering::Equal);
        assert_eq!(items[4].as_flonum(mc), Some(1e300));
        // A shared object is still shared, and an object that referred to itself still does.
        let vector = vectors.vector(items[5]).unwrap();
        let shared = vector.get(mc, 0).unwrap();
        assert_eq!(vector.get(mc, 1), Some(shared));
        assert_eq!(vector.get(mc, 2), Some(items[5]));
        let pair = Pair::of(shared).unwrap();
        assert_eq!((pair.head(mc), pair.tail(mc)), (fix(1), fix(2)));
        // An identity table finds its object keys at their new indices.
        let table = Table::<Strong>::of(items[6].downcast::<TableHead>(mc).unwrap());
        assert_eq!(table.get_eq(mc, shared).unwrap(), Some(fix(10)));
        assert_eq!(table.get_eq(mc, name.value(mc)).unwrap(), Some(fix(20)));
        assert_eq!(table.get_eq(mc, fix(5)).unwrap(), Some(fix(30)));
        assert_eq!(table.get_eq(mc, pairs.cons(fix(1), fix(2)).unwrap().value(mc)).unwrap(), None);
        // A frozen value is loaded as a copy of the saved value.
        let span = Syntax::of(items[7]).unwrap().span(mc);
        assert_eq!((span.start(), span.end()), (4, 7));
        let source = span.source().unwrap();
        assert_eq!(source.name(mc).unwrap().bytes(mc), b"file.rg");
        assert_eq!(source.line_starts(mc), &[0, 4, 8]);
        assert_eq!((items[8], items[9]), (Value::TRUE, fix(-3)));
    });
    // The loaded data survives a collection, and can be saved again.
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
    fn loaded(bytes: &[u8], stamp: u64) -> Result<usize, LoadError> {
        Arena::new(1 << 22, 0).mutate(|mc| load(mc, stamp, bytes, &descs(), &kinds(), &()).map(|roots| roots.len()))
    }
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
    // An arena whose symbols are hashed with another seed cannot load the image.
    let mut arena = Arena::new(1 << 22, 0);
    let other = arena.mutate(|mc| {
        Symbols::with_seed(mc, 12345).unwrap();
        load(mc, STAMP, &bytes, &descs(), &kinds(), &()).map(|roots| roots.len())
    });
    assert_eq!(other, Err(LoadError::Symbols));
    // An arena that is too small reports `OutOfMemory`.
    let small = Arena::new(1 << 12, 0).mutate(|mc| load(mc, STAMP, &bytes, &descs(), &kinds(), &()).map(|roots| roots.len()));
    assert_eq!(small, Err(LoadError::OutOfMemory));
}

#[test]
fn what_the_host_owns_is_not_saved() {
    let mut arena = Arena::new(1 << 22, 0);
    arena.mutate(|mc| {
        let host: HostRef<u32> = mc.host(5u32).unwrap();
        let holder = Holder::new(mc, Some(host), Value::NULL).unwrap();
        let number = Holder::DESC.number.unwrap();
        assert_eq!(save(mc, STAMP, &[Value::object(mc, holder)], &kinds()), Err(SaveError::Host(number)));
        // A frozen value that matches none of the given kinds also counts as owned by the host.
        let session = SyntaxSession::new(mc, "text").unwrap();
        let span = SyntaxSpan::new(mc, session.source(mc).unwrap(), 0, 4).unwrap();
        let source = Syntax::new(mc, Value::NULL, span, None).unwrap().value(mc);
        assert!(matches!(save(mc, STAMP, &[source], &[]), Err(SaveError::Frozen(_))));
        assert!(save(mc, STAMP, &[source], &kinds()).is_ok());
        // A host field that holds no host value is saved.
        let empty = Holder::new(mc, None, fix(1)).unwrap();
        assert!(save(mc, STAMP, &[Value::object(mc, empty)], &kinds()).is_ok());
    });
    assert_eq!(shape(&descs(), &kinds()), shape(&descs(), &kinds()));
    assert_ne!(shape(&descs(), &kinds()), shape(&descs(), &[]));
}

/// A string in an image is loaded as the arena's interned string with its characters. If the arena already has that text, the loaded string is the arena's own.
#[test]
fn loaded_strings_are_the_interned_strings_of_the_arena() {
    const FIRST: &str = "a string that the image holds";
    const SECOND: &str = "another string of the image, with two-byte characters: Ārvīds";
    let mut saving = Arena::new(1 << 22, 0);
    let bytes = saving.mutate(|mc| {
        let (strings, pairs) = (Strings::new(mc), Pairs::new(mc));
        let first = string::from_str(&strings, FIRST).unwrap().value();
        let second = string::from_str(&strings, SECOND).unwrap().value();
        // The first string is saved from two places.
        save(mc, STAMP, &[pairs.list(&[first, second, first]).unwrap()], &kinds()).unwrap()
    });
    // An arena that has not made the texts takes the loaded strings as its interned strings.
    let mut fresh = Arena::new(1 << 22, 0);
    fresh.mutate(|mc| {
        let roots = load(mc, STAMP, &bytes, &descs(), &kinds(), &()).unwrap();
        let (strings, pairs) = (Strings::new(mc), Pairs::new(mc));
        let items: Vec<Value> = pairs.elements(roots[0]).collect();
        assert_eq!((text(mc, items[0]), text(mc, items[1]), items[0] == items[2]), (FIRST.to_string(), SECOND.to_string(), true));
        let first = strings.string(items[0]).unwrap();
        assert!(strings.is_interned(first) && strings.is_interned(strings.string(items[1]).unwrap()));
        assert_eq!((string::from_str(&strings, FIRST), string::from_str(&strings, SECOND).map(Str::value)), (Ok(first), Ok(items[1])));
    });
    // An arena with the same seed that made the first text before the load keeps its own string, and the loaded data refers to it.
    let seed = fresh.mutate(|mc| Symbols::of_arena(mc).unwrap().seed(mc));
    let mut used = Arena::new(1 << 22, 0);
    used.mutate(|mc| {
        Symbols::with_seed(mc, seed).unwrap();
        let (strings, pairs) = (Strings::new(mc), Pairs::new(mc));
        let own = string::from_str(&strings, FIRST).unwrap();
        let roots = load(mc, STAMP, &bytes, &descs(), &kinds(), &()).unwrap();
        let items: Vec<Value> = pairs.elements(roots[0]).collect();
        assert_eq!((items[0], items[2], text(mc, items[1])), (own.value(), own.value(), SECOND.to_string()));
    });
}
