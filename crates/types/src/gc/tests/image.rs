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

/// A rope that is an interned string is saved as its text, so it is loaded as the arena's interned string with that text. A rope that is not interned is loaded as a rope.
#[test]
fn an_interned_rope_is_loaded_as_the_interned_string() {
    let (head, tail) = ("a piece that ropes share. ".repeat(30), "the end of the first rope");
    let whole = format!("{head}{tail}");
    let mut saving = Arena::new(1 << 22, 0);
    let bytes = saving.mutate(|mc| {
        let (strings, pairs) = (Strings::new(mc), Pairs::new(mc));
        let piece = string::from_str(&strings, &head).unwrap();
        let interned = string::concat(&strings, piece, string::from_str(&strings, tail).unwrap()).unwrap();
        assert_eq!((strings.intern(interned), string::is_flat(&strings, interned)), (Ok(interned), false));
        // The second rope has the same characters, and reads as the first once the two are compared. The third is never interned.
        let twin = string::concat(&strings, piece, string::from_str(&strings, tail).unwrap()).unwrap();
        assert_eq!((string::equal(&strings, twin, interned), twin == interned), (Ok(true), false));
        let plain = string::concat(&strings, piece, string::from_str(&strings, "the end of a rope that is not interned").unwrap()).unwrap();
        save(mc, STAMP, &[pairs.list(&[interned.value(), twin.value(), plain.value(), interned.value()]).unwrap()], &kinds()).unwrap()
    });
    let mut fresh = Arena::new(1 << 22, 0);
    fresh.mutate(|mc| {
        let roots = load(mc, STAMP, &bytes, &descs(), &kinds(), &()).unwrap();
        let (strings, pairs) = (Strings::new(mc), Pairs::new(mc));
        let items: Vec<Value> = pairs.elements(roots[0]).collect();
        let (interned, twin, plain) = (strings.string(items[0]).unwrap(), strings.string(items[1]).unwrap(), strings.string(items[2]).unwrap());
        assert_eq!((text(mc, items[0]), text(mc, items[1]), text(mc, items[2]), items[0] == items[3]), (whole.clone(), whole.clone(), format!("{head}the end of a rope that is not interned"), true));
        assert!(strings.is_interned(interned) && !strings.is_interned(plain) && !string::is_flat(&strings, plain));
        let made = string::from_str(&strings, &whole).unwrap();
        assert_eq!((strings.intern(made), strings.intern(twin), string::equal(&strings, twin, interned)), (Ok(interned), Ok(interned), Ok(true)));
    });
    // An arena whose interned string of the text is a rope keeps that rope, and the loaded data refers to it.
    let seed = fresh.mutate(|mc| Symbols::of_arena(mc).unwrap().seed(mc));
    let mut used = Arena::new(1 << 22, 0);
    used.mutate(|mc| {
        Symbols::with_seed(mc, seed).unwrap();
        let (strings, pairs) = (Strings::new(mc), Pairs::new(mc));
        let own = string::concat(&strings, string::from_str(&strings, &head).unwrap(), string::from_str(&strings, tail).unwrap()).unwrap();
        assert_eq!(strings.intern(own), Ok(own));
        let roots = load(mc, STAMP, &bytes, &descs(), &kinds(), &()).unwrap();
        let items: Vec<Value> = pairs.elements(roots[0]).collect();
        assert_eq!((items[0], items[3], strings.intern(strings.string(items[1]).unwrap()), text(mc, items[0])), (own.value(), own.value(), Ok(own), whole.clone()));
    });
}

/// An external string that is an interned string is saved as its text, and is loaded as a string of the arena.
#[test]
fn an_interned_external_string_is_loaded_as_text() {
    let name: std::sync::Arc<str> = std::sync::Arc::from("a text of the host that is long enough to be kept outside the arena");
    let mut saving = Arena::new(1 << 22, 0);
    let bytes = saving.mutate(|mc| {
        let (strings, pairs) = (Strings::new(mc), Pairs::new(mc));
        let outside = strings.external(string::ExternalText::new(name.clone())).unwrap();
        assert_eq!((strings.intern(outside), strings.is_external(outside)), (Ok(outside), true));
        save(mc, STAMP, &[pairs.list(&[outside.value(), outside.value()]).unwrap()], &kinds()).unwrap()
    });
    let mut fresh = Arena::new(1 << 22, 0);
    fresh.mutate(|mc| {
        let roots = load(mc, STAMP, &bytes, &descs(), &kinds(), &()).unwrap();
        let (strings, pairs) = (Strings::new(mc), Pairs::new(mc));
        let items: Vec<Value> = pairs.elements(roots[0]).collect();
        let loaded = strings.string(items[0]).unwrap();
        assert!(items[0] == items[1] && strings.is_interned(loaded) && !strings.is_external(loaded));
        assert_eq!((text(mc, items[0]), string::from_str(&strings, &name)), (name.to_string(), Ok(loaded)));
    });
}

/// A long flat string, which lives outside the arena, is saved as its text whether it is interned or not. So a program with a long string in it can be saved.
#[test]
fn a_long_string_is_saved_as_its_text() {
    let long = "a line of a long text that a program holds. ".repeat(40);
    let mut saving = Arena::new(1 << 22, 0);
    let bytes = saving.mutate(|mc| {
        let (strings, pairs) = (Strings::new(mc), Pairs::new(mc));
        let held = string::from_str(&strings, &long).unwrap();
        assert!(strings.is_external(held) && !strings.is_interned(held));
        save(mc, STAMP, &[pairs.list(&[held.value(), held.value()]).unwrap()], &kinds()).unwrap()
    });
    let mut fresh = Arena::new(1 << 22, 0);
    fresh.mutate(|mc| {
        let roots = load(mc, STAMP, &bytes, &descs(), &kinds(), &()).unwrap();
        let (strings, pairs) = (Strings::new(mc), Pairs::new(mc));
        let items: Vec<Value> = pairs.elements(roots[0]).collect();
        let loaded = strings.string(items[0]).unwrap();
        assert!(items[0] == items[1] && strings.is_external(loaded) && strings.is_interned(loaded));
        assert_eq!((text(mc, items[0]), strings.as_str(loaded)), (long.clone(), Some(&*long)));
    });
}

/// Arenas that load one template refer to the template's frozen values, and have no copies of them. Their objects are their own. An
/// arena lets go of the values when it is dropped.
#[test]
fn arenas_that_load_a_template_share_its_frozen_values() {
    let template = Template::new(STAMP, &saved(), &kinds(), &()).unwrap();
    let count = template.frozen_values();
    assert!(count >= 2, "{count} frozen values");
    assert_eq!(Rc::strong_count(&template.frozen), 1);
    let (mut first, mut second) = (Arena::new(1 << 22, 1), Arena::new(1 << 22, 1));
    for (arena, holders) in [(&mut first, 2), (&mut second, 3)] {
        arena.mutate(|mc| {
            let roots = template.load(mc, &descs()).unwrap();
            assert_eq!((roots.len(), roots[1]), (2, fix(9)));
            mc.set_root(0, roots[0]);
        });
        assert_eq!(Rc::strong_count(&template.frozen), holders);
        // The arena has no slot of its own for a shared value, and is charged for each as if it had a copy.
        assert_eq!((arena.frozen_values(), arena.meta.frozen.table_bytes() < 4096), (count, true));
        assert_eq!(arena.meta.frozen.charged(), template.frozen.iter().map(|value| value.cost).sum::<usize>());
    }
    // A change of an object in one arena is not seen in the other.
    first.mutate(|mc| {
        let items: Vec<Value> = Pairs::new(mc).elements(mc.root(0)).collect();
        Vectors::new(mc).mutable(items[5]).unwrap().items(mc).set(mc, 0, fix(77));
    });
    for (arena, expected) in [(&mut first, Some(77)), (&mut second, None)] {
        arena.set_evacuate_all(true);
        arena.collect();
        arena.mutate(|mc| {
            let items: Vec<Value> = Pairs::new(mc).elements(mc.root(0)).collect();
            assert_eq!(Vectors::new(mc).vector(items[5]).unwrap().get(mc, 0).unwrap().as_fixnum(), expected);
            // Both read the shared values.
            let source = Syntax::of(items[7]).unwrap().span(mc).source().unwrap();
            assert_eq!((source.name(mc).unwrap().bytes(mc), source.line_starts(mc)), (&b"file.rg"[..], &[0, 4, 8][..]));
        });
    }
    // An arena makes frozen values of its own beside the shared ones. A collection frees them, and never a shared value.
    second.mutate(|mc| {
        let own = SyntaxSession::named(mc, "other.rg", "four\nfive").unwrap();
        assert_eq!(own.source(mc).unwrap().line_starts(mc), &[0, 5]);
        let items: Vec<Value> = Pairs::new(mc).elements(mc.root(0)).collect();
        assert_eq!(Syntax::of(items[7]).unwrap().span(mc).source().unwrap().line_starts(mc), &[0, 4, 8]);
    });
    assert!(second.frozen_values() > count);
    second.mutate(|mc| mc.set_root(0, Value::NULL));
    second.collect();
    assert_eq!((second.frozen_values(), Rc::strong_count(&template.frozen)), (count, 3));
    // The arena saves its shared values like its own, and the image loads into an arena that shares nothing.
    let again = first.mutate(|mc| save(mc, STAMP, &[mc.root(0)], &kinds())).unwrap();
    let mut plain = Arena::new(1 << 22, 1);
    plain.mutate(|mc| {
        let roots = load(mc, STAMP, &again, &descs(), &kinds(), &()).unwrap();
        let items: Vec<Value> = Pairs::new(mc).elements(roots[0]).collect();
        assert_eq!(Syntax::of(items[7]).unwrap().span(mc).source().unwrap().line_starts(mc), &[0, 4, 8]);
        // An arena that holds frozen values already cannot share a template's.
        assert_eq!(template.load(mc, &descs()).err(), Some(LoadError::Used));
    });
    drop((first, second));
    assert_eq!(Rc::strong_count(&template.frozen), 1);
    // An image of another build makes no template.
    assert_eq!(Template::new(STAMP + 1, &saved(), &kinds(), &()).err(), Some(LoadError::Stamp));
}

/// Returns a list of tables for [`an_arena_that_loads_an_image_hashes_with_its_own_seed`]: a table with strings, numbers and a symbol as
/// keys, a table with a pair as a key, that pair, and 40 tables in shape mode whose shapes add one key each to a common shape.
fn keyed<'gc>(mc: &Mutation<'gc>) -> Value<'gc> {
    let (symbols, strings, tables, pairs) = (Symbols::of_arena(mc).unwrap(), Strings::new(mc), crate::table::Tables::new(mc), Pairs::new(mc));
    let plain = tables.make().unwrap();
    for number in 0..200 {
        let text = string::from_str(&strings, &format!("a key with the number {number}")).unwrap().value();
        plain.set(mc, text, fix(number)).unwrap();
        plain.set(mc, fix(number), fix(-number)).unwrap();
    }
    let pair = pairs.cons(fix(1), fix(2)).unwrap().value(mc);
    plain.set(mc, symbols.intern_str(&strings, "name").unwrap().value(mc), fix(1000)).unwrap();
    plain.set(mc, Value::flonum(mc, 1.5).unwrap(), fix(2000)).unwrap();
    // A key that is hashed by its place is in a table of its own. Such a table rebuilds its index after every collection that moves objects,
    // and the first table must be found right without that.
    let placed = tables.make().unwrap();
    placed.set(mc, pair, fix(3000)).unwrap();
    placed.set(mc, string::from_str(&strings, "beside the pair").unwrap().value(), fix(4000)).unwrap();
    let common = tables.shape(&[symbols.intern_str(&strings, "first").unwrap().value(mc), symbols.intern_str(&strings, "second").unwrap().value(mc)]).unwrap();
    let mut items = vec![plain.value(mc), placed.value(mc), pair];
    for number in 0..40 {
        let field = symbols.intern_str(&strings, &format!("field-{number}")).unwrap().value(mc);
        let shape = common.child(mc, field).unwrap();
        items.push(tables.shaped(shape, [Some(fix(1)), Some(fix(2)), Some(fix(number))].into_iter()).unwrap().value(mc));
    }
    pairs.list(&items).unwrap()
}

/// An image does not hold the hash seed of the arena that saved it. An arena that loads the image hashes with a seed of its own, and
/// finds every key of the loaded tables and shapes.
#[test]
fn an_arena_that_loads_an_image_hashes_with_its_own_seed() {
    let mut saving = Arena::new(1 << 22, 0);
    let bytes = saving.mutate(|mc| {
        Symbols::with_seed(mc, 777).unwrap();
        save(mc, STAMP, &[keyed(mc)], &kinds()).unwrap()
    });
    let template = Template::new(STAMP, &bytes, &kinds(), &()).unwrap();
    let mut seeds = Vec::new();
    // The first two arenas are new, and load the image and the template. The third has symbols already, and keeps their seed.
    for way in 0..3 {
        let mut arena = Arena::new(1 << 22, 1);
        let seed = arena.mutate(|mc| {
            let roots = match way {
                0 => load(mc, STAMP, &bytes, &descs(), &kinds(), &()).unwrap(),
                1 => template.load(mc, &descs()).unwrap(),
                _ => {
                    Symbols::with_seed(mc, 12345).unwrap();
                    load(mc, STAMP, &bytes, &descs(), &kinds(), &()).unwrap()
                }
            };
            mc.set_root(0, roots[0]);
            Symbols::of_arena(mc).unwrap().seed(mc)
        });
        seeds.push(seed);
        // The tables are read as they were loaded, and again after a collection that moves objects.
        for moved in [false, true] {
            if moved {
                arena.set_evacuate_all(true);
                arena.collect();
            }
            arena.mutate(|mc| read_keyed(mc, moved));
        }
    }
    assert!(seeds[0] != 777 && seeds[1] != 777 && seeds[0] != seeds[1], "{seeds:?}");
    assert_eq!(seeds[2], 12345);
}

/// Checks the tables that [`keyed`] made, in an arena that loaded them. `again` is whether this arena has checked them before.
fn read_keyed<'gc>(mc: &Mutation<'gc>, again: bool) {
    let (symbols, strings, tables, pairs) = (Symbols::of_arena(mc).unwrap(), Strings::new(mc), crate::table::Tables::new(mc), Pairs::new(mc));
    let items: Vec<Value> = pairs.elements(mc.root(0)).collect();
    let plain = tables.table(items[0]).unwrap();
    assert_eq!(plain.len(mc), if again { 403 } else { 402 });
    for number in 0..200 {
        let text = string::from_str(&strings, &format!("a key with the number {number}")).unwrap().value();
        assert_eq!((plain.get(mc, text).unwrap(), plain.get(mc, fix(number)).unwrap()), (Some(fix(number)), Some(fix(-number))));
    }
    assert_eq!(plain.get(mc, symbols.intern_str(&strings, "name").unwrap().value(mc)).unwrap(), Some(fix(1000)));
    assert_eq!(plain.get(mc, Value::flonum(mc, 1.5).unwrap()).unwrap(), Some(fix(2000)));
    let placed = tables.table(items[1]).unwrap();
    assert_eq!(placed.get(mc, items[2]).unwrap(), Some(fix(3000)));
    assert_eq!(placed.get(mc, string::from_str(&strings, "beside the pair").unwrap().value()).unwrap(), Some(fix(4000)));
    assert_eq!(plain.get(mc, string::from_str(&strings, "a key that is not there").unwrap().value()).unwrap(), None);
    plain.set(mc, string::from_str(&strings, "a key added after the load").unwrap().value(), fix(7)).unwrap();
    assert_eq!(plain.len(mc), 403);
    let (first, second) = (symbols.intern_str(&strings, "first").unwrap().value(mc), symbols.intern_str(&strings, "second").unwrap().value(mc));
    for number in 0..40 {
        let field = symbols.intern_str(&strings, &format!("field-{number}")).unwrap().value(mc);
        let shaped = tables.table(items[3 + number as usize]).unwrap();
        assert_eq!((shaped.get(mc, first).unwrap(), shaped.get(mc, second).unwrap(), shaped.get(mc, field).unwrap()), (Some(fix(1)), Some(fix(2)), Some(fix(number))));
        assert_eq!(shaped.get(mc, symbols.intern_str(&strings, "field-40").unwrap().value(mc)).unwrap(), None);
        // The shape that this arena makes for the same keys is the loaded one: the loaded shapes find their children.
        assert_eq!(tables.shape(&[first, second, field]).unwrap(), shaped.shape(mc).unwrap(), "shape {number}");
    }
}

