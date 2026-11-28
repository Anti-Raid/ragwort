use std::cell::Cell;
use std::rc::Rc;

use crate::external::{ExternalKind, ExternalRef, ExternalRefs};
use crate::gc::Arena;
use crate::num::int;
use crate::pair::Pairs;
use crate::string::{concat, from_str};
use crate::symbol::Symbol;

use super::*;

/// Returns an arena. Root 0 holds the symbol table. Root 1 holds the values that a test keeps across collections.
fn arena() -> Arena {
    let mut arena = Arena::new(64 << 20, 2);
    arena.mutate(|mc| mc.set_root(0, Symbols::with_seed(mc, 1).unwrap().value(mc)));
    arena
}

fn fix<'gc>(number: i64) -> Value<'gc> {
    Value::fixnum(number).unwrap()
}

fn text<'gc>(mc: &Mutation<'gc>, string: &str) -> Value<'gc> {
    from_str(&Strings::new(mc), string).unwrap().value()
}

fn symbol<'gc>(mc: &Mutation<'gc>, name: &str) -> Value<'gc> {
    Symbols::of(mc.root(0)).unwrap().intern_str(&Strings::new(mc), name).unwrap().value(mc)
}

/// The lookups of a table with each place reduced to its position, for the tests that are not about shapes.
trait Positions<'gc> {
    fn found(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<(usize, Value<'gc>)>, Error>;
    fn set_found(self, mc: &Mutation<'gc>, key: Value<'gc>, value: Value<'gc>) -> Result<Option<usize>, TableError>;
    fn field_set(self, mc: &Mutation<'gc>, key: Value<'gc>, value: Value<'gc>) -> Result<Option<usize>, TableError>;
    fn found_from(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize) -> Result<Option<(usize, Value<'gc>)>, Error>;
}

impl<'gc> Positions<'gc> for Table<'gc> {
    fn found(self, mc: &Mutation<'gc>, key: Value<'gc>) -> Result<Option<(usize, Value<'gc>)>, Error> {
        Ok(self.find(mc, key)?.map(|(place, value)| (place.position, value)))
    }

    fn set_found(self, mc: &Mutation<'gc>, key: Value<'gc>, value: Value<'gc>) -> Result<Option<usize>, TableError> {
        Ok(self.set_finding(mc, key, value)?.map(|place| place.position))
    }

    fn field_set(self, mc: &Mutation<'gc>, key: Value<'gc>, value: Value<'gc>) -> Result<Option<usize>, TableError> {
        Ok(self.set_field(mc, key, value)?.map(|place| place.position))
    }

    fn found_from(self, mc: &Mutation<'gc>, key: Value<'gc>, position: usize) -> Result<Option<(usize, Value<'gc>)>, Error> {
        Ok(self.find_from(mc, key, position)?.map(|(place, value)| (place.position, value)))
    }
}

fn entries<'gc>(mc: &Mutation<'gc>, table: Table<'gc>) -> Vec<(Value<'gc>, Value<'gc>)> {
    table.entries(mc).unwrap().collect()
}

/// Adds `key` with a value no other key of the table has, and returns that value.
fn add<'gc>(mc: &Mutation<'gc>, table: Table<'gc>, key: Value<'gc>) -> Value<'gc> {
    let value = fix(table.len(mc) as i64 + 1);
    table.set(mc, key, value).unwrap();
    value
}

#[test]
fn a_table_holds_what_is_set_until_it_is_removed() {
    arena().mutate(|mc| {
        let table = Tables::new(mc).make().unwrap();
        assert!(table.is_empty(mc));
        assert_eq!(table.get(mc, fix(1)), Ok(None));
        assert_eq!(table.delete(mc, fix(1)), Ok(false));
        table.set(mc, fix(1), Value::TRUE).unwrap();
        table.set(mc, fix(2), Value::FALSE).unwrap();
        assert_eq!((table.len(mc), table.get(mc, fix(1)), table.get(mc, fix(2))), (2, Ok(Some(Value::TRUE)), Ok(Some(Value::FALSE))));
        // Setting a key again changes its value and nothing else.
        table.set(mc, fix(1), Value::NULL).unwrap();
        assert_eq!((table.len(mc), table.get(mc, fix(1))), (2, Ok(Some(Value::NULL))));
        assert_eq!(table.delete(mc, fix(1)), Ok(true));
        assert_eq!(table.delete(mc, fix(1)), Ok(false));
        assert_eq!((table.len(mc), table.get(mc, fix(1)), table.get(mc, fix(2))), (1, Ok(None), Ok(Some(Value::FALSE))));
        table.clear(mc).unwrap();
        assert_eq!((table.len(mc), table.get(mc, fix(2)), entries(mc, table)), (0, Ok(None), vec![]));
        table.set(mc, fix(3), fix(4)).unwrap();
        assert_eq!(entries(mc, table), [(fix(3), fix(4))]);
        assert!(Table::of(fix(1)).is_none() && Table::of(table.value(mc)) == Some(table));
    });
}

#[test]
fn entries_stay_in_the_order_they_were_added() {
    arena().mutate(|mc| {
        let table = Tables::new(mc).make().unwrap();
        // Add enough entries to rebuild the arrays several times, in an order that no hash order would produce.
        let keys: Vec<i64> = (0..5000).map(|i| (i * 7919) % 5000).collect();
        for &key in &keys {
            table.set(mc, fix(key), fix(key * 2)).unwrap();
        }
        assert_eq!(entries(mc, table), keys.iter().map(|&key| (fix(key), fix(key * 2))).collect::<Vec<_>>());
        // Setting an existing key keeps its position. A key that was removed and is set again becomes the last entry.
        table.set(mc, fix(keys[10]), Value::TRUE).unwrap();
        assert_eq!(entries(mc, table)[10], (fix(keys[10]), Value::TRUE));
        assert_eq!(table.delete(mc, fix(keys[3])), Ok(true));
        table.set(mc, fix(keys[3]), Value::FALSE).unwrap();
        let after = entries(mc, table);
        assert_eq!((after.len(), after[3].0, after[4999]), (5000, fix(keys[4]), (fix(keys[3]), Value::FALSE)));
        // Removing most entries and adding others keeps the remaining entries in order, through the rebuilds that drop the tombstones.
        for &key in keys.iter().filter(|&&key| key % 10 != 0) {
            assert_eq!(table.delete(mc, fix(key)), Ok(true));
        }
        for extra in 5000..9000 {
            table.set(mc, fix(extra), Value::NULL).unwrap();
        }
        let kept = keys.iter().filter(|&&key| key % 10 == 0 && key != keys[3]).map(|&key| fix(key));
        let last = if keys[3] % 10 == 0 {
            Some(fix(keys[3]))
        } else {
            None
        };
        let expected: Vec<_> = kept.chain(last).chain((5000..9000).map(fix)).collect();
        assert_eq!(table.entries(mc).unwrap().map(|(key, _)| key).collect::<Vec<_>>(), expected);
        assert_eq!(table.len(mc), expected.len());
        for &key in &keys {
            assert_eq!(table.get(mc, fix(key)).unwrap().is_some(), key % 10 == 0, "{key}");
        }
    });
}

#[test]
fn a_table_made_with_room_takes_that_many_entries_as_it_is() {
    let mut arena = arena();
    arena.mutate(|mc| mc.set_root(1, Tables::new(mc).with_room(100).unwrap().value(mc)));
    let before = arena.used();
    arena.mutate(|mc| {
        let table = Table::of(mc.root(1)).unwrap();
        for key in 0..100 {
            table.set(mc, fix(key), fix(key)).unwrap();
        }
        assert_eq!((table.len(mc), table.get(mc, fix(99))), (100, Ok(Some(fix(99)))));
    });
    assert_eq!(arena.used(), before);
}

#[test]
fn keys_are_the_same_by_value_or_by_identity_as_their_kind_has_it() {
    arena().mutate(|mc| {
        let (strings, nums, pairs) = (Strings::new(mc), Nums::new(mc), Pairs::new(mc));
        let table = Tables::new(mc).make().unwrap();
        // Strings are compared by their characters, however they are stored: inline in the value word, flat, or as a rope.
        let long = "a string of more characters than a value holds, with é and 日本 in it";
        let (short, flat) = (add(mc, table, text(mc, "id")), add(mc, table, text(mc, long)));
        let rope = concat(&strings, strings.string(text(mc, &long[..20])).unwrap(), strings.string(text(mc, &long[20..])).unwrap()).unwrap();
        assert_eq!(table.get(mc, text(mc, "id")), Ok(Some(short)));
        assert_eq!(table.get(mc, text(mc, long)), Ok(Some(flat)));
        assert_eq!(table.get(mc, rope.value()), Ok(Some(flat)));
        assert_eq!(table.get(mc, text(mc, &long[1..])), Ok(None));
        // A symbol and the string of its name are different keys.
        let named = add(mc, table, symbol(mc, "id"));
        assert_eq!((table.get(mc, symbol(mc, "id")), table.get(mc, text(mc, "id"))), (Ok(Some(named)), Ok(Some(short))));
        assert_eq!(table.get(mc, symbol(mc, "other")), Ok(None));
        // Numbers are compared by value and exactness.
        fn big<'gc>(nums: &Nums<'_, 'gc>, negative: bool) -> Value<'gc> {
            let large = if negative {
                -(1 << 100)
            } else {
                1 << 100
            };
            int::from_i128(nums, large).unwrap().value()
        }
        let (one, one_inexact, huge) = (add(mc, table, fix(1)), add(mc, table, Value::flonum(mc, 1.0).unwrap()), add(mc, table, big(&nums, false)));
        assert_eq!(table.get(mc, fix(1)), Ok(Some(one)));
        assert_eq!(table.get(mc, Value::flonum(mc, 1.0).unwrap()), Ok(Some(one_inexact)));
        assert_eq!(table.get(mc, big(&nums, false)), Ok(Some(huge)));
        assert_eq!(table.get(mc, big(&nums, true)), Ok(None));
        // A flonum that does not fit in the value word is an object. It is still compared by its value.
        let boxed = 1e300;
        assert!(Value::inline_flonum(boxed).is_none());
        let small = add(mc, table, Value::flonum(mc, boxed).unwrap());
        assert_eq!(table.get(mc, Value::flonum(mc, boxed).unwrap()), Ok(Some(small)));
        // Characters and constants are compared by their value words.
        let (letter, truth, empty) = (add(mc, table, Value::char('x')), add(mc, table, Value::TRUE), add(mc, table, Value::NULL));
        assert_eq!((table.get(mc, Value::char('x')), table.get(mc, Value::TRUE), table.get(mc, Value::NULL)), (Ok(Some(letter)), Ok(Some(truth)), Ok(Some(empty))));
        assert_eq!((table.get(mc, Value::char('y')), table.get(mc, Value::FALSE)), (Ok(None), Ok(None)));
        // Any other object is compared by identity: two lists with the same items are two keys.
        let (first, second) = (pairs.list(&[fix(1), fix(2)]).unwrap(), pairs.list(&[fix(1), fix(2)]).unwrap());
        let (one_list, other_list) = (add(mc, table, first), add(mc, table, second));
        assert_eq!((table.get(mc, first), table.get(mc, second)), (Ok(Some(one_list)), Ok(Some(other_list))));
        assert_eq!(table.get(mc, pairs.list(&[fix(1), fix(2)]).unwrap()), Ok(None));
        assert_eq!(table.len(mc), 12);
    });
}

/// An object that is compared by identity is hashed by its object word. A collection that moves objects changes those hashes, and the table must still find every key.
#[test]
fn keys_by_identity_are_found_after_objects_move() {
    let mut arena = arena();
    arena.mutate(|mc| {
        let (tables, pairs) = (Tables::new(mc), Pairs::new(mc));
        let (table, plain) = (tables.make().unwrap(), tables.make().unwrap());
        let mut keys = Value::NULL;
        for number in 0..2000 {
            let key = pairs.cons(fix(number), Value::NULL).unwrap().value(mc);
            table.set(mc, key, fix(number)).unwrap();
            table.set(mc, fix(number), key).unwrap();
            plain.set(mc, text(mc, &format!("a longer key, number {number}")), fix(number)).unwrap();
            keys = pairs.cons(key, keys).unwrap().value(mc);
            // Allocate garbage between the keys, so that a collection has holes to move the keys into.
            pairs.list(&[fix(number); 20]).unwrap();
        }
        assert!(!table.is_stale(mc) && !plain.is_stale(mc));
        mc.set_root(1, pairs.list(&[table.value(mc), plain.value(mc), keys]).unwrap());
    });
    for round in 0..3 {
        arena.set_evacuate_all(true);
        arena.collect();
        arena.mutate(|mc| {
            let pairs = Pairs::new(mc);
            let kept: Vec<_> = pairs.elements(mc.root(1)).collect();
            let (table, plain) = (Table::of(kept[0]).unwrap(), Table::of(kept[1]).unwrap());
            // Only the table with keys hashed by object word has to rebuild its index.
            assert!(table.is_stale(mc) && !plain.is_stale(mc), "round {round}");
            let mut number = 2000;
            for key in pairs.elements(kept[2]) {
                number -= 1;
                assert_eq!(table.get(mc, key), Ok(Some(fix(number))));
                assert_eq!(table.get(mc, fix(number)), Ok(Some(key)));
                assert_eq!(plain.get(mc, text(mc, &format!("a longer key, number {number}"))), Ok(Some(fix(number))));
            }
            assert!(!table.is_stale(mc));
            assert_eq!((table.len(mc), plain.len(mc)), (4000, 2000));
            // The table still works after the rebuild: a removed key is gone, and a key that is set again is found.
            let first = pairs.elements(kept[2]).next().unwrap();
            assert_eq!(table.delete(mc, first), Ok(true));
            assert_eq!(table.get(mc, first), Ok(None));
            table.set(mc, first, fix(1999)).unwrap();
            assert_eq!(table.get(mc, first), Ok(Some(fix(1999))));
        });
    }
}

struct UserId(u64);

static USER_ID: ExternalKind<UserId> = ExternalKind::by_value("user-id", |first, second| first.0 == second.0, |id| id.0);
static OTHER_ID: ExternalKind<i64> = ExternalKind::by_value("other-id", |first, second| first == second, |id| *id as u64);
static HANDLE: ExternalKind<u64> = ExternalKind::by_identity("handle");

/// An external reference is compared as a key the way its kind specifies: by the host's equality, or by identity.
#[test]
fn external_references_are_keys_as_their_kind_says() {
    let mut arena = arena();
    arena.mutate(|mc| {
        fn user<'gc>(mc: &Mutation<'gc>, externals: &ExternalRefs<'_, 'gc>, id: u64) -> Value<'gc> {
            externals.make(&USER_ID, UserId(id), 0, Value::NULL).unwrap().value(mc)
        }
        let externals = ExternalRefs::new(mc);
        let (by_value, by_identity) = (Tables::new(mc).make().unwrap(), Tables::new(mc).make().unwrap());
        for id in 0..500 {
            by_value.set(mc, user(mc, &externals, id), fix(id as i64)).unwrap();
        }
        // Another reference to an equal value is the same key. A reference of another kind is a different key, although it has the same hash. The number 7 is a different key too.
        assert_eq!(by_value.len(mc), 500);
        by_value.set(mc, user(mc, &externals, 7), Value::TRUE).unwrap();
        assert_eq!((by_value.len(mc), by_value.get(mc, user(mc, &externals, 7)), by_value.get(mc, user(mc, &externals, 8)), by_value.get(mc, user(mc, &externals, 500))), (500, Ok(Some(Value::TRUE)), Ok(Some(fix(8))), Ok(None)));
        let other = externals.make(&OTHER_ID, 7, 0, Value::NULL).unwrap().value(mc);
        assert_eq!((by_value.get(mc, other), by_value.get(mc, fix(7))), (Ok(None), Ok(None)));
        by_value.set(mc, other, Value::FALSE).unwrap();
        assert_eq!((by_value.get(mc, other), by_value.get(mc, user(mc, &externals, 7)), by_value.len(mc)), (Ok(Some(Value::FALSE)), Ok(Some(Value::TRUE)), 501));
        assert_eq!(by_value.delete(mc, user(mc, &externals, 7)), Ok(true));
        assert_eq!((by_value.get(mc, user(mc, &externals, 7)), by_value.get(mc, other)), (Ok(None), Ok(Some(Value::FALSE))));
        // For a kind without an equality function, each reference is its own key.
        let handles: Vec<_> = (0..500).map(|number| externals.make(&HANDLE, number % 2, 0, Value::NULL).unwrap().value(mc)).collect();
        for (number, &handle) in handles.iter().enumerate() {
            by_identity.set(mc, handle, fix(number as i64)).unwrap();
        }
        assert_eq!((by_identity.len(mc), by_identity.get(mc, handles[3]), by_identity.get(mc, externals.make(&HANDLE, 1, 0, Value::NULL).unwrap().value(mc))), (500, Ok(Some(fix(3))), Ok(None)));
        let pairs = Pairs::new(mc);
        mc.set_root(1, pairs.list(&[by_value.value(mc), by_identity.value(mc), pairs.list(&handles).unwrap()]).unwrap());
    });
    arena.set_evacuate_all(true);
    arena.collect();
    arena.mutate(|mc| {
        let (externals, pairs) = (ExternalRefs::new(mc), Pairs::new(mc));
        let kept: Vec<_> = pairs.elements(mc.root(1)).collect();
        let (by_value, by_identity) = (Table::of(kept[0]).unwrap(), Table::of(kept[1]).unwrap());
        // A key hashed by the host's hash function does not depend on its object word. A key compared by identity does.
        assert!(!by_value.is_stale(mc) && by_identity.is_stale(mc));
        assert_eq!(by_value.get(mc, externals.make(&USER_ID, UserId(8), 0, Value::NULL).unwrap().value(mc)), Ok(Some(fix(8))));
        for (number, handle) in pairs.elements(kept[2]).enumerate() {
            assert_eq!(by_identity.get(mc, handle), Ok(Some(fix(number as i64))));
        }
    });
}

/// A message as a host received it, with a nested author. Its fields are read in place. `reads` counts the calls of `get`. `dropped` is set when the arena drops the message.
struct Message {
    id: i64,
    content: &'static str,
    author: Option<&'static str>,
    reads: Rc<Cell<usize>>,
    dropped: Rc<Cell<bool>>,
}

/// The author of a [`Message`]. A message creates a new `Author` table on each read of its `author` key.
struct Author(&'static str);

impl Drop for Message {
    fn drop(&mut self) {
        self.dropped.set(true);
    }
}

impl ExternalTable for Message {
    fn len(&self) -> usize {
        2 + usize::from(self.author.is_some())
    }

    fn has(&self, key: Key<'_>) -> bool {
        matches!(key, Key::Symbol("id" | "content")) || key == Key::Symbol("author") && self.author.is_some()
    }

    fn get<'gc>(&self, mc: &Mutation<'gc>, key: Key<'_>) -> Result<Option<Value<'gc>>, Error> {
        self.reads.set(self.reads.get() + 1);
        Ok(match key {
            Key::Symbol("id") => Value::fixnum(self.id),
            Key::Symbol("content") => Some(text(mc, self.content)),
            Key::Symbol("author") => match self.author {
                Some(name) => Some(Tables::new(mc).external(Author(name), 0)?.value(mc)),
                None => None,
            },
            _ => None,
        })
    }

    fn keys(&self) -> impl Iterator<Item = Key<'_>> {
        [Key::Symbol("id"), Key::Symbol("content"), Key::Symbol("author")].into_iter().take(self.len())
    }
}

impl ExternalTable for Author {
    fn len(&self) -> usize {
        1
    }

    fn has(&self, key: Key<'_>) -> bool {
        key == Key::String("name")
    }

    fn get<'gc>(&self, mc: &Mutation<'gc>, key: Key<'_>) -> Result<Option<Value<'gc>>, Error> {
        let found = if self.has(key) {
            Some(text(mc, self.0))
        } else {
            None
        };
        Ok(found)
    }

    fn keys(&self) -> impl Iterator<Item = Key<'_>> {
        std::iter::once(Key::String("name"))
    }
}

/// Counters that the host owns and programs can modify: integer values under string or integer keys, in the order they were added.
#[derive(Default)]
struct Counters(Vec<(CounterKey, i64)>);

#[derive(PartialEq)]
enum CounterKey {
    Name(String),
    Number(i64),
}

impl CounterKey {
    fn of(key: Key<'_>) -> Option<Self> {
        match key {
            Key::String(name) => Some(Self::Name(name.to_string())),
            Key::Integer(number) => Some(Self::Number(number)),
            _ => None,
        }
    }
}

impl ExternalTable for Counters {
    const WRITABLE: bool = true;

    fn len(&self) -> usize {
        self.0.len()
    }

    fn has(&self, key: Key<'_>) -> bool {
        CounterKey::of(key).is_some_and(|key| self.0.iter().any(|(held, _)| *held == key))
    }

    fn get<'gc>(&self, _: &Mutation<'gc>, key: Key<'_>) -> Result<Option<Value<'gc>>, Error> {
        let Some(key) = CounterKey::of(key) else { return Ok(None) };
        Ok(self.0.iter().find(|(held, _)| *held == key).and_then(|&(_, count)| Value::fixnum(count)))
    }

    fn keys(&self) -> impl Iterator<Item = Key<'_>> {
        self.0.iter().map(|(key, _)| match key {
            CounterKey::Name(name) => Key::String(name),
            CounterKey::Number(number) => Key::Integer(*number),
        })
    }

    fn set<'gc>(&mut self, _: &Mutation<'gc>, key: Key<'_>, value: Value<'gc>) -> Result<(), Refused> {
        let (Some(key), Some(count)) = (CounterKey::of(key), value.as_fixnum()) else { return Err(Refused) };
        match self.0.iter_mut().find(|(held, _)| *held == key) {
            Some(entry) => entry.1 = count,
            None => self.0.push((key, count)),
        }
        Ok(())
    }

    fn delete(&mut self, key: Key<'_>) -> bool {
        let Some(key) = CounterKey::of(key) else { return false };
        let before = self.0.len();
        self.0.retain(|(held, _)| *held != key);
        self.0.len() < before
    }

    fn clear(&mut self) {
        self.0.clear();
    }
}

/// Returns the counts that the host of `table` holds, in the host's order.
fn counts<'gc>(mc: &Mutation<'gc>, table: Table<'gc>) -> Vec<i64> {
    table.host::<Counters>(mc).unwrap().0.iter().map(|&(_, count)| count).collect()
}

fn message<'gc>(mc: &Mutation<'gc>, author: Option<&'static str>, reads: &Rc<Cell<usize>>, dropped: &Rc<Cell<bool>>) -> Table<'gc> {
    let host = Message { id: 7, content: "a message long enough not to fit in a word", author, reads: reads.clone(), dropped: dropped.clone() };
    Tables::new(mc).external(host, 64).unwrap()
}

/// A program reads an external table like any other. Each value is read from the host once. The table returns that cached value from then on.
#[test]
fn an_external_table_is_read_from_its_host_once() {
    let (reads, dropped) = (Rc::new(Cell::new(0)), Rc::new(Cell::new(false)));
    let mut arena = arena();
    arena.mutate(|mc| {
        let table = message(mc, Some("ann"), &reads, &dropped);
        assert!(table.is_external() && !table.is_writable(mc) && !table.is_stale(mc));
        assert_eq!((Table::of(table.value(mc)), table.len(mc), reads.get()), (Some(table), 3, 0));
        // Checking whether a key is present does not read its value.
        assert_eq!((table.has(mc, symbol(mc, "content")), table.has(mc, symbol(mc, "missing")), table.has(mc, text(mc, "content")), reads.get()), (Ok(true), Ok(false), Ok(false), 0));
        let content = table.get(mc, symbol(mc, "content")).unwrap().unwrap();
        assert_eq!((table.get(mc, symbol(mc, "id")), reads.get()), (Ok(Some(fix(7))), 2));
        assert_eq!((table.get(mc, symbol(mc, "content")), table.get(mc, symbol(mc, "id")), table.has(mc, symbol(mc, "id")), reads.get()), (Ok(Some(content)), Ok(Some(fix(7))), Ok(true), 2));
        // A nested table that the host created for a key is the same table on every read.
        let author = table.get(mc, symbol(mc, "author")).unwrap().unwrap();
        assert_eq!((table.get(mc, symbol(mc, "author")), reads.get()), (Ok(Some(author)), 3));
        assert_eq!(Table::of(author).unwrap().get(mc, text(mc, "name")), Ok(Some(text(mc, "ann"))));
        // A missing key is requested from the host on every read, and nothing is cached for it. A key of a kind that the host cannot accept is never passed to the host.
        assert_eq!((table.get(mc, symbol(mc, "missing")), table.get(mc, symbol(mc, "missing")), reads.get()), (Ok(None), Ok(None), 5));
        let pair = Pairs::new(mc).list(&[fix(1)]).unwrap();
        assert_eq!((table.get(mc, pair), table.get(mc, Value::NIL), table.has(mc, pair), reads.get()), (Ok(None), Ok(None), Ok(false), 5));
        // `host` returns the host's value for its own type. It returns `None` for another type, and for a table in the arena.
        assert_eq!(table.host::<Message>(mc).map(|host| host.id), Some(7));
        assert!(table.host::<Counters>(mc).is_none() && Tables::new(mc).make().unwrap().host::<Message>(mc).is_none());
        mc.set_root(1, Pairs::new(mc).list(&[table.value(mc), content, author]).unwrap());
    });
    // The cached values survive a collection that moves objects, and are still not read from the host again.
    arena.set_evacuate_all(true);
    arena.collect();
    arena.mutate(|mc| {
        let kept: Vec<_> = Pairs::new(mc).elements(mc.root(1)).collect();
        let table = Table::of(kept[0]).unwrap();
        assert_eq!((table.get(mc, symbol(mc, "content")), table.get(mc, symbol(mc, "author")), reads.get()), (Ok(Some(kept[1])), Ok(Some(kept[2])), 5));
        mc.set_root(1, Value::NULL);
    });
    assert!(!dropped.get());
    arena.collect();
    arena.collect();
    assert!(dropped.get());
}

#[test]
fn an_external_table_is_walked_in_its_hosts_order() {
    let (reads, dropped) = (Rc::new(Cell::new(0)), Rc::new(Cell::new(false)));
    arena().mutate(|mc| {
        let table = message(mc, None, &reads, &dropped);
        let id = table.get(mc, symbol(mc, "id")).unwrap().unwrap();
        // Iterating the table reads each value that is not cached yet, once. A second iteration reads nothing from the host.
        let walked = entries(mc, table);
        assert_eq!(walked.iter().map(|&(key, _)| key).collect::<Vec<_>>(), [symbol(mc, "id"), symbol(mc, "content")]);
        assert_eq!((walked[0].1, reads.get()), (id, 2));
        assert_eq!((entries(mc, table), reads.get()), (walked.clone(), 2));
        assert_eq!((0..5).map(|index| table.held(mc, index)).collect::<Vec<_>>(), [Some(walked[0].0), Some(walked[0].1), Some(walked[1].0), Some(walked[1].1), None]);
        assert_eq!(table.get(mc, symbol(mc, "content")), Ok(Some(walked[1].1)));
    });
}

/// A host that implements `entries`, and so supplies its entries in one pass: three numbers and a nested table under symbol keys. `walks` counts the passes, and `gets` counts the calls of `get`.
struct Listed {
    walks: Rc<Cell<usize>>,
    gets: Rc<Cell<usize>>,
}

const LISTED: [&str; 4] = ["one", "two", "inner", "three"];

impl Listed {
    fn value<'gc>(mc: &Mutation<'gc>, name: &str) -> Result<Option<Value<'gc>>, Error> {
        Ok(match name {
            "one" => Some(fix(1)),
            "two" => Some(fix(2)),
            "three" => Some(fix(3)),
            // This creates a new table on every call. The arena's cache is what makes later reads return the same table.
            "inner" => Some(Tables::new(mc).external(Author("ann"), 0)?.value(mc)),
            _ => None,
        })
    }
}

impl ExternalTable for Listed {
    fn len(&self) -> usize {
        LISTED.len()
    }

    fn has(&self, key: Key<'_>) -> bool {
        matches!(key, Key::Symbol(name) if LISTED.contains(&name))
    }

    fn get<'gc>(&self, mc: &Mutation<'gc>, key: Key<'_>) -> Result<Option<Value<'gc>>, Error> {
        self.gets.set(self.gets.get() + 1);
        let Key::Symbol(name) = key else { return Ok(None) };
        Self::value(mc, name)
    }

    fn keys(&self) -> impl Iterator<Item = Key<'_>> {
        LISTED.into_iter().map(Key::Symbol)
    }

    fn entries<'gc>(&self, mc: &Mutation<'gc>) -> Option<impl Iterator<Item = Result<(Key<'_>, Value<'gc>), Error>>> {
        self.walks.set(self.walks.get() + 1);
        Some(LISTED.into_iter().map(move |name| Ok((Key::Symbol(name), Self::value(mc, name)?.expect("a listed name has a value")))))
    }
}

/// A host that implements `entries` is called once for an iteration, not once for each value. A value that was cached before the iteration stays the same.
#[test]
fn a_host_that_gives_its_entries_is_asked_once_for_a_walk() {
    let (walks, gets) = (Rc::new(Cell::new(0)), Rc::new(Cell::new(0)));
    arena().mutate(|mc| {
        let table = Tables::new(mc).external(Listed { walks: walks.clone(), gets: gets.clone() }, 0).unwrap();
        let inner = table.get(mc, symbol(mc, "inner")).unwrap().unwrap();
        assert_eq!((walks.get(), gets.get()), (0, 1));
        let walked = entries(mc, table);
        assert_eq!((walks.get(), gets.get()), (1, 1));
        assert_eq!(walked, [(symbol(mc, "one"), fix(1)), (symbol(mc, "two"), fix(2)), (symbol(mc, "inner"), inner), (symbol(mc, "three"), fix(3))]);
        // The values that the iteration supplied are cached like values that were read one by one. No later read or iteration calls the host again.
        assert_eq!((table.get(mc, symbol(mc, "three")), table.get(mc, symbol(mc, "inner")), entries(mc, table) == walked), (Ok(Some(fix(3))), Ok(Some(inner)), true));
        assert_eq!((walks.get(), gets.get()), (1, 1));
    });
}

#[test]
fn a_table_whose_type_is_not_writable_refuses_every_change() {
    let (reads, dropped) = (Rc::new(Cell::new(0)), Rc::new(Cell::new(false)));
    arena().mutate(|mc| {
        let table = message(mc, None, &reads, &dropped);
        assert_eq!(table.set(mc, symbol(mc, "id"), fix(8)), Err(TableError::Immutable));
        assert_eq!(table.set(mc, symbol(mc, "new"), fix(8)), Err(TableError::Immutable));
        assert_eq!((table.delete(mc, symbol(mc, "id")), table.clear(mc)), (Err(TableError::Immutable), Err(TableError::Immutable)));
        assert_eq!((table.len(mc), table.get(mc, symbol(mc, "id")), table.has(mc, symbol(mc, "new"))), (2, Ok(Some(fix(7))), Ok(false)));
    });
}

/// A write to a writable external table changes the host's data. A later read returns the value that was written, as it does for a table in the arena.
#[test]
fn a_writable_external_table_changes_its_hosts_entries() {
    arena().mutate(|mc| {
        let table = Tables::new(mc).external(Counters::default(), 0).unwrap();
        assert!(table.is_writable(mc) && table.is_empty(mc));
        table.set(mc, text(mc, "hits"), fix(1)).unwrap();
        table.set(mc, fix(404), fix(2)).unwrap();
        table.set(mc, text(mc, "a longer name than a word holds"), fix(3)).unwrap();
        assert_eq!((table.len(mc), counts(mc, table), table.get(mc, text(mc, "hits")), table.get(mc, fix(404))), (3, vec![1, 2, 3], Ok(Some(fix(1))), Ok(Some(fix(2)))));
        // Setting a key again changes the host's entry, and the cached walk is rebuilt.
        assert_eq!(entries(mc, table).len(), 3);
        table.set(mc, text(mc, "hits"), fix(10)).unwrap();
        assert_eq!((counts(mc, table), table.get(mc, text(mc, "hits")), entries(mc, table)[0]), (vec![10, 2, 3], Ok(Some(fix(10))), (text(mc, "hits"), fix(10))));
        // The host rejects what it cannot hold. This host accepts only integer values under string or integer keys.
        assert_eq!(table.set(mc, text(mc, "hits"), text(mc, "many")), Err(TableError::Refused));
        assert_eq!(table.set(mc, symbol(mc, "hits"), fix(1)), Err(TableError::Refused));
        assert_eq!(table.set(mc, Pairs::new(mc).list(&[fix(1)]).unwrap(), fix(1)), Err(TableError::Refused));
        assert_eq!((counts(mc, table), table.get(mc, text(mc, "hits"))), (vec![10, 2, 3], Ok(Some(fix(10)))));
        // Removing an entry removes it from the host and from the cache.
        assert_eq!((table.delete(mc, fix(404)), table.delete(mc, fix(404)), table.delete(mc, symbol(mc, "hits"))), (Ok(true), Ok(false), Ok(false)));
        assert_eq!((table.len(mc), table.get(mc, fix(404)), table.has(mc, fix(404)), entries(mc, table).len()), (2, Ok(None), Ok(false), 2));
        table.clear(mc).unwrap();
        assert_eq!((table.len(mc), table.get(mc, text(mc, "hits")), entries(mc, table), counts(mc, table)), (0, Ok(None), vec![], vec![]));
        table.set(mc, text(mc, "hits"), fix(1)).unwrap();
        assert_eq!(entries(mc, table), [(text(mc, "hits"), fix(1))]);
    });
}

fn user<'gc>(mc: &Mutation<'gc>, kind: &'static ExternalKind<UserId>, id: u64) -> Value<'gc> {
    ExternalRefs::new(mc).make(kind, UserId(id), 0, Value::NULL).unwrap().value(mc)
}

static CHANNEL_ID: ExternalKind<UserId> = ExternalKind::by_value("channel-id", |first, second| first.0 == second.0, |id| id.0);

/// Two kinds can share a type. Their references are never equal, in either order, and are two keys.
#[test]
fn references_of_two_kinds_of_one_type_are_not_equal() {
    arena().mutate(|mc| {
        let (ann, channel) = (user(mc, &USER_ID, 7), user(mc, &CHANNEL_ID, 7));
        let (ann, channel) = (ExternalRef::of(ann).unwrap(), ExternalRef::of(channel).unwrap());
        assert_eq!((ann.same(mc, channel), channel.same(mc, ann), ann.hash(mc) == channel.hash(mc)), (false, false, true));
        assert!(ann.same(mc, ExternalRef::of(user(mc, &USER_ID, 7)).unwrap()));
        let table = Tables::new(mc).make().unwrap();
        table.set(mc, ann.value(mc), fix(1)).unwrap();
        table.set(mc, channel.value(mc), fix(2)).unwrap();
        assert_eq!((table.len(mc), table.get(mc, user(mc, &USER_ID, 7)), table.get(mc, user(mc, &CHANNEL_ID, 7))), (2, Ok(Some(fix(1))), Ok(Some(fix(2)))));
    });
}

const LONG: &str = "a key that is a good deal longer than the bytes a short key is copied into";
/// Forty-two bytes of two-byte characters. The copy of this text outgrows the 40-byte inline buffer partway through, and continues in a `String`.
const ACCENTED: &str = "ééééééééééééééééééééé";

/// A host whose keys are the largest and the smallest `i64`, text longer than the inline buffer of a copied key, and the empty string.
struct Wide;

impl Wide {
    fn number(key: Key<'_>) -> Option<i64> {
        match key {
            Key::Integer(i64::MAX) => Some(1),
            Key::Integer(i64::MIN) => Some(2),
            Key::String(LONG) => Some(3),
            Key::Symbol(ACCENTED) => Some(4),
            Key::String("") => Some(5),
            _ => None,
        }
    }
}

impl ExternalTable for Wide {
    fn len(&self) -> usize {
        5
    }

    fn has(&self, key: Key<'_>) -> bool {
        Self::number(key).is_some()
    }

    fn get<'gc>(&self, _: &Mutation<'gc>, key: Key<'_>) -> Result<Option<Value<'gc>>, Error> {
        Ok(Self::number(key).map(fix))
    }

    fn keys(&self) -> impl Iterator<Item = Key<'_>> {
        [Key::Integer(i64::MAX), Key::Integer(i64::MIN), Key::String(LONG), Key::Symbol(ACCENTED), Key::String("")].into_iter()
    }
}

fn wide<'gc>(mc: &Mutation<'gc>, number: i128) -> Value<'gc> {
    int::from_i128(&Nums::new(mc), number).unwrap().value()
}

/// An integer key is passed to the host whenever it fits in an `i64`, although the arena stores the largest ones as bignums. Text is passed to the host in full, whatever its length.
#[test]
fn a_host_is_given_wide_integers_and_long_text_as_keys() {
    arena().mutate(|mc| {
        let table = Tables::new(mc).external(Wide, 0).unwrap();
        let (most, least) = (wide(mc, i128::from(i64::MAX)), wide(mc, i128::from(i64::MIN)));
        assert_eq!((most.as_fixnum(), least.as_fixnum()), (None, None));
        assert_eq!((table.get(mc, most), table.get(mc, least), table.has(mc, most)), (Ok(Some(fix(1))), Ok(Some(fix(2))), Ok(true)));
        // `i64::MAX + 1` does not fit in an `i64`, so no host has it as a key.
        let past = wide(mc, i128::from(i64::MAX) + 1);
        assert_eq!((table.get(mc, past), table.has(mc, past)), (Ok(None), Ok(false)));
        assert_eq!((table.get(mc, text(mc, LONG)), table.get(mc, symbol(mc, ACCENTED)), table.get(mc, text(mc, ""))), (Ok(Some(fix(3))), Ok(Some(fix(4))), Ok(Some(fix(5)))));
        assert_eq!((table.get(mc, symbol(mc, LONG)), table.get(mc, text(mc, &LONG[..40])), table.get(mc, text(mc, &ACCENTED[..40]))), (Ok(None), Ok(None), Ok(None)));
    });
    // An iteration lists every key that the host has, including the extreme integers and the long text.
    arena().mutate(|mc| {
        let table = Tables::new(mc).external(Wide, 0).unwrap();
        let values: Vec<_> = entries(mc, table).into_iter().map(|(_, value)| value).collect();
        assert_eq!((values, table.len(mc)), (vec![fix(1), fix(2), fix(3), fix(4), fix(5)], 5));
    });
}

/// A position is the place where an entry was found. It finds that entry again without hashing, for as long as the entry stays at that position.
#[test]
fn an_entry_is_read_and_set_at_the_position_it_was_found() {
    arena().mutate(|mc| {
        let table = Tables::new(mc).make().unwrap();
        let (name, id, count) = (symbol(mc, "name"), symbol(mc, "id"), fix(3));
        assert_eq!((table.set_found(mc, name, fix(1)), table.set_found(mc, id, fix(2)), table.set_found(mc, count, fix(3))), (Ok(Some(0)), Ok(Some(1)), Ok(Some(2))));
        assert_eq!((table.found(mc, id), table.found(mc, symbol(mc, "other"))), (Ok(Some((1, fix(2)))), Ok(None)));
        assert_eq!((table.get_at(mc, id, 1), table.get_at(mc, count, 2)), (Some(fix(2)), Some(fix(3))));
        // The position of another key finds nothing, and neither does a position past the entries.
        assert_eq!((table.get_at(mc, id, 0), table.get_at(mc, id, 3), table.get_at(mc, id, usize::MAX / 4)), (None, None, None));
        assert_eq!((table.set_at(mc, id, 1, fix(20)), table.set_at(mc, id, 0, fix(30)), table.set_at(mc, id, 9, fix(40))), (true, false, false));
        assert_eq!((table.get(mc, id), table.get(mc, name)), (Ok(Some(fix(20))), Ok(Some(fix(1)))));
        // Setting an existing key keeps its position.
        assert_eq!(table.set_found(mc, id, fix(21)), Ok(Some(1)));
        // A removed entry is not found at its old position. The key gets a new position when it is set again.
        assert_eq!(table.delete(mc, id), Ok(true));
        assert_eq!((table.get_at(mc, id, 1), table.set_at(mc, id, 1, fix(5))), (None, false));
        assert_eq!((table.set_found(mc, id, fix(22)), table.get_at(mc, id, 3), table.get_at(mc, count, 2)), (Ok(Some(3)), Some(fix(22)), Some(fix(3))));
        // A rebuild compacts the entries. The old positions then find nothing, or hold another key.
        for extra in 100..200 {
            table.set(mc, fix(extra), Value::NULL).unwrap();
        }
        assert_eq!((table.found(mc, name), table.found(mc, count), table.found(mc, id)), (Ok(Some((0, fix(1)))), Ok(Some((1, fix(3)))), Ok(Some((2, fix(22))))));
        assert_eq!((table.get_at(mc, id, 3), table.get_at(mc, count, 2)), (None, None));
    });
    // In an external table, a position is a position in the table of cached values, and `set_at` sets nothing.
    arena().mutate(|mc| {
        let table = Tables::new(mc).external(Counters(vec![(CounterKey::Name("seen".to_owned()), 5)]), 0).unwrap();
        let seen = text(mc, "seen");
        assert_eq!(table.get_at(mc, seen, 0), None);
        assert_eq!((table.found(mc, seen), table.get_at(mc, seen, 0)), (Ok(Some((0, fix(5)))), Some(fix(5))));
        assert_eq!((table.set_at(mc, seen, 0, fix(6)), table.set_found(mc, seen, fix(7)), table.get(mc, seen)), (false, Ok(None), Ok(Some(fix(7)))));
    });
}

const LONG_KEY: &str = "a string key that is too long to fit in a word";

/// Returns one key of each kind that is compared by value.
fn value_keys<'gc>(mc: &Mutation<'gc>) -> Vec<Value<'gc>> {
    vec![symbol(mc, "id"), text(mc, LONG_KEY), fix(7), Value::char('x'), Value::TRUE, Value::flonum(mc, 1.5).unwrap()]
}

/// Returns a shape with the symbols `names` as its keys.
fn shape_of<'gc>(mc: &Mutation<'gc>, names: &[&str]) -> Shape<'gc> {
    let keys: Vec<Value<'gc>> = names.iter().map(|name| symbol(mc, name)).collect();
    Tables::new(mc).shape(&keys).unwrap()
}

/// Returns a table of `shape` whose values are the numbers `values`, with `None` for a key that is left out.
fn shaped<'gc>(mc: &Mutation<'gc>, shape: Shape<'gc>, values: &[Option<i64>]) -> Table<'gc> {
    Tables::new(mc).shaped(shape, values.iter().map(|value| value.map(fix))).unwrap()
}

/// Returns the entries of `table` as names and numbers. The keys are symbols and the values are fixnums.
fn named<'gc>(mc: &Mutation<'gc>, table: Table<'gc>) -> Vec<(String, i64)> {
    let strings = Strings::new(mc);
    entries(mc, table).into_iter().map(|(key, value)| (crate::string::display(&strings, Symbol::of(key).unwrap().name(mc)).to_string(), value.as_fixnum().unwrap())).collect()
}

fn pairs_of(entries: &[(&str, i64)]) -> Vec<(String, i64)> {
    entries.iter().map(|&(name, number)| (name.to_string(), number)).collect()
}

/// A table made from a shape has the entries that setting each key in order gives, and every key is at its position in the shape.
#[test]
fn a_table_made_from_a_shape_has_the_entries_its_keys_and_values_make() {
    arena().mutate(|mc| {
        let tables = Tables::new(mc);
        let keys = value_keys(mc);
        let shape = tables.shape(&keys).unwrap();
        assert_eq!((shape.len(mc), shape.is_empty(mc), shape.key(mc, 1), shape.key(mc, 6)), (6, false, Some(keys[1]), None));
        let values: Vec<Value> = (10..16).map(fix).collect();
        let made = tables.shaped(shape, values.iter().map(|&value| Some(value))).unwrap();
        let plain = tables.make().unwrap();
        for (&key, &value) in keys.iter().zip(&values) {
            plain.set(mc, key, value).unwrap();
        }
        assert_eq!((entries(mc, made), made.len(mc)), (entries(mc, plain), 6));
        // Keys are found by value: another string with the same characters, and another number with the same value.
        assert_eq!((made.get(mc, text(mc, LONG_KEY)), made.get(mc, Value::flonum(mc, 1.5).unwrap()), made.has(mc, Value::char('x'))), (Ok(Some(fix(11))), Ok(Some(fix(15))), Ok(true)));
        assert_eq!((made.get(mc, symbol(mc, "other")), made.get(mc, fix(8)), made.get(mc, Value::FALSE)), (Ok(None), Ok(None), Ok(None)));
        for (position, &key) in keys.iter().enumerate() {
            assert_eq!((shape.position(mc, key), made.found(mc, key)), (Ok(Some(position)), Ok(Some((position, values[position])))));
        }
        assert_eq!((shape.position(mc, symbol(mc, "other")), made.get_at(mc, keys[0], 0), made.get_at(mc, keys[2], 2), made.get_at(mc, keys[2], 0)), (Ok(None), Some(fix(10)), Some(fix(12)), None));
        // A shape is not a table, and a table is not a shape.
        assert!(Table::of(shape.value(mc)).is_none() && Shape::of(made.value(mc)).is_none() && Shape::of(shape.value(mc)) == Some(shape));
    });
}

/// The tables of a shape share its index and nothing else. Whatever a program does to one of them, the others and the shape stay as they were.
#[test]
fn changes_to_a_table_of_a_shape_do_not_reach_the_others() {
    arena().mutate(|mc| {
        let shape = shape_of(mc, &["x", "y", "z"]);
        let (first, second) = (shaped(mc, shape, &[Some(1), Some(2), Some(3)]), shaped(mc, shape, &[Some(4), Some(5), Some(6)]));
        let (x, y, w) = (symbol(mc, "x"), symbol(mc, "y"), symbol(mc, "w"));
        // A new value for a key stays in its table.
        first.set(mc, y, fix(20)).unwrap();
        assert_eq!((named(mc, first), named(mc, second)), (pairs_of(&[("x", 1), ("y", 20), ("z", 3)]), pairs_of(&[("x", 4), ("y", 5), ("z", 6)])));
        // A new key is added at the end, as in any table.
        first.set(mc, w, fix(4)).unwrap();
        assert_eq!((named(mc, first), second.get(mc, w), second.len(mc)), (pairs_of(&[("x", 1), ("y", 20), ("z", 3), ("w", 4)]), Ok(None), 3));
        // A removed key that is set again is a new entry at the end.
        assert_eq!((first.delete(mc, x), first.get(mc, x)), (Ok(true), Ok(None)));
        first.set(mc, x, fix(10)).unwrap();
        assert_eq!(named(mc, first), pairs_of(&[("y", 20), ("z", 3), ("w", 4), ("x", 10)]));
        assert_eq!((second.delete(mc, y), second.delete(mc, y)), (Ok(true), Ok(false)));
        assert_eq!(named(mc, second), pairs_of(&[("x", 4), ("z", 6)]));
        second.set(mc, y, fix(9)).unwrap();
        assert_eq!(named(mc, second), pairs_of(&[("x", 4), ("z", 6), ("y", 9)]));
        // Many more keys, and a table that is emptied, change nothing for the shape.
        for extra in 0..500 {
            first.set(mc, fix(extra), fix(extra)).unwrap();
        }
        second.clear(mc).unwrap();
        second.set(mc, w, fix(1)).unwrap();
        assert_eq!((first.len(mc), first.get(mc, fix(499)), first.get(mc, symbol(mc, "z")), named(mc, second)), (504, Ok(Some(fix(499))), Ok(Some(fix(3))), pairs_of(&[("w", 1)])));
        // A table made from the shape afterwards is as the first ones were.
        let third = shaped(mc, shape, &[Some(7), Some(8), Some(9)]);
        assert_eq!((named(mc, third), third.found(mc, symbol(mc, "z")), third.get(mc, w)), (pairs_of(&[("x", 7), ("y", 8), ("z", 9)]), Ok(Some((2, fix(9)))), Ok(None)));
    });
}

/// A key that is given no value is not in the table. Setting it later adds it at the end, as for any key that the table does not have.
#[test]
fn a_table_of_a_shape_leaves_out_the_keys_without_a_value() {
    arena().mutate(|mc| {
        let shape = shape_of(mc, &["x", "y", "z"]);
        let (y, z) = (symbol(mc, "y"), symbol(mc, "z"));
        let table = shaped(mc, shape, &[Some(1), None, Some(3)]);
        assert_eq!((named(mc, table), table.len(mc), table.get(mc, y), table.has(mc, y), table.found(mc, z)), (pairs_of(&[("x", 1), ("z", 3)]), 2, Ok(None), Ok(false), Ok(Some((2, fix(3))))));
        assert_eq!((table.get_at(mc, y, 1), table.delete(mc, y)), (None, Ok(false)));
        table.set(mc, y, fix(2)).unwrap();
        assert_eq!(named(mc, table), pairs_of(&[("x", 1), ("z", 3), ("y", 2)]));
        // Keys past the values given are left out, and values past the keys are ignored.
        assert_eq!(named(mc, shaped(mc, shape, &[Some(1)])), pairs_of(&[("x", 1)]));
        assert_eq!(named(mc, shaped(mc, shape, &[Some(1), Some(2), Some(3), Some(4)])), pairs_of(&[("x", 1), ("y", 2), ("z", 3)]));
        assert_eq!((shaped(mc, shape, &[]).len(mc), shaped(mc, shape, &[None, None, None]).len(mc)), (0, 0));
        // A shape with no keys makes empty tables that grow like any other.
        let empty = shape_of(mc, &[]);
        let grown = shaped(mc, empty, &[]);
        assert_eq!((empty.len(mc), empty.is_empty(mc), grown.len(mc), grown.get(mc, y)), (0, true, 0, Ok(None)));
        grown.set(mc, y, fix(5)).unwrap();
        assert_eq!(named(mc, grown), pairs_of(&[("y", 5)]));
    });
}

/// The keys of a shape are different keys, and none of them is compared by identity.
#[test]
fn a_shape_takes_keys_that_are_compared_by_value_once_each() {
    arena().mutate(|mc| {
        let tables = Tables::new(mc);
        let (x, y) = (symbol(mc, "x"), symbol(mc, "y"));
        assert_eq!(tables.shape(&[x, y, x]).err(), Some(ShapeError::Duplicate(2)));
        // Two strings with the same characters are one key, and so are two numbers with the same value.
        assert_eq!(tables.shape(&[text(mc, LONG_KEY), x, text(mc, LONG_KEY)]).err(), Some(ShapeError::Duplicate(2)));
        assert_eq!(tables.shape(&[Value::flonum(mc, 2.5).unwrap(), Value::flonum(mc, 2.5).unwrap()]).err(), Some(ShapeError::Duplicate(1)));
        // The number 1 and the number 1.0 are two keys, and a symbol is not the string of its name.
        assert!(tables.shape(&[fix(1), Value::flonum(mc, 1.0).unwrap(), x, text(mc, "x")]).is_ok());
        let pair = Pairs::new(mc).cons(fix(1), Value::NULL).unwrap().value(mc);
        assert_eq!(tables.shape(&[x, pair]).err(), Some(ShapeError::Identity(1)));
        assert_eq!(tables.shape(&[tables.make().unwrap().value(mc)]).err(), Some(ShapeError::Identity(0)));
        // An external reference is a key of a shape only if its kind compares by value.
        assert!(tables.shape(&[user(mc, &USER_ID, 7), user(mc, &USER_ID, 8)]).is_ok());
        assert_eq!(tables.shape(&[user(mc, &USER_ID, 7), user(mc, &USER_ID, 7)]).err(), Some(ShapeError::Duplicate(1)));
        let handle = ExternalRefs::new(mc).make(&HANDLE, 1, 0, Value::NULL).unwrap().value(mc);
        assert_eq!(tables.shape(&[handle]).err(), Some(ShapeError::Identity(0)));
    });
}

/// A table of a shape takes less than half the memory of a table that is filled key by key, and it still finds its keys after a collection has moved every object.
#[test]
fn tables_of_a_shape_are_small_and_survive_moving_collections() {
    const NAMES: [&str; 6] = ["id", "content", "author", "channel", "guild", "pinned"];
    const COUNT: usize = 4000;
    fn fill(arena: &mut Arena, with_shape: bool) -> usize {
        arena.collect();
        let before = arena.used();
        arena.mutate(|mc| {
            let tables = Tables::new(mc);
            let shape = shape_of(mc, &NAMES);
            let keep = crate::vector::Vectors::new(mc).make(COUNT + 1, Value::NULL).unwrap();
            keep.items(mc).set(mc, COUNT, shape.value(mc));
            for number in 0..COUNT {
                let table = if with_shape {
                    tables.shaped(shape, (0..NAMES.len()).map(|field| Some(fix((number * 10 + field) as i64)))).unwrap()
                } else {
                    let table = tables.make().unwrap();
                    for (field, name) in NAMES.iter().enumerate() {
                        table.set(mc, symbol(mc, name), fix((number * 10 + field) as i64)).unwrap();
                    }
                    table
                };
                keep.items(mc).set(mc, number, table.value(mc));
            }
            mc.set_root(1, keep.value(mc));
        });
        arena.collect();
        arena.used() - before
    }
    let plain = fill(&mut arena(), false);
    let mut arena = arena();
    let small = fill(&mut arena, true);
    assert!(small * 2 < plain, "{small} bytes with a shape, {plain} bytes without");
    for round in 0..2 {
        arena.set_evacuate_all(true);
        arena.collect();
        arena.mutate(|mc| {
            let keep = crate::vector::AnyVector::of(mc.root(1)).unwrap();
            let shape = Shape::of(keep.get(mc, COUNT).unwrap()).unwrap();
            for number in (0..COUNT).step_by(37) {
                let table = Table::of(keep.get(mc, number).unwrap()).unwrap();
                assert!(!table.is_stale(mc), "round {round}");
                for (field, name) in NAMES.iter().enumerate() {
                    assert_eq!(table.found(mc, symbol(mc, name)), Ok(Some((field, fix((number * 10 + field) as i64)))), "round {round}");
                }
            }
            assert_eq!(named(mc, shaped(mc, shape, &[Some(1), Some(2), Some(3), Some(4), Some(5), Some(6)])).len(), 6);
        });
    }
}

/// The arena has one shape for each sequence of keys. A shape is reached from the shape with no keys by adding its keys in order, whichever way it is asked for.
#[test]
fn a_sequence_of_keys_has_one_shape() {
    arena().mutate(|mc| {
        let tables = Tables::new(mc);
        let (x, y, z) = (symbol(mc, "x"), symbol(mc, "y"), symbol(mc, "z"));
        let root = tables.root().unwrap();
        assert_eq!((root.len(mc), root.is_empty(mc), root.parent(mc), tables.shape(&[]).ok(), root.key(mc, 0), root.position(mc, x)), (0, true, None, Some(root), None, Ok(None)));
        let first = tables.shape(&[x, y]).unwrap();
        assert_eq!((tables.shape(&[x, y]).ok(), root.child(mc, x).unwrap().child(mc, y).ok()), (Some(first), Some(first)));
        assert_eq!((first.parent(mc), first.parent(mc).unwrap().parent(mc)), (tables.shape(&[x]).ok(), Some(root)));
        // The order of the keys is part of the shape, and one shape can be extended by several keys.
        let (swapped, other, longer) = (tables.shape(&[y, x]).unwrap(), tables.shape(&[x, z]).unwrap(), tables.shape(&[x, y, z]).unwrap());
        assert!(swapped != first && other != first && longer != first && other.parent(mc) == first.parent(mc) && longer.parent(mc) == Some(first));
        // A shape has its own keys only, though a shape and the shapes made from it can share their arrays.
        assert_eq!((first.len(mc), first.position(mc, z), first.key(mc, 2), longer.position(mc, z), longer.key(mc, 2)), (2, Ok(None), None, Ok(Some(2)), Some(z)));
        assert_eq!((other.position(mc, y), other.position(mc, z), other.key(mc, 1), swapped.position(mc, x), swapped.key(mc, 0)), (Ok(None), Ok(Some(1)), Some(z), Ok(Some(1)), Some(y)));
        let single = tables.shape(&[x]).unwrap();
        assert_eq!((single.len(mc), single.position(mc, y), single.position(mc, z), single.key(mc, 1)), (1, Ok(None), Ok(None), None));
        // A shape keeps every shape that was made from it findable, however many there are.
        let made: Vec<Shape> = (0..50).map(|number| root.child(mc, fix(number)).unwrap()).collect();
        for (number, &shape) in made.iter().enumerate() {
            assert_eq!((root.child(mc, fix(number as i64)).ok(), shape.key(mc, 0), shape.len(mc)), (Some(shape), Some(fix(number as i64)), 1));
        }
        assert_eq!(tables.shape(&[x, y]).ok(), Some(first));
        // A key that a shape cannot take is reported with the position it would have had.
        let pair = Pairs::new(mc).cons(fix(1), Value::NULL).unwrap().value(mc);
        assert_eq!((first.child(mc, x).err(), first.child(mc, pair).err(), root.child(mc, Value::BROKEN).err()), (Some(ShapeError::Duplicate(2)), Some(ShapeError::Identity(2)), Some(ShapeError::Identity(0))));
        // A shape has at most `SHAPE_KEYS` keys.
        let keys: Vec<Value> = (100..100 + SHAPE_KEYS as i64 + 1).map(fix).collect();
        let full = tables.shape(&keys[..SHAPE_KEYS]).unwrap();
        assert_eq!((full.len(mc), full.position(mc, keys[SHAPE_KEYS - 1]), tables.shape(&keys).err(), full.child(mc, x).err()), (SHAPE_KEYS, Ok(Some(SHAPE_KEYS - 1)), Some(ShapeError::TooMany(SHAPE_KEYS)), Some(ShapeError::TooMany(SHAPE_KEYS))));
    });
}

/// A shape that nothing uses is collected, and is made again when it is asked for. A shape that is in use keeps the shapes it was reached through.
#[test]
fn unused_shapes_are_collected_and_used_ones_stay_reachable() {
    const NAMES: [&str; 5] = ["a", "b", "c", "d", "e"];
    let mut arena = arena();
    arena.mutate(|mc| {
        let kept = shape_of(mc, &NAMES);
        // Other shapes that branch off the kept chain at every length, and are then dropped.
        for length in 0..NAMES.len() {
            let mut names = NAMES[..length].to_vec();
            names.extend(["p", "q", "r"]);
            assert_eq!(shape_of(mc, &names).len(mc), length + 3);
        }
        mc.set_root(1, shaped(mc, kept, &[Some(1), Some(2), Some(3), Some(4), Some(5)]).value(mc));
    });
    for round in 0..3 {
        arena.set_evacuate_all(true);
        arena.collect();
        arena.mutate(|mc| {
            let table = Table::of(mc.root(1)).unwrap();
            let kept = table.shape(mc).unwrap();
            // The table's shape is still the one shape of its keys, and so is each shape on the way to it.
            assert_eq!((shape_of(mc, &NAMES), named(mc, table)), (kept, pairs_of(&[("a", 1), ("b", 2), ("c", 3), ("d", 4), ("e", 5)])), "round {round}");
            let mut shape = kept;
            for length in (0..NAMES.len()).rev() {
                shape = shape.parent(mc).unwrap();
                assert_eq!((shape_of(mc, &NAMES[..length]), shape.len(mc)), (shape, length), "round {round}");
            }
            // The dropped branches are made again, and work.
            let again = shape_of(mc, &["a", "b", "p", "q", "r"]);
            assert_eq!((again.len(mc), again.position(mc, symbol(mc, "q")), again.position(mc, symbol(mc, "c")), named(mc, shaped(mc, again, &[Some(1), None, Some(3), Some(4), Some(5)]))), (5, Ok(Some(3)), Ok(None), pairs_of(&[("a", 1), ("p", 3), ("q", 4), ("r", 5)])), "round {round}");
        });
    }
}

/// A table that gets its keys as fields keeps a shape, and has the shape of every other table that got the same keys in the same order, however that table was made.
#[test]
fn a_table_filled_field_by_field_shares_its_shape() {
    arena().mutate(|mc| {
        let tables = Tables::new(mc);
        let (x, y, z) = (symbol(mc, "x"), symbol(mc, "y"), symbol(mc, "z"));
        let table = tables.make().unwrap();
        assert_eq!((table.shape(mc), table.len(mc), table.get(mc, x), table.held(mc, 0)), (tables.root().ok(), 0, Ok(None), None));
        assert_eq!((table.field_set(mc, x, fix(1)), table.field_set(mc, y, fix(2)), table.field_set(mc, x, fix(10))), (Ok(Some(0)), Ok(Some(1)), Ok(Some(0))));
        let second = tables.make().unwrap();
        second.set_field(mc, x, fix(3)).unwrap();
        second.set_field(mc, y, fix(4)).unwrap();
        let both = tables.shape(&[x, y]).unwrap();
        assert_eq!((table.shape(mc), second.shape(mc), shaped(mc, both, &[Some(5), Some(6)]).shape(mc)), (Some(both), Some(both), Some(both)));
        assert_eq!((named(mc, table), named(mc, second), table.len(mc)), (pairs_of(&[("x", 10), ("y", 2)]), pairs_of(&[("x", 3), ("y", 4)]), 2));
        assert_eq!((table.get(mc, y), table.has(mc, z), table.found(mc, y), table.get_at(mc, y, 1), table.get_at(mc, y, 0), table.is_stale(mc)), (Ok(Some(fix(2))), Ok(false), Ok(Some((1, fix(2)))), Some(fix(2)), None, false));
        assert_eq!((table.get_hinted(mc, y, 1, both.value(mc)), second.get_hinted(mc, y, 1, both.value(mc)), table.set_hinted(mc, y, 1, both.value(mc), fix(20)), table.get(mc, y), second.get(mc, y)), (Some(fix(2)), Some(fix(4)), true, Ok(Some(fix(20))), Ok(Some(fix(4)))));
        let held: Vec<_> = (0..5).map(|index| table.held(mc, index)).collect();
        assert_eq!(held, [Some(x), Some(fix(10)), Some(y), Some(fix(20)), None]);
        // A write that remembers the shape with one key more adds that key, while the table has a slot for it.
        let three = tables.shape(&[x, y, z]).unwrap();
        assert_eq!((second.set_hinted(mc, z, 2, three.value(mc), fix(7)), second.shape(mc), named(mc, second), second.len(mc)), (true, Some(three), pairs_of(&[("x", 3), ("y", 4), ("z", 7)]), 3));
        // It does not add a key at another position, or to a table of another shape.
        assert_eq!((table.set_hinted(mc, z, 1, three.value(mc), fix(7)), second.set_hinted(mc, z, 2, three.value(mc), fix(8)), tables.make().unwrap().set_hinted(mc, z, 2, three.value(mc), fix(9)), table.shape(mc), second.get(mc, z)), (false, true, false, Some(both), Ok(Some(fix(8)))));
        // The values array grows as fields are added.
        let wide = tables.make().unwrap();
        let names: Vec<String> = (0..20).map(|number| format!("field{number}")).collect();
        for (number, name) in names.iter().enumerate() {
            assert_eq!(wide.field_set(mc, symbol(mc, name), fix(number as i64)), Ok(Some(number)));
        }
        let expected: Vec<(String, i64)> = names.iter().cloned().zip(0..).collect();
        assert_eq!((named(mc, wide), wide.shape(mc).map(|shape| shape.len(mc)), wide.len(mc)), (expected, Some(20), 20));
    });
}

/// A table leaves its shape when a key is added in a way that the shape cannot express. It keeps its entries and their order.
#[test]
fn a_table_leaves_its_shape_for_keys_that_a_shape_cannot_hold() {
    arena().mutate(|mc| {
        let tables = Tables::new(mc);
        let (x, y, z) = (symbol(mc, "x"), symbol(mc, "y"), symbol(mc, "z"));
        fn fielded<'gc>(mc: &Mutation<'gc>, names: &[&str]) -> Table<'gc> {
            let table = Tables::new(mc).make().unwrap();
            for (number, name) in names.iter().enumerate() {
                table.set_field(mc, symbol(mc, name), fix(number as i64 + 1)).unwrap();
            }
            table
        }
        // A symbol is a field name in a plain write as well. A key of another kind is the key of a map, unless it is set as a field.
        let mapped = fielded(mc, &["x", "y"]);
        mapped.set(mc, y, fix(20)).unwrap();
        mapped.set(mc, z, fix(3)).unwrap();
        assert_eq!((mapped.shape(mc), named(mc, mapped)), (tables.shape(&[x, y, z]).ok(), pairs_of(&[("x", 1), ("y", 20), ("z", 3)])));
        mapped.set_field(mc, fix(7), fix(70)).unwrap();
        assert_eq!(mapped.shape(mc), tables.shape(&[x, y, z, fix(7)]).ok());
        mapped.set(mc, fix(7), fix(71)).unwrap();
        assert_eq!((mapped.shape(mc).map(|shape| shape.len(mc)), mapped.get(mc, fix(7))), (Some(4), Ok(Some(fix(71)))));
        mapped.set(mc, fix(8), fix(80)).unwrap();
        let listed: Vec<_> = mapped.entries(mc).unwrap().collect();
        assert_eq!((mapped.shape(mc), listed, mapped.found(mc, fix(8)), mapped.get_at(mc, x, 0), mapped.len(mc)), (None, vec![(x, fix(1)), (y, fix(20)), (z, fix(3)), (fix(7), fix(71)), (fix(8), fix(80))], Ok(Some((4, fix(80)))), Some(fix(1)), 5));
        mapped.set(mc, symbol(mc, "w"), fix(4)).unwrap();
        assert_eq!((mapped.shape(mc), mapped.len(mc)), (None, 6));
        // A table that a host fills with symbol keys has the shape of every table filled the same way.
        let plain = tables.make().unwrap();
        plain.set(mc, x, fix(1)).unwrap();
        plain.set(mc, y, fix(2)).unwrap();
        assert_eq!((plain.shape(mc), tables.make().unwrap().set_found(mc, x, fix(1)), named(mc, plain)), (tables.shape(&[x, y]).ok(), Ok(Some(0)), pairs_of(&[("x", 1), ("y", 2)])));
        // A table made with all its values takes a new key the same two ways.
        let grown = shaped(mc, tables.shape(&[x]).unwrap(), &[Some(1)]);
        grown.set(mc, y, fix(2)).unwrap();
        assert_eq!((grown.shape(mc), named(mc, grown)), (tables.shape(&[x, y]).ok(), pairs_of(&[("x", 1), ("y", 2)])));
        let keyed = shaped(mc, tables.shape(&[x]).unwrap(), &[Some(1)]);
        keyed.set(mc, fix(2), fix(20)).unwrap();
        assert_eq!((keyed.shape(mc), keyed.get(mc, x), keyed.get(mc, fix(2)), keyed.len(mc)), (None, Ok(Some(fix(1))), Ok(Some(fix(20))), 2));
        // A removed key keeps the shape. Setting it again makes it the last entry, which leaves the shape.
        let removed = fielded(mc, &["x", "y", "z"]);
        assert_eq!((removed.delete(mc, x), removed.delete(mc, x), removed.shape(mc).map(|shape| shape.len(mc)), named(mc, removed), removed.len(mc), removed.get(mc, x)), (Ok(true), Ok(false), Some(3), pairs_of(&[("y", 2), ("z", 3)]), 2, Ok(None)));
        removed.set_field(mc, x, fix(9)).unwrap();
        assert_eq!((removed.shape(mc), named(mc, removed)), (None, pairs_of(&[("y", 2), ("z", 3), ("x", 9)])));
        // A key that is compared by identity.
        let pair = Pairs::new(mc).cons(fix(1), Value::NULL).unwrap().value(mc);
        let keyed = fielded(mc, &["x"]);
        keyed.set_field(mc, pair, fix(2)).unwrap();
        assert_eq!((keyed.shape(mc), keyed.get(mc, pair), keyed.get(mc, x), keyed.len(mc)), (None, Ok(Some(fix(2))), Ok(Some(fix(1))), 2));
        // More keys than a shape has room for.
        let wide = tables.make().unwrap();
        for number in 0..SHAPE_KEYS as i64 {
            wide.set_field(mc, fix(number), fix(number)).unwrap();
        }
        assert_eq!(wide.shape(mc).map(|shape| shape.len(mc)), Some(SHAPE_KEYS));
        wide.set_field(mc, fix(1000), fix(1000)).unwrap();
        assert_eq!((wide.shape(mc), wide.len(mc), wide.get(mc, fix(0)), wide.get(mc, fix(SHAPE_KEYS as i64 - 1)), wide.found(mc, fix(1000))), (None, SHAPE_KEYS + 1, Ok(Some(fix(0))), Ok(Some(fix(SHAPE_KEYS as i64 - 1))), Ok(Some((SHAPE_KEYS, fix(1000))))));
        // An emptied table has no shape, and a table made with room never had one.
        let emptied = fielded(mc, &["x", "y"]);
        emptied.clear(mc).unwrap();
        assert_eq!((emptied.shape(mc), emptied.len(mc), tables.with_room(8).unwrap().shape(mc), tables.with_room(0).unwrap().shape(mc)), (None, 0, None, tables.root().ok()));
        emptied.set_field(mc, z, fix(5)).unwrap();
        assert_eq!(named(mc, emptied), pairs_of(&[("z", 5)]));
        // A table that was made with all its values gains a field and keeps a shape: the shape with that key added.
        let record = shaped(mc, tables.shape(&[x, y]).unwrap(), &[Some(1), Some(2)]);
        let value = record.value(mc);
        assert_eq!((record.field_set(mc, z, fix(3)), record.shape(mc), named(mc, record), record.value(mc) == value), (Ok(Some(2)), tables.shape(&[x, y, z]).ok(), pairs_of(&[("x", 1), ("y", 2), ("z", 3)]), true));
        let longer = tables.shape(&[x, y, z]).unwrap();
        assert_eq!((record.get_hinted(mc, z, 2, longer.value(mc)), record.set_hinted(mc, x, 0, longer.value(mc), fix(11)), record.get(mc, x), record.len(mc)), (Some(fix(3)), true, Ok(Some(fix(11))), 3));
    });
}

/// A copy has the entries of its source in the same order, and is a separate table. It has the shape of its source, if the source has one.
#[test]
fn a_copy_keeps_the_entries_and_the_shape() {
    arena().mutate(|mc| {
        let tables = Tables::new(mc);
        let (x, y, z) = (symbol(mc, "x"), symbol(mc, "y"), symbol(mc, "z"));
        let shape = tables.shape(&[x, y, z]).unwrap();
        // A table made with all its values, and one with a key left out.
        let record = shaped(mc, shape, &[Some(1), None, Some(3)]);
        let copy = record.copy(mc).unwrap();
        assert_eq!((copy.shape(mc), named(mc, copy), copy.len(mc), copy.value(mc) == record.value(mc)), (Some(shape), pairs_of(&[("x", 1), ("z", 3)]), 2, false));
        copy.set(mc, x, fix(10)).unwrap();
        copy.set_field(mc, symbol(mc, "w"), fix(4)).unwrap();
        assert_eq!((named(mc, record), named(mc, copy), copy.shape(mc), record.shape(mc)), (pairs_of(&[("x", 1), ("z", 3)]), pairs_of(&[("x", 10), ("z", 3), ("w", 4)]), tables.shape(&[x, y, z, symbol(mc, "w")]).ok(), Some(shape)));
        // A table filled field by field, and a copy of the copy that grew.
        let fielded = tables.make().unwrap();
        fielded.set_field(mc, x, fix(1)).unwrap();
        fielded.set_field(mc, y, fix(2)).unwrap();
        let (first, second) = (fielded.copy(mc).unwrap(), copy.copy(mc).unwrap());
        assert_eq!((first.shape(mc), named(mc, first), second.shape(mc), named(mc, second)), (tables.shape(&[x, y]).ok(), pairs_of(&[("x", 1), ("y", 2)]), copy.shape(mc), pairs_of(&[("x", 10), ("z", 3), ("w", 4)])));
        // A table with keys of its own, with a removed entry and a key compared by identity.
        let pair = Pairs::new(mc).cons(fix(1), Value::NULL).unwrap().value(mc);
        let mapped = tables.with_room(4).unwrap();
        for (key, value) in [(fix(5), fix(50)), (x, fix(1)), (pair, fix(7)), (fix(6), fix(60))] {
            mapped.set(mc, key, value).unwrap();
        }
        mapped.delete(mc, x).unwrap();
        let copy = mapped.copy(mc).unwrap();
        let listed: Vec<_> = copy.entries(mc).unwrap().collect();
        assert_eq!((copy.shape(mc), listed, copy.get(mc, pair), copy.len(mc)), (None, vec![(fix(5), fix(50)), (pair, fix(7)), (fix(6), fix(60))], Ok(Some(fix(7))), 3));
        // An empty table.
        let empty = tables.make().unwrap().copy(mc).unwrap();
        assert_eq!((empty.len(mc), empty.field_set(mc, x, fix(1)), named(mc, empty)), (0, Ok(Some(0)), pairs_of(&[("x", 1)])));
    });
}

/// Equal strings are one string, so tables that are given the same text as a field name share a shape. A rope is stored as its interned string. External references are shared as keys only if they are the same object.
#[test]
fn equal_strings_are_one_key_of_a_shape() {
    arena().mutate(|mc| {
        let tables = Tables::new(mc);
        let strings = Strings::new(mc);
        let (first_key, second_key) = (text(mc, LONG_KEY), text(mc, LONG_KEY));
        assert!(first_key == second_key);
        let (first, second) = (tables.make().unwrap(), tables.make().unwrap());
        first.set_field(mc, first_key, fix(1)).unwrap();
        second.set_field(mc, second_key, fix(2)).unwrap();
        assert!(first.shape(mc).is_some() && first.shape(mc) == second.shape(mc));
        assert_eq!((tables.shape(&[text(mc, LONG_KEY)]).ok(), first.get(mc, second_key), entries(mc, second)), (first.shape(mc), Ok(Some(fix(1))), vec![(first_key, fix(2))]));
        // A key that is a rope is stored as its interned string, in a table with a shape and in a table with keys of its own. The rope and every string with its characters find the entry.
        let (head, tail) = ("a long key ".repeat(60), "that is a rope".to_string());
        let rope = concat(&strings, strings.string(text(mc, &head)).unwrap(), strings.string(text(mc, &tail)).unwrap()).unwrap();
        assert!(!string::is_flat(&strings, rope));
        let (fielded, mapped) = (tables.make().unwrap(), tables.with_room(4).unwrap());
        fielded.set_field(mc, rope.value(), fix(1)).unwrap();
        mapped.set(mc, rope.value(), fix(2)).unwrap();
        // The rope is the interned string of its characters, so it is the key that the tables hold. A flat string that is made with them is another object, and finds the entries.
        let flat = text(mc, &format!("{head}{tail}"));
        assert!(flat != rope.value() && strings.is_interned(rope));
        assert_eq!((entries(mc, fielded), entries(mc, mapped), tables.shape(&[rope.value()]).ok()), (vec![(rope.value(), fix(1))], vec![(rope.value(), fix(2))], fielded.shape(mc)));
        let again = concat(&strings, strings.string(text(mc, &head[..330])).unwrap(), strings.string(text(mc, &format!("{}{tail}", &head[330..]))).unwrap()).unwrap();
        assert!(!string::is_flat(&strings, again));
        assert_eq!((fielded.get(mc, rope.value()), mapped.get(mc, again.value()), mapped.get(mc, flat), mapped.has(mc, text(mc, &head))), (Ok(Some(fix(1))), Ok(Some(fix(2))), Ok(Some(fix(2))), Ok(false)));
        // Numbers that are objects are shared by value as well.
        let (third, fourth) = (tables.make().unwrap(), tables.make().unwrap());
        third.set_field(mc, Value::flonum(mc, 2.5).unwrap(), fix(3)).unwrap();
        fourth.set_field(mc, Value::flonum(mc, 2.5).unwrap(), fix(4)).unwrap();
        assert!(third.shape(mc).is_some() && third.shape(mc) == fourth.shape(mc));
        // Two equal external references are one key of a table. As field names they are shared only if they are the same object, so each table lists the reference it was given.
        let (ann, same_ann) = (user(mc, &USER_ID, 7), user(mc, &USER_ID, 7));
        let (fifth, sixth, seventh) = (tables.make().unwrap(), tables.make().unwrap(), tables.make().unwrap());
        fifth.set_field(mc, ann, fix(5)).unwrap();
        sixth.set_field(mc, same_ann, fix(6)).unwrap();
        seventh.set_field(mc, ann, fix(7)).unwrap();
        assert!(fifth.shape(mc).is_some() && sixth.shape(mc).is_some() && fifth.shape(mc) != sixth.shape(mc) && fifth.shape(mc) == seventh.shape(mc));
        assert_eq!((entries(mc, fifth), entries(mc, sixth), sixth.get(mc, ann), fifth.field_set(mc, same_ann, fix(50)), entries(mc, fifth)), (vec![(ann, fix(5))], vec![(same_ann, fix(6))], Ok(Some(fix(6))), Ok(Some(0)), vec![(ann, fix(50))]));
    });
}

/// A shape can have thousands of shapes made from it. Each of them is found again, also after a collection has removed most of them.
#[test]
fn a_shape_with_many_children_finds_each_of_them() {
    const MANY: i64 = 3000;
    let mut arena = arena();
    arena.mutate(|mc| {
        let tables = Tables::new(mc);
        let root = tables.root().unwrap();
        let made: Vec<Shape> = (0..MANY).map(|number| root.child(mc, fix(number)).unwrap()).collect();
        for (number, &shape) in made.iter().enumerate() {
            assert_eq!((root.child(mc, fix(number as i64)).ok(), shape.key(mc, 0), shape.child(mc, fix(-1)).unwrap().parent(mc)), (Some(shape), Some(fix(number as i64)), Some(shape)));
        }
        // One shape in ten stays in use, by a table that the arena keeps.
        let mut kept = Value::NULL;
        for number in (0..MANY).step_by(10) {
            let table = tables.make().unwrap();
            table.set_field(mc, fix(number), fix(number)).unwrap();
            kept = Pairs::new(mc).cons(table.value(mc), kept).unwrap().value(mc);
        }
        mc.set_root(1, kept);
    });
    for round in 0..3 {
        arena.set_evacuate_all(true);
        arena.collect();
        arena.mutate(|mc| {
            let root = Tables::new(mc).root().unwrap();
            let mut tables = 0;
            for value in Pairs::new(mc).elements(mc.root(1)) {
                let table = Table::of(value).unwrap();
                let key = table.held(mc, 0).unwrap();
                assert_eq!((root.child(mc, key).ok(), table.get(mc, key)), (table.shape(mc), Ok(Some(key))), "round {round}");
                tables += 1;
            }
            assert_eq!(tables, MANY / 10);
            // The shapes that were collected are made again, and each is found again.
            for number in (0..MANY).rev() {
                let shape = root.child(mc, fix(number)).unwrap();
                assert_eq!((root.child(mc, fix(number)).ok(), shape.key(mc, 0), shape.len(mc)), (Some(shape), Some(fix(number)), 1), "round {round}");
            }
        });
    }
}

/// A lookup returns the place of its key: the shape that the position belongs to, or no shape for a position whose key has to be compared. A write returns the place of the entry it set.
#[test]
fn a_lookup_returns_the_shape_with_the_position() {
    arena().mutate(|mc| {
        let tables = Tables::new(mc);
        let (x, y, z) = (symbol(mc, "x"), symbol(mc, "y"), symbol(mc, "z"));
        let (one, two, three) = (tables.shape(&[x]).unwrap(), tables.shape(&[x, y]).unwrap(), tables.shape(&[x, y, z]).unwrap());
        fn place<'gc>(shape: Option<Shape<'gc>>, position: usize) -> Place<'gc> {
            Place { shape, position }
        }
        // A table made with all its values. A key that it gains as a field moves it to the next shape, which the write returns.
        let record = shaped(mc, two, &[Some(1), Some(2)]);
        assert_eq!((record.find(mc, y), record.set_finding(mc, x, fix(10)), record.find(mc, z)), (Ok(Some((place(Some(two), 1), fix(2)))), Ok(Some(place(Some(two), 0))), Ok(None)));
        assert_eq!((record.set_field(mc, z, fix(3)), record.find(mc, x), record.find_from(mc, z, 0)), (Ok(Some(place(Some(three), 2))), Ok(Some((place(Some(three), 0), fix(10)))), Ok(Some((place(Some(three), 2), fix(3))))));
        // A table that is filled field by field.
        let fielded = tables.make().unwrap();
        assert_eq!((fielded.set_finding(mc, x, fix(1)), fielded.set_field(mc, y, fix(2)), fielded.set_finding(mc, x, fix(11)), fielded.find(mc, y)), (Ok(Some(place(Some(one), 0))), Ok(Some(place(Some(two), 1))), Ok(Some(place(Some(two), 0))), Ok(Some((place(Some(two), 1), fix(2))))));
        // A key that is not a field name gives the table keys of its own. Its places have no shape from then on.
        assert_eq!((fielded.set_finding(mc, fix(7), fix(70)), fielded.find(mc, y), fielded.set_field(mc, z, fix(3)), fielded.shape(mc)), (Ok(Some(place(None, 2))), Ok(Some((place(None, 1), fix(2)))), Ok(Some(place(None, 3))), None));
        // A place is enough to read the key again, in the same table and in another table of the shape.
        let other = shaped(mc, three, &[Some(4), Some(5), Some(6)]);
        let (found, _) = record.find(mc, z).unwrap().unwrap();
        let remembered = found.shape.map_or(Value::FALSE, |shape| shape.value(mc));
        assert_eq!((record.get_hinted(mc, z, found.position, remembered), other.get_hinted(mc, z, found.position, remembered), fielded.get_hinted(mc, z, found.position, remembered)), (Some(fix(3)), Some(fix(6)), None));
    });
}

/// A program can give a writable external table a key outside the table's shape. The cached values then have positions of their own. A lookup returns those positions without the shape, so a read that remembers the place does not use them in another table of the shape.
#[test]
fn an_external_table_with_a_key_outside_its_shape_gives_places_without_the_shape() {
    arena().mutate(|mc| {
        let tables = Tables::new(mc);
        let shape = tables.shape(&[fix(1)]).unwrap();
        let record = tables.shaped(shape, [Some(fix(10))].into_iter()).unwrap();
        // A table that is only read caches by the positions of its shape.
        let read = tables.external_shaped(shape, Counters(vec![(CounterKey::Number(1), 10)]), 0).unwrap();
        assert_eq!((read.find(mc, fix(1)), read.find_from(mc, fix(1), 0), read.shape(mc)), (Ok(Some((Place { shape: Some(shape), position: 0 }, fix(10)))), Ok(Some((Place { shape: Some(shape), position: 0 }, fix(10)))), Some(shape)));
        // The key 2 is cached first, at position 0. That is the position of the key 1 in the shape.
        let table = tables.external_shaped(shape, Counters(vec![(CounterKey::Number(1), 10)]), 0).unwrap();
        assert_eq!((table.shape(mc), table.set_finding(mc, fix(2), fix(20))), (Some(shape), Ok(None)));
        let (found, value) = table.find(mc, fix(2)).unwrap().unwrap();
        assert_eq!((found, value, table.find_from(mc, fix(2), 0), table.shape(mc)), (Place { shape: None, position: 0 }, fix(20), Ok(Some((found, fix(20)))), None));
        // A read remembers the place, as the VM does. It must not find the key 2 in a table that has only the key 1.
        let remembered = found.shape.map_or(Value::FALSE, |shape| shape.value(mc));
        assert_eq!((record.get_hinted(mc, fix(2), found.position, remembered), record.get(mc, fix(2)), table.get_hinted(mc, fix(2), found.position, remembered)), (None, Ok(None), Some(fix(20))));
        assert_eq!((table.get(mc, fix(1)), table.get(mc, fix(2)), table.len(mc), counts(mc, table)), (Ok(Some(fix(10))), Ok(Some(fix(20))), 2, vec![10, 20]));
        // An emptied table caches by the positions of its shape again.
        table.clear(mc).unwrap();
        table.set(mc, fix(1), fix(11)).unwrap();
        assert_eq!((table.find(mc, fix(1)), table.shape(mc)), (Ok(Some((Place { shape: Some(shape), position: 0 }, fix(11)))), Some(shape)));
    });
}

/// A read that remembers the shape of the table in which it found its key reads the next table of that shape by position alone. For any other table it compares the key at the position.
#[test]
fn a_read_that_remembers_a_shape_finds_its_key_by_position() {
    arena().mutate(|mc| {
        let (first, second) = (shape_of(mc, &["x", "y", "z"]), shape_of(mc, &["y", "x"]));
        let (x, y, w) = (symbol(mc, "x"), symbol(mc, "y"), symbol(mc, "w"));
        let table = shaped(mc, first, &[Some(1), Some(2), None]);
        assert_eq!((table.shape(mc), table.len(mc)), (Some(first), 2));
        assert_eq!((table.get_hinted(mc, y, 1, first.value(mc)), table.get_hinted(mc, x, 0, first.value(mc))), (Some(fix(2)), Some(fix(1))));
        // With the remembered shape the key is not looked at: the caller only ever passes the position it found that key at.
        assert_eq!(table.get_hinted(mc, w, 1, first.value(mc)), Some(fix(2)));
        // A key that the table does not have, and a position past the keys of the shape, have no value.
        assert_eq!((table.get_hinted(mc, symbol(mc, "z"), 2, first.value(mc)), table.get_hinted(mc, y, 3, first.value(mc))), (None, None));
        // A table of another shape is read at the position only if its key there is the key.
        let other = shaped(mc, second, &[Some(10), Some(20)]);
        assert_eq!((other.get_hinted(mc, y, 1, first.value(mc)), other.get_hinted(mc, y, 0, first.value(mc)), other.get_hinted(mc, x, 1, Value::FALSE)), (None, Some(fix(10)), Some(fix(20))));
        // A write through a remembered shape replaces the value, and does not add a key that the table lacks.
        assert_eq!((table.set_hinted(mc, y, 1, first.value(mc), fix(22)), table.set_hinted(mc, symbol(mc, "z"), 2, first.value(mc), fix(3)), other.set_hinted(mc, y, 1, first.value(mc), fix(5))), (true, false, false));
        assert_eq!((named(mc, table), named(mc, other)), (pairs_of(&[("x", 1), ("y", 22)]), pairs_of(&[("y", 10), ("x", 20)])));
        // A table with keys of its own has no shape. Its keys are compared whatever shape is passed.
        let plain = Tables::new(mc).with_room(4).unwrap();
        plain.set(mc, x, fix(7)).unwrap();
        assert_eq!((plain.shape(mc), plain.get_hinted(mc, x, 0, first.value(mc)), plain.get_hinted(mc, y, 0, first.value(mc)), plain.set_hinted(mc, x, 0, first.value(mc), fix(8))), (None, Some(fix(7)), None, true));
    });
}

/// A table of a shape keeps its shape while its keys are changed or removed. A removed key that is set again moves its entries to an ordinary table, and the table works on as before.
#[test]
fn a_table_of_a_shape_gives_up_its_shape_when_a_removed_key_is_set_again() {
    arena().mutate(|mc| {
        let shape = shape_of(mc, &["x", "y", "z"]);
        let (x, y, z, w) = (symbol(mc, "x"), symbol(mc, "y"), symbol(mc, "z"), symbol(mc, "w"));
        let table = shaped(mc, shape, &[Some(1), Some(2), Some(3)]);
        let value = table.value(mc);
        table.set(mc, y, fix(20)).unwrap();
        assert_eq!((table.delete(mc, x), table.shape(mc), table.len(mc)), (Ok(true), Some(shape), 2));
        // Slots are read as keys and values in turn. Both slots of the removed key read as unused.
        let held: Vec<_> = (0..7).map(|index| table.held(mc, index)).collect();
        assert_eq!(held, [Some(Value::BROKEN), Some(Value::BROKEN), Some(y), Some(fix(20)), Some(z), Some(fix(3)), None]);
        // The removed key comes back as a new last entry, which the shape cannot express.
        table.set(mc, x, fix(10)).unwrap();
        assert_eq!((table.shape(mc), named(mc, table), table.value(mc) == value, Table::of(value) == Some(table)), (None, pairs_of(&[("y", 20), ("z", 3), ("x", 10)]), true, true));
        // Reads and writes that remember the old shape and positions still give right answers.
        assert_eq!((table.get_hinted(mc, y, 1, shape.value(mc)), table.get_hinted(mc, y, 0, shape.value(mc)), table.get_at(mc, x, 2), table.found(mc, z)), (None, Some(fix(20)), Some(fix(10)), Ok(Some((1, fix(3))))));
        assert_eq!((table.set_hinted(mc, z, 1, shape.value(mc), fix(30)), table.set_hinted(mc, z, 2, shape.value(mc), fix(31)), table.get(mc, z)), (true, false, Ok(Some(fix(30)))));
        table.set(mc, w, fix(4)).unwrap();
        assert_eq!((table.delete(mc, y), named(mc, table), table.len(mc), table.is_stale(mc)), (Ok(true), pairs_of(&[("z", 30), ("x", 10), ("w", 4)]), 3, false));
        // An emptied table of a shape has no shape either, and takes new entries.
        let emptied = shaped(mc, shape, &[Some(1), Some(2), Some(3)]);
        emptied.clear(mc).unwrap();
        assert_eq!((emptied.shape(mc), emptied.len(mc), emptied.get(mc, x), emptied.get_hinted(mc, x, 0, shape.value(mc)), emptied.held(mc, 0)), (None, 0, Ok(None), None, None));
        emptied.set(mc, z, fix(9)).unwrap();
        assert_eq!(named(mc, emptied), pairs_of(&[("z", 9)]));
    });
}

/// An event with the fields `x`, `y` and `z`, whose values are 1, 2 and 3. It counts the reads by key and the reads by position. If `partial`, it has no `z`.
struct Event {
    by_key: Rc<Cell<usize>>,
    by_position: Rc<Cell<usize>>,
    positional: bool,
    partial: bool,
}

impl Event {
    const FIELDS: [&str; 3] = ["x", "y", "z"];

    fn field<'gc>(&self, position: usize) -> Option<Value<'gc>> {
        if position < if self.partial {
            2
        } else {
            3
        } {
            Some(fix(position as i64 + 1))
        } else {
            None
        }
    }
}

impl ExternalTable for Event {
    fn len(&self) -> usize {
        if self.partial {
            2
        } else {
            3
        }
    }

    fn has(&self, key: Key<'_>) -> bool {
        matches!(key, Key::Symbol(name) if Self::FIELDS.iter().position(|&field| field == name).is_some_and(|position| self.field(position).is_some()))
    }

    fn get<'gc>(&self, _: &Mutation<'gc>, key: Key<'_>) -> Result<Option<Value<'gc>>, Error> {
        self.by_key.set(self.by_key.get() + 1);
        let Key::Symbol(name) = key else { return Ok(None) };
        Ok(Self::FIELDS.iter().position(|&field| field == name).and_then(|position| self.field(position)))
    }

    fn keys(&self) -> impl Iterator<Item = Key<'_>> {
        Self::FIELDS.into_iter().take(self.len()).map(Key::Symbol)
    }

    fn get_at<'gc>(&self, _: &Mutation<'gc>, position: usize) -> Option<Result<Option<Value<'gc>>, Error>> {
        if !self.positional {
            return None;
        }
        self.by_position.set(self.by_position.get() + 1);
        Some(Ok(self.field(position)))
    }
}

/// The counters of an [`Event`]: reads by key, then reads by position.
struct Reads(Rc<Cell<usize>>, Rc<Cell<usize>>);

impl Reads {
    fn counts(&self) -> (usize, usize) {
        (self.0.get(), self.1.get())
    }
}

fn event<'gc>(mc: &Mutation<'gc>, shape: Shape<'gc>, positional: bool, partial: bool) -> (Table<'gc>, Reads) {
    let reads = Reads(Rc::new(Cell::new(0)), Rc::new(Cell::new(0)));
    let host = Event { by_key: reads.0.clone(), by_position: reads.1.clone(), positional, partial };
    (Tables::new(mc).external_shaped(shape, host, 0).unwrap(), reads)
}

/// An external table with a shape caches what it reads at the positions of the shape. A read that names the position of its key asks the host by position and hashes nothing.
#[test]
fn an_external_table_of_a_shape_is_read_by_position() {
    arena().mutate(|mc| {
        let shape = shape_of(mc, &Event::FIELDS);
        let (x, y, z, w) = (symbol(mc, "x"), symbol(mc, "y"), symbol(mc, "z"), symbol(mc, "w"));
        let (table, reads) = event(mc, shape, true, false);
        assert_eq!((table.is_external(), table.len(mc), table.get_at(mc, y, 1), reads.counts()), (true, 3, None, (0, 0)));
        // The first read at the position of the key asks the host by position. Later reads ask nothing.
        assert_eq!((table.found_from(mc, y, 1), reads.counts()), (Ok(Some((1, fix(2)))), (0, 1)));
        assert_eq!((table.get_at(mc, y, 1), table.found_from(mc, y, 1), table.get(mc, y), table.found(mc, y), reads.counts()), (Some(fix(2)), Ok(Some((1, fix(2)))), Ok(Some(fix(2))), Ok(Some((1, fix(2)))), (0, 1)));
        // A read that names another position finds the key the general way. A value that was read stays cached.
        assert_eq!((table.found_from(mc, y, 0), table.found_from(mc, y, 9), reads.counts()), (Ok(Some((1, fix(2)))), Ok(Some((1, fix(2)))), (0, 1)));
        assert_eq!((table.found_from(mc, z, 0), table.get_at(mc, z, 2), reads.counts()), (Ok(Some((2, fix(3)))), Some(fix(3)), (1, 1)));
        // A read by key caches its value at the position of the shape as well.
        assert_eq!((table.get(mc, x), table.get_at(mc, x, 0), table.has(mc, x), reads.counts()), (Ok(Some(fix(1))), Some(fix(1)), Ok(true), (2, 1)));
        // A key outside the shape is asked for by key, every time, since the host has none.
        assert_eq!((table.get(mc, w), table.found_from(mc, w, 1), table.has(mc, w), reads.counts()), (Ok(None), Ok(None), Ok(false), (4, 1)));
        assert_eq!((named(mc, table), reads.counts()), (pairs_of(&[("x", 1), ("y", 2), ("z", 3)]), (4, 1)));
        // Another table of the shape has its own cache.
        let (other, other_reads) = event(mc, shape, true, false);
        assert_eq!((other.get_at(mc, y, 1), other.found_from(mc, y, 1), other_reads.counts(), reads.counts()), (None, Ok(Some((1, fix(2)))), (0, 1), (4, 1)));
    });
    // A key of the shape that the host has no entry for is not in the table. It is asked for again on the next read.
    arena().mutate(|mc| {
        let shape = shape_of(mc, &Event::FIELDS);
        let (y, z) = (symbol(mc, "y"), symbol(mc, "z"));
        let (table, reads) = event(mc, shape, true, true);
        assert_eq!((table.found_from(mc, z, 2), table.found_from(mc, z, 2), table.get_at(mc, z, 2), reads.counts()), (Ok(None), Ok(None), None, (0, 2)));
        assert_eq!((table.get(mc, z), table.has(mc, z), table.len(mc), table.found_from(mc, y, 1), reads.counts()), (Ok(None), Ok(false), 2, Ok(Some((1, fix(2)))), (1, 3)));
        assert_eq!(named(mc, table), pairs_of(&[("x", 1), ("y", 2)]));
    });
    // A host that does not look values up by position is asked by key. The value is still cached at the position of the shape.
    arena().mutate(|mc| {
        let shape = shape_of(mc, &Event::FIELDS);
        let y = symbol(mc, "y");
        let (table, reads) = event(mc, shape, false, false);
        assert_eq!((table.found_from(mc, y, 1), table.get_at(mc, y, 1), table.found_from(mc, y, 1), reads.counts()), (Ok(Some((1, fix(2)))), Some(fix(2)), Ok(Some((1, fix(2)))), (1, 0)));
    });
}

/// A writable external table with a shape takes every change that one without a shape takes. Its cache follows the changes.
#[test]
fn a_writable_external_table_of_a_shape_changes_like_any_other() {
    arena().mutate(|mc| {
        let tables = Tables::new(mc);
        let (seen, sent, extra) = (text(mc, "seen"), text(mc, "sent"), text(mc, "extra"));
        let shape = tables.shape(&[seen, sent]).unwrap();
        let host = Counters(vec![(CounterKey::Name("seen".to_owned()), 5), (CounterKey::Name("sent".to_owned()), 6)]);
        let table = tables.external_shaped(shape, host, 0).unwrap();
        assert_eq!((table.found_from(mc, sent, 1), table.get_at(mc, sent, 1), table.get_at(mc, seen, 0)), (Ok(Some((1, fix(6)))), Some(fix(6)), None));
        // A new value for a key of the shape is cached at its position. A key outside the shape is added after the keys of the shape.
        table.set(mc, seen, fix(50)).unwrap();
        table.set(mc, extra, fix(7)).unwrap();
        assert_eq!((table.get_at(mc, seen, 0), table.found(mc, extra), table.get_at(mc, sent, 1), counts(mc, table)), (Some(fix(50)), Ok(Some((2, fix(7)))), Some(fix(6)), vec![50, 6, 7]));
        // A removed key is not found at its position. When it is set again, it is found wherever the cache put it.
        assert_eq!((table.delete(mc, seen), table.found_from(mc, seen, 0), table.get_at(mc, seen, 0), table.len(mc)), (Ok(true), Ok(None), None, 2));
        table.set(mc, seen, fix(8)).unwrap();
        let found = table.found_from(mc, seen, 0).unwrap().unwrap();
        assert_eq!((found.1, table.get_at(mc, seen, found.0), table.get(mc, sent), counts(mc, table)), (fix(8), Some(fix(8)), Ok(Some(fix(6))), vec![6, 7, 8]));
        // An emptied table has nothing at any position, and takes new entries.
        table.clear(mc).unwrap();
        assert_eq!((table.found_from(mc, sent, 1), table.get(mc, seen), table.len(mc)), (Ok(None), Ok(None), 0));
        table.set(mc, sent, fix(1)).unwrap();
        assert_eq!((table.found_from(mc, sent, 1), counts(mc, table)), (Ok(Some((1, fix(1)))), vec![1]));
    });
}

#[test]
fn held_values_are_read_by_position() {
    arena().mutate(|mc| {
        let table = Tables::new(mc).make().unwrap();
        assert_eq!(table.held(mc, 0), None);
        for key in 0..3 {
            table.set(mc, fix(key), fix(key + 10)).unwrap();
        }
        table.delete(mc, fix(1)).unwrap();
        let held: Vec<_> = (0..7).map(|index| table.held(mc, index)).collect();
        assert_eq!(held, [Some(fix(0)), Some(fix(10)), Some(Value::BROKEN), Some(Value::BROKEN), Some(fix(2)), Some(fix(12)), None]);
    });
}

/// A key that is an external string is stored as it is: the table keeps the string of the host, and copies no character. A flat string, a rope and another external string with its characters find the entry.
#[test]
fn an_external_string_is_a_key_as_itself() {
    arena().mutate(|mc| {
        let (tables, strings) = (Tables::new(mc), Strings::new(mc));
        let name: std::sync::Arc<str> = std::sync::Arc::from(format!("{} of the host", "a key that is kept outside the arena, ".repeat(16)));
        let outside = strings.external(crate::string::ExternalText::new(name.clone())).unwrap();
        assert!(strings.is_external(outside) && !strings.is_interned(outside));
        let (fielded, mapped) = (tables.make().unwrap(), tables.with_room(4).unwrap());
        fielded.set_field(mc, outside.value(), fix(1)).unwrap();
        mapped.set(mc, outside.value(), fix(2)).unwrap();
        assert!(strings.is_interned(outside) && strings.is_external(outside));
        assert_eq!((entries(mc, fielded), entries(mc, mapped), tables.shape(&[outside.value()]).ok()), (vec![(outside.value(), fix(1))], vec![(outside.value(), fix(2))], fielded.shape(mc)));
        // The same text in three other forms.
        let flat = text(mc, &name);
        let rope = concat(&strings, strings.string(text(mc, &name[..300])).unwrap(), strings.string(text(mc, &name[300..])).unwrap()).unwrap();
        let second = strings.external(crate::string::ExternalText::new(name.clone())).unwrap();
        assert!(flat != outside.value() && rope != outside && second != outside);
        assert_eq!((fielded.get(mc, flat), mapped.get(mc, rope.value()), mapped.get(mc, second.value()), fielded.get(mc, second.value())), (Ok(Some(fix(1))), Ok(Some(fix(2))), Ok(Some(fix(2))), Ok(Some(fix(1)))));
        // A write through another form changes the entry, and the key stays the first external string.
        mapped.set(mc, second.value(), fix(3)).unwrap();
        assert_eq!((entries(mc, mapped), mapped.has(mc, text(mc, &name[1..]))), (vec![(outside.value(), fix(3))], Ok(false)));
    });
}

