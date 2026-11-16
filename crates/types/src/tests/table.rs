use std::cell::Cell;
use std::rc::Rc;

use crate::external::{ExternalKind, ExternalRefs};
use crate::gc::Arena;
use crate::num::int;
use crate::pair::Pairs;
use crate::string::{concat, from_str};

use super::*;

/// Root 0 holds the symbols, root 1 what a test keeps across collections.
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
        // Enough entries for the arrays to be made again several times, in an order no hash would give.
        let keys: Vec<i64> = (0..5000).map(|i| (i * 7919) % 5000).collect();
        for &key in &keys {
            table.set(mc, fix(key), fix(key * 2)).unwrap();
        }
        assert_eq!(entries(mc, table), keys.iter().map(|&key| (fix(key), fix(key * 2))).collect::<Vec<_>>());
        // Setting a key that is there keeps its place. A key that was removed and is set again goes last.
        table.set(mc, fix(keys[10]), Value::TRUE).unwrap();
        assert_eq!(entries(mc, table)[10], (fix(keys[10]), Value::TRUE));
        assert_eq!(table.delete(mc, fix(keys[3])), Ok(true));
        table.set(mc, fix(keys[3]), Value::FALSE).unwrap();
        let after = entries(mc, table);
        assert_eq!((after.len(), after[3].0, after[4999]), (5000, fix(keys[4]), (fix(keys[3]), Value::FALSE)));
        // Removing most entries and adding others keeps the rest in order, through the rebuilds that drop the dead ones.
        for &key in keys.iter().filter(|&&key| key % 10 != 0) {
            assert_eq!(table.delete(mc, fix(key)), Ok(true));
        }
        for extra in 5000..9000 {
            table.set(mc, fix(extra), Value::NULL).unwrap();
        }
        let kept = keys.iter().filter(|&&key| key % 10 == 0 && key != keys[3]).map(|&key| fix(key));
        let last = (keys[3] % 10 == 0).then_some(fix(keys[3]));
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
        // Strings by their characters, however they are held: in the value, flat, or as a rope.
        let long = "a string of more characters than a value holds, with é and 日本 in it";
        let (short, flat) = (add(mc, table, text(mc, "id")), add(mc, table, text(mc, long)));
        let rope = concat(&strings, strings.string(text(mc, &long[..20])).unwrap(), strings.string(text(mc, &long[20..])).unwrap()).unwrap();
        assert_eq!(table.get(mc, text(mc, "id")), Ok(Some(short)));
        assert_eq!(table.get(mc, text(mc, long)), Ok(Some(flat)));
        assert_eq!(table.get(mc, rope.value()), Ok(Some(flat)));
        assert_eq!(table.get(mc, text(mc, &long[1..])), Ok(None));
        // A symbol is not the string of its name.
        let named = add(mc, table, symbol(mc, "id"));
        assert_eq!((table.get(mc, symbol(mc, "id")), table.get(mc, text(mc, "id"))), (Ok(Some(named)), Ok(Some(short))));
        assert_eq!(table.get(mc, symbol(mc, "other")), Ok(None));
        // Numbers by value and exactness.
        let big = |negative| int::from_i128(&nums, if negative { -(1 << 100) } else { 1 << 100 }).unwrap().value();
        let (one, one_inexact, huge) = (add(mc, table, fix(1)), add(mc, table, Value::flonum(mc, 1.0).unwrap()), add(mc, table, big(false)));
        assert_eq!(table.get(mc, fix(1)), Ok(Some(one)));
        assert_eq!(table.get(mc, Value::flonum(mc, 1.0).unwrap()), Ok(Some(one_inexact)));
        assert_eq!(table.get(mc, big(false)), Ok(Some(huge)));
        assert_eq!(table.get(mc, big(true)), Ok(None));
        // A flonum that does not fit the value word is an object, and still a key by its value.
        let boxed = 1e300;
        assert!(Value::inline_flonum(boxed).is_none());
        let small = add(mc, table, Value::flonum(mc, boxed).unwrap());
        assert_eq!(table.get(mc, Value::flonum(mc, boxed).unwrap()), Ok(Some(small)));
        // Characters and constants by what they are.
        let (letter, truth, empty) = (add(mc, table, Value::char('x')), add(mc, table, Value::TRUE), add(mc, table, Value::NULL));
        assert_eq!((table.get(mc, Value::char('x')), table.get(mc, Value::TRUE), table.get(mc, Value::NULL)), (Ok(Some(letter)), Ok(Some(truth)), Ok(Some(empty))));
        assert_eq!((table.get(mc, Value::char('y')), table.get(mc, Value::FALSE)), (Ok(None), Ok(None)));
        // Anything else by identity: two lists of the same items are two keys.
        let (first, second) = (pairs.list(&[fix(1), fix(2)]).unwrap(), pairs.list(&[fix(1), fix(2)]).unwrap());
        let (one_list, other_list) = (add(mc, table, first), add(mc, table, second));
        assert_eq!((table.get(mc, first), table.get(mc, second)), (Ok(Some(one_list)), Ok(Some(other_list))));
        assert_eq!(table.get(mc, pairs.list(&[fix(1), fix(2)]).unwrap()), Ok(None));
        assert_eq!(table.len(mc), 12);
    });
}

/// A key compared by identity is hashed by where it is. Collections that move objects change that, and the table must still find every key.
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
            // Garbage between the keys, so that a collection has holes to move them into.
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
            // Only the table with keys hashed by place has to make its index again.
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
            // The table goes on working: a removed key is gone, and a new one is found.
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

/// An external reference is a key as its kind has it: by the host's equality, or by identity.
#[test]
fn external_references_are_keys_as_their_kind_says() {
    let mut arena = arena();
    arena.mutate(|mc| {
        let externals = ExternalRefs::new(mc);
        let user = |id| externals.make(&USER_ID, UserId(id), 0, Value::NULL).unwrap().value(mc);
        let (by_value, by_identity) = (Tables::new(mc).make().unwrap(), Tables::new(mc).make().unwrap());
        for id in 0..500 {
            by_value.set(mc, user(id), fix(id as i64)).unwrap();
        }
        // Another reference to an equal value is the same key. One of another kind is not, though it hashes the same, and neither is the number.
        assert_eq!(by_value.len(mc), 500);
        by_value.set(mc, user(7), Value::TRUE).unwrap();
        assert_eq!((by_value.len(mc), by_value.get(mc, user(7)), by_value.get(mc, user(8)), by_value.get(mc, user(500))), (500, Ok(Some(Value::TRUE)), Ok(Some(fix(8))), Ok(None)));
        let other = externals.make(&OTHER_ID, 7, 0, Value::NULL).unwrap().value(mc);
        assert_eq!((by_value.get(mc, other), by_value.get(mc, fix(7))), (Ok(None), Ok(None)));
        by_value.set(mc, other, Value::FALSE).unwrap();
        assert_eq!((by_value.get(mc, other), by_value.get(mc, user(7)), by_value.len(mc)), (Ok(Some(Value::FALSE)), Ok(Some(Value::TRUE)), 501));
        assert_eq!(by_value.delete(mc, user(7)), Ok(true));
        assert_eq!((by_value.get(mc, user(7)), by_value.get(mc, other)), (Ok(None), Ok(Some(Value::FALSE))));
        // A kind with no equality of its own makes each reference its own key.
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
        // Keys hashed by the host's hash do not depend on where they are. Keys compared by identity do.
        assert!(!by_value.is_stale(mc) && by_identity.is_stale(mc));
        assert_eq!(by_value.get(mc, externals.make(&USER_ID, UserId(8), 0, Value::NULL).unwrap().value(mc)), Ok(Some(fix(8))));
        for (number, handle) in pairs.elements(kept[2]).enumerate() {
            assert_eq!(by_identity.get(mc, handle), Ok(Some(fix(number as i64))));
        }
    });
}

/// A message as a host received it, with a nested author. Its fields are read where they are. `reads` counts the calls of `get`, and `dropped` is set when the arena lets go of it.
struct Message {
    id: i64,
    content: &'static str,
    author: Option<&'static str>,
    reads: Rc<Cell<usize>>,
    dropped: Rc<Cell<bool>>,
}

/// The author of a [`Message`], which a message makes anew on each read of its `author` key.
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
        Ok(if self.has(key) { Some(text(mc, self.0)) } else { None })
    }

    fn keys(&self) -> impl Iterator<Item = Key<'_>> {
        std::iter::once(Key::String("name"))
    }
}

/// Counters that the host keeps and programs can change: integer values under string or integer keys, in the order they were added.
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

/// The counts the host of `table` holds, in its order.
fn counts<'gc>(mc: &Mutation<'gc>, table: Table<'gc>) -> Vec<i64> {
    table.host::<Counters>(mc).unwrap().0.iter().map(|&(_, count)| count).collect()
}

fn message<'gc>(mc: &Mutation<'gc>, author: Option<&'static str>, reads: &Rc<Cell<usize>>, dropped: &Rc<Cell<bool>>) -> Table<'gc> {
    let host = Message { id: 7, content: "a message long enough not to fit in a word", author, reads: reads.clone(), dropped: dropped.clone() };
    Tables::new(mc).external(host, 64).unwrap()
}

/// A program reads an external table like any other. Each value is read from the host once, and what it gave is what the table gives from then on.
#[test]
fn an_external_table_is_read_from_its_host_once() {
    let (reads, dropped) = (Rc::new(Cell::new(0)), Rc::new(Cell::new(false)));
    let mut arena = arena();
    arena.mutate(|mc| {
        let table = message(mc, Some("ann"), &reads, &dropped);
        assert!(table.is_external() && !table.is_writable(mc) && !table.is_stale(mc));
        assert_eq!((Table::of(table.value(mc)), table.len(mc), reads.get()), (Some(table), 3, 0));
        // Asking whether a key is there does not read its value.
        assert_eq!((table.has(mc, symbol(mc, "content")), table.has(mc, symbol(mc, "missing")), table.has(mc, text(mc, "content")), reads.get()), (Ok(true), Ok(false), Ok(false), 0));
        let content = table.get(mc, symbol(mc, "content")).unwrap().unwrap();
        assert_eq!((table.get(mc, symbol(mc, "id")), reads.get()), (Ok(Some(fix(7))), 2));
        assert_eq!((table.get(mc, symbol(mc, "content")), table.get(mc, symbol(mc, "id")), table.has(mc, symbol(mc, "id")), reads.get()), (Ok(Some(content)), Ok(Some(fix(7))), Ok(true), 2));
        // A nested table the host made for a key is the same table on every read.
        let author = table.get(mc, symbol(mc, "author")).unwrap().unwrap();
        assert_eq!((table.get(mc, symbol(mc, "author")), reads.get()), (Ok(Some(author)), 3));
        assert_eq!(Table::of(author).unwrap().get(mc, text(mc, "name")), Ok(Some(text(mc, "ann"))));
        // A key that is not there is asked for each time, and nothing is kept for it. A key of a kind the host cannot take is not asked for at all.
        assert_eq!((table.get(mc, symbol(mc, "missing")), table.get(mc, symbol(mc, "missing")), reads.get()), (Ok(None), Ok(None), 5));
        let pair = Pairs::new(mc).list(&[fix(1)]).unwrap();
        assert_eq!((table.get(mc, pair), table.get(mc, Value::NIL), table.has(mc, pair), reads.get()), (Ok(None), Ok(None), Ok(false), 5));
        // The host's own value is still its own.
        assert_eq!(table.host::<Message>(mc).map(|host| host.id), Some(7));
        assert!(table.host::<Counters>(mc).is_none() && Tables::new(mc).make().unwrap().host::<Message>(mc).is_none());
        mc.set_root(1, Pairs::new(mc).list(&[table.value(mc), content, author]).unwrap());
    });
    // What was read stays what it was through collections that move objects, and is still not read again.
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
        // A walk reads what was not read yet, once, and a second walk reads nothing.
        let walked = entries(mc, table);
        assert_eq!(walked.iter().map(|&(key, _)| key).collect::<Vec<_>>(), [symbol(mc, "id"), symbol(mc, "content")]);
        assert_eq!((walked[0].1, reads.get()), (id, 2));
        assert_eq!((entries(mc, table), reads.get()), (walked.clone(), 2));
        assert_eq!((0..5).map(|index| table.held(mc, index)).collect::<Vec<_>>(), [Some(walked[0].0), Some(walked[0].1), Some(walked[1].0), Some(walked[1].1), None]);
        assert_eq!(table.get(mc, symbol(mc, "content")), Ok(Some(walked[1].1)));
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

/// A writable external table changes the host's data, and reads back what was written as a table in the arena does.
#[test]
fn a_writable_external_table_changes_its_hosts_entries() {
    arena().mutate(|mc| {
        let table = Tables::new(mc).external(Counters::default(), 0).unwrap();
        assert!(table.is_writable(mc) && table.is_empty(mc));
        table.set(mc, text(mc, "hits"), fix(1)).unwrap();
        table.set(mc, fix(404), fix(2)).unwrap();
        table.set(mc, text(mc, "a longer name than a word holds"), fix(3)).unwrap();
        assert_eq!((table.len(mc), counts(mc, table), table.get(mc, text(mc, "hits")), table.get(mc, fix(404))), (3, vec![1, 2, 3], Ok(Some(fix(1))), Ok(Some(fix(2)))));
        // Setting a key again changes the host's entry, and the walk that was kept is made again.
        assert_eq!(entries(mc, table).len(), 3);
        table.set(mc, text(mc, "hits"), fix(10)).unwrap();
        assert_eq!((counts(mc, table), table.get(mc, text(mc, "hits")), entries(mc, table)[0]), (vec![10, 2, 3], Ok(Some(fix(10))), (text(mc, "hits"), fix(10))));
        // The host takes only what it can hold: here integer values under string or integer keys.
        assert_eq!(table.set(mc, text(mc, "hits"), text(mc, "many")), Err(TableError::Refused));
        assert_eq!(table.set(mc, symbol(mc, "hits"), fix(1)), Err(TableError::Refused));
        assert_eq!(table.set(mc, Pairs::new(mc).list(&[fix(1)]).unwrap(), fix(1)), Err(TableError::Refused));
        assert_eq!((counts(mc, table), table.get(mc, text(mc, "hits"))), (vec![10, 2, 3], Ok(Some(fix(10)))));
        // Removing an entry removes it from the host and from what was read.
        assert_eq!((table.delete(mc, fix(404)), table.delete(mc, fix(404)), table.delete(mc, symbol(mc, "hits"))), (Ok(true), Ok(false), Ok(false)));
        assert_eq!((table.len(mc), table.get(mc, fix(404)), table.has(mc, fix(404)), entries(mc, table).len()), (2, Ok(None), Ok(false), 2));
        table.clear(mc).unwrap();
        assert_eq!((table.len(mc), table.get(mc, text(mc, "hits")), entries(mc, table), counts(mc, table)), (0, Ok(None), vec![], vec![]));
        table.set(mc, text(mc, "hits"), fix(1)).unwrap();
        assert_eq!(entries(mc, table), [(text(mc, "hits"), fix(1))]);
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
