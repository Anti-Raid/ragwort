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
    table.entries(mc).collect()
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
        table.set(mc, fix(1), Value::NIL).unwrap();
        assert_eq!((table.len(mc), table.get(mc, fix(1))), (2, Ok(Some(Value::NIL))));
        assert_eq!(table.delete(mc, fix(1)), Ok(true));
        assert_eq!(table.delete(mc, fix(1)), Ok(false));
        assert_eq!((table.len(mc), table.get(mc, fix(1)), table.get(mc, fix(2))), (1, Ok(None), Ok(Some(Value::FALSE))));
        table.clear(mc);
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
            table.set(mc, fix(extra), Value::NIL).unwrap();
        }
        let kept = keys.iter().filter(|&&key| key % 10 == 0 && key != keys[3]).map(|&key| fix(key));
        let last = (keys[3] % 10 == 0).then_some(fix(keys[3]));
        let expected: Vec<_> = kept.chain(last).chain((5000..9000).map(fix)).collect();
        assert_eq!(table.entries(mc).map(|(key, _)| key).collect::<Vec<_>>(), expected);
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
        let (letter, truth, empty) = (add(mc, table, Value::char('x')), add(mc, table, Value::TRUE), add(mc, table, Value::NIL));
        assert_eq!((table.get(mc, Value::char('x')), table.get(mc, Value::TRUE), table.get(mc, Value::NIL)), (Ok(Some(letter)), Ok(Some(truth)), Ok(Some(empty))));
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
        let mut keys = Value::NIL;
        for number in 0..2000 {
            let key = pairs.cons(fix(number), Value::NIL).unwrap().value(mc);
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
        let user = |id| externals.make(&USER_ID, UserId(id), 0, Value::NIL).unwrap().value(mc);
        let (by_value, by_identity) = (Tables::new(mc).make().unwrap(), Tables::new(mc).make().unwrap());
        for id in 0..500 {
            by_value.set(mc, user(id), fix(id as i64)).unwrap();
        }
        // Another reference to an equal value is the same key. One of another kind is not, though it hashes the same, and neither is the number.
        assert_eq!(by_value.len(mc), 500);
        by_value.set(mc, user(7), Value::TRUE).unwrap();
        assert_eq!((by_value.len(mc), by_value.get(mc, user(7)), by_value.get(mc, user(8)), by_value.get(mc, user(500))), (500, Ok(Some(Value::TRUE)), Ok(Some(fix(8))), Ok(None)));
        let other = externals.make(&OTHER_ID, 7, 0, Value::NIL).unwrap().value(mc);
        assert_eq!((by_value.get(mc, other), by_value.get(mc, fix(7))), (Ok(None), Ok(None)));
        by_value.set(mc, other, Value::FALSE).unwrap();
        assert_eq!((by_value.get(mc, other), by_value.get(mc, user(7)), by_value.len(mc)), (Ok(Some(Value::FALSE)), Ok(Some(Value::TRUE)), 501));
        assert_eq!(by_value.delete(mc, user(7)), Ok(true));
        assert_eq!((by_value.get(mc, user(7)), by_value.get(mc, other)), (Ok(None), Ok(Some(Value::FALSE))));
        // A kind with no equality of its own makes each reference its own key.
        let handles: Vec<_> = (0..500).map(|number| externals.make(&HANDLE, number % 2, 0, Value::NIL).unwrap().value(mc)).collect();
        for (number, &handle) in handles.iter().enumerate() {
            by_identity.set(mc, handle, fix(number as i64)).unwrap();
        }
        assert_eq!((by_identity.len(mc), by_identity.get(mc, handles[3]), by_identity.get(mc, externals.make(&HANDLE, 1, 0, Value::NIL).unwrap().value(mc))), (500, Ok(Some(fix(3))), Ok(None)));
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
        assert_eq!(by_value.get(mc, externals.make(&USER_ID, UserId(8), 0, Value::NIL).unwrap().value(mc)), Ok(Some(fix(8))));
        for (number, handle) in pairs.elements(kept[2]).enumerate() {
            assert_eq!(by_identity.get(mc, handle), Ok(Some(fix(number as i64))));
        }
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
