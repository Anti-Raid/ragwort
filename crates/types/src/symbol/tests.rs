use ragwort_gc::{Arena, GcVec, Rootable};

use super::*;
use crate::string::*;

struct Table;
impl Rootable for Table {
    type Root<'gc> = (Symbols<'gc>, GcVec<'gc, Value<'gc>>);
}

fn arena() -> Arena<Table> {
    Arena::<Table>::new(16 << 20, |_| Ok((Symbols::with_seed(1), GcVec::new()))).unwrap()
}

fn names(n: usize) -> Vec<String> {
    (0..n).map(|i| format!("name {i} {}", ["", "é", "日本", "😀"][i % 4])).collect()
}

/// However its name is held, a name has one symbol, which keeps the name and its hash.
#[test]
fn one_symbol_per_name() {
    let mut arena = arena();
    arena.mutate(|mc, (symbols, _)| {
        let h = Strings::new(mc).unwrap();
        for text in ["content", "", "café", "日本語", "😀", &"long name ".repeat(300)] {
            let half = text.len() / 2;
            let half = (0..=half).rev().find(|&i| text.is_char_boundary(i)).unwrap();
            let rope = concat(&h, from_str(&h, &text[..half]).unwrap(), from_str(&h, &text[half..]).unwrap()).unwrap();
            let flattened = concat(&h, from_str(&h, &text[..half]).unwrap(), from_str(&h, &text[half..]).unwrap()).unwrap();
            flatten(&h, flattened).unwrap();
            let external = h.external(ExternalText::new(String::from(text))).unwrap();
            let first = symbols.intern_str(&h, text).unwrap();
            for s in [from_str(&h, text).unwrap(), rope, flattened, external] {
                assert_eq!(symbols.intern(&h, s), Ok(first), "{text:?}");
            }
            assert_eq!(symbols.intern_str(&h, text), Ok(first));
            let name = h.name(first);
            assert!(is_flat(&h, name));
            assert_eq!(display(&h, name).to_string(), text);
            assert_eq!(h.symbol_hash(first), hash_str(text, symbols.seed()));
            assert_eq!(h.symbol(first.value()), Some(first));
            assert_eq!(h.string(first.value()), None);
            assert_eq!(h.symbol(name.value()), None);
        }
        let all: Vec<_> = names(500).iter().map(|n| symbols.intern_str(&h, n).unwrap()).collect();
        let distinct: std::collections::HashSet<_> = all.iter().map(|s| s.value().to_bits()).collect();
        assert_eq!(distinct.len(), all.len());
    }).unwrap();
}

/// Symbols kept through collections that move everything are still the ones their names
/// intern to.
#[test]
fn symbols_survive_moving_collections() {
    let mut arena = arena();
    arena.set_evacuate_all(true);
    let names = names(2000);
    arena.mutate(|mc, (symbols, kept)| {
        let h = Strings::new(mc).unwrap();
        for n in &names {
            kept.push(mc, symbols.intern_str(&h, n).unwrap().value()).unwrap();
        }
    }).unwrap();
    arena.collect();
    arena.collect();
    arena.mutate(|mc, (symbols, kept)| {
        let h = Strings::new(mc).unwrap();
        for (i, n) in names.iter().enumerate() {
            let s = symbols.intern_str(&h, n).unwrap();
            assert_eq!(Some(s.value()), kept.get(mc, i));
            assert_eq!(display(&h, h.name(s)).to_string(), *n);
        }
    }).unwrap();
}

/// The table doesn't keep symbols alive. Ones still reached stay unique however many of their
/// neighbors in the table died, and a dead one's name gets a new symbol.
#[test]
fn unreachable_symbols_are_collected() {
    let mut arena = arena();
    let names = names(3000);
    arena.mutate(|mc, (symbols, kept)| {
        let h = Strings::new(mc).unwrap();
        for (i, n) in names.iter().enumerate() {
            let s = symbols.intern_str(&h, n).unwrap();
            if i % 3 == 0 {
                kept.push(mc, s.value()).unwrap();
            }
        }
    }).unwrap();
    let before = arena.metrics().objects;
    arena.collect();
    arena.collect();
    let after = arena.metrics().objects;
    assert!(after + 2 * 2000 <= before, "{before} objects, then {after}");
    arena.mutate(|mc, (symbols, kept)| {
        let h = Strings::new(mc).unwrap();
        let again: Vec<_> = names.iter().map(|n| symbols.intern_str(&h, n).unwrap()).collect();
        for (i, s) in again.iter().enumerate() {
            match i % 3 {
                0 => assert_eq!(Some(s.value()), kept.get(mc, i / 3)),
                _ => assert!(kept.get(mc, i / 3) != Some(s.value())),
            }
            assert_eq!(symbols.intern_str(&h, &names[i]), Ok(*s));
            assert_eq!(symbols.intern(&h, h.name(*s)), Ok(*s));
        }
    }).unwrap();
}

/// Names made and dropped over and over don't grow the table past what the live ones need.
#[test]
fn churn_leaves_the_table_small() {
    let mut arena = arena();
    arena.mutate(|mc, (symbols, kept)| {
        let h = Strings::new(mc).unwrap();
        for n in names(100) {
            kept.push(mc, symbols.intern_str(&h, &n).unwrap().value()).unwrap();
        }
    }).unwrap();
    for round in 0..30 {
        arena.mutate(|mc, (symbols, _)| {
            let h = Strings::new(mc).unwrap();
            for i in 0..500 {
                symbols.intern_str(&h, &format!("round {round} message {i}")).unwrap();
            }
            assert!(symbols.capacity(&h) <= 2048, "{} slots", symbols.capacity(&h));
        }).unwrap();
        arena.collect();
    }
    arena.mutate(|mc, (symbols, kept)| {
        let h = Strings::new(mc).unwrap();
        for (i, n) in names(100).iter().enumerate() {
            assert_eq!(Some(symbols.intern_str(&h, n).unwrap().value()), kept.get(mc, i));
        }
    }).unwrap();
}

#[test]
fn tables_are_seeded_apart() {
    assert_ne!(Symbols::new().seed(), Symbols::new().seed());
}
