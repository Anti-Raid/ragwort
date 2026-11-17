use crate::gc::{Arena, GcVec, slot};

use super::*;
use crate::string::*;

/// Returns an arena. Root 0 holds the intern table. Root 1 holds the symbols that a test keeps.
fn arena() -> Arena {
    let mut arena = Arena::new(16 << 20, 2);
    arena.mutate(|mc| {
        mc.set_root(0, Symbols::with_seed(mc, 1).unwrap().value(mc));
        mc.set_root(1, Value::object(mc, GcVec::<slot::Value>::new(mc).unwrap().head()));
    });
    arena
}

fn roots<'gc>(mc: &Mutation<'gc>) -> (Symbols<'gc>, GcVec<'gc>) {
    (Symbols::of(mc.root(0)).unwrap(), GcVec::of(mc.root(1).downcast(mc).unwrap()))
}

fn names(n: usize) -> Vec<String> {
    (0..n).map(|i| format!("name {i} {}", ["", "é", "日本", "😀"][i % 4])).collect()
}

/// A name has one symbol, however the string of the name is stored. The symbol stores the name and its hash.
#[test]
fn one_symbol_per_name() {
    let mut arena = arena();
    arena.mutate(|mc| {
        let (symbols, _) = roots(mc);
        let h = Strings::new(mc);
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
            let name = first.name(mc);
            assert!(is_flat(&h, name));
            assert_eq!(display(&h, name).to_string(), text);
            assert_eq!(first.hash(mc), hash_str(text, symbols.seed(mc)));
            assert_eq!(Symbol::of(first.value(mc)), Some(first));
            assert_eq!(h.string(first.value(mc)), None);
            assert_eq!(Symbol::of(name.value()), None);
        }
        let all: Vec<_> = names(500).iter().map(|n| symbols.intern_str(&h, n).unwrap()).collect();
        let distinct: std::collections::HashSet<_> = all.iter().map(|s| s.value(mc).to_bits()).collect();
        assert_eq!(distinct.len(), all.len());
    });
}

/// A symbol that is kept through collections that move every object is still the symbol that
/// its name interns to.
#[test]
fn symbols_survive_moving_collections() {
    let mut arena = arena();
    arena.set_evacuate_all(true);
    let names = names(2000);
    arena.mutate(|mc| {
        let (symbols, kept) = roots(mc);
        let h = Strings::new(mc);
        for n in &names {
            kept.push(mc, symbols.intern_str(&h, n).unwrap().value(mc)).unwrap();
        }
    });
    arena.collect();
    arena.collect();
    arena.mutate(|mc| {
        let (symbols, kept) = roots(mc);
        let h = Strings::new(mc);
        for (i, n) in names.iter().enumerate() {
            let s = symbols.intern_str(&h, n).unwrap();
            assert_eq!(Some(s.value(mc)), kept.get(mc, i));
            assert_eq!(display(&h, s.name(mc)).to_string(), *n);
        }
    });
}

/// The intern table does not keep symbols alive. A symbol that is still reachable stays unique,
/// however many of its neighbors in the table were collected. The name of a collected symbol gets a new symbol.
#[test]
fn unreachable_symbols_are_collected() {
    let mut arena = arena();
    let names = names(3000);
    arena.mutate(|mc| {
        let (symbols, kept) = roots(mc);
        let h = Strings::new(mc);
        for (i, n) in names.iter().enumerate() {
            let s = symbols.intern_str(&h, n).unwrap();
            if i % 3 == 0 {
                kept.push(mc, s.value(mc)).unwrap();
            }
        }
    });
    arena.collect();
    arena.collect();
    // The live objects are the kept symbols, their names, and a few containers.
    let live = arena.objects();
    assert!((2 * 1000..2 * 1000 + 10).contains(&live), "{live} objects");
    arena.mutate(|mc| {
        let (symbols, kept) = roots(mc);
        let h = Strings::new(mc);
        let again: Vec<_> = names.iter().map(|n| symbols.intern_str(&h, n).unwrap()).collect();
        for (i, s) in again.iter().enumerate() {
            match i % 3 {
                0 => assert_eq!(Some(s.value(mc)), kept.get(mc, i / 3)),
                _ => assert!(kept.get(mc, i / 3) != Some(s.value(mc))),
            }
            assert_eq!(symbols.intern_str(&h, &names[i]), Ok(*s));
            assert_eq!(symbols.intern(&h, s.name(mc)), Ok(*s));
        }
    });
}

/// Interning and dropping names repeatedly does not grow the table beyond the size that the live symbols need.
#[test]
fn churn_leaves_the_table_small() {
    let mut arena = arena();
    arena.mutate(|mc| {
        let (symbols, kept) = roots(mc);
        let h = Strings::new(mc);
        for n in names(100) {
            kept.push(mc, symbols.intern_str(&h, &n).unwrap().value(mc)).unwrap();
        }
    });
    for round in 0..30 {
        arena.mutate(|mc| {
            let (symbols, _) = roots(mc);
            let h = Strings::new(mc);
            for i in 0..500 {
                symbols.intern_str(&h, &format!("round {round} message {i}")).unwrap();
            }
            assert!(symbols.capacity(mc) <= 2048, "{} slots", symbols.capacity(mc));
        });
        arena.collect();
    }
    arena.mutate(|mc| {
        let (symbols, kept) = roots(mc);
        let h = Strings::new(mc);
        for (i, n) in names(100).iter().enumerate() {
            assert_eq!(Some(symbols.intern_str(&h, n).unwrap().value(mc)), kept.get(mc, i));
        }
    });
}

#[test]
fn an_arena_has_one_table_seeded_apart_from_others() {
    fn seed(arena: &mut Arena) -> u64 {
        arena.mutate(|mc| Symbols::of_arena(mc).unwrap().seed(mc))
    }
    let (mut a, mut b) = (Arena::new(1 << 20, 0), Arena::new(1 << 20, 0));
    assert_ne!(seed(&mut a), seed(&mut b));
    a.mutate(|mc| {
        let symbols = Symbols::of_arena(mc).unwrap();
        assert_eq!(Symbols::with_seed(mc, symbols.seed(mc) ^ 1), Ok(symbols));
    });
    // The arena keeps the intern table alive when nothing else references it. So the seed, and with it the hash of a name, is the same after a collection.
    let kept = a.mutate(|mc| Symbols::of_arena(mc).unwrap().intern_str(&Strings::new(mc), "kept").unwrap().hash(mc));
    a.collect();
    a.mutate(|mc| assert_eq!(Symbols::of_arena(mc).unwrap().intern_str(&Strings::new(mc), "kept").unwrap().hash(mc), kept));
}

/// A name has one keyword, which is distinct from its symbol. A collection keeps the keyword while it is reachable.
#[test]
fn one_keyword_per_name() {
    let mut arena = arena();
    arena.mutate(|mc| {
        let (symbols, kept) = roots(mc);
        let h = Strings::new(mc);
        let when = symbols.keyword(mc, symbols.intern_str(&h, "when").unwrap()).unwrap();
        assert_eq!(symbols.keyword(mc, symbols.intern_str(&h, "when").unwrap()).unwrap(), when);
        assert_ne!(symbols.keyword(mc, symbols.intern_str(&h, "unless").unwrap()).unwrap(), when);
        assert!(Symbol::of(when.value(mc)).is_none() && Keyword::of(when.value(mc)).is_some());
        kept.push(mc, when.value(mc)).unwrap();
    });
    arena.collect();
    arena.mutate(|mc| {
        let (symbols, kept) = roots(mc);
        let when = Keyword::of(kept.get(mc, 0).unwrap()).unwrap();
        assert_eq!(display(&Strings::new(mc), when.symbol(mc).name(mc)).to_string(), "when");
        assert_eq!(symbols.keyword(mc, when.symbol(mc)).unwrap(), when);
    });
}
