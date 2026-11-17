use std::cell::Cell;
use std::cmp::Ordering;
use std::rc::Rc;
use std::sync::Arc;

use super::*;
use crate::gc::{Arena, GcVec, slot};

fn root<'gc>(mc: &Mutation<'gc>) -> GcVec<'gc> {
    GcVec::of(mc.root(0).downcast(mc).unwrap())
}

fn string<'gc>(h: &Strings<'_, 'gc>, text: &str) -> Str<'gc> {
    from_str(h, text).unwrap()
}

fn arena(limit: usize) -> Arena {
    let mut arena = Arena::new(limit, 1);
    arena.mutate(|mc| {
        let v = GcVec::<slot::Value>::new(mc).unwrap();
        mc.set_root(0, Value::object(mc, v.head()));
    });
    arena
}

/// Flat strings of each width and ropes over them survive collections that move them.
#[test]
fn strings_live_in_the_arena() {
    let mut arena = arena(8 << 20);
    arena.set_evacuate_all(true);
    let pieces = ["", "plain ascii", "café", "Ārvīds 日本語", "emoji 😀 here"];
    let expected = arena.mutate(|mc| {
        let h = Strings::new(mc);
        let flats: Vec<_> = pieces.iter().map(|p| from_str(&h, p).unwrap()).collect();
        let widths: Vec<_> = flats.iter().map(|&s| width(&h, s)).collect();
        assert_eq!(widths, [Width::One, Width::One, Width::One, Width::Two, Width::Four]);
        let long = repeat(&h, 'x', 2000).unwrap();
        let mut rope = long;
        for &s in flats.iter().cycle().take(40) {
            rope = concat(&h, rope, s).unwrap();
        }
        assert!(!is_flat(&h, rope));
        let middle = substring(&h, rope, 1990, 2030).unwrap();
        let flattened = concat(&h, rope, flats[2]).unwrap();
        flatten(&h, flattened).unwrap();
        let kept = [flats[3], flats[4], rope, middle, flattened];
        for s in kept {
            root(mc).push(mc, s.value()).unwrap();
        }
        assert_eq!(h.string(rope.value()), Some(rope));
        assert_eq!(h.string(Value::TRUE), None);
        kept.map(|s| display(&h, s).to_string())
    });
    arena.collect();
    arena.collect();
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        for (i, want) in expected.iter().enumerate() {
            let s = h.string(root(mc).get(mc, i).unwrap()).unwrap();
            assert_eq!(&display(&h, s).to_string(), want);
            if i == 4 {
                assert_eq!(chunks(&h, s).count(), 1, "reads use the kept flat copy");
            }
            let flat = flatten(&h, s).unwrap();
            assert_eq!(equal(&h, s, flat), Ok(true));
            assert_eq!(flatten(&h, s), Ok(flat));
        }
    });
}

/// Runs the operations that a bot performs on a message, on an external string and on a rope over
/// it. The results survive collections that move them.
#[test]
fn text_operations_work_on_every_kind_of_string() {
    let mut arena = arena(8 << 20);
    arena.set_evacuate_all(true);
    let message = format!("  !Ban @someone {} ", "for being rude".repeat(10));
    let command = message.trim();
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let external = h.external(ExternalText::new(message.clone())).unwrap();
        let rope = concat(&h, string(&h, &"x".repeat(600)), external).unwrap();
        assert!(h.is_external(external) && !is_flat(&h, rope));
        let trimmed = trim(&h, external).unwrap();
        assert_eq!(display(&h, trimmed).to_string(), command);
        let words: Vec<_> = split_whitespace(&h, external).map(Result::unwrap).collect();
        assert_eq!(words.len(), command.split_whitespace().count());
        assert_eq!(compare_ci(&h, words[0], string(&h, "!BAN")), Ok(Ordering::Equal));
        assert_eq!(starts_with(&h, words[1], string(&h, "@")), Ok(true));
        assert_eq!(find(&h, rope, string(&h, "rude"), 0), Ok(command.find("rude").map(|i| i + 600 + 2)));
        assert_eq!(split(&h, rope, string(&h, "rude")).count(), 11);
        let loud = upcase(&h, rope).unwrap();
        assert_eq!(ends_with(&h, loud, string(&h, "RUDE ")), Ok(true));
        assert_eq!(equal(&h, foldcase(&h, loud).unwrap(), downcase(&h, rope).unwrap()), Ok(true));
        for kept in [trimmed, words[1], loud] {
            root(mc).push(mc, kept.value()).unwrap();
        }
    });
    arena.collect_minor();
    arena.collect();
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let got: Vec<String> = (0..3).map(|i| display(&h, h.string(root(mc).get(mc, i).unwrap()).unwrap()).to_string()).collect();
        assert_eq!(got, [command.to_string(), "@someone".to_string(), format!("{}{}", "X".repeat(600), message.to_uppercase())]);
    });
}

/// A Latin-1 string of up to seven characters is an immediate value, not an object. Creating one
/// allocates nothing, equal ones are the same value, and it reads like any other flat string.
#[test]
fn short_strings_live_in_the_word() {
    let mut arena = arena(8 << 20);
    arena.set_evacuate_all(true);
    let texts = ["", "a", "!ping", "café", "1234567", "ÿÿÿÿÿÿÿ"];
    arena.fail_after(Some(0));
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        for &t in &texts {
            let v = from_str(&h, t).unwrap();
            assert!(v.value().immediate().is_some(), "{t:?}");
            assert_eq!(v, from_str(&h, t).unwrap(), "equal ones are the same value");
            assert_eq!((display(&h, v).to_string(), len(&h, v)), (t.to_string(), t.chars().count()));
            assert_eq!(hash(&h, v, 9), Ok(hash_str(t, 9)), "{t:?}");
            assert_eq!(utf8_len(&h, v), Ok(t.len()));
        }
        assert_eq!(from_str(&h, "12345678"), Err(Error::OutOfMemory), "the first allocation is the one that fails");
    });
    arena.fail_after(None);
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        for &t in &texts {
            root(mc).push(mc, string(&h, t).value()).unwrap();
        }
        for t in ["12345678", "Ā", "日本"] {
            assert!(string(&h, t).value().immediate().is_none(), "{t:?}");
        }
        let long = string(&h, &format!("!ban user42 7d spam {}", "and links ".repeat(300)));
        let words: Vec<_> = split(&h, long, string(&h, " ")).take(4).map(Result::unwrap).collect();
        assert_eq!(words, ["!ban", "user42", "7d", "spam"].map(|text| string(&h, text)), "pieces of a longer string");
        assert_eq!(substring(&h, long, 5, 11), Ok(string(&h, "user42")));
        assert_eq!(concat(&h, string(&h, "ab"), string(&h, "cd")), Ok(string(&h, "abcd")));
        assert!(concat(&h, string(&h, "abcd"), string(&h, "efgh")).unwrap().value().immediate().is_none());
        assert_eq!(find(&h, long, string(&h, "links"), 0), Ok(Some(24)));
        assert_eq!(find(&h, string(&h, "!ping"), string(&h, "in"), 0), Ok(Some(2)));
        assert_eq!(rfind(&h, string(&h, "abcabc"), string(&h, "b"), 6), Ok(Some(4)));
        assert_eq!(starts_with(&h, long, string(&h, "!ban u")), Ok(true));
        assert_eq!(upcase(&h, string(&h, "café")), Ok(string(&h, "CAFÉ")));
        assert_eq!(compare_ci(&h, string(&h, "!BAN"), words[0]), Ok(Ordering::Equal));
        assert_eq!(compare(&h, string(&h, "abc"), substring(&h, long, 5, 9).unwrap()), Ok(Ordering::Less));
        assert_eq!(equal_str(&h, string(&h, "café"), "café"), Ok(true));
        assert_eq!(char_at(&h, string(&h, "café"), 3), Ok('é'));
        let rope = concat(&h, long, string(&h, "!")).unwrap();
        let text = format!("{}!", display(&h, long));
        assert!(!is_flat(&h, rope));
        assert_eq!(display(&h, rope).to_string(), text);
        assert_eq!(hash(&h, rope, 3), Ok(hash_str(&text, 3)));
        assert_eq!(equal(&h, rope, flatten(&h, rope).unwrap()), Ok(true));
        assert_eq!(ends_with(&h, rope, string(&h, "links !")), Ok(true));
        root(mc).push(mc, rope.value()).unwrap();
    });
    arena.collect();
    arena.collect();
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        for (i, t) in texts.iter().enumerate() {
            assert_eq!(h.string(root(mc).get(mc, i).unwrap()), Some(from_str(&h, t).unwrap()));
        }
        let rope = h.string(root(mc).get(mc, texts.len()).unwrap()).unwrap();
        assert_eq!(ends_with(&h, rope, from_str(&h, "links !").unwrap()), Ok(true));
    });
}

#[test]
fn parts_join_a_word_at_a_time() {
    arena(8 << 20).mutate(|mc| {
        let h = Strings::new(mc);
        let long = string(&h, "0123456789abcdefghijklmnopqrstuvwxyz0123456789abcdefghijklmnopqrstuvwxyz");
        let external = h.external(ExternalText::new("an external string, long enough to stay outside")).unwrap();
        let outside = h.external(ExternalText::new("an external string that's long enough to be kept outside the arena")).unwrap();
        assert!(h.is_external(outside));
        let cases = [
            (vec![string(&h, "<@"), string(&h, "user"), string(&h, ">")], "<@user>"),
            (vec![string(&h, "ab"), string(&h, ""), string(&h, "cde"), string(&h, "fgh")], "abcdefgh"),
            (vec![string(&h, "caf"), string(&h, "é!")], "café!"),
            (vec![string(&h, "a"), string(&h, "🦀")], "a🦀"),
            (vec![string(&h, "ab"), substring(&h, long, 3, 6).unwrap(), string(&h, "z")], "ab345z"),
            (vec![string(&h, "x"), substring(&h, external, 3, 6).unwrap()], "xext"),
            (vec![string(&h, "x"), concat(&h, long, long).unwrap()], &*format!("x{0}{0}", display(&h, long))),
            (vec![string(&h, "abc"), long, string(&h, "de"), outside, string(&h, "é")], &*format!("abc{}de{}é", display(&h, long), display(&h, outside))),
        ];
        for (parts, want) in cases {
            let joined = concat_all(&h, &parts).unwrap();
            assert_eq!(display(&h, joined).to_string(), want);
            assert_eq!(len(&h, joined), want.chars().count());
        }
    });
}

/// Strings that are created and dropped in the young generation are freed by the next minor
/// collection. The strings that are kept keep their characters.
#[test]
fn young_strings_free_their_characters() {
    let mut arena = arena(8 << 20);
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        for i in 0..10_000 {
            let s = from_str(&h, &format!("message {i}: {}", "é".repeat(i % 50))).unwrap();
            if i % 100 == 0 {
                root(mc).push(mc, s.value()).unwrap();
            }
        }
    });
    arena.collect_minor();
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        for (i, s) in root(mc).iter(mc).enumerate() {
            let want = format!("message {}: {}", i * 100, "é".repeat(i * 100 % 50));
            assert_eq!(display(&h, h.string(s).unwrap()).to_string(), want);
        }
    });
}

#[test]
fn errors_come_back_as_the_crate_error() {
    let mut arena = arena(1 << 20);
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let s = from_str(&h, "abc").unwrap();
        assert_eq!(char_at(&h, s, 3), Err(Error::Str(StrError::OutOfRange)));
        assert_eq!(repeat(&h, 'x', 4 << 20), Err(Error::OutOfMemory));
        // Build a rope that shares one string many times and is too long to flatten in this arena.
        // Searching it and splitting it both need a flat copy.
        let mut big = from_str(&h, "word word ").unwrap();
        for _ in 0..17 {
            big = concat(&h, big, big).unwrap();
        }
        assert_eq!(find(&h, big, s, 0), Err(Error::OutOfMemory));
        let mut words = split_whitespace(&h, big);
        assert_eq!(words.next(), Some(Err(Error::OutOfMemory)));
        assert_eq!(words.next(), None, "an error ends the split");
    });
}

/// External characters that record when they are dropped.
struct Watched(ExternalText<Arc<str>>, Rc<Cell<bool>>);

impl External for Watched {
    fn units(&self) -> Units<'_> {
        self.0.units()
    }
}

impl Drop for Watched {
    fn drop(&mut self) {
        self.1.set(true);
    }
}

/// External characters stay outside the arena while the string is reachable, through moving
/// collections. Their owner is dropped once the string is unreachable.
#[test]
fn external_strings_keep_their_owner_while_reachable() {
    let mut arena = arena(8 << 20);
    arena.set_evacuate_all(true);
    let dropped = [Rc::new(Cell::new(false)), Rc::new(Cell::new(false))];
    let texts: [Arc<str>; 2] = ["a message from discord, long enough to stay outside ".repeat(20).into(), "日本語のメッセージ 😀 ".repeat(20).into()];
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        for (text, dropped) in texts.iter().zip(&dropped) {
            let s = h.external(Watched(ExternalText::new(text.clone()), dropped.clone())).unwrap();
            assert!(h.is_external(s) && is_flat(&h, s));
            let with = concat(&h, from_str(&h, "> ").unwrap(), s).unwrap();
            root(mc).push(mc, s.value()).unwrap();
            root(mc).push(mc, with.value()).unwrap();
        }
        let short = h.external(ExternalText::new("short")).unwrap();
        assert!(!h.is_external(short), "short externals are copied");
        assert_eq!(display(&h, short).to_string(), "short");
    });
    arena.collect();
    arena.collect();
    assert!(dropped.iter().all(|d| !d.get()));
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        for (i, text) in texts.iter().enumerate() {
            let s = h.string(root(mc).get(mc, 2 * i).unwrap()).unwrap();
            assert_eq!(display(&h, s).to_string(), **text);
            let with = h.string(root(mc).get(mc, 2 * i + 1).unwrap()).unwrap();
            assert_eq!(display(&h, with).to_string(), format!("> {text}"));
        }
        root(mc).truncate(mc, 2);
    });
    arena.collect();
    arena.collect();
    assert_eq!(dropped.each_ref().map(|d| d.get()), [false, true], "the second owner went with its strings");
}

#[test]
fn external_characters_stored_wide_are_refused() {
    struct Wide(Vec<u32>);
    impl External for Wide {
        fn units(&self) -> Units<'_> {
            Units::Four(&self.0)
        }
    }
    let mut arena = arena(1 << 20);
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        assert_eq!(h.external(Wide(vec![0x41; 100])), Err(Error::Str(StrError::NotNarrowest)));
        assert!(h.is_external(h.external(Wide(vec![0x1F600; 100])).unwrap()));
    });
}
