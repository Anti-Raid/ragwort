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

/// A string's hash depends on its characters only, and is kept in a flat string object and in an external string without changing what the string reads as.
#[test]
fn a_string_keeps_its_hash() {
    const LONG: &str = "a string that is long enough to be an object, with é and more";
    let mut arena = arena(1 << 22);
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        // The same characters stored five ways: in the word, as an object, as a rope, outside the arena, and wide.
        let object = string(&h, LONG);
        let again = string(&h, LONG);
        let rope = concat(&h, repeat(&h, 'x', 600).unwrap(), object).unwrap();
        let same_rope = concat(&h, string(&h, &"x".repeat(300)), concat(&h, string(&h, &"x".repeat(300)), again).unwrap()).unwrap();
        let padded: Arc<str> = Arc::from(format!("{LONG}{}", " ".repeat(40)));
        let outside = h.external(ExternalText::new(padded.clone())).unwrap();
        let inside = string(&h, &padded);
        assert!(h.is_external(outside) && !h.is_external(inside) && object != again);
        assert_eq!((h.hash(object), h.hash(outside), h.hash(rope)), (h.hash(again), h.hash(inside), h.hash(same_rope)));
        assert_eq!((h.hash(string(&h, "id")), h.hash(string(&h, "wide ← text"))), (h.hash(string(&h, "id")), h.hash(string(&h, "wide ← text"))));
        // Strings with other characters have other hashes, and no hash is 0.
        let hashes = [h.hash(object), h.hash(outside), h.hash(rope), h.hash(string(&h, "id")), h.hash(string(&h, "")), h.hash(string(&h, &LONG[1..]))].map(Result::unwrap);
        for (index, hash) in hashes.iter().enumerate() {
            assert!(*hash != 0 && !hashes[..index].contains(hash), "{hashes:?}");
        }
        // A string that has been hashed reads as before: the hash is beside its length, not in it.
        for (text, expected) in [(object, LONG), (again, LONG), (outside, &*padded), (inside, &*padded)] {
            assert_eq!((len(&h, text), display(&h, text).to_string(), h.hash(text) == h.hash(text)), (expected.chars().count(), expected.to_string(), true));
        }
        assert_eq!(equal(&h, object, again), Ok(true));
        root(mc).push(mc, object.value()).unwrap();
        root(mc).push(mc, outside.value()).unwrap();
    });
    // The hash moves with the string.
    arena.set_evacuate_all(true);
    arena.collect();
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let (object, outside) = (h.string(root(mc).get(mc, 0).unwrap()).unwrap(), h.string(root(mc).get(mc, 1).unwrap()).unwrap());
        assert_eq!((h.hash(object), display(&h, object).to_string(), len(&h, outside)), (h.hash(string(&h, LONG)), LONG.to_string(), LONG.chars().count() + 40));
    });
}

/// A flat string cannot be longer than its length field holds. The request fails before anything is allocated.
#[test]
fn a_flat_string_has_a_longest_length() {
    let mut arena = arena(1 << 20);
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        assert_eq!(h.flat(Width::One, FLAT_MAX + 1, |_| {}).err(), Some(Error::Str(StrError::TooLong)));
        assert_eq!(h.flat(Width::Four, FLAT_MAX + 1, |_| {}).err(), Some(Error::Str(StrError::TooLong)));
    });
}

/// Interning gives one string for each text. A string that is interned first becomes that string as it is, and an equal string interned later is answered with it.
#[test]
fn interning_gives_one_string_for_a_text() {
    const LONG: &str = "a string that is long enough to be an object";
    let mut arena = arena(1 << 22);
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let (first, second) = (string(&h, LONG), string(&h, LONG));
        assert!(first != second && !h.is_interned(first));
        assert_eq!((h.interned(first), h.interned_count()), (Ok(None), 0));
        assert_eq!((h.intern(first), h.is_interned(first), h.is_interned(second)), (Ok(first), true, false));
        // The second string is not registered. Looking it up and interning it both give the first.
        assert_eq!((h.interned(second), h.intern(second), h.is_interned(second), h.intern(first), h.interned_count()), (Ok(Some(first)), Ok(first), false, Ok(first), 1));
        assert_eq!((h.interned(string(&h, &LONG[1..])), h.interned_count()), (Ok(None), 1));
        // A string in the value word is interned as it is, and takes no place in a table.
        let short = string(&h, "id");
        assert_eq!((h.is_interned(short), h.intern(short), h.interned(short), h.interned_count()), (true, Ok(short), Ok(Some(short)), 1));
        // Strings of each width of unit are interned apart. A text has one width, so it is never looked for in two tables.
        let texts = ["Ārvīds and the others, in two-byte units", "an emoji 😀 makes the units four bytes wide", LONG];
        for (number, text) in texts.iter().enumerate() {
            let (made, again) = (string(&h, text), string(&h, text));
            let interned = h.intern(made).unwrap();
            assert_eq!((h.intern(again), h.interned(again), h.is_interned(interned)), (Ok(interned), Ok(Some(interned)), true), "{text}");
            assert_eq!(h.interned_count(), (number + 2).min(3));
        }
        // Interning leaves the string as it reads, and its hash is the hash of any string with its characters.
        assert_eq!((display(&h, first).to_string(), len(&h, first), h.hash(first)), (LONG.to_string(), LONG.len(), h.hash(string(&h, LONG))));
    });
}

/// A rope is interned as its flat copy. A lookup finds the interned string of a rope's text without flattening the rope. An external string is not interned yet.
#[test]
fn ropes_and_external_strings_meet_the_interned_strings() {
    let mut arena = arena(1 << 22);
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let (head, tail) = ("x".repeat(600), "y".repeat(40));
        let rope = concat(&h, string(&h, &head), string(&h, &tail)).unwrap();
        assert!(!is_flat(&h, rope) && !h.is_interned(rope));
        assert_eq!(h.interned(rope), Ok(None));
        assert_eq!(chunks(&h, rope).count(), 2, "a lookup does not flatten the rope");
        let interned = h.intern(rope).unwrap();
        assert!(is_flat(&h, interned) && h.is_interned(interned) && interned != rope);
        assert_eq!((display(&h, interned).to_string(), h.interned_count()), (format!("{head}{tail}"), 1));
        // The rope itself stays a rope. It and every equal string lead to the one interned string.
        let other = concat(&h, string(&h, &head[..300]), concat(&h, string(&h, &head[300..]), string(&h, &tail)).unwrap()).unwrap();
        assert_eq!((h.intern(rope), h.interned(rope), h.interned(other), h.intern(string(&h, &format!("{head}{tail}"))), h.interned_count()), (Ok(interned), Ok(Some(interned)), Ok(Some(interned)), Ok(interned), 1));
        assert!(!h.is_interned(rope) && !is_flat(&h, other));
        // An external string is returned as it is. A lookup still finds an interned string with its characters.
        let text: Arc<str> = Arc::from("external text of a length that is kept outside the arena, well past the limit");
        let outside = h.external(ExternalText::new(text.clone())).unwrap();
        assert!(h.is_external(outside));
        assert_eq!((h.interned(outside), h.intern(outside), h.is_interned(outside), h.interned_count()), (Ok(None), Ok(outside), false, 1));
        let inside = h.intern(string(&h, &text)).unwrap();
        assert_eq!((h.interned(outside), h.interned_count()), (Ok(Some(inside)), 2));
    });
}

/// The arena holds its interned strings weakly. An interned string that nothing refers to is collected, and one that is kept stays interned when it is moved.
#[test]
fn interned_strings_are_held_weakly() {
    const KEPT: &str = "an interned string that the root keeps";
    const DROPPED: &str = "an interned string that nothing keeps";
    let mut arena = arena(1 << 22);
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let kept = h.intern(string(&h, KEPT)).unwrap();
        h.intern(string(&h, DROPPED)).unwrap();
        for number in 0..200 {
            h.intern(string(&h, &format!("a string that is interned and dropped, number {number}"))).unwrap();
        }
        assert_eq!(h.interned_count(), 202);
        root(mc).push(mc, kept.value()).unwrap();
    });
    for _ in 0..2 {
        arena.set_evacuate_all(true);
        arena.collect();
        arena.mutate(|mc| {
            let h = Strings::new(mc);
            let kept = h.string(root(mc).get(mc, 0).unwrap()).unwrap();
            assert_eq!((h.interned_count(), h.is_interned(kept), display(&h, kept).to_string()), (1, true, KEPT.to_string()));
            assert_eq!((h.intern(string(&h, KEPT)), h.interned(string(&h, KEPT)), h.interned(string(&h, DROPPED))), (Ok(kept), Ok(Some(kept)), Ok(None)));
            // The dropped text is interned again, as a new string.
            let again = h.intern(string(&h, DROPPED)).unwrap();
            assert_eq!((h.is_interned(again), h.interned_count(), h.intern(string(&h, DROPPED))), (true, 2, Ok(again)));
        });
    }
}

