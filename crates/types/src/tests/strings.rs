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
        // A flat string is interned when it is made, so making the same text again gives the same string.
        assert!(h.is_external(outside) && !h.is_external(inside) && object == again);
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

/// The arena has one flat string for each text. Making a text again gives the string that is there, whatever the width of its characters.
#[test]
fn a_text_has_one_flat_string() {
    const LONG: &str = "a string that is long enough to be an object";
    let mut arena = arena(1 << 22);
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        assert_eq!(h.interned_count(), 0);
        let (first, second) = (string(&h, LONG), string(&h, LONG));
        assert!(first == second && h.is_interned(first));
        assert_eq!((h.intern(first), h.interned(first), h.interned_count()), (Ok(first), Ok(Some(first)), 1));
        // Strings that are made in other ways are the same string too: a copy of a part, a repeated character, a join that is short enough to be flat.
        let parts = concat(&h, string(&h, &LONG[..20]), string(&h, &LONG[20..])).unwrap();
        let cut = substring(&h, string(&h, &format!("--{LONG}--")), 2, 2 + LONG.len()).unwrap();
        assert_eq!((parts, cut, repeat(&h, 'x', 30)), (first, first, Ok(string(&h, &"x".repeat(30)))));
        // A string in the value word is interned as it is, and takes no place in a table.
        let before = h.interned_count();
        let short = string(&h, "id");
        assert_eq!((h.is_interned(short), h.intern(short), h.interned(short), h.interned_count()), (true, Ok(short), Ok(Some(short)), before));
        // Strings of each width of unit are interned apart. A text has one width, so it is never looked for in two tables.
        for text in ["Ārvīds and the others, in two-byte units", "an emoji 😀 makes the units four bytes wide"] {
            let before = h.interned_count();
            let (made, again) = (string(&h, text), string(&h, text));
            assert_eq!((made, h.intern(again), h.interned(again), h.is_interned(made), h.interned_count()), (again, Ok(made), Ok(Some(made)), true, before + 1), "{text}");
        }
        // Two flat strings with other characters are other strings, and are told apart without a look at their characters.
        let other = string(&h, &LONG.replace("long", "wide"));
        assert_eq!((equal(&h, first, other), equal(&h, first, second), len(&h, other) == len(&h, first)), (Ok(false), Ok(true), true));
        assert_eq!((display(&h, first).to_string(), len(&h, first), h.hash(first)), (LONG.to_string(), LONG.len(), h.hash(string(&h, LONG))));
    });
}

/// A rope is interned as its flat copy when it is first compared with a string of its length, or interned by name. It then reads as that copy and lets go of its halves. An external string is not interned yet.
#[test]
fn ropes_and_external_strings_meet_the_interned_strings() {
    let mut arena = arena(1 << 22);
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let (head, tail) = ("x".repeat(600), "y".repeat(40));
        let rope = concat(&h, string(&h, &head), string(&h, &tail)).unwrap();
        assert!(!is_flat(&h, rope) && !h.is_interned(rope));
        // A lookup finds nothing, and leaves the rope as it is. So does a comparison with a string of another length.
        assert_eq!((h.interned(rope), equal(&h, rope, string(&h, &head)), chunks(&h, rope).count()), (Ok(None), Ok(false), 2));
        let before = h.interned_count();
        let interned = h.intern(rope).unwrap();
        assert!(is_flat(&h, interned) && h.is_interned(interned) && interned != rope);
        assert_eq!((display(&h, interned).to_string(), h.interned_count()), (format!("{head}{tail}"), before + 1));
        // The rope reads as its flat copy from now on, and every string with its characters leads to the one interned string.
        assert_eq!((h.intern(rope), h.interned(rope), flatten(&h, rope), chunks(&h, rope).count(), equal(&h, rope, interned)), (Ok(interned), Ok(Some(interned)), Ok(interned), 1, Ok(true)));
        assert_eq!((string(&h, &format!("{head}{tail}")), h.interned_count()), (interned, before + 1));
        // Another rope with the same characters is found by a lookup without being flattened. A comparison with a string of its length flattens it, and it then stands for the same interned string.
        let other = concat(&h, string(&h, &head[..300]), concat(&h, string(&h, &head[300..]), string(&h, &tail)).unwrap()).unwrap();
        assert_eq!((h.interned(other), is_flat(&h, other)), (Ok(Some(interned)), false));
        assert_eq!((equal(&h, other, rope), is_flat(&h, other), h.intern(other), h.interned_count()), (Ok(true), true, Ok(interned), h.interned_count()));
        // An external string is returned as it is, and is compared by its characters. A lookup finds an interned string with its characters.
        let text: Arc<str> = Arc::from("external text of a length that is kept outside the arena, well past the limit");
        let outside = h.external(ExternalText::new(text.clone())).unwrap();
        assert!(h.is_external(outside));
        assert_eq!((h.interned(outside), h.intern(outside), h.is_interned(outside)), (Ok(None), Ok(outside), false));
        let inside = string(&h, &text);
        assert_eq!((h.interned(outside), equal(&h, outside, inside), equal(&h, outside, interned), inside == outside), (Ok(Some(inside)), Ok(true), Ok(false), false));
    });
}

/// A flattened rope lets go of its halves: once it is flattened, the halves are collected if nothing else holds them.
#[test]
fn a_flattened_rope_keeps_its_characters_once() {
    let mut arena = arena(1 << 22);
    let before = arena.mutate(|mc| {
        let h = Strings::new(mc);
        let rope = concat(&h, string(&h, &"left ".repeat(200)), string(&h, &"right ".repeat(200))).unwrap();
        assert!(!is_flat(&h, rope));
        root(mc).push(mc, rope.value()).unwrap();
        h.interned_count()
    });
    assert_eq!(before, 2);
    arena.collect();
    // The rope and its two halves are alive.
    arena.mutate(|mc| assert_eq!(Strings::new(mc).interned_count(), 2));
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let rope = h.string(root(mc).get(mc, 0).unwrap()).unwrap();
        let flat = h.intern(rope).unwrap();
        assert_eq!((len(&h, flat), h.interned_count(), is_flat(&h, rope)), (2200, 3, true));
    });
    arena.collect();
    arena.collect();
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let rope = h.string(root(mc).get(mc, 0).unwrap()).unwrap();
        // Only the flat copy is left. The rope still reads as before.
        assert_eq!((h.interned_count(), len(&h, rope), display(&h, rope).to_string()), (1, 2200, format!("{}{}", "left ".repeat(200), "right ".repeat(200))));
    });
}

/// The arena holds its interned strings weakly. A string that nothing refers to is collected, and one that is kept stays interned when it is moved.
#[test]
fn interned_strings_are_held_weakly() {
    const KEPT: &str = "an interned string that the root keeps";
    const DROPPED: &str = "an interned string that nothing keeps";
    let mut arena = arena(1 << 22);
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let kept = string(&h, KEPT);
        string(&h, DROPPED);
        for number in 0..200 {
            string(&h, &format!("a string that is made and dropped, number {number}"));
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
            assert_eq!((string(&h, KEPT), h.interned_count()), (kept, 1));
            // The dropped text is made again, as a new string.
            let again = string(&h, DROPPED);
            assert_eq!((h.is_interned(again), h.interned_count(), string(&h, DROPPED)), (true, 2, again));
        });
    }
}

/// An interned string stays the one string of its text while its neighbors in the table die and their slots are taken again. The check runs over several collections, with strings of both lengths that are looked up before and after they are allocated.
#[test]
fn interned_strings_outlive_their_neighbors() {
    const COUNT: usize = 6000;
    fn text(number: usize, round: usize) -> String {
        // One string in eight is longer than the buffer that short strings are built in.
        let filler = if number % 8 == 0 { "long ".repeat(120) } else { String::new() };
        format!("string {number} of round {round}, {filler}é")
    }
    let mut arena = arena(64 << 20);
    for round in 0..4 {
        arena.mutate(|mc| {
            let h = Strings::new(mc);
            let kept = root(mc);
            // The strings that the rounds before have kept are still the strings of their texts.
            for index in 0..kept.len(mc) {
                let held = h.string(kept.get(mc, index).unwrap()).unwrap();
                let again = string(&h, &display(&h, held).to_string());
                assert!(again == held && h.is_interned(held), "round {round}, string {index}");
            }
            let before = h.interned_count();
            assert_eq!(before, kept.len(mc), "round {round}");
            // Every third new string is kept. The others die at the next collection.
            for number in 0..COUNT {
                let made = string(&h, &text(number, round));
                assert_eq!(string(&h, &text(number, round)), made);
                if number % 3 == 0 {
                    kept.push(mc, made.value()).unwrap();
                }
            }
            assert_eq!(h.interned_count(), before + COUNT);
        });
        arena.set_evacuate_all(round % 2 == 0);
        arena.collect();
        arena.collect();
    }
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        assert_eq!((h.interned_count(), root(mc).len(mc)), (4 * COUNT / 3, 4 * COUNT / 3));
        // A text whose string died is made again, once.
        let made = string(&h, &text(1, 0));
        assert_eq!((string(&h, &text(1, 0)), h.interned_count()), (made, 4 * COUNT / 3 + 1));
    });
}

