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

/// Flat strings with characters of each size and ropes over them survive collections that move them.
#[test]
fn strings_live_in_the_arena() {
    let mut arena = arena(8 << 20);
    arena.set_evacuate_all(true);
    let pieces = ["", "plain ascii", "café", "Ārvīds 日本語", "emoji 😀 here"];
    let expected = arena.mutate(|mc| {
        let h = Strings::new(mc);
        let flats: Vec<_> = pieces.iter().map(|p| from_str(&h, p).unwrap()).collect();
        let sizes: Vec<_> = flats.iter().map(|&s| (byte_len(&h, s), len(&h, s))).collect();
        assert_eq!(sizes, [(0, 0), (11, 11), (5, 4), (18, 10), (15, 12)]);
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
            let again = flatten(&h, s).unwrap();
            assert_eq!((is_flat(&h, again), equal(&h, again, flat)), (true, Ok(true)));
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

/// A string of up to seven bytes is an immediate value, not an object. Creating one
/// allocates nothing, equal ones are the same value, and it reads like any other flat string.
#[test]
fn short_strings_live_in_the_word() {
    let mut arena = arena(8 << 20);
    arena.set_evacuate_all(true);
    let texts = ["", "a", "!ping", "café", "1234567", "ÿÿÿa", "😀é", "日本"];
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
        // A string of eight bytes or more is an object, however few characters it has.
        for t in ["12345678", "ÿÿÿÿ", "日本語", "😀😀"] {
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
    fn text(&self) -> &str {
        self.0.text()
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

/// An external string holds text of any characters as the host has it. Its characters are counted when it is first read.
#[test]
fn external_text_of_any_characters_stays_outside() {
    let mut arena = arena(1 << 20);
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let text: Arc<str> = Arc::from("😀 é ".repeat(20));
        let outside = h.external(ExternalText::new(text.clone())).unwrap();
        assert!(h.is_external(outside));
        assert_eq!((len(&h, outside), byte_len(&h, outside), display(&h, outside).to_string()), (80, 160, text.to_string()));
        assert_eq!((char_at(&h, outside, 0), char_at(&h, outside, 2), char_at(&h, outside, 78), char_at(&h, outside, 80).is_err()), (Ok('😀'), Ok('é'), Ok('é'), true));
        assert_eq!(substring(&h, outside, 4, 8).map(|part| display(&h, part).to_string()), Ok("😀 é ".to_string()));
        // The host gets the text of an external string back as it is, with no copy. A string in the arena is copied out.
        let inside = string(&h, "text that the arena holds");
        assert_eq!((h.as_str(outside), h.as_str(inside), h.as_str(string(&h, "id"))), (Some(&*text), None, None));
        assert_eq!((to_string(&h, outside), to_string(&h, inside)), (text.to_string(), "text that the arena holds".to_string()));
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
        assert_eq!(h.flat(FLAT_MAX + 1, FLAT_MAX + 1, |_| {}).err(), Some(Error::Str(StrError::TooLong)));
        assert_eq!(h.flat(FLAT_MAX + 1, 1, |_| {}).err(), Some(Error::Str(StrError::TooLong)));
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

/// A rope is interned as it is when it is first compared with a string of its length, or interned by name. It keeps its halves. A flat string that is made with its characters afterwards becomes its flat copy. An external string is not interned yet.
#[test]
fn ropes_and_external_strings_meet_the_interned_strings() {
    let mut arena = arena(1 << 22);
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let (head, tail) = ("x".repeat(600), "y".repeat(40));
        let rope = concat(&h, string(&h, &head), string(&h, &tail)).unwrap();
        assert!(!is_flat(&h, rope) && !h.is_interned(rope));
        // A lookup finds nothing, and leaves the rope as it is. So does a comparison with a string of another length.
        assert_eq!((h.interned(rope), equal(&h, rope, string(&h, &head)), h.is_interned(rope)), (Ok(None), Ok(false), false));
        let before = h.interned_count();
        let interned = h.intern(rope).unwrap();
        // The rope itself is the interned string. Nothing was copied: it still has its two halves.
        assert!(interned == rope && h.is_interned(rope) && !is_flat(&h, rope));
        assert_eq!((chunks(&h, rope).count(), h.interned_count(), h.intern(rope), h.interned(rope), h.hash(rope)), (2, before + 1, Ok(rope), Ok(Some(rope)), h.hash(rope)));
        // Another rope with the same characters is found by a lookup, which leaves it as it is. A comparison makes it read as the interned rope.
        let other = concat(&h, string(&h, &head), string(&h, &tail)).unwrap();
        assert_eq!((h.interned(other), h.is_interned(other), other == rope), (Ok(Some(rope)), false, false));
        assert_eq!((equal(&h, other, rope), h.intern(other), h.interned(other), chunks(&h, other).count(), h.interned_count()), (Ok(true), Ok(rope), Ok(Some(rope)), 2, before + 1));
        assert_eq!((display(&h, other).to_string(), h.hash(other)), (format!("{head}{tail}"), h.hash(rope)));
        // A long flat string that is made with these characters is a string of its own, outside the arena. It is not interned until it is compared, and then it leads to the rope.
        let made = string(&h, &format!("{head}{tail}"));
        assert!(made != rope && is_flat(&h, made) && h.is_external(made) && !h.is_interned(made));
        assert_eq!((h.interned(made), equal(&h, made, rope), h.intern(made), h.is_interned(made), h.interned_count()), (Ok(Some(rope)), Ok(true), Ok(rope), false, before + 1));
        // The rope stays the interned string when it is flattened, and reads as a flat string from then on.
        assert_eq!((flatten(&h, rope).map(|flat| is_flat(&h, flat)), is_flat(&h, rope), is_flat(&h, other), h.is_interned(rope), h.intern(rope)), (Ok(true), true, true, true, Ok(rope)));
        assert_eq!((h.interned_count(), equal(&h, other, made), display(&h, rope).to_string()), (before + 1, Ok(true), format!("{head}{tail}")));
        // A rope that is deeper than the interned string reads as it too. A rope with other characters of the same length does not.
        let deeper = concat(&h, string(&h, &head[..300]), concat(&h, string(&h, &head[300..]), string(&h, &tail)).unwrap()).unwrap();
        let unlike = concat(&h, string(&h, &head), string(&h, &"z".repeat(40))).unwrap();
        let count = h.interned_count();
        assert_eq!((equal(&h, deeper, rope), h.intern(deeper), is_flat(&h, deeper), h.interned_count()), (Ok(true), Ok(rope), true, count));
        assert_eq!((equal(&h, unlike, rope), h.intern(unlike), is_flat(&h, unlike), h.interned_count()), (Ok(false), Ok(unlike), false, count + 1));
        let interned = rope;
        // An external string is not interned when it is made. A lookup finds nothing and leaves it as it is.
        let text: Arc<str> = Arc::from("external text of a length that is kept outside the arena, well past the limit");
        let outside = h.external(ExternalText::new(text.clone())).unwrap();
        let count = h.interned_count();
        assert!(h.is_external(outside));
        assert_eq!((h.interned(outside), h.is_interned(outside), equal(&h, outside, interned), h.is_interned(outside), h.interned_count()), (Ok(None), false, Ok(false), false, count));
        // Interned, it is the interned string itself, and its characters stay outside. A flat string that is made with them afterwards is the external string.
        assert_eq!((h.intern(outside), h.is_interned(outside), h.is_external(outside), h.interned_count()), (Ok(outside), true, true, count + 1));
        assert_eq!((string(&h, &text), h.interned(outside), h.interned_count()), (outside, Ok(Some(outside)), count + 1));
        // A second external string with the same characters leads to the first, and stays as it is.
        let second = h.external(ExternalText::new(text.clone())).unwrap();
        assert_eq!((equal(&h, second, outside), h.intern(second), h.interned(second), h.is_interned(second), second == outside, h.interned_count()), (Ok(true), Ok(outside), Ok(Some(outside)), false, false, count + 1));
        // Where the flat string was made first, it is the interned string, and a comparison with an external string finds it.
        let other: Arc<str> = Arc::from("another external text, which the arena has as a flat string before it arrives");
        let inside = string(&h, &other);
        let late = h.external(ExternalText::new(other.clone())).unwrap();
        assert_eq!((equal(&h, late, inside), h.intern(late), h.is_interned(late), equal(&h, late, outside), h.interned_count()), (Ok(true), Ok(inside), false, Ok(false), count + 2));
        // A comparison of an external string with a string of its length interns it. A rope with its characters then reads as it.
        let long: Arc<str> = Arc::from(format!("{head}{}", "w".repeat(40)));
        let wide = h.external(ExternalText::new(long.clone())).unwrap();
        assert_eq!((equal(&h, wide, rope), h.is_interned(wide)), (Ok(false), true));
        let joined = concat(&h, string(&h, &head), string(&h, &"w".repeat(40))).unwrap();
        assert_eq!((equal(&h, joined, wide), h.intern(joined), is_flat(&h, joined), display(&h, joined).to_string()), (Ok(true), Ok(wide), true, long.to_string()));
    });
}

/// An interned rope keeps its halves until it is flattened. Once it is flattened, the halves are collected if nothing else holds them, and the rope is still the interned string.
/// The halves and the flat copy are long strings, so each has a store outside the arena. The number of stores shows which of them are alive.
#[test]
fn a_flattened_rope_keeps_its_characters_once() {
    let mut arena = arena(1 << 22);
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let rope = concat(&h, string(&h, &"left ".repeat(200)), string(&h, &"right ".repeat(200))).unwrap();
        assert!(!is_flat(&h, rope));
        root(mc).push(mc, rope.value()).unwrap();
        // Long strings are not interned when they are made.
        assert_eq!(h.interned_count(), 0);
    });
    arena.collect();
    arena.collect();
    arena.mutate(|_| {});
    // The two halves are alive.
    assert_eq!(arena.frozen_values(), 2);
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let rope = h.string(root(mc).get(mc, 0).unwrap()).unwrap();
        assert_eq!((h.intern(rope), len(&h, rope), h.interned_count(), is_flat(&h, rope)), (Ok(rope), 2200, 1, false));
    });
    arena.collect();
    arena.collect();
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let rope = h.string(root(mc).get(mc, 0).unwrap()).unwrap();
        // The interned rope has kept its halves.
        assert_eq!((h.interned_count(), is_flat(&h, rope), h.is_interned(rope)), (1, false, true));
        // The flat copy belongs to the rope. It is not one more interned string.
        assert_eq!((flatten(&h, rope).map(|flat| is_flat(&h, flat)), is_flat(&h, rope), h.interned_count()), (Ok(true), true, 1));
    });
    arena.set_evacuate_all(true);
    arena.collect();
    arena.collect();
    arena.mutate(|_| {});
    // Only the store of the flat copy is left.
    assert_eq!(arena.frozen_values(), 1);
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let rope = h.string(root(mc).get(mc, 0).unwrap()).unwrap();
        let text = format!("{}{}", "left ".repeat(200), "right ".repeat(200));
        // The rope is still the interned string, and it reads as before. A string that is made with its characters leads to it.
        assert_eq!((h.interned_count(), len(&h, rope), display(&h, rope).to_string(), h.is_interned(rope)), (1, 2200, text.clone(), true));
        assert_eq!((h.intern(string(&h, &text)), h.interned(rope), h.interned_count()), (Ok(rope), Ok(Some(rope)), 1));
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
        let filler = if number.is_multiple_of(8) { "long ".repeat(120) } else { String::new() };
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
                let again = h.intern(string(&h, &display(&h, held).to_string())).unwrap();
                assert!(again == held && h.is_interned(held), "round {round}, string {index}");
            }
            let before = h.interned_count();
            assert_eq!(before, kept.len(mc), "round {round}");
            // Every third new string is kept. The others die at the next collection.
            // A short string is interned when it is made. A long one, which lives outside the arena, is interned here.
            for number in 0..COUNT {
                let made = h.intern(string(&h, &text(number, round))).unwrap();
                assert_eq!(h.intern(string(&h, &text(number, round))), Ok(made));
                if number.is_multiple_of(3) {
                    kept.push(mc, made.value()).unwrap();
                }
            }
            assert_eq!(h.interned_count(), before + COUNT);
        });
        arena.set_evacuate_all(round.is_multiple_of(2));
        arena.collect();
        arena.collect();
    }
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        assert_eq!((h.interned_count(), root(mc).len(mc)), (4 * COUNT / 3, 4 * COUNT / 3));
        // A text whose string died is made again, once.
        let made = string(&h, &text(1, 0));
        assert_eq!((string(&h, &text(1, 0)), h.interned_count()), (made, 4 * COUNT / 3 + 1));
        // The same holds for a long text, once it is interned.
        let long = h.intern(string(&h, &text(8, 0))).unwrap();
        assert_eq!((h.intern(string(&h, &text(8, 0))), h.interned_count()), (Ok(long), 4 * COUNT / 3 + 2));
    });
}

/// A flat string object has the hash that its text has as a `&str`, at every length around the limits between the three forms of the hash, and at each width of unit.
#[test]
fn a_flat_string_hashes_as_its_text() {
    let mut arena = arena(1 << 22);
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let seed = Symbols::of_arena(mc).unwrap().seed(mc);
        let mut seen = std::collections::HashSet::new();
        for widest in ['w', 'é', 'Ā', '😀'] {
            for count in 8..=70 {
                let text: String = (0..count).map(|index| if index == count / 2 { widest } else { char::from(b'a' + (index % 26) as u8) }).collect();
                let made = string(&h, &text);
                assert_eq!(h.hash(made), Ok(narrowed(hash_str(&text, seed))), "{count} characters with {widest}");
                assert!(seen.insert(h.hash(made).unwrap()), "{count} characters with {widest}");
            }
        }
        // Changing any one character of a string of 17 to 32 bytes changes the hash.
        let text = "seventeen to thirty-two bytes";
        for index in 0..text.len() {
            let mut other = text.as_bytes().to_vec();
            other[index] ^= 1;
            assert_ne!(h.hash(string(&h, std::str::from_utf8(&other).unwrap())), h.hash(string(&h, text)), "character {index}");
        }
    });
}

/// A long flat string lives in a store outside the arena, and is a view of it. A large part of it is a view of the same store, and a small part is copied.
#[test]
fn long_strings_are_views_of_a_store() {
    let mut arena = arena(1 << 22);
    let text = format!("{} ünd 😀 {}", "a long line of text. ".repeat(60), "the end of it. ".repeat(40));
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let whole = string(&h, &text);
        assert!(h.is_external(whole) && is_flat(&h, whole) && !h.is_interned(whole));
        assert_eq!((h.as_str(whole), len(&h, whole), byte_len(&h, whole)), (Some(&*text), text.chars().count(), text.len()));
        root(mc).push(mc, whole.value()).unwrap();
        // More than half of the string: a view of the same store. Its characters are found from character positions.
        let chars: Vec<char> = text.chars().collect();
        let large = substring(&h, whole, 100, chars.len() - 50).unwrap();
        let expected: String = chars[100..chars.len() - 50].iter().collect();
        assert!(h.is_external(large));
        assert_eq!((h.as_str(large), len(&h, large), char_at(&h, large, 3)), (Some(&*expected), expected.chars().count(), Ok(chars[103])));
        root(mc).push(mc, large.value()).unwrap();
        // A part of a part shares too, while it is at least half of the store.
        let inner = substring(&h, large, 10, len(&h, large) - 10).unwrap();
        assert!(h.is_external(inner) && equal_str(&h, inner, &expected.chars().skip(10).take(expected.chars().count() - 20).collect::<String>()) == Ok(true));
        root(mc).push(mc, inner.value()).unwrap();
        // Less than half: a copy. A short copy is a string in the arena, and a long one gets a store of its own.
        let short = substring(&h, whole, 0, 40).unwrap();
        let third = substring(&h, whole, 0, chars.len() / 3).unwrap();
        assert!(!h.is_external(short) && h.is_interned(short) && h.is_external(third));
        assert_eq!((display(&h, short).to_string(), display(&h, third).to_string()), (chars[..40].iter().collect::<String>(), chars[..chars.len() / 3].iter().collect::<String>()));
        root(mc).push(mc, third.value()).unwrap();
    });
    arena.set_evacuate_all(true);
    arena.collect();
    arena.collect();
    arena.mutate(|_| {});
    // Two stores: the one of the whole string, which its two parts share, and the one of the copied third.
    assert_eq!(arena.frozen_values(), 2);
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let whole = h.string(root(mc).get(mc, 0).unwrap()).unwrap();
        let large = h.string(root(mc).get(mc, 1).unwrap()).unwrap();
        assert_eq!((h.as_str(whole), display(&h, large).to_string() == text.chars().skip(100).take(text.chars().count() - 150).collect::<String>()), (Some(&*text), true));
        // The whole string is dropped. Its store stays, because the parts read from it.
        root(mc).set(mc, 0, Value::FALSE);
    });
    arena.collect();
    arena.collect();
    arena.mutate(|_| {});
    assert_eq!(arena.frozen_values(), 2);
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let large = h.string(root(mc).get(mc, 1).unwrap()).unwrap();
        assert!(h.as_str(large).is_some_and(|part| text.contains(part)));
    });
}

/// A text that the arena is given twice is kept once: when the second string meets the first, it is pointed at the same store, and its own store is freed.
#[test]
fn equal_long_strings_come_to_share_a_store() {
    let mut arena = arena(1 << 22);
    let text: Arc<str> = Arc::from("the same payload text, given to the arena twice. ".repeat(30));
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let first = h.external(ExternalText::new(text.clone())).unwrap();
        let second = h.external(ExternalText::new(text.clone())).unwrap();
        let made = string(&h, &text);
        for kept in [first, second, made] {
            root(mc).push(mc, kept.value()).unwrap();
        }
        assert_eq!((equal(&h, first, second), equal(&h, made, first), h.intern(second), h.intern(made), h.interned_count()), (Ok(true), Ok(true), Ok(first), Ok(first), 1));
        // The three are still three strings, and each reads the text.
        assert!(first != second && second != made && h.is_interned(first) && !h.is_interned(second));
        assert_eq!((h.as_str(first), h.as_str(second), h.as_str(made), equal(&h, second, made)), (Some(&*text), Some(&*text), Some(&*text), Ok(true)));
    });
    arena.collect();
    arena.collect();
    arena.mutate(|_| {});
    assert_eq!(arena.frozen_values(), 1);
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        for index in 0..3 {
            let kept = h.string(root(mc).get(mc, index).unwrap()).unwrap();
            assert_eq!((h.as_str(kept), len(&h, kept)), (Some(&*text), text.len()));
        }
    });
}

/// The text in a large part of an external bytevector becomes a string without a copy: the string reads from the store of the bytevector. A small part is copied, and bytes that are no text are refused.
#[test]
fn text_in_an_external_bytevector_is_shared() {
    use crate::bytevector::Bytevectors;
    let mut arena = arena(1 << 22);
    let payload: Vec<u8> = format!("{{\"content\": \"{}\", \"tail\": \"é😀\"}}", "words of a message ".repeat(20)).into_bytes();
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let bytes = Bytevectors::new(mc).external(payload.clone()).unwrap();
        let whole = h.from_utf8_of(bytes, 0, payload.len()).unwrap();
        let content = h.from_utf8_of(bytes, 13, payload.len() - 20).unwrap();
        let key = h.from_utf8_of(bytes, 2, 9).unwrap();
        assert!(h.is_external(whole) && h.is_external(content) && !h.is_external(key));
        assert_eq!((h.as_str(whole), h.as_str(content), display(&h, key).to_string()), (std::str::from_utf8(&payload).ok(), std::str::from_utf8(&payload[13..payload.len() - 20]).ok(), "content".to_string()));
        assert_eq!((len(&h, whole), byte_len(&h, whole)), (std::str::from_utf8(&payload).unwrap().chars().count(), payload.len()));
        // A range that cuts the last character holds no text.
        assert_eq!(h.from_utf8_of(bytes, 0, payload.len() - 4).err(), Some(Error::Str(StrError::NotUtf8)));
        for kept in [whole, content] {
            root(mc).push(mc, kept.value()).unwrap();
        }
    });
    arena.collect();
    arena.collect();
    arena.mutate(|_| {});
    // The bytevector is gone, and its store is alive: the two strings read from it.
    assert_eq!(arena.frozen_values(), 1);
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let content = h.string(root(mc).get(mc, 1).unwrap()).unwrap();
        assert_eq!(h.as_str(content), std::str::from_utf8(&payload[13..payload.len() - 20]).ok());
    });
}

