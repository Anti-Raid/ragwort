use std::cell::Cell;
use std::cmp::Ordering;
use std::rc::Rc;
use std::sync::Arc;

use super::*;
use crate::{Arena, GcVec, slot};

fn root<'gc>(mc: &Mutation<'gc>) -> GcVec<'gc> {
    GcVec::of(mc.root(0).downcast(mc).unwrap())
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

/// What a bot does to a message, on an external string and a rope over it, and what that makes
/// survives collections that move it.
#[test]
fn text_operations_work_on_every_kind_of_string() {
    let mut arena = arena(8 << 20);
    arena.set_evacuate_all(true);
    let message = format!("  !Ban @someone {} ", "for being rude".repeat(10));
    let command = message.trim();
    arena.mutate(|mc| {
        let h = Strings::new(mc);
        let s = |t: &str| from_str(&h, t).unwrap();
        let external = h.external(ExternalText::new(message.clone())).unwrap();
        let rope = concat(&h, s(&"x".repeat(600)), external).unwrap();
        assert!(h.is_external(external) && !is_flat(&h, rope));
        let trimmed = trim(&h, external).unwrap();
        assert_eq!(display(&h, trimmed).to_string(), command);
        let words: Vec<_> = split_whitespace(&h, external).map(Result::unwrap).collect();
        assert_eq!(words.len(), command.split_whitespace().count());
        assert_eq!(compare_ci(&h, words[0], s("!BAN")), Ok(Ordering::Equal));
        assert_eq!(starts_with(&h, words[1], s("@")), Ok(true));
        assert_eq!(find(&h, rope, s("rude"), 0), Ok(command.find("rude").map(|i| i + 600 + 2)));
        assert_eq!(split(&h, rope, s("rude")).count(), 11);
        let loud = upcase(&h, rope).unwrap();
        assert_eq!(ends_with(&h, loud, s("RUDE ")), Ok(true));
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

/// Strings made and dropped in the young generation go at the next minor collection, and the
/// kept ones keep their characters.
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
        // A rope that shares one string many times, too long to flatten here: searching and
        // splitting it need a flat copy.
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

/// External characters that say when they're dropped.
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
/// collections, and their owner is dropped once it isn't.
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
