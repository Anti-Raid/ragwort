use std::cmp::Ordering;

use crate::testing::{Rng, TestHost, TestStr, shapes};
use crate::*;

fn text_of(h: &TestHost, s: TestStr) -> String {
    chars(h, s).collect()
}

#[test]
fn case_maps_like_char() {
    let h = TestHost::with_capacity(1 << 20);
    let mut rng = Rng(21);
    for _ in 0..1500 {
        let text = match rng.below(3) {
            0 => {
                let n = rng.below(30);
                (0..n).map(|_| char::from(0x20 + rng.below(0x60) as u8)).collect()
            }
            _ => rng.text(),
        };
        let want_up: String = text.iter().flat_map(|c| c.to_uppercase()).collect();
        let want_down: String = text.iter().flat_map(|c| c.to_lowercase()).collect();
        for s in shapes(&h, &text, rng.below(text.len() + 1)) {
            let (up, down, fold) = (upcase(&h, s).unwrap(), downcase(&h, s).unwrap(), foldcase(&h, s).unwrap());
            h.check(up);
            assert_eq!(text_of(&h, up), want_up);
            assert_eq!(text_of(&h, down), want_down);
            // Folding forgets case, except for dotless ı, which folds to itself but uppercases to I.
            if !text.contains(&'ı') {
                let fold_text = text_of(&h, fold);
                assert_eq!(text_of(&h, foldcase(&h, up).unwrap()), fold_text);
                assert_eq!(text_of(&h, foldcase(&h, down).unwrap()), fold_text);
                assert_eq!(compare_ci(&h, s, up), Ok(Ordering::Equal));
            }
        }
    }
}

#[test]
fn ascii_case_maps_at_the_edges_of_the_letters() {
    let h = TestHost::new();
    let text = "@AZ[`az{ 09 ~\x7f\0 mixed Case, longer than a word";
    // Made one after the other, so they're in both of the test host's layouts.
    for s in [from_str(&h, text).unwrap(), from_str(&h, text).unwrap()] {
        assert_eq!(text_of(&h, upcase(&h, s).unwrap()), "@AZ[`AZ{ 09 ~\x7f\0 MIXED CASE, LONGER THAN A WORD");
        assert_eq!(text_of(&h, downcase(&h, s).unwrap()), "@az[`az{ 09 ~\x7f\0 mixed case, longer than a word");
        assert_eq!(text_of(&h, foldcase(&h, s).unwrap()), "@az[`az{ 09 ~\x7f\0 mixed case, longer than a word");
    }
}

#[test]
fn folding_follows_unicode() {
    let h = TestHost::new();
    for (text, folded) in [
        ("Straße", "strasse"),
        ("STRAẞE", "strasse"),
        ("ΣΊΣΥΦΟΣ", "σίσυφοσ"),
        ("ſ K Å µ", "s k å μ"),
        ("ﬁ ǅ", "fi ǆ"),
        ("İı", "i\u{307}ı"),
        ("Ꭰꭰᏸ", "ᎠᎠᏰ"),
    ] {
        assert_eq!(text_of(&h, foldcase(&h, from_str(&h, text).unwrap()).unwrap()), folded, "{text}");
    }
}

#[test]
fn unchanged_strings_come_back_as_they_are() {
    let h = TestHost::new();
    for text in ["already lower", "ünïcode ok", ""] {
        let s = from_str(&h, text).unwrap();
        assert_eq!(downcase(&h, s), Ok(s));
        assert_eq!(foldcase(&h, s), Ok(s));
    }
    let s = from_str(&h, "SHOUT 123").unwrap();
    assert_eq!(upcase(&h, s), Ok(s));
}

#[test]
fn caseless_comparison_orders_by_the_folds() {
    let h = TestHost::with_capacity(1 << 20);
    let mut rng = Rng(23);
    let mut pool: Vec<(TestStr, String)> = Vec::new();
    for _ in 0..1500 {
        let text: Vec<char> = if rng.below(2) == 0 {
            rng.text()
        } else {
            let n = rng.below(5);
            (0..n).map(|_| ['a', 'B', 'c', 'D', 'A'][rng.below(5)]).collect()
        };
        let s = shapes(&h, &text, rng.below(text.len() + 1))[rng.below(if text.len() >= 2 { 4 } else { 2 })];
        let fold = text_of(&h, foldcase(&h, s).unwrap());
        for (t, other) in pool.iter().rev().take(8) {
            assert_eq!(compare_ci(&h, s, *t), Ok(fold.chars().cmp(other.chars())), "{text:?} vs {other:?}");
        }
        pool.push((s, fold));
    }
    let (a, b) = (from_str(&h, "Hello").unwrap(), from_str(&h, "hELLO world").unwrap());
    assert_eq!(compare_ci(&h, a, b), Ok(Ordering::Less));
    assert_eq!(compare_ci(&h, from_str(&h, "B").unwrap(), from_str(&h, "a").unwrap()), Ok(Ordering::Greater));
}
