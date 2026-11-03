use crate::testing::{Rng, TestError, TestHost, TestStr, shapes};
use crate::*;

fn naive(text: &[char], pattern: &[char], from: usize) -> Option<usize> {
    (from..=text.len().checked_sub(pattern.len())?).find(|&i| text[i..i + pattern.len()] == *pattern)
}

fn naive_last(text: &[char], pattern: &[char], to: usize) -> Option<usize> {
    (0..=to.checked_sub(pattern.len())?).rev().find(|&i| text[i..i + pattern.len()] == *pattern)
}

/// Mostly two letters, so patterns often match in part, and now and then a wider one.
fn few_letters(rng: &mut Rng, len: usize) -> Vec<char> {
    let letters = ['a', 'b', 'c', 'Ā', '😀'];
    (0..len).map(|_| letters[if rng.below(8) == 0 { rng.below(5) } else { rng.below(2) }]).collect()
}

fn text_of(h: &TestHost, s: TestStr) -> Vec<char> {
    chars(h, s).collect()
}

/// Runs of the pattern's characters, partial repeats of short ones, and random ones.
fn pattern_for(rng: &mut Rng, text: &[char]) -> Vec<char> {
    match rng.below(4) {
        0 if !text.is_empty() => {
            let i = rng.below(text.len());
            let j = i + rng.below(text.len() - i + 1);
            text[i..j].to_vec()
        }
        1 => {
            let n = 1 + rng.below(3);
            let unit = few_letters(rng, n);
            let n = 1 + rng.below(12);
            unit.iter().copied().cycle().take(n).collect()
        }
        _ => {
            let n = rng.below(8);
            few_letters(rng, n)
        }
    }
}

#[test]
fn find_agrees_with_a_naive_search() {
    let h = TestHost::with_capacity(1 << 20);
    let mut rng = Rng(7);
    for _ in 0..4000 {
        let n = if rng.below(10) == 0 { rng.below(700) } else { rng.below(60) };
        let text = few_letters(&mut rng, n);
        let pattern = pattern_for(&mut rng, &text);
        let (from, to) = (rng.below(text.len() + 1), rng.below(text.len() + 1));
        let (want, want_last) = (naive(&text, &pattern, from), naive_last(&text, &pattern, to));
        let patterns = shapes(&h, &pattern, rng.below(pattern.len() + 1));
        for s in shapes(&h, &text, rng.below(text.len() + 1)) {
            for &p in &patterns {
                assert_eq!(find(&h, s, p, from), Ok(want), "{pattern:?} in {text:?} from {from}");
                assert_eq!(rfind(&h, s, p, to), Ok(want_last), "last {pattern:?} in {text:?} to {to}");
            }
        }
    }
}

/// Patterns whose halves repeat, where a two-way search has to remember what matched.
#[test]
fn periodic_patterns_are_found() {
    let h = TestHost::new();
    for (text, pattern, want) in [
        ("aaaaaaaab", "aaab", Some(5)),
        ("abababababc", "ababc", Some(6)),
        ("aabaabaabaaab", "aabaaab", Some(6)),
        ("abaabaabaab", "abaabab", None),
        ("xyzxyzxyzxy", "zxyzxy", Some(2)),
        ("bbbbbbbbbb", "bbbbbbbbbbb", None),
    ] {
        let (s, p) = (from_str(&h, text).unwrap(), from_str(&h, pattern).unwrap());
        assert_eq!(find(&h, s, p, 0), Ok(want), "{pattern} in {text}");
        let (text, pattern): (String, String) = (text.chars().rev().collect(), pattern.chars().rev().collect());
        let (s, p) = (from_str(&h, &text).unwrap(), from_str(&h, &pattern).unwrap());
        let last = want.map(|i| text.len() - i - pattern.len());
        assert_eq!(rfind(&h, s, p, text.len()), Ok(last), "last {pattern} in {text}");
    }
}

#[test]
fn find_checks_where_it_starts() {
    let h = TestHost::new();
    let (s, p, empty) = (from_str(&h, "abc").unwrap(), from_str(&h, "c").unwrap(), from_str(&h, "").unwrap());
    assert_eq!(find(&h, s, empty, 3), Ok(Some(3)));
    assert_eq!(find(&h, s, p, 3), Ok(None));
    assert_eq!(find(&h, s, p, 4), Err(TestError::Str(StrError::OutOfRange)));
    assert_eq!(rfind(&h, s, empty, 0), Ok(Some(0)));
    assert_eq!(rfind(&h, s, empty, 2), Ok(Some(2)));
    assert_eq!(rfind(&h, s, p, 2), Ok(None), "the match has to end by `to`");
    assert_eq!(rfind(&h, s, p, 4), Err(TestError::Str(StrError::OutOfRange)));
    assert_eq!(find(&h, s, from_str(&h, "Ā").unwrap(), 0), Ok(None), "wider than the text");
    // Bytes past the end of a packed word read as zero, and mustn't match one.
    let nul = from_str(&h, "\0").unwrap();
    for text in ["abc", "abcdefghij"] {
        for _ in 0..2 {
            assert_eq!(find(&h, from_str(&h, text).unwrap(), nul, 0), Ok(None));
            assert_eq!(rfind(&h, from_str(&h, text).unwrap(), nul, text.len()), Ok(None));
        }
    }
}

#[test]
fn prefixes_and_suffixes() {
    let h = TestHost::new();
    let mut rng = Rng(3);
    for _ in 0..2000 {
        let n = rng.below(40);
        let text = few_letters(&mut rng, n);
        let part = pattern_for(&mut rng, &text);
        let parts = shapes(&h, &part, rng.below(part.len() + 1));
        for s in shapes(&h, &text, rng.below(text.len() + 1)) {
            for &p in &parts {
                assert_eq!(starts_with(&h, s, p), Ok(text.starts_with(&part)), "{text:?} starts {part:?}");
                assert_eq!(ends_with(&h, s, p), Ok(text.ends_with(&part)), "{text:?} ends {part:?}");
            }
        }
    }
}

fn split_model(text: &[char], separator: &[char]) -> Vec<Vec<char>> {
    if separator.is_empty() {
        return if text.is_empty() { vec![vec![]] } else { text.iter().map(|&c| vec![c]).collect() };
    }
    let (mut out, mut at) = (Vec::new(), 0);
    while let Some(i) = naive(text, separator, at) {
        out.push(text[at..i].to_vec());
        at = i + separator.len();
    }
    out.push(text[at..].to_vec());
    out
}

#[test]
fn splits_agree_with_a_model() {
    let h = TestHost::with_capacity(1 << 20);
    let mut rng = Rng(5);
    for _ in 0..2000 {
        let n = rng.below(50);
        let text = few_letters(&mut rng, n);
        let n = if rng.below(10) == 0 { 0 } else { 1 + rng.below(2) };
        let separator = few_letters(&mut rng, n);
        let want = split_model(&text, &separator);
        let limit = rng.below(want.len() + 2);
        let want_n = match limit {
            0 => vec![],
            _ if limit >= want.len() => want.clone(),
            _ => {
                let mut pieces = want[..limit - 1].to_vec();
                pieces.push(want[limit - 1..].join(&separator[..]));
                pieces
            }
        };
        let sep = from_chars(&h, separator.iter().copied()).unwrap();
        for s in shapes(&h, &text, rng.below(text.len() + 1)) {
            let got: Vec<_> = split(&h, s, sep).map(|piece| text_of(&h, piece.unwrap())).collect();
            assert_eq!(got, want, "{text:?} split by {separator:?}");
            let got: Vec<_> = splitn(&h, s, sep, limit).map(|piece| text_of(&h, piece.unwrap())).collect();
            assert_eq!(got, want_n, "{text:?} split by {separator:?} in at most {limit}");
        }
    }
}

/// Whitespace of every kind `char::is_whitespace` knows, among letters.
fn spaced(rng: &mut Rng, len: usize) -> String {
    let pool = [' ', ' ', '\t', '\n', '\r', '\u{a0}', '\u{3000}', '\u{2028}', 'a', 'b', 'é', 'Ā', '😀', 'x', 'y', 'z'];
    (0..len).map(|_| pool[rng.below(pool.len())]).collect()
}

#[test]
fn whitespace_splits_and_trims_like_str() {
    let h = TestHost::with_capacity(1 << 20);
    let mut rng = Rng(9);
    for _ in 0..2000 {
        let n = rng.below(30);
        let text = spaced(&mut rng, n);
        let chars_: Vec<char> = text.chars().collect();
        for s in shapes(&h, &chars_, rng.below(chars_.len() + 1)) {
            let words: Vec<String> = split_whitespace(&h, s).map(|w| text_of(&h, w.unwrap()).into_iter().collect()).collect();
            assert_eq!(words, text.split_whitespace().collect::<Vec<_>>(), "{text:?}");
            let show = |t: TestStr| text_of(&h, t).into_iter().collect::<String>();
            assert_eq!(show(trim(&h, s).unwrap()), text.trim());
            assert_eq!(show(trim_start(&h, s).unwrap()), text.trim_start());
            assert_eq!(show(trim_end(&h, s).unwrap()), text.trim_end());
        }
    }
    let s = from_str(&h, "word").unwrap();
    assert_eq!(trim(&h, s), Ok(s), "nothing to trim gives the same string");
}
