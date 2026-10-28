use std::cmp::Ordering;

use crate::testing::{Rng, TestError, TestHost, TestStr};
use crate::*;

fn make(h: &TestHost, text: &[char]) -> TestStr {
    let s = from_chars(h, text.iter().copied()).unwrap();
    h.check(s);
    s
}

const SEED: u64 = 0x5eed;

fn hash_of(h: &TestHost, s: TestStr) -> u64 {
    hash(h, s, SEED).unwrap()
}

/// Checks everything readable of `s` against the characters it should hold.
fn agrees(h: &TestHost, rng: &mut Rng, s: TestStr, want: &[char]) {
    h.check(s);
    assert_eq!(len(h, s), want.len());
    let widest = want.iter().map(|&c| Width::of(c)).max().unwrap_or(Width::One);
    assert_eq!(width(h, s), widest);
    assert!(chars(h, s).eq(want.iter().copied()));
    for _ in 0..20.min(want.len()) {
        let i = rng.below(want.len());
        assert_eq!(char_at(h, s, i), Ok(want[i]));
    }
    assert_eq!(char_at(h, s, want.len()), Err(TestError::Str(StrError::OutOfRange)));
    let text: String = want.iter().collect();
    assert_eq!(display(h, s).to_string(), text);
    assert_eq!(utf8_len(h, s), Ok(text.len()));
    assert_eq!(hash_of(h, s), hash_str(&text, SEED));
    assert_eq!(equal_str(h, s, &text), Ok(true));
    if let Some(&last) = want.last() {
        let changed: String = want[..want.len() - 1].iter().chain([&char::from_u32(last as u32 ^ 1).unwrap_or('a')]).collect();
        assert_eq!(equal_str(h, s, &changed), Ok(false));
        assert_eq!(equal_str(h, s, &text[..text.len() - last.len_utf8()]), Ok(false));
    }
}

#[test]
fn strings_match_a_model() {
    for seed in 0..12 {
        let h = TestHost::new();
        let mut rng = Rng(seed);
        let mut pool: Vec<(TestStr, Vec<char>)> = Vec::new();
        for _ in 0..600 {
            let pick = |rng: &mut Rng, pool: &[(TestStr, Vec<char>)]| pool[rng.below(pool.len())].clone();
            let (s, want) = match rng.below(if pool.is_empty() { 1 } else { 6 }) {
                0 => {
                    let text = rng.text();
                    let s = match rng.below(3) {
                        0 => make(&h, &text),
                        1 => from_str(&h, &text.iter().collect::<String>()).unwrap(),
                        _ => h.external(ExternalText::new(text.iter().collect::<String>())).unwrap(),
                    };
                    (s, text)
                }
                1 | 2 => {
                    let ((a, x), (b, y)) = (pick(&mut rng, &pool), pick(&mut rng, &pool));
                    if x.len() + y.len() > 20_000 {
                        continue;
                    }
                    (concat(&h, a, b).unwrap(), [x, y].concat())
                }
                3 => {
                    let (a, x) = pick(&mut rng, &pool);
                    let (i, j) = (rng.below(x.len() + 1), rng.below(x.len() + 1));
                    let (start, end) = (i.min(j), i.max(j));
                    (substring(&h, a, start, end).unwrap(), x[start..end].to_vec())
                }
                4 => {
                    let parts: Vec<_> = (0..rng.below(6)).map(|_| pick(&mut rng, &pool)).collect();
                    let want: Vec<char> = parts.iter().flat_map(|(_, x)| x.iter().copied()).collect();
                    if want.len() > 20_000 {
                        continue;
                    }
                    let strs: Vec<_> = parts.iter().map(|&(s, _)| s).collect();
                    (concat_all(&h, &strs).unwrap(), want)
                }
                _ => {
                    let (a, x) = pick(&mut rng, &pool);
                    let flat = flatten(&h, a).unwrap();
                    assert!(is_flat(&h, flat));
                    agrees(&h, &mut rng, a, &x);
                    (flat, x)
                }
            };
            agrees(&h, &mut rng, s, &want);
            let (b, y) = pick(&mut rng, &pool.iter().chain([&(s, want.clone())]).cloned().collect::<Vec<_>>());
            assert_eq!(compare(&h, s, b), Ok(want.cmp(&y)), "{want:?} vs {y:?}");
            assert_eq!(equal(&h, s, b), Ok(want == y));
            if pool.len() < 60 {
                pool.push((s, want));
            } else {
                let i = rng.below(pool.len());
                pool[i] = (s, want);
            }
        }
    }
}

#[test]
fn shape_doesnt_change_what_a_string_is() {
    let h = TestHost::new();
    let mut rng = Rng(7);
    let text: Vec<char> = (0..5000).map(|_| rng.char(Width::Two)).collect();
    let flat = make(&h, &text);
    let mut ropes = Vec::new();
    for _ in 0..10 {
        let cuts: Vec<usize> = {
            let mut cuts: Vec<usize> = (0..rng.below(20)).map(|_| rng.below(text.len())).collect();
            cuts.extend([0, text.len()]);
            cuts.sort();
            cuts
        };
        let parts: Vec<_> = cuts.windows(2).map(|w| make(&h, &text[w[0]..w[1]])).collect();
        let joined = parts.iter().fold(empty(&h).unwrap(), |acc, &p| concat(&h, acc, p).unwrap());
        h.check(joined);
        ropes.push(joined);
    }
    for &s in &ropes {
        assert_eq!(equal(&h, s, flat), Ok(true));
        assert_eq!(compare(&h, s, flat), Ok(Ordering::Equal));
        assert_eq!(hash_of(&h, s), hash_of(&h, flat));
    }
    let other = make(&h, &[&text[..4999], &['\u{100}']].concat());
    assert_eq!(equal(&h, ropes[0], other), Ok(text[4999] == '\u{100}'));
}

#[test]
fn widths_are_the_narrowest() {
    let h = TestHost::new();
    for (text, want) in [("", Width::One), ("abc", Width::One), ("café", Width::One), ("Ā", Width::Two), ("日本", Width::Two), ("😀", Width::Four)] {
        assert_eq!(width(&h, from_str(&h, text).unwrap()), want, "{text}");
    }
    let wide = from_str(&h, "😀abc").unwrap();
    let tail = substring(&h, wide, 1, 4).unwrap();
    assert_eq!(width(&h, tail), Width::One);
    assert_eq!(equal(&h, tail, from_str(&h, "abc").unwrap()), Ok(true));
}

/// Building a string a piece at a time, at either end, gives nearly full flat strings in a
/// balanced rope.
#[test]
fn piece_at_a_time_stays_shallow() {
    for piece in [1, 7, 100] {
        for prepend in [false, true] {
            let h = TestHost::with_capacity(1 << 20);
            let mut rng = Rng(piece as u64);
            let mut s = empty(&h).unwrap();
            let mut pieces = Vec::new();
            for _ in 0..20_000 {
                let text: Vec<char> = (0..piece).map(|_| rng.char(Width::One)).collect();
                let p = make(&h, &text);
                s = if prepend { concat(&h, p, s) } else { concat(&h, s, p) }.unwrap();
                pieces.push(text);
            }
            if prepend {
                pieces.reverse();
            }
            let want = pieces.concat();
            h.check(s);
            assert!(chars(&h, s).eq(want.iter().copied()));
            let leaves = h.leaves(s);
            let depth = crate::info(&h, s).depth as f64;
            assert!(depth <= 1.45 * (leaves as f64 + 2.0).log2(), "depth {depth} for {leaves} leaves");
            // Flat strings fill to about 512 bytes; without merging at the edges, to about half.
            assert!(want.len() / leaves >= 384, "{leaves} leaves for {} characters", want.len());
        }
    }
}

#[test]
fn length_is_capped() {
    let h = TestHost::new();
    let mut s = from_str(&h, "ab").unwrap();
    let mut n = 2usize;
    loop {
        match concat(&h, s, s) {
            Ok(t) => (s, n) = (t, n * 2),
            Err(e) => {
                assert_eq!(e, TestError::Str(StrError::TooLong));
                break;
            }
        }
    }
    assert_eq!(n, 1 << 47);
    assert_eq!(len(&h, s), n);
    h.check(s);
    assert_eq!(char_at(&h, s, n - 1), Ok('b'));
    assert_eq!(char_at(&h, s, n - 2), Ok('a'));
    let tail = substring(&h, s, n - 5, n).unwrap();
    assert_eq!(display(&h, tail).to_string(), "babab");
    assert_eq!(repeat(&h, 'x', MAX_LEN + 1), Err(TestError::Str(StrError::TooLong)));
}

#[test]
fn ranges_are_checked() {
    let h = TestHost::new();
    let s = from_str(&h, "hello").unwrap();
    assert_eq!(substring(&h, s, 3, 2), Err(TestError::Str(StrError::OutOfRange)));
    assert_eq!(substring(&h, s, 0, 6), Err(TestError::Str(StrError::OutOfRange)));
    assert_eq!(char_at(&h, s, 5), Err(TestError::Str(StrError::OutOfRange)));
    let e = empty(&h).unwrap();
    assert_eq!(concat(&h, e, s), Ok(s));
    assert_eq!(concat(&h, s, e), Ok(s));
    assert_eq!(compare(&h, e, s), Ok(Ordering::Less));
    assert_eq!(display(&h, repeat(&h, 'é', 3).unwrap()).to_string(), "ééé");
    assert_eq!(concat_all(&h, &[]).map(|s| len(&h, s)), Ok(0));
}

#[test]
fn info_round_trips() {
    for info in [
        Info { len: 0, width: Width::One, depth: 0 },
        Info { len: MAX_LEN, width: Width::Four, depth: 95 },
        Info { len: 12345, width: Width::Two, depth: 3 },
    ] {
        assert_eq!(Info::from_bits(info.to_bits()), info);
    }
}


#[test]
fn external_characters_must_be_narrowest() {
    struct Wide(Vec<u16>);
    impl External for Wide {
        fn units(&self) -> Units<'_> {
            Units::Two(&self.0)
        }
    }
    let h = TestHost::new();
    assert_eq!(h.external(Wide(vec![0x61, 0x62])), Err(TestError::Str(StrError::NotNarrowest)));
    let s = h.external(Wide(vec![0x61, 0x101])).unwrap();
    assert_eq!(display(&h, s).to_string(), "a\u{101}");
    for text in ["", "ascii only", "café", "日本語", "mixed 😀 width"] {
        let s = h.external(ExternalText::new(text)).unwrap();
        assert_eq!(display(&h, s).to_string(), text);
        assert_eq!(equal(&h, s, from_str(&h, text).unwrap()), Ok(true));
    }
}

/// Reading a rope by position often enough flattens it once, and reads then use the copy.
#[test]
fn reads_by_position_flatten_a_rope() {
    let h = TestHost::with_capacity(1 << 20);
    let mut rng = Rng(3);
    let mut s = empty(&h).unwrap();
    let mut want = Vec::new();
    for _ in 0..400 {
        let text: Vec<char> = (0..50).map(|_| rng.char(Width::Two)).collect();
        s = concat(&h, s, make(&h, &text)).unwrap();
        want.extend(text);
    }
    let shared = concat(&h, s, from_str(&h, &"z".repeat(600)).unwrap()).unwrap();
    assert!(!h.is_flattened(s));
    let reads = want.len().div_ceil(crate::rope::CHARS_PER_READ as usize);
    for n in 0..reads + 10 {
        let i = rng.below(want.len());
        assert_eq!(char_at(&h, s, i), Ok(want[i]));
        assert_eq!(h.is_flattened(s), n + 1 >= reads, "after {} reads", n + 1);
    }
    h.check(s);
    h.check(shared);
    let flat = flatten(&h, s).unwrap();
    assert_eq!(flatten(&h, s), Ok(flat), "the copy is kept");
    assert!(chars(&h, s).eq(want.iter().copied()));
    assert_eq!(chunks(&h, s).count(), 1, "iterating reads the copy");
    assert_eq!(char_at(&h, shared, want.len()), Ok('z'));
}

/// Appending between reads makes a new rope each time, so nothing is flattened and each step
/// stays logarithmic.
#[test]
fn appends_between_reads_dont_flatten() {
    let h = TestHost::with_capacity(1 << 20);
    let piece = from_str(&h, &"ab".repeat(100)).unwrap();
    let mut s = empty(&h).unwrap();
    for i in 0..2000 {
        s = concat(&h, s, piece).unwrap();
        assert_eq!(char_at(&h, s, i * 200 + 1), Ok('b'));
        assert!(is_flat(&h, s) || !h.is_flattened(s));
    }
}

/// Strings that differ in one character, at each width and in each shape, compare as their
/// characters do.
#[test]
fn near_misses_compare_by_their_characters() {
    let h = TestHost::with_capacity(1 << 20);
    let mut rng = Rng(11);
    for widest in [Width::One, Width::Two, Width::Four] {
        for len in [1, 7, 600, 3000] {
            let text: Vec<char> = (0..len).map(|_| rng.char(widest)).collect();
            for at in [0, len / 2, len - 1] {
                let mut other = text.clone();
                other[at] = if other[at] == 'a' { 'b' } else { 'a' };
                let shapes = |t: &[char]| {
                    let flat = make(&h, t);
                    let half = t.len() / 2;
                    let rope = concat(&h, make(&h, &t[..half]), make(&h, &t[half..])).unwrap();
                    let flattened = concat(&h, make(&h, &t[..half]), make(&h, &t[half..])).unwrap();
                    flatten(&h, flattened).unwrap();
                    [flat, rope, flattened]
                };
                for x in shapes(&text) {
                    for y in shapes(&other) {
                        assert_eq!(equal(&h, x, y), Ok(text == other));
                        assert_eq!(compare(&h, x, y), Ok(text.cmp(&other)));
                        assert_eq!(compare(&h, y, x), Ok(other.cmp(&text)));
                    }
                }
            }
        }
    }
}

/// Ropes with pieces narrower than the whole, cut at each offset in a word, hash as the flat
/// string does, while every character and the seed change the hash.
#[test]
fn hashes_follow_the_characters() {
    let h = TestHost::with_capacity(1 << 20);
    let mut rng = Rng(5);
    for widest in [Width::One, Width::Two, Width::Four] {
        let mut text: Vec<char> = (0..1500).map(|_| rng.char(Width::One)).collect();
        text.extend((0..1500).map(|_| rng.char(widest)));
        let flat = make(&h, &text);
        let want = hash_of(&h, flat);
        for cut in 1..20 {
            let cuts = [0, cut, 700 + cut, 1500 + cut, 2200 + cut, text.len()];
            let rope = cuts.windows(2).fold(empty(&h).unwrap(), |acc, w| concat(&h, acc, make(&h, &text[w[0]..w[1]])).unwrap());
            assert!(!is_flat(&h, rope));
            assert_eq!(hash_of(&h, rope), want);
        }
        let mut seen = std::collections::HashSet::from([want]);
        for i in [0, 1, 7, 8, 9, 15, 16, 1499, 1500, 2999] {
            let mut other = text.clone();
            other[i] = if other[i] == 'a' { 'b' } else { 'a' };
            assert!(seen.insert(hash_of(&h, make(&h, &other))), "changing {i}");
        }
        assert!(seen.insert(hash(&h, flat, SEED + 1).unwrap()));
    }
    // Every string of up to four of these, including ones whose packed words match across widths.
    let alphabet = ['\0', 'a', 'b', '\u{6261}', '😀'];
    let mut texts = vec![String::new()];
    for _ in 0..4 {
        let longer: Vec<String> = texts.iter().flat_map(|t| alphabet.map(|c| format!("{t}{c}"))).collect();
        texts.extend(longer);
        texts.dedup();
    }
    texts.sort();
    texts.dedup();
    let hashes: std::collections::HashSet<u64> = texts.iter().map(|t| hash_str(t, SEED)).collect();
    assert_eq!(hashes.len(), texts.len());
    assert_ne!(hash_str("abcd", SEED), hash_str("\u{6261}\u{6463}\0\0", SEED));
    // Each character of a short string changes its hash, wherever it falls in a word.
    for widest in [Width::One, Width::Two, Width::Four] {
        let text: Vec<char> = (0..40).map(|_| rng.char(widest)).collect();
        for n in 0..=text.len() {
            let mut seen = std::collections::HashSet::from([hash_of(&h, make(&h, &text[..n]))]);
            for i in 0..n {
                let mut other = text[..n].to_vec();
                other[i] = char::from_u32(other[i] as u32 ^ 1).unwrap_or('a');
                assert!(seen.insert(hash_of(&h, make(&h, &other))), "{n} long, changing {i}");
            }
        }
    }
}
