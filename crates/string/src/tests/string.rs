use std::cmp::Ordering;

use crate::testing::{Rng, TestError, TestHost, TestStr, Width, shapes};
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

/// Checks every read operation on `s` against `want`, the characters that `s` should hold.
fn agrees(h: &TestHost, rng: &mut Rng, s: TestStr, want: &[char]) {
    h.check(s);
    assert_eq!(len(h, s), want.len());
    assert_eq!(byte_len(h, s), want.iter().map(|character| character.len_utf8()).sum::<usize>());
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
    fn pick(rng: &mut Rng, pool: &[(TestStr, Vec<char>)]) -> (TestStr, Vec<char>) {
        pool[rng.below(pool.len())].clone()
    }
    for seed in 0..12 {
        let h = TestHost::new();
        let mut rng = Rng(seed);
        let mut pool: Vec<(TestStr, Vec<char>)> = Vec::new();
        for _ in 0..600 {
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

/// A string takes the bytes of its UTF-8 encoding, and a substring takes the bytes of its own characters.
#[test]
fn a_string_takes_its_utf8_bytes() {
    let h = TestHost::new();
    for (text, want) in [("", 0), ("abc", 3), ("café", 5), ("Ā", 2), ("日本", 6), ("😀", 4)] {
        let made = from_str(&h, text).unwrap();
        assert_eq!((byte_len(&h, made), len(&h, made)), (want, text.chars().count()), "{text}");
    }
    let wide = from_str(&h, "😀abc").unwrap();
    let tail = substring(&h, wide, 1, 4).unwrap();
    assert_eq!((byte_len(&h, tail), len(&h, tail)), (3, 3));
    assert_eq!(equal(&h, tail, from_str(&h, "abc").unwrap()), Ok(true));
    // Positions count characters, wherever the bytes of a character end.
    let mixed = from_str(&h, "aé日😀z").unwrap();
    for (index, character) in "aé日😀z".chars().enumerate() {
        assert_eq!(char_at(&h, mixed, index), Ok(character));
        assert_eq!(display(&h, substring(&h, mixed, index, index + 1).unwrap()).to_string(), character.to_string());
    }
    assert_eq!(find(&h, mixed, from_str(&h, "😀").unwrap(), 0), Ok(Some(3)));
    assert_eq!(find(&h, mixed, from_str(&h, "z").unwrap(), 4), Ok(Some(4)));
    assert_eq!(rfind(&h, mixed, from_str(&h, "é").unwrap(), 5), Ok(Some(1)));
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
            // Flat strings fill to about 512 bytes. Without merging at the edges, they would fill to about half of that.
            let bytes = byte_len(&h, s);
            assert!(bytes / leaves >= 384, "{leaves} leaves for {bytes} bytes");
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

/// An external string holds the text of the host as it is, whatever characters it has.
#[test]
fn external_text_is_read_as_it_is() {
    let h = TestHost::new();
    for text in ["", "ascii only", "café", "日本語", "mixed 😀 width"] {
        let s = h.external(ExternalText::new(text)).unwrap();
        assert_eq!(display(&h, s).to_string(), text);
        assert_eq!(equal(&h, s, from_str(&h, text).unwrap()), Ok(true));
    }
}

/// Reading an ASCII rope by index often enough flattens it once, and later reads use the flat copy. A rope with other characters is never flattened by reads:
/// its nodes count the characters of each piece, which a flat copy cannot do.
#[test]
fn reads_by_position_flatten_a_rope() {
    let h = TestHost::with_capacity(1 << 20);
    let mut rng = Rng(3);
    let (mut s, mut mixed) = (empty(&h).unwrap(), empty(&h).unwrap());
    let (mut want, mut mixed_want) = (Vec::new(), Vec::new());
    for _ in 0..400 {
        let text: Vec<char> = (0..50).map(|_| char::from(b' ' + rng.below(95) as u8)).collect();
        s = concat(&h, s, make(&h, &text)).unwrap();
        want.extend(text);
        let text: Vec<char> = (0..50).map(|_| rng.char(Width::Two)).collect();
        mixed = concat(&h, mixed, make(&h, &text)).unwrap();
        mixed_want.extend(text);
    }
    let shared = concat(&h, s, from_str(&h, &"z".repeat(600)).unwrap()).unwrap();
    assert!(!h.is_flattened(s));
    let reads = want.len().div_ceil(crate::rope::CHARS_PER_READ as usize);
    for n in 0..reads + 10 {
        let i = rng.below(want.len());
        assert_eq!(char_at(&h, s, i), Ok(want[i]));
        assert_eq!(h.is_flattened(s), n + 1 >= reads, "after {} reads", n + 1);
        assert_eq!(char_at(&h, mixed, i), Ok(mixed_want[i]));
        assert!(!h.is_flattened(mixed), "after {} reads", n + 1);
    }
    h.check(s);
    h.check(shared);
    h.check(mixed);
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
    fn shapes(h: &TestHost, text: &[char]) -> [TestStr; 3] {
        let flat = make(h, text);
        let half = text.len() / 2;
        let rope = concat(h, make(h, &text[..half]), make(h, &text[half..])).unwrap();
        let flattened = concat(h, make(h, &text[..half]), make(h, &text[half..])).unwrap();
        flatten(h, flattened).unwrap();
        [flat, rope, flattened]
    }
    let h = TestHost::with_capacity(1 << 20);
    let mut rng = Rng(11);
    for widest in [Width::One, Width::Two, Width::Four] {
        for len in [1, 7, 600, 3000] {
            let text: Vec<char> = (0..len).map(|_| rng.char(widest)).collect();
            for at in [0, len / 2, len - 1] {
                let mut other = text.clone();
                other[at] = if other[at] == 'a' { 'b' } else { 'a' };
                for x in shapes(&h, &text) {
                    for y in shapes(&h, &other) {
                        assert_eq!(equal(&h, x, y), Ok(text == other));
                        assert_eq!(compare(&h, x, y), Ok(text.cmp(&other)));
                        assert_eq!(compare(&h, y, x), Ok(other.cmp(&text)));
                    }
                }
            }
        }
    }
}

/// A string short enough to hash from at most 32 bytes has the same hash as a flat string, as a rope cut at any index and as a `&str`.
/// This holds at every width and on both sides of each length cutoff. Each string also compares equal to its text.
#[test]
fn short_strings_hash_alike_in_every_shape() {
    let h = TestHost::with_capacity(1 << 20);
    let mut rng = Rng(9);
    for widest in [Width::One, Width::Two, Width::Four] {
        for n in 0..=36 {
            let text: Vec<char> = (0..n).map(|i| if i == n / 2 { rng.char(widest) } else { rng.char(Width::One) }).collect();
            let string: String = text.iter().collect();
            let flat = make(&h, &text);
            let want = hash_of(&h, flat);
            assert_eq!(hash_str(&string, SEED), want, "{n} long at {widest:?}");
            assert_eq!(equal_str(&h, flat, &string), Ok(true));
            for cut in 1..n {
                let rope = concat(&h, make(&h, &text[..cut]), make(&h, &text[cut..])).unwrap();
                assert_eq!(hash_of(&h, rope), want, "{n} long at {widest:?}, cut at {cut}");
                assert_eq!(equal(&h, rope, flat), Ok(true));
            }
        }
    }
    // Texts of 16 and 17 bytes, on either side of the cutoff, hash differently. So do texts that differ only in a high bit.
    assert_ne!(hash_str("abcdefghijklmnop", SEED), hash_str("abcdefghijklmnopq", SEED));
    assert_ne!(hash_str("\u{e9}", SEED), hash_str("i", SEED));
    let s = make(&h, &"caf\u{e9}".chars().collect::<Vec<_>>());
    assert_eq!(equal_str(&h, s, "caf\u{e9}"), Ok(true));
    assert_eq!(equal_str(&h, s, "cafi"), Ok(false));
    // One-byte units can hold the same bytes as the UTF-8 encoding of other text. "Ã©" is the units C3 A9, which are the UTF-8 bytes of "é".
    for n in [0, 3, 6, 7, 14, 15, 30] {
        let pad = "x".repeat(n);
        let latin: Vec<char> = format!("{pad}\u{c3}\u{a9}").chars().collect();
        for s in [make(&h, &latin), make(&h, &latin)] {
            assert_eq!(equal_str(&h, s, &format!("{pad}\u{e9}")), Ok(false), "{n} before");
        }
    }
}

/// A rope with pieces narrower than the whole string, cut at each offset within a word, has the same hash as the flat
/// string. Changing any character or the seed changes the hash.
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
    // Hash every string of up to four of these characters. Some of them pack into equal words at different widths, and they must still hash differently.
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
    // Changing any one character of a short string changes the hash, at every position within a word.
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

/// Strings that look like Discord ids spread evenly over the buckets of a table, under several seeds. The ids are 18 to 20 digits, which the hash takes in its form for 17 to 32 bytes. They differ in the ways that real ids do: by one, by a multiple of 2^22, and in their first digits only.
#[test]
fn id_strings_spread_over_the_buckets() {
    const COUNT: u64 = 1 << 18;
    const BUCKETS: usize = 1 << 16;
    /// Returns the chi-squared statistic of `hashes` over `BUCKETS` buckets, taken from the hash bits from `shift` up.
    fn spread(hashes: &[u64], shift: u32) -> f64 {
        let mut loads = vec![0u32; BUCKETS];
        for hash in hashes {
            loads[(hash >> shift) as usize % BUCKETS] += 1;
        }
        let expected = hashes.len() as f64 / BUCKETS as f64;
        loads.iter().map(|&load| (f64::from(load) - expected).powi(2) / expected).sum()
    }
    let families: [(&str, u64, u64); 4] = [
        ("ids that differ by one", 1_187_000_000_000_000_000, 1),
        ("ids that differ by 2^22", 1_187_000_000_000_000_000, 1 << 22),
        ("ids of 18 digits", 187_000_000_000_000_000, 1 << 22 | 1),
        ("ids that differ in their first digits", 10_000_000_000_000_000_007, 30_000_000_000_000),
    ];
    for seed in [SEED, 0, 1, u64::MAX, 0x9E37_79B9_7F4A_7C15] {
        for (name, start, step) in families {
            let hashes: Vec<u64> = (0..COUNT).map(|index| hash_str(&(start + index * step).to_string(), seed)).collect();
            let distinct: std::collections::HashSet<u64> = hashes.iter().copied().collect();
            assert_eq!(distinct.len(), hashes.len(), "{name}, seed {seed:#x}");
            // A string keeps the low 32 bits of its hash. About 8 pairs of 2^18 random 32-bit numbers are equal, so far fewer than 40 are.
            let kept: std::collections::HashSet<u32> = hashes.iter().map(|&hash| hash as u32).collect();
            assert!(hashes.len() - kept.len() < 40, "{name}, seed {seed:#x}: {} strings share their kept hash", hashes.len() - kept.len());
            // With evenly spread hashes the statistic is near the number of buckets, and its standard deviation is about 362. The bound is six of them.
            for shift in [0, 16] {
                let statistic = spread(&hashes, shift);
                assert!((statistic - BUCKETS as f64).abs() < 6.0 * 362.0, "{name}, seed {seed:#x}, bits from {shift}: {statistic}");
            }
        }
    }
}

/// The procedures that take byte offsets agree with the ones that take character indices, in every shape of string. An offset inside a character is refused.
#[test]
fn byte_offsets_agree_with_character_indices() {
    let h = TestHost::with_capacity(1 << 20);
    let mut rng = Rng(21);
    for round in 0..300 {
        let text = rng.text();
        let string: String = text.iter().collect();
        let starts: Vec<usize> = string.char_indices().map(|(offset, _)| offset).chain([string.len()]).collect();
        for s in shapes(&h, &text, rng.below(text.len().max(1))) {
            assert_eq!(byte_len(&h, s), string.len());
            for _ in 0..8 {
                let index = rng.below(text.len() + 1);
                let offset = starts[index];
                assert_eq!((byte_offset_of(&h, s, index), char_index(&h, s, offset), is_boundary(&h, s, offset)), (Ok(offset), Ok(index), true), "round {round}");
                if index < text.len() {
                    assert_eq!(char_at_byte(&h, s, offset), Ok((text[index], text[index].len_utf8())));
                    assert_eq!((byte_at(&h, s, offset), byte_before(&h, s, starts[index + 1])), (Ok(string.as_bytes()[offset]), Ok(offset)));
                    // The bytes inside a character are no positions.
                    for inside in offset + 1..starts[index + 1] {
                        assert!(!is_boundary(&h, s, inside));
                        assert_eq!(char_at_byte(&h, s, inside), Err(TestError::Str(StrError::OutOfRange)));
                        assert_eq!(char_index(&h, s, inside), Err(TestError::Str(StrError::OutOfRange)));
                        assert_eq!(substring_bytes(&h, s, 0, inside).err(), Some(TestError::Str(StrError::OutOfRange)));
                        assert_eq!(byte_before(&h, s, inside), Err(TestError::Str(StrError::OutOfRange)));
                    }
                }
                let other = rng.below(text.len() + 1);
                let (first, last) = (index.min(other), index.max(other));
                let by_bytes = substring_bytes(&h, s, starts[first], starts[last]).unwrap();
                h.check(by_bytes);
                assert_eq!(equal(&h, by_bytes, substring(&h, s, first, last).unwrap()), Ok(true));
                // A search by offset finds what a search by index finds.
                if last > first {
                    let pattern = make(&h, &text[first..(first + 3).min(last)]);
                    let from = rng.below(first + 1);
                    assert_eq!(find_bytes(&h, s, pattern, starts[from]), find(&h, s, pattern, from).map(|found| found.map(|index| starts[index])));
                    assert_eq!(rfind_bytes(&h, s, pattern, starts[last]), rfind(&h, s, pattern, last).map(|found| found.map(|index| starts[index])));
                }
            }
            assert_eq!((byte_before(&h, s, 0), char_at_byte(&h, s, string.len()), is_boundary(&h, s, string.len() + 1)), (Err(TestError::Str(StrError::OutOfRange)), Err(TestError::Str(StrError::OutOfRange)), false));
            assert_eq!((byte_offset_of(&h, s, text.len() + 1), byte_at(&h, s, string.len())), (Err(TestError::Str(StrError::OutOfRange)), Err(TestError::Str(StrError::OutOfRange))));
        }
    }
}

/// A string goes out to the host as its bytes, in every shape: as a `String`, appended to a buffer, and a part at a time. Bytes that are text come in as a string, and other bytes are refused.
#[test]
fn text_crosses_to_the_host_as_bytes() {
    let h = TestHost::with_capacity(1 << 20);
    let mut rng = Rng(34);
    for _ in 0..200 {
        let text = rng.text();
        let string: String = text.iter().collect();
        let starts: Vec<usize> = string.char_indices().map(|(offset, _)| offset).chain([string.len()]).collect();
        for s in shapes(&h, &text, rng.below(text.len().max(1))) {
            assert_eq!(to_string(&h, s), string);
            let mut buffer = b"before ".to_vec();
            append_utf8(&h, s, &mut buffer);
            assert_eq!(buffer, [b"before ", string.as_bytes()].concat());
            let (first, second) = (rng.below(text.len() + 1), rng.below(text.len() + 1));
            let (from, to) = (starts[first.min(second)], starts[first.max(second)]);
            let mut part = vec![0; to - from];
            copy_bytes(&h, s, from, to, &mut part);
            assert_eq!(part, &string.as_bytes()[from..to]);
        }
        let back = from_utf8(&h, string.as_bytes()).unwrap();
        h.check(back);
        assert_eq!((len(&h, back), byte_len(&h, back), equal_str(&h, back, &string)), (text.len(), string.len(), Ok(true)));
    }
    // Bytes that are no text: a byte that starts nothing, a character cut short, and a code that is too long for its character.
    for bytes in [&[0x68, 0xFF][..], &[0xE6, 0x97], &[0xC0, 0xAF], &[0xED, 0xA0, 0x80]] {
        assert_eq!(from_utf8(&h, bytes).err(), Some(TestError::Str(StrError::NotUtf8)), "{bytes:?}");
    }
}

