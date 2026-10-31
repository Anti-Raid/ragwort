//! Symbol interning, as a reader does it: mostly hits on a few hundred names, with some
//! common keywords far more frequent than the rest. Run with `--release`. Given a file of
//! names, one per line, it times interning those instead, after interning each once.

use std::collections::HashMap;
use std::hint::black_box;
use std::time::{Duration, Instant};

use ragwort_types::gc::{Arena, Rootable};
use ragwort_types::string::{Strings, equal_str, from_str, hash_str};
use ragwort_types::symbol::Symbols;

struct Table;
impl Rootable for Table {
    type Root<'gc> = Symbols<'gc>;
}

const KEYWORDS: &[&str] = &[
    "define", "lambda", "let", "if", "cond", "else", "begin", "set!", "quote", "car", "cdr", "cons", "list", "null?",
    "pair?", "eq?", "equal?", "+", "-", "*", "=", "<", "not", "and", "or", "when", "unless", "let*", "letrec", "do",
];

/// A deterministic generator, so every run sees the same names.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

fn names(distinct: usize, rng: &mut Rng) -> Vec<String> {
    const PARTS: &[&str] = &["make", "get", "set", "list", "string", "vector", "count", "user", "guild", "message",
        "channel", "role", "x", "i", "n", "acc", "loop", "result", "item", "key", "value", "->", "ref", "length"];
    let mut out: Vec<String> = KEYWORDS.iter().map(|s| s.to_string()).collect();
    while out.len() < distinct {
        let parts = 1 + rng.next() as usize % 3;
        let name = (0..parts).map(|_| PARTS[rng.next() as usize % PARTS.len()]).collect::<Vec<_>>().join("-");
        let name = if rng.next().is_multiple_of(4) { format!("{name}{}", rng.next() % 100) } else { name };
        if !out.contains(&name) {
            out.push(name);
        }
    }
    out
}

/// Source text of `count` tokens, as a reader would slice it: half the tokens are keywords,
/// the rest spread over all the names.
fn source(names: &[String], count: usize, rng: &mut Rng) -> String {
    let tokens: Vec<&str> = (0..count)
        .map(|_| {
            let r = rng.next() as usize;
            if r.is_multiple_of(2) { names[r / 2 % KEYWORDS.len()].as_str() } else { names[r / 2 % names.len()].as_str() }
        })
        .collect();
    tokens.join(" ")
}

fn time(label: &str, ops: usize, mut run: impl FnMut() -> Duration) {
    let best = (0..7).map(|_| run()).min().unwrap_or_default();
    println!("{label:<36} {:>8.2} ns/op", best.as_nanos() as f64 / ops as f64);
}

/// Interns the names in `path` in order, after interning each once.
fn intern_file(path: &str) {
    let text = std::fs::read_to_string(path).expect("names file");
    let tokens: Vec<&str> = text.lines().collect();
    let mut arena = Arena::<Table>::new(256 << 20, |_| Ok(Symbols::with_seed(1))).expect("arena");
    time(&format!("intern_str, {} names from {path}", tokens.len()), tokens.len(), || {
        arena
            .mutate_root(|mc, root| {
                let strings = Strings::new(mc).expect("tags");
                for t in &tokens {
                    root.intern_str(&strings, t).expect("intern");
                }
                let start = Instant::now();
                for t in &tokens {
                    black_box(root.intern_str(&strings, black_box(t)).expect("intern"));
                }
                start.elapsed()
            })
            .expect("step")
    });
}

fn main() {
    if let Some(path) = std::env::args().nth(1) {
        return intern_file(&path);
    }
    const TOKENS: usize = 1_000_000;
    for distinct in [300, 5_000] {
        let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
        let names = names(distinct, &mut rng);
        let source = source(&names, TOKENS, &mut rng);
        let tokens: Vec<&str> = source.split(' ').collect();
        let mut arena = Arena::<Table>::new(256 << 20, |_| Ok(Symbols::with_seed(1))).expect("arena");
        arena
            .mutate_root(|mc, root| {
                let strings = Strings::new(mc).expect("tags");
                for name in &names {
                    root.intern_str(&strings, name).expect("intern");
                }
            })
            .expect("step");

        time(&format!("intern_str hit, {distinct} names"), TOKENS, || {
            arena
                .mutate_root(|mc, root| {
                    let strings = Strings::new(mc).expect("tags");
                    let start = Instant::now();
                    for t in &tokens {
                        black_box(root.intern_str(&strings, black_box(t)).expect("intern"));
                    }
                    start.elapsed()
                })
                .expect("step")
        });

        time(&format!("intern hit (Str), {distinct} names"), TOKENS, || {
            arena
                .mutate_root(|mc, root| {
                    let strings = Strings::new(mc).expect("tags");
                    let strs: Vec<_> = tokens.iter().take(100_000).map(|t| from_str(&strings, t).expect("str")).collect();
                    let start = Instant::now();
                    for _ in 0..TOKENS / strs.len() {
                        for &s in &strs {
                            black_box(root.intern(&strings, black_box(s)).expect("intern"));
                        }
                    }
                    start.elapsed()
                })
                .expect("step")
        });

        time(&format!("  hash_str only, {distinct} names"), TOKENS, || {
            let start = Instant::now();
            for t in &tokens {
                black_box(hash_str(black_box(t), 1));
            }
            start.elapsed()
        });

        time(&format!("  equal_str only, {distinct} names"), TOKENS, || {
            arena
                .mutate_root(|mc, _| {
                    let strings = Strings::new(mc).expect("tags");
                    let strs: Vec<_> = tokens.iter().take(100_000).map(|t| from_str(&strings, t).expect("str")).collect();
                    let start = Instant::now();
                    for _ in 0..TOKENS / strs.len() {
                        for (s, t) in strs.iter().zip(&tokens) {
                            black_box(equal_str(&strings, black_box(*s), black_box(t)).expect("equal"));
                        }
                    }
                    start.elapsed()
                })
                .expect("step")
        });

        let map: HashMap<&str, usize> = names.iter().enumerate().map(|(i, n)| (n.as_str(), i)).collect();
        time(&format!("std HashMap<&str> hit, {distinct} names"), TOKENS, || {
            let start = Instant::now();
            for t in &tokens {
                black_box(map.get(black_box(*t)));
            }
            start.elapsed()
        });
    }

    let long: Vec<String> = (0..1000).map(|i| format!("guild-member-role-permission-cache-{i}")).collect();
    let mut arena = Arena::<Table>::new(256 << 20, |_| Ok(Symbols::with_seed(1))).expect("arena");
    time("intern_str hit, 40-byte names", TOKENS, || {
        arena
            .mutate_root(|mc, root| {
                let strings = Strings::new(mc).expect("tags");
                let start = Instant::now();
                for t in long.iter().cycle().take(TOKENS) {
                    black_box(root.intern_str(&strings, black_box(t)).expect("intern"));
                }
                start.elapsed()
            })
            .expect("step")
    });

    let text = "ab".repeat(512);
    time("hash_str, 1 KiB", 100_000, || {
        let start = Instant::now();
        for _ in 0..100_000 {
            black_box(hash_str(black_box(&text), 1));
        }
        start.elapsed()
    });

    time("intern_str miss (new names)", 200_000, || {
        let mut arena = Arena::<Table>::new(256 << 20, |_| Ok(Symbols::with_seed(1))).expect("arena");
        let fresh: Vec<String> = (0..200_000).map(|i| format!("name-{i}")).collect();
        arena
            .mutate_root(|mc, root| {
                let strings = Strings::new(mc).expect("tags");
                let start = Instant::now();
                for t in &fresh {
                    black_box(root.intern_str(&strings, t).expect("intern"));
                }
                start.elapsed()
            })
            .expect("step")
    });
}
