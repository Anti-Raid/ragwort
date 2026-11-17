//! Workloads that are generic over the string host and the number host, so that every host runs the same code.

use std::hint::black_box;
use std::time::Instant;

use ragwort_num::{Host as NumHost, int};
use ragwort_string::{Host, char_at, concat, display, equal, find, from_str, hash, len, split};

/// Keeps the best time of each benchmark. The runs of the benchmarks are interleaved, and noise only adds time.
#[derive(Default)]
pub struct Best(pub Vec<(&'static str, f64)>);

impl Best {
    pub fn time(&mut self, name: &'static str, f: impl FnOnce()) {
        let start = Instant::now();
        f();
        let ms = start.elapsed().as_secs_f64() * 1e3;
        match self.0.iter_mut().find(|(n, _)| *n == name) {
            Some((_, best)) => *best = best.min(ms),
            None => self.0.push((name, ms)),
        }
    }

    pub fn print(&self) {
        for (name, ms) in &self.0 {
            println!("{name:40} {ms:>8.2} ms");
        }
    }
}

pub const MESSAGES: [&str; 4] = ["user#1234: hello there", "!ping", "a much longer message about nothing much at all", "ok"];

/// Creates and drops short strings, as a bot does when it handles messages.
#[inline(never)]
pub fn make_short<H: Host>(h: &H, n: usize) {
    for i in 0..n {
        black_box(from_str(h, MESSAGES[i & 3]).ok().expect("alloc"));
    }
}

/// Compares equal flat strings, so every comparison reads all the characters.
#[inline(never)]
pub fn equal_flat<H: Host>(h: &H, n: usize) -> usize {
    let a = from_str(h, &"abcdefgh".repeat(8)).ok().expect("alloc");
    let b = from_str(h, &"abcdefgh".repeat(8)).ok().expect("alloc");
    (0..n).filter(|_| equal(h, black_box(a), black_box(b)).ok().expect("equal")).count()
}

/// Reads characters by index. Each read looks the string up again.
#[inline(never)]
pub fn char_reads<H: Host>(h: &H, n: usize) -> u64 {
    let s = from_str(h, &"the quick brown fox ".repeat(50)).ok().expect("alloc");
    let l = len(h, s);
    (0..n).map(|i| char_at(h, black_box(s), i % l).ok().expect("in range") as u64).sum()
}

#[inline(never)]
pub fn hashes<H: Host>(h: &H, n: usize) -> u64 {
    let s = from_str(h, "user#1234: hello there friend").ok().expect("alloc");
    (0..n).fold(0, |acc, i| acc ^ hash(h, black_box(s), i as u64).ok().expect("hash"))
}

/// Assembles a reply from parts and writes it out as UTF-8.
#[inline(never)]
pub fn replies<H: Host>(h: &H, n: usize) -> usize {
    let (hi, name) = (from_str(h, "hello, ").ok().expect("alloc"), from_str(h, "Ārvīds").ok().expect("alloc"));
    let mut out = String::new();
    for _ in 0..n {
        let s = concat(h, hi, name).ok().expect("concat");
        let s = concat(h, s, from_str(h, "!").ok().expect("alloc")).ok().expect("concat");
        out.clear();
        use std::fmt::Write;
        write!(out, "{}", display(h, s)).ok().expect("write");
    }
    out.len()
}

/// Compares short strings, as a bot does when it matches a command name against the names it knows.
#[inline(never)]
pub fn equal_short<H: Host>(h: &H, n: usize) -> usize {
    let names = ["!help", "!ping", "!ban", "!kick"].map(|s| from_str(h, s).ok().expect("alloc"));
    let got = from_str(h, "!ban").ok().expect("alloc");
    (0..n).filter(|&i| equal(h, black_box(got), black_box(names[i & 3])).ok().expect("equal")).count()
}

#[inline(never)]
pub fn hash_short<H: Host>(h: &H, n: usize) -> u64 {
    let s = from_str(h, "!ping").ok().expect("alloc");
    (0..n).fold(0, |acc, i| acc ^ hash(h, black_box(s), i as u64).ok().expect("hash"))
}

/// Splits a command into its arguments, most of which are short.
#[inline(never)]
pub fn split_commands<H: Host>(h: &H, n: usize) -> usize {
    let (s, space) = (from_str(h, "!ban user42 7d spam links").ok().expect("alloc"), from_str(h, " ").ok().expect("alloc"));
    (0..n).map(|_| split(h, black_box(s), space).filter(|p| black_box(p.is_ok())).count()).sum()
}

/// Searches for a short word in a message.
#[inline(never)]
pub fn find_short<H: Host>(h: &H, n: usize) -> usize {
    let (s, word) = (from_str(h, MESSAGES[2]).ok().expect("alloc"), from_str(h, "nothing").ok().expect("alloc"));
    (0..n).filter_map(|_| find(h, black_box(s), black_box(word), 0).ok().expect("find")).sum()
}

/// Multiplies four-digit bignums and drops the results.
#[inline(never)]
pub fn big_muls<H: NumHost>(h: &H, n: usize) {
    let digits = b"123456789012345678901234567890123456789012345678901234567890123456789012";
    let x = int::parse(h, digits, 10, false).ok().expect("alloc").expect("parse");
    for _ in 0..n {
        black_box(int::mul(h, black_box(x), black_box(x)).ok().expect("mul"));
    }
}

/// Parses bignums and prints them back.
#[inline(never)]
pub fn big_round_trips<H: NumHost>(h: &H, n: usize) -> usize {
    let mut total = 0;
    for i in 0..n {
        let text = format!("{}{:020}", 98765432109876543210u128, i);
        let x = int::parse(h, text.as_bytes(), 10, false).ok().expect("alloc").expect("parse");
        total += int::to_string(h, x, 10).ok().expect("print").len();
    }
    total
}
