//! Reader throughput on bot-like source: nested lists of a few hundred names, quotes and
//! dotted tails, or the file named by the first argument. Run with `--release`.

use std::hint::black_box;
use std::time::{Duration, Instant};

use ragwort_parser::read_all;
use ragwort_types::gc::{Arena, Rootable};
use ragwort_types::symbol::Symbols;
use ragwort_types::syntax::SyntaxSession;

struct Root;
impl Rootable for Root {
    type Root<'gc> = Symbols<'gc>;
}

/// Roughly `bytes` of source, the same every run.
fn source(bytes: usize) -> String {
    const NAMES: &[&str] = &["define", "lambda", "let", "if", "cond", "else", "car", "cdr", "cons", "list", "null?",
        "message", "guild", "user", "channel", "role", "send-message!", "get-member", "x", "acc", "rest", "loop"];
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state as usize
    };
    let mut out = String::new();
    while out.len() < bytes {
        out.push_str("(define (handler msg . rest)");
        let mut open = vec![')'];
        for _ in 0..6 {
            out.push_str("\n  (");
            open.push(')');
            for _ in 0..1 + next() % 5 {
                match next() % 8 {
                    0 => {
                        out.push_str("'(");
                        open.push(')');
                    }
                    1 => {
                        out.push('[');
                        open.push(']');
                    }
                    _ => {}
                }
                out.push_str(NAMES[next() % NAMES.len()]);
                out.push(' ');
            }
            out.push_str(NAMES[next() % NAMES.len()]);
            while open.len() > 1 {
                out.extend(open.pop());
            }
        }
        out.extend(open.pop());
        out.push('\n');
    }
    out
}

fn main() {
    let text = match std::env::args().nth(1) {
        Some(path) => std::fs::read_to_string(path).expect("source file"),
        None => source(1 << 20),
    };
    let mut data = 0;
    let (mut best, mut best_session) = (Duration::MAX, Duration::MAX);
    for _ in 0..7 {
        let mut arena = Arena::<Root>::new(64 << 20, |_| Ok(Symbols::with_seed(1))).expect("arena");
        let (session, read) = arena
            .mutate(|mc, symbols| {
                let start = Instant::now();
                let session = SyntaxSession::new(mc, &text).expect("session");
                let made = start.elapsed();
                let start = Instant::now();
                data = black_box(read_all(mc, symbols, &session).expect("read")).len();
                (made, start.elapsed())
            })
            .expect("step");
        best = best.min(read);
        best_session = best_session.min(session);
    }
    let tokens = text.split(|c: char| c.is_whitespace() || "()[]'".contains(c)).filter(|t| !t.is_empty()).count();
    println!("read {} KiB, {data} top-level data, {tokens} identifiers", text.len() >> 10);
    let (secs, len) = (best.as_secs_f64(), text.len() as f64);
    println!("{:.2} ms, {:.0} MB/s, {:.1} ns per identifier", secs * 1e3, len / secs / 1e6, secs * 1e9 / tokens as f64);
    println!("making the session first: {:.2} ms", best_session.as_secs_f64() * 1e3);
}
