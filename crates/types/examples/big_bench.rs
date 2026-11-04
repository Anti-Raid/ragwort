//! Bignum arithmetic from just past fixnums to thousands of digits, through the generic layer.

use std::hint::black_box;
use std::time::Instant;

use ragwort_types::gc::Arena;
use ragwort_types::num::{Integer, Nums, int};

fn big<'gc>(h: &Nums<'_, 'gc>, base: i64, e: u64) -> Integer<'gc> {
    int::expt(h, int::from_i64(h, base).expect("alloc"), e).expect("alloc")
}

/// Runs `f` over `n` operations in steps of `batch`, `f` doing a step's, with a minor
/// collection between steps.
fn run(arena: &mut Arena, n: usize, batch: usize, f: impl Fn(&Nums<'_, '_>, usize)) {
    for _ in 0..n / batch {
        arena.mutate(|mc| f(&Nums::new(mc), batch));
        arena.collect_minor();
    }
}

fn main() {
    let mut arena = Arena::new(256 << 20, 0);
    let mut best: Vec<(&str, f64)> = Vec::new();
    let mut time = |name: &'static str, f: &mut dyn FnMut()| {
        let start = Instant::now();
        f();
        let ms = start.elapsed().as_secs_f64() * 1e3;
        match best.iter_mut().find(|(n, _)| *n == name) {
            Some((_, b)) => *b = b.min(ms),
            None => best.push((name, ms)),
        }
    };
    for _ in 0..5 {
        time("2-digit add x 5M", &mut || {
            run(&mut arena, 5_000_000, 50_000, |h, n| {
                let x = big(h, 2, 100);
                (0..n).for_each(|_| _ = black_box(int::add(h, black_box(x), black_box(x)).expect("add")));
            })
        });
        time("2-digit mul to 4 x 5M", &mut || {
            run(&mut arena, 5_000_000, 50_000, |h, n| {
                let x = big(h, 3, 70);
                (0..n).for_each(|_| _ = black_box(int::mul(h, black_box(x), black_box(x)).expect("mul")));
            })
        });
        time("64-digit mul x 50K", &mut || {
            run(&mut arena, 50_000, 1_000, |h, n| {
                let x = big(h, 7, 1400);
                (0..n).for_each(|_| _ = black_box(int::mul(h, black_box(x), black_box(x)).expect("mul")));
            })
        });
        time("1000-digit add x 200K", &mut || {
            run(&mut arena, 200_000, 2_000, |h, n| {
                let x = big(h, 3, 40_000);
                (0..n).for_each(|_| _ = black_box(int::add(h, black_box(x), black_box(x)).expect("add")));
            })
        });
        time("1000-digit mul x 500", &mut || {
            run(&mut arena, 500, 50, |h, n| {
                let x = big(h, 3, 40_000);
                (0..n).for_each(|_| _ = black_box(int::mul(h, black_box(x), black_box(x)).expect("mul")));
            })
        });
        time("500 by 250 digit divide x 5K", &mut || {
            run(&mut arena, 5_000, 250, |h, n| {
                let (x, y) = (big(h, 3, 20_000), big(h, 5, 6_900));
                (0..n).for_each(|_| _ = black_box(int::quotient_remainder(h, black_box(x), black_box(y)).expect("divide")));
            })
        });
        time("3000-char parse + print x 500", &mut || {
            let text = "1234567890".repeat(300);
            run(&mut arena, 500, 50, |h, n| {
                for _ in 0..n {
                    let x = int::parse(h, black_box(text.as_bytes()), 10, false).expect("alloc").expect("parse");
                    black_box(int::to_string(h, x, 10).expect("print"));
                }
            })
        });
        time("3^20000 x 500", &mut || run(&mut arena, 500, 50, |h, n| (0..n).for_each(|_| _ = black_box(big(h, 3, 20_000)))));
    }
    for (name, ms) in best {
        println!("{name:40} {ms:>8.2} ms");
    }
}
