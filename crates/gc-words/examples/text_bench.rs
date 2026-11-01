//! Strings and bignums on this arena, with characters packed into words and digits in blobs. The same workloads
//! run on `ragwort-types`, where they're inline, as its `text_bench` example.

#[path = "common/text_work.rs"]
mod work;

use ragwort_gc_words::Arena;
use ragwort_gc_words::nums::Nums;
use ragwort_gc_words::strings::Strings;
use work::*;

const BATCH: usize = 50_000;

fn main() {
    let mut arena = Arena::new(256 << 20, 1);
    let mut best = Best::default();
    for _ in 0..7 {
        best.time("make 2M short strings", || {
            for _ in 0..2_000_000 / BATCH {
                arena.mutate(|mc| make_short(&Strings::new(mc), BATCH));
                arena.collect_minor();
            }
        });
        arena.mutate(|mc| {
            let h = Strings::new(mc);
            best.time("equal 64 chars x 5M", || assert_eq!(equal_flat(&h, 5_000_000), 5_000_000));
            best.time("char_at x 20M", || assert!(char_reads(&h, 20_000_000) > 0));
            best.time("hash 29 chars x 10M", || assert!(hashes(&h, 10_000_000) != 1));
        });
        best.time("reply concat + display x 500K", || {
            for _ in 0..500_000 / BATCH {
                arena.mutate(|mc| assert!(replies(&Strings::new(mc), BATCH) > 0));
                arena.collect_minor();
            }
        });
        best.time("4-digit bignum mul x 2M", || {
            for _ in 0..2_000_000 / BATCH {
                arena.mutate(|mc| big_muls(&Nums::new(mc), BATCH));
                arena.collect_minor();
            }
        });
        best.time("bignum parse + print x 200K", || {
            for _ in 0..200_000 / BATCH * 10 {
                arena.mutate(|mc| assert!(big_round_trips(&Nums::new(mc), BATCH / 10) > 0));
                arena.collect_minor();
            }
        });
    }
    best.print();
}
