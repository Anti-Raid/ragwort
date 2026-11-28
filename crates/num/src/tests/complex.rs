use crate::complex::*;
use crate::int::{self, NumError};
use crate::rational;
use crate::testing::{Oracle, ROUNDS, Rng, TestError, TestHost, TestInt, TestNumber, TestRational, TestReal, WIDTHS, error_token};

type Op = fn(&TestHost, TestNumber, TestNumber) -> Result<TestNumber, TestError>;

fn show(h: &TestHost, x: Result<TestNumber, TestError>) -> String {
    x.map_or_else(error_token, |x| h.show_number(x))
}

fn show_real(h: &TestHost, x: Result<TestReal, TestError>) -> String {
    x.map_or_else(error_token, |x| h.show_real(x))
}

#[test]
fn arithmetic() {
    let ops: [(&str, Op); 4] = [("xadd", add), ("xsub", sub), ("xmul", mul), ("xdiv", div)];
    let (mut rng, mut oracle) = (Rng(51), Oracle::default());
    for bits in WIDTHS {
        let h = TestHost::new(bits);
        for _ in 0..ROUNDS / WIDTHS.len() {
            let (x, y) = (h.random_number(&mut rng, 2), h.random_number(&mut rng, 2));
            let args = [h.show_number(x), h.show_number(y)];
            for (name, op) in ops {
                oracle.case(name, &args, show(&h, op(&h, x, y)));
            }
            oracle.case("xeq", &args, (equal(&h, x, y).unwrap() as u8).to_string());
            oracle.case("xinexact", &args[..1], show(&h, inexact(&h, x)));
            oracle.case("xexact", &args[..1], show(&h, exact(&h, x)));
        }
    }
    oracle.check();
}

#[test]
fn rectangular_keeps_racket_shapes() {
    let (mut rng, mut oracle) = (Rng(52), Oracle::default());
    for bits in WIDTHS {
        let h = TestHost::new(bits);
        for _ in 0..ROUNDS / WIDTHS.len() {
            let (re, im) = (h.random_real(&mut rng, 2), h.random_real(&mut rng, 2));
            oracle.case("xrect", &[h.show_real(re), h.show_real(im)], show(&h, rectangular(&h, re, im)));
        }
    }
    oracle.check();
}

/// Returns a number whose parts are small enough that `cosh` and `exp` stay finite. The parts include the points where branch cuts and
/// special cases lie. With `wide`, a real result can be any real whose integers have up to two digits.
fn moderate(h: &TestHost, rng: &mut Rng, wide: bool) -> TestNumber {
    fn exact(h: &TestHost, rng: &mut Rng) -> TestReal {
        let n = int::from_i64(h, rng.below(81) as i64 - 40).unwrap();
        let d = int::from_i64(h, rng.below(8) as i64 + 1).unwrap();
        TestReal::Exact(rational::from_parts(h, n, d).unwrap())
    }
    fn flonum(rng: &mut Rng) -> TestReal {
        let special = [0.0, -0.0, 1.0, -1.0, 0.5, -0.5, 2.0, -2.0, 1e-300, -1e-300];
        TestReal::Flonum(match rng.below(3) {
            0 => special[rng.below(special.len() as u64) as usize],
            _ => (rng.u64() >> 11) as f64 / (1u64 << 53) as f64 * 20.0 - 10.0,
        })
    }
    let zero = TestReal::Exact(TestRational::Int(TestInt::Small(0)));
    let (re, im) = match rng.below(6) {
        0 if wide => return TestNumber::Real(h.random_real(rng, 2)),
        0 => return TestNumber::Real(flonum(rng)),
        1 => return TestNumber::Real(exact(h, rng)),
        2 => (exact(h, rng), exact(h, rng)),
        3 => (zero, flonum(rng)),
        _ => (flonum(rng), flonum(rng)),
    };
    rectangular(h, re, im).unwrap()
}

type Unary = fn(&TestHost, TestNumber) -> Result<TestNumber, TestError>;

/// Real inputs must match Python's `math` to the bit. Complex inputs must match `cmath` to within a few
/// ulps, because some of our formulas are Racket's and not CPython's. The inverse functions are compared loosely for every input.
#[test]
fn elementary_functions() {
    let functions: [(&str, Unary); 9] =
        [("sqrt", sqrt), ("exp", exp), ("log", log), ("sin", sin), ("cos", cos), ("tan", tan), ("asin", asin), ("acos", acos), ("atan", atan)];
    let (mut rng, mut oracle) = (Rng(53), Oracle::default());
    for bits in WIDTHS {
        let h = TestHost::new(bits);
        for _ in 0..ROUNDS / WIDTHS.len() {
            let z = moderate(&h, &mut rng, true);
            let zs = h.show_number(z);
            let loose = !is_real(&h, z);
            for (name, f) in functions {
                let loose = loose || name.starts_with('a');
                near(&mut oracle, &[name.into(), (loose as u8).to_string(), zs.clone()], show(&h, f(&h, z)));
            }
            // Python has its own `hypot`, which is more careful than the C library's. Racket and this crate use the C library's, so the comparison is loose.
            near(&mut oracle, &["magnitude".into(), "1".into(), zs.clone()], show_real(&h, magnitude(&h, z)));
            near(&mut oracle, &["angle".into(), "0".into(), zs.clone()], show_real(&h, angle(&h, z)));
            let b = moderate(&h, &mut rng, true);
            near(&mut oracle, &["logb".into(), "1".into(), zs.clone(), h.show_number(b)], show(&h, log_base(&h, z, b)));
            let (y, x) = (h.random_real(&mut rng, 2), h.random_real(&mut rng, 2));
            near(&mut oracle, &["atan2".into(), "0".into(), h.show_real(y), h.show_real(x)], show_real(&h, atan2(&h, y, x)));
            near(&mut oracle, &["polar".into(), "0".into(), h.show_real(y), h.show_real(x)], show(&h, polar(&h, y, x)));
        }
    }
    oracle.check();
}

/// Adds a `near` case to `oracle`. The `near` operation takes our result as its last argument and answers `ok` if the result is close enough.
fn near(oracle: &mut Oracle, args: &[String], ours: String) {
    let mut args = args.to_vec();
    args.push(ours);
    oracle.case("near", &args, "ok".into());
}

#[test]
fn powers() {
    fn ratio(h: &TestHost, n: i64, d: i64) -> TestNumber {
        let r = rational::from_parts(h, int::from_i64(h, n).unwrap(), int::from_i64(h, d).unwrap()).unwrap();
        TestNumber::Real(TestReal::Exact(r))
    }
    fn flo(float: f64) -> TestNumber {
        TestNumber::Real(TestReal::Flonum(float))
    }
    let (mut rng, mut oracle) = (Rng(54), Oracle::default());
    for bits in WIDTHS {
        let h = TestHost::new(bits);
        let special_bases = [ratio(&h, 0, 1), ratio(&h, 1, 1), ratio(&h, -1, 1), ratio(&h, -8, 1), ratio(&h, 4, 9), flo(0.0), flo(-0.0), flo(1.0), flo(-2.0), flo(f64::INFINITY), flo(f64::NEG_INFINITY), flo(f64::NAN)];
        let exponents = [
            ratio(&h, 0, 1),
            ratio(&h, 1, 1),
            ratio(&h, 2, 1),
            ratio(&h, 3, 1),
            ratio(&h, -1, 1),
            ratio(&h, -2, 1),
            ratio(&h, 7, 1),
            ratio(&h, 1, 2),
            ratio(&h, 1, 3),
            ratio(&h, -1, 2),
            ratio(&h, 5, 2),
            flo(0.0),
            flo(-0.0),
            flo(0.5),
            flo(2.0),
            flo(-3.0),
            flo(1.5),
            flo(-0.5),
            flo(f64::INFINITY),
            flo(f64::NEG_INFINITY),
            flo(f64::NAN),
        ];
        for _ in 0..ROUNDS / WIDTHS.len() / 4 {
            let z = if rng.bool() {
                special_bases[rng.below(special_bases.len() as u64) as usize]
            } else {
                moderate(&h, &mut rng, true)
            };
            let w = match rng.below(3) {
                0 => moderate(&h, &mut rng, false),
                _ => exponents[rng.below(exponents.len() as u64) as usize],
            };
            near(&mut oracle, &["expt".into(), "1".into(), h.show_number(z), h.show_number(w)], show(&h, expt(&h, z, w)));
        }
    }
    oracle.check();
}

fn parse(h: &TestHost, text: &str) -> TestNumber {
    fn real(h: &TestHost, text: &str) -> TestReal {
        if let Some((n, d)) = text.split_once('/') {
            let n = int::from_i64(h, n.parse().unwrap()).unwrap();
            let d = int::from_i64(h, d.parse().unwrap()).unwrap();
            return TestReal::Exact(rational::from_parts(h, n, d).unwrap());
        }
        match text.parse::<i64>() {
            Ok(n) => TestReal::Exact(TestRational::Int(int::from_i64(h, n).unwrap())),
            Err(_) => TestReal::Flonum(text.parse().unwrap()),
        }
    }
    match text.split_once('|') {
        Some((re, im)) => rectangular(h, real(h, re), real(h, im)).unwrap(),
        None => TestNumber::Real(real(h, text)),
    }
}

/// Returns `z` in Racket's printed form. The form is close enough to check the examples from the Racket reference.
fn racket(h: &TestHost, z: TestNumber) -> String {
    fn real(h: &TestHost, x: TestReal) -> String {
        match x {
            TestReal::Exact(r) => rational::to_string(h, r, 10).unwrap(),
            TestReal::Flonum(f) if f.is_nan() => "+nan.0".into(),
            TestReal::Flonum(f) if f.is_infinite() => {
                let text = if f > 0.0 {
                    "+inf.0"
                } else {
                    "-inf.0"
                };
                text.into()
            }
            TestReal::Flonum(f) if f.fract() == 0.0 && f.abs() < 1e16 => format!("{f:.1}"),
            TestReal::Flonum(f) if f != 0.0 && f.abs() < 1e-4 => format!("{f:e}").replace("e-", "e-"),
            TestReal::Flonum(f) => format!("{f}"),
        }
    }
    match z {
        TestNumber::Real(x) => real(h, x),
        TestNumber::Complex(re, im) => {
            let im = real(h, im);
            let sign = if im.starts_with(['-', '+']) {
                ""
            } else {
                "+"
            };
            let re = if crate::real::is_exact_zero(h, re) {
                String::new()
            } else {
                real(h, re)
            };
            format!("{re}{sign}{im}i")
        }
    }
}

/// Returns whether `z` prints as `want` after each of its flonum parts is moved by at most one ulp.
fn within_an_ulp(h: &TestHost, z: TestNumber, want: &str) -> bool {
    fn near(x: TestReal) -> Vec<TestReal> {
        match x {
            TestReal::Flonum(f) if f.is_finite() => vec![x, TestReal::Flonum(f.next_up()), TestReal::Flonum(f.next_down())],
            _ => vec![x],
        }
    }
    match z {
        TestNumber::Real(x) => near(x).into_iter().any(|x| racket(h, TestNumber::Real(x)) == want),
        TestNumber::Complex(re, im) => near(re)
            .into_iter()
            .any(|re| near(im).into_iter().any(|im| racket(h, TestNumber::Complex(re, im)) == want)),
    }
}

/// Examples from the Racket reference. They fix the exactness of each result and, to within an ulp, its digits. Like
/// Racket and Chez, this crate takes `exp`, `sin` and similar functions from the system's maths library.
/// Those libraries differ in the last place: FreeBSD's `exp(1)` is one ulp above the value from macOS and glibc.
#[test]
fn racket_reference_examples() {
    let h = TestHost::new(64);
    fn check(h: &TestHost, got: Result<TestNumber, TestError>, want: &str, what: &str) {
        let got = got.unwrap();
        let shown = racket(h, got);
        assert!(shown == want || within_an_ulp(h, got, want), "{what}: {shown}, want {want}");
    }
    fn real(x: Result<TestReal, TestError>) -> TestNumber {
        TestNumber::Real(x.unwrap())
    }
    let pi_half = TestNumber::Real(TestReal::Flonum(std::f64::consts::FRAC_PI_2));
    check(&h, sqrt(&h, parse(&h, "4/9")), "2/3", "(sqrt 4/9)");
    check(&h, sqrt(&h, parse(&h, "2")), "1.4142135623730951", "(sqrt 2)");
    check(&h, sqrt(&h, parse(&h, "-1")), "+1i", "(sqrt -1)");
    check(&h, sqrt(&h, parse(&h, "-4.0")), "+2.0i", "(sqrt -4.0)");
    check(&h, sqrt(&h, parse(&h, "-3|4")), "1+2i", "(sqrt -3+4i)");
    check(&h, exp(&h, parse(&h, "0")), "1", "(exp 0)");
    check(&h, exp(&h, parse(&h, "1")), "2.718281828459045", "(exp 1)");
    check(&h, exp(&h, parse(&h, "2|3")), "-7.315110094901103+1.0427436562359045i", "(exp 2+3i)");
    check(&h, log(&h, parse(&h, "1")), "0", "(log 1)");
    check(&h, log(&h, parse(&h, "2|3")), "1.2824746787307684+0.982793723247329i", "(log 2+3i)");
    check(&h, log(&h, parse(&h, "-1")), "+3.141592653589793i", "(log -1)");
    check(&h, log_base(&h, parse(&h, "100"), parse(&h, "10")), "2.0", "(log 100 10)");
    check(&h, log_base(&h, parse(&h, "8"), parse(&h, "2")), "3.0", "(log 8 2)");
    check(&h, log_base(&h, parse(&h, "5"), parse(&h, "5")), "1.0", "(log 5 5)");
    check(&h, sin(&h, parse(&h, "1.0|5.0")), "62.44551846769654+40.0921657779984i", "(sin 1.0+5.0i)");
    check(&h, cos(&h, parse(&h, "1.0|5.0")), "40.09580630629883-62.43984868079963i", "(cos 1.0+5.0i)");
    // Racket prints ...597e-5 here. Both are within an ulp of 8.25671983422959604e-5, and our
    // formula, Kahan's, doesn't lose accuracy near poles the way Racket's does.
    check(&h, tan(&h, parse(&h, "1.0|5.0")), "8.256719834229595e-5+1.0000377833796008i", "(tan 1.0+5.0i)");
    check(&h, asin(&h, parse(&h, "1.0|5.0")), "0.1937931365549322+2.3309746530493123i", "(asin 1.0+5.0i)");
    check(&h, acos(&h, parse(&h, "1.0|5.0")), "1.3770031902399644-2.3309746530493123i", "(acos 1.0+5.0i)");
    check(&h, acos(&h, parse(&h, "0.25")), "1.318116071652818", "(acos 0.25)");
    check(&h, asin(&h, parse(&h, "0.25")), "0.25268025514207865", "(asin 0.25)");
    check(&h, sin(&h, parse(&h, "0")), "0", "(sin 0)");
    check(&h, cos(&h, parse(&h, "0")), "1.0", "(cos 0)");
    check(&h, expt(&h, parse(&h, "2"), parse(&h, "3")), "8", "(expt 2 3)");
    check(&h, expt(&h, parse(&h, "4"), parse(&h, "0.5")), "2.0", "(expt 4 0.5)");
    check(&h, expt(&h, parse(&h, "9"), parse(&h, "1/2")), "3", "(expt 9 1/2)");
    check(&h, expt(&h, parse(&h, "9"), parse(&h, "0.5")), "3.0", "(expt 9 0.5)");
    check(&h, expt(&h, parse(&h, "16"), parse(&h, "1/4")), "2.0", "(expt 16 1/4)");
    check(&h, expt(&h, parse(&h, "inf"), parse(&h, "0")), "1", "(expt +inf.0 0)");
    check(&h, expt(&h, parse(&h, "nan"), parse(&h, "0.0")), "1.0", "(expt +nan.0 0.0)");
    check(&h, expt(&h, parse(&h, "1.0"), parse(&h, "nan")), "1.0", "(expt 1.0 +nan.0)");
    check(&h, expt(&h, parse(&h, "0"), parse(&h, "nan")), "+nan.0", "(expt 0 +nan.0)");
    check(&h, expt(&h, parse(&h, "0.0"), parse(&h, "-1")), "+inf.0", "(expt 0.0 -1)");
    check(&h, expt(&h, parse(&h, "-0.0"), parse(&h, "-3")), "-inf.0", "(expt -0.0 -3)");
    check(&h, add(&h, add(&h, parse(&h, "1.0"), parse(&h, "2|3")).unwrap(), parse(&h, "5")), "8.0+3.0i", "(+ 1.0 2+3i 5)");
    check(&h, rectangular(&h, real_part(&h, parse(&h, "3")), real_part(&h, parse(&h, "4.0"))), "3.0+4.0i", "(make-rectangular 3 4.0)");
    check(&h, polar(&h, real_part(&h, parse(&h, "10")), real_part(&h, pi_half)), "6.123233995736766e-16+10.0i", "(make-polar 10 pi/2)");
    check(&h, Ok(real(magnitude(&h, parse(&h, "3|4")))), "5", "(magnitude 3+4i)");
    check(&h, Ok(real(magnitude(&h, parse(&h, "-3")))), "3", "(magnitude -3)");
    check(&h, Ok(real(magnitude(&h, parse(&h, "3.0")))), "3.0", "(magnitude 3.0)");
    check(&h, Ok(real(angle(&h, parse(&h, "-3")))), "3.141592653589793", "(angle -3)");
    check(&h, Ok(real(angle(&h, parse(&h, "3.0")))), "0", "(angle 3.0)");
    check(&h, Ok(real(angle(&h, parse(&h, "3|4")))), "0.9272952180016122", "(angle 3+4i)");
    check(&h, Ok(real(angle(&h, parse(&h, "inf|inf")))), "0.7853981633974483", "(angle +inf.0+inf.0i)");
    check(&h, Ok(real(imag_part(&h, parse(&h, "5.0")))), "0", "(imag-part 5.0)");
    check(&h, Ok(real(atan2(&h, TestReal::Flonum(f64::INFINITY), TestReal::Flonum(f64::NEG_INFINITY)))), "2.356194490192345", "(atan +inf.0 -inf.0)");
    let div0 = Err(TestError::Num(NumError::DivideByZero));
    assert_eq!(log(&h, parse(&h, "0")), div0, "(log 0)");
    assert_eq!(angle(&h, parse(&h, "0")).map(TestNumber::Real), div0, "(angle 0)");
    assert_eq!(atan(&h, parse(&h, "0|1")), div0, "(atan +i)");
    assert_eq!(atan(&h, parse(&h, "0|-1")), div0, "(atan -i)");
    assert_eq!(log_base(&h, parse(&h, "2"), parse(&h, "1")), div0, "(log 2 1)");
    assert_eq!(expt(&h, parse(&h, "0"), parse(&h, "-1")), div0, "(expt 0 -1)");
    assert_eq!(expt(&h, parse(&h, "0"), parse(&h, "-1|1")), div0, "(expt 0 -1+i)");
    assert_eq!(expt(&h, parse(&h, "0"), parse(&h, "0|1")), div0, "(expt 0 +i)");
    check(&h, expt(&h, parse(&h, "0"), parse(&h, "1|1")), "0", "(expt 0 1+i)");
    check(&h, expt(&h, parse(&h, "0"), parse(&h, "0.0")), "1.0", "(expt 0 0.0)");
}

impl PartialEq for TestNumber {
    fn eq(&self, other: &Self) -> bool {
        format!("{self:?}") == format!("{other:?}")
    }
}

#[test]
fn eqv_needs_matching_parts() {
    fn hash_of(h: &TestHost, z: TestNumber) -> u64 {
        let mut state = std::hash::DefaultHasher::new();
        hash(h, z, &mut state);
        std::hash::Hasher::finish(&state)
    }
    let h = TestHost::new(64);
    assert!(eqv(&h, parse(&h, "1|2"), parse(&h, "1|2")));
    assert!(!eqv(&h, parse(&h, "1|2"), parse(&h, "1.0|2.0")));
    assert!(!eqv(&h, parse(&h, "0|2.0"), parse(&h, "0.0|2.0")));
    assert!(!eqv(&h, parse(&h, "1.0|0.0"), parse(&h, "1.0|-0.0")));
    assert!(!eqv(&h, parse(&h, "1.0|0.0"), parse(&h, "1.0")));
    assert!(equal(&h, parse(&h, "1.0|0.0"), parse(&h, "1")).unwrap());
    assert!(eqv(&h, parse(&h, "nan|1.0"), parse(&h, "nan|1.0")));
    assert_eq!(hash_of(&h, parse(&h, "3/4|-2")), hash_of(&h, mul(&h, parse(&h, "3/8|-1"), parse(&h, "2")).unwrap()));
}

#[test]
fn huge_exact_powers_fail_like_running_out_of_memory() {
    let h = TestHost::new(64);
    let huge = int::arithmetic_shift(&h, int::from_i64(&h, 1).unwrap(), 70).unwrap();
    let huge = TestNumber::Real(TestReal::Exact(TestRational::Int(huge)));
    assert_eq!(expt(&h, parse(&h, "2"), huge), Err(TestError::TooBig));
    assert_eq!(expt(&h, parse(&h, "1|1"), huge), Err(TestError::TooBig));
    assert_eq!(racket(&h, expt(&h, parse(&h, "-1"), huge).unwrap()), "1");
}

/// Returns a ratio whose parts have up to `max_len` digits each. Its magnitude can be far outside the range of `f64`.
fn spread(h: &TestHost, rng: &mut Rng, max_len: usize) -> TestReal {
    let num = int::from_digits(h, rng.bool(), crate::bigint::Digits::new(&rng.nonzero(max_len))).unwrap();
    let den = int::from_digits(h, false, crate::bigint::Digits::new(&rng.nonzero(max_len))).unwrap();
    TestReal::Exact(rational::from_parts(h, num, den).unwrap())
}

/// Exact numbers whose `f64` would overflow or underflow still get square roots, logarithms and angles
/// as accurate as those of numbers in range.
#[test]
fn exact_numbers_beyond_the_range_of_doubles() {
    let (mut rng, mut oracle) = (Rng(55), Oracle::default());
    let mut h = TestHost::new(64);
    // Only a few rounds, because numbers of this size are slow in debug builds.
    for i in 0..ROUNDS / 16 {
        // A test host has a fixed capacity for bignums, so start a new host every 50 rounds.
        if i % 50 == 0 {
            h = TestHost::new(64);
        }
        let (x, y) = (spread(&h, &mut rng, 20), spread(&h, &mut rng, 20));
        let z = rectangular(&h, x, y).unwrap();
        for (name, f) in [("sqrt", sqrt as Unary), ("log", log)] {
            let ours = show(&h, f(&h, TestNumber::Real(x)));
            near(&mut oracle, &[name.into(), "0".into(), h.show_real(x)], ours);
        }
        near(&mut oracle, &["angle".into(), "0".into(), h.show_number(z)], show_real(&h, angle(&h, z)));
        near(&mut oracle, &["magnitude".into(), "0".into(), h.show_number(z)], show_real(&h, magnitude(&h, z)));
        near(&mut oracle, &["atan2".into(), "0".into(), h.show_real(y), h.show_real(x)], show_real(&h, atan2(&h, y, x)));
    }
    oracle.check();
}

/// Tests parts that are large enough for `exp` and `cosh` to overflow, or small enough to be subnormal.
#[test]
fn extreme_parts() {
    let functions: [(&str, Unary); 9] =
        [("sqrt", sqrt), ("exp", exp), ("log", log), ("sin", sin), ("cos", cos), ("tan", tan), ("asin", asin), ("acos", acos), ("atan", atan)];
    let parts = [0.0, -0.0, 1.0, -2.5, 700.0, 708.5, 709.5, -709.5, 710.0, -745.5, 1e-300, 1e-310, -2e-315, 5e-324, 1e300, -1e308, 1.7e308];
    let mut oracle = Oracle::default();
    let h = TestHost::new(64);
    for re in parts {
        for im in parts {
            let Ok(z) = rectangular(&h, TestReal::Flonum(re), TestReal::Flonum(im)) else { continue };
            let zs = h.show_number(z);
            for (name, f) in functions {
                near(&mut oracle, &[name.into(), "1".into(), zs.clone()], show(&h, f(&h, z)));
            }
        }
    }
    oracle.check();
}

/// Checks Racket's results for exact parts beyond the range of `f64`, and for negative bases with
/// exact fractional powers. One of those powers rounds to an integral `f64`.
#[test]
#[allow(clippy::approx_constant, reason = "Racket's printed answers")]
fn racket_agrees_past_the_range_of_doubles() {
    fn int(h: &TestHost, n: i64) -> TestInt {
        int::from_i64(h, n).unwrap()
    }
    // Returns `n · 10^k` as an exact number.
    fn exact(h: &TestHost, n: i64, k: i64) -> TestReal {
        let power = int::expt(h, int(h, 10), k.unsigned_abs()).unwrap();
        let r = if k >= 0 {
            TestRational::Int(int::mul(h, int(h, n), power).unwrap())
        } else {
            rational::from_parts(h, int(h, n), power).unwrap()
        };
        TestReal::Exact(r)
    }
    fn complex(h: &TestHost, a: TestReal, b: TestReal) -> TestNumber {
        rectangular(h, a, b).unwrap()
    }
    let h = TestHost::new(64);
    let two_100 = int::arithmetic_shift(&h, int(&h, 1), 100).unwrap();
    let near_one = TestNumber::Real(TestReal::Exact(rational::from_parts(&h, int::add(&h, two_100, int(&h, 1)).unwrap(), two_100).unwrap()));
    let cases = [
        ("(sqrt 10^400+10^400i)", sqrt(&h, complex(&h, exact(&h, 1, 400), exact(&h, 1, 400))), (1.09868411346781e200, 4.550898605622274e199)),
        ("(sqrt 10^400+i)", sqrt(&h, complex(&h, exact(&h, 1, 400), exact(&h, 1, 0))), (1e200, 0.0)),
        ("(sqrt 1+10^-400i)", sqrt(&h, complex(&h, exact(&h, 1, 0), exact(&h, 1, -400))), (1.0, 0.0)),
        ("(sqrt 10^-400+3·10^-400i)", sqrt(&h, complex(&h, exact(&h, 1, -400), exact(&h, 3, -400))), (1.442615274452683e-200, 1.0397782600555706e-200)),
        ("(expt -2 (+ 1 2^-100))", expt(&h, parse(&h, "-2"), near_one), (-2.0, 2.4492935982947064e-16)),
        ("(expt -8 1/3)", expt(&h, parse(&h, "-8"), parse(&h, "1/3")), (1.0, 1.732050807568877)),
        ("(expt -2.0 0.5)", expt(&h, parse(&h, "-2.0"), parse(&h, "0.5")), (8.659560562354932e-17, 1.414213562373095)),
    ];
    for (what, got, (re, im)) in cases {
        let (re, im): (f64, f64) = (re, im);
        let Ok(TestNumber::Complex(TestReal::Flonum(x), TestReal::Flonum(y))) = got else { panic!("{what}: {got:?}") };
        let tolerance = 4.0 * f64::EPSILON * re.abs().max(im.abs());
        assert!((x - re).abs() <= tolerance && (y - im).abs() <= tolerance, "{what} = {x:e}+{y:e}i, want {re:e}+{im:e}i");
    }
}

/// Checks the special values of C99 Annex G, read from `special.txt` (see `special.py`). A NaN matches any NaN.
/// Zeros and infinities must match with their signs, unless the table leaves a sign unspecified.
/// Other finite parts may differ by a few ulps.
#[test]
fn special_values_follow_annex_g() {
    let h = TestHost::new(64);
    let functions: [(&str, Unary); 9] =
        [("exp", exp), ("log", log), ("sqrt", sqrt), ("sin", sin), ("cos", cos), ("tan", tan), ("asin", asin), ("acos", acos), ("atan", atan)];
    fn flonum(x: TestReal) -> f64 {
        match x {
            TestReal::Flonum(f) => f,
            TestReal::Exact(_) => panic!("exact part"),
        }
    }
    fn close(want: f64, got: f64, any_sign: bool, scale: f64) -> bool {
        let (want, got) = if any_sign {
            (want.abs(), got.abs())
        } else {
            (want, got)
        };
        want.is_nan() && got.is_nan()
            || want.to_bits() == got.to_bits()
            || want.is_finite() && got.is_finite() && (want != 0.0 || got != 0.0) && (want - got).abs() <= 4.0 * f64::EPSILON * scale
    }
    let mut wrong = Vec::new();
    for line in include_str!("../special.txt").lines() {
        let mut words = line.split(' ');
        let name = words.next().unwrap();
        let [re, im, want_re, want_im] = [(); 4].map(|_| f64::from_bits(u64::from_str_radix(words.next().unwrap(), 16).unwrap()));
        let loose = words.next().unwrap();
        let f = functions.iter().find(|(n, _)| *n == name).unwrap().1;
        let z = rectangular(&h, TestReal::Flonum(re), TestReal::Flonum(im)).unwrap();
        let (got_re, got_im) = match f(&h, z) {
            Ok(TestNumber::Complex(r, i)) => (flonum(r), flonum(i)),
            Ok(TestNumber::Real(r)) => (flonum(r), 0.0),
            Err(e) => panic!("{name}({re:?}, {im:?}): {e:?}"),
        };
        let scale = [want_re, want_im].iter().filter(|f| f.is_finite()).fold(0.0f64, |m, f| m.max(f.abs()));
        if !close(want_re, got_re, loose.contains('r'), scale) || !close(want_im, got_im, loose.contains('i'), scale) {
            wrong.push(format!("{name}({re:?}, {im:?}) = ({got_re:?}, {got_im:?}), want ({want_re:?}, {want_im:?})"));
        }
    }
    assert!(wrong.is_empty(), "{} wrong:\n{}", wrong.len(), wrong.join("\n"));
}
