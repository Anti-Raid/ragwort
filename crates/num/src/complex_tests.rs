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

/// Parts small enough that cosh and exp stay finite, with the points where branch cuts and
/// special cases sit. `wide` lets reals be anything, as huge as two digits.
fn moderate(h: &TestHost, rng: &mut Rng, wide: bool) -> TestNumber {
    let exact = |rng: &mut Rng| {
        let n = int::from_i64(h, rng.below(81) as i64 - 40).unwrap();
        let d = int::from_i64(h, rng.below(8) as i64 + 1).unwrap();
        TestReal::Exact(rational::from_parts(h, n, d).unwrap())
    };
    let flonum = |rng: &mut Rng| {
        let special = [0.0, -0.0, 1.0, -1.0, 0.5, -0.5, 2.0, -2.0, 1e-300, -1e-300];
        TestReal::Flonum(match rng.below(3) {
            0 => special[rng.below(special.len() as u64) as usize],
            _ => (rng.u64() >> 11) as f64 / (1u64 << 53) as f64 * 20.0 - 10.0,
        })
    };
    let zero = TestReal::Exact(TestRational::Int(TestInt::Small(0)));
    let (re, im) = match rng.below(6) {
        0 if wide => return TestNumber::Real(h.random_real(rng, 2)),
        0 => return TestNumber::Real(flonum(rng)),
        1 => return TestNumber::Real(exact(rng)),
        2 => (exact(rng), exact(rng)),
        3 => (zero, flonum(rng)),
        _ => (flonum(rng), flonum(rng)),
    };
    rectangular(h, re, im).unwrap()
}

type Unary = fn(&TestHost, TestNumber) -> Result<TestNumber, TestError>;

/// Real inputs match Python's `math` to the bit. Complex ones follow `cmath` to within a few
/// ulps, since some of our formulas are Racket's rather than CPython's.
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
            // Python's hypot is its own, more careful than C's, which Racket and we use.
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

/// The `near` op takes our answer as its last argument and says `ok` if it's close enough.
fn near(oracle: &mut Oracle, args: &[String], ours: String) {
    let mut args = args.to_vec();
    args.push(ours);
    oracle.case("near", &args, "ok".into());
}

#[test]
fn powers() {
    let (mut rng, mut oracle) = (Rng(54), Oracle::default());
    for bits in WIDTHS {
        let h = TestHost::new(bits);
        let r = |n, d| {
            let r = rational::from_parts(&h, int::from_i64(&h, n).unwrap(), int::from_i64(&h, d).unwrap()).unwrap();
            TestNumber::Real(TestReal::Exact(r))
        };
        let f = |f| TestNumber::Real(TestReal::Flonum(f));
        let special_bases = [r(0, 1), r(1, 1), r(-1, 1), r(-8, 1), r(4, 9), f(0.0), f(-0.0), f(1.0), f(-2.0), f(f64::INFINITY), f(f64::NEG_INFINITY), f(f64::NAN)];
        let exponents = [
            r(0, 1),
            r(1, 1),
            r(2, 1),
            r(3, 1),
            r(-1, 1),
            r(-2, 1),
            r(7, 1),
            r(1, 2),
            r(1, 3),
            r(-1, 2),
            r(5, 2),
            f(0.0),
            f(-0.0),
            f(0.5),
            f(2.0),
            f(-3.0),
            f(1.5),
            f(-0.5),
            f(f64::INFINITY),
            f(f64::NEG_INFINITY),
            f(f64::NAN),
        ];
        for _ in 0..ROUNDS / WIDTHS.len() / 4 {
            let z = if rng.bool() { special_bases[rng.below(special_bases.len() as u64) as usize] } else { moderate(&h, &mut rng, true) };
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
    let real = |s: &str| -> TestReal {
        if let Some((n, d)) = s.split_once('/') {
            let n = int::from_i64(h, n.parse().unwrap()).unwrap();
            let d = int::from_i64(h, d.parse().unwrap()).unwrap();
            return TestReal::Exact(rational::from_parts(h, n, d).unwrap());
        }
        match s.parse::<i64>() {
            Ok(n) => TestReal::Exact(TestRational::Int(int::from_i64(h, n).unwrap())),
            Err(_) => TestReal::Flonum(s.parse().unwrap()),
        }
    };
    match text.split_once('|') {
        Some((re, im)) => rectangular(h, real(re), real(im)).unwrap(),
        None => TestNumber::Real(real(text)),
    }
}

/// Racket's printed form, near enough to check examples from its reference.
fn racket(h: &TestHost, z: TestNumber) -> String {
    let real = |x: TestReal| match x {
        TestReal::Exact(r) => rational::to_string(h, r, 10).unwrap(),
        TestReal::Flonum(f) if f.is_nan() => "+nan.0".into(),
        TestReal::Flonum(f) if f.is_infinite() => (if f > 0.0 { "+inf.0" } else { "-inf.0" }).into(),
        TestReal::Flonum(f) if f.fract() == 0.0 && f.abs() < 1e16 => format!("{f:.1}"),
        TestReal::Flonum(f) if f != 0.0 && f.abs() < 1e-4 => format!("{f:e}").replace("e-", "e-"),
        TestReal::Flonum(f) => format!("{f}"),
    };
    match z {
        TestNumber::Real(x) => real(x),
        TestNumber::Complex(re, im) => {
            let im = real(im);
            let sign = if im.starts_with(['-', '+']) { "" } else { "+" };
            let re = if crate::real::is_exact_zero(h, re) { String::new() } else { real(re) };
            format!("{re}{sign}{im}i")
        }
    }
}

/// Examples from Racket's reference, which pin down both exactness and the last digit.
#[test]
fn racket_reference_examples() {
    let h = TestHost::new(64);
    let p = |s| parse(&h, s);
    let pi_half = TestNumber::Real(TestReal::Flonum(std::f64::consts::FRAC_PI_2));
    let check = |got: Result<TestNumber, TestError>, want: &str, what: &str| assert_eq!(racket(&h, got.unwrap()), want, "{what}");
    check(sqrt(&h, p("4/9")), "2/3", "(sqrt 4/9)");
    check(sqrt(&h, p("2")), "1.4142135623730951", "(sqrt 2)");
    check(sqrt(&h, p("-1")), "+1i", "(sqrt -1)");
    check(sqrt(&h, p("-4.0")), "+2.0i", "(sqrt -4.0)");
    check(sqrt(&h, p("-3|4")), "1+2i", "(sqrt -3+4i)");
    check(exp(&h, p("0")), "1", "(exp 0)");
    check(exp(&h, p("1")), "2.718281828459045", "(exp 1)");
    check(exp(&h, p("2|3")), "-7.315110094901103+1.0427436562359045i", "(exp 2+3i)");
    check(log(&h, p("1")), "0", "(log 1)");
    check(log(&h, p("2|3")), "1.2824746787307684+0.982793723247329i", "(log 2+3i)");
    check(log(&h, p("-1")), "+3.141592653589793i", "(log -1)");
    check(log_base(&h, p("100"), p("10")), "2.0", "(log 100 10)");
    check(log_base(&h, p("8"), p("2")), "3.0", "(log 8 2)");
    check(log_base(&h, p("5"), p("5")), "1.0", "(log 5 5)");
    check(sin(&h, p("1.0|5.0")), "62.44551846769654+40.0921657779984i", "(sin 1.0+5.0i)");
    check(cos(&h, p("1.0|5.0")), "40.09580630629883-62.43984868079963i", "(cos 1.0+5.0i)");
    // Racket prints ...597e-5 here. Both are within an ulp of 8.25671983422959604e-5, and our
    // formula, Kahan's, doesn't lose accuracy near poles the way Racket's does.
    check(tan(&h, p("1.0|5.0")), "8.256719834229595e-5+1.0000377833796008i", "(tan 1.0+5.0i)");
    check(asin(&h, p("1.0|5.0")), "0.1937931365549322+2.3309746530493123i", "(asin 1.0+5.0i)");
    check(acos(&h, p("1.0|5.0")), "1.3770031902399644-2.3309746530493123i", "(acos 1.0+5.0i)");
    check(acos(&h, p("0.25")), "1.318116071652818", "(acos 0.25)");
    check(asin(&h, p("0.25")), "0.25268025514207865", "(asin 0.25)");
    check(sin(&h, p("0")), "0", "(sin 0)");
    check(cos(&h, p("0")), "1.0", "(cos 0)");
    check(expt(&h, p("2"), p("3")), "8", "(expt 2 3)");
    check(expt(&h, p("4"), p("0.5")), "2.0", "(expt 4 0.5)");
    check(expt(&h, p("9"), p("1/2")), "3", "(expt 9 1/2)");
    check(expt(&h, p("9"), p("0.5")), "3.0", "(expt 9 0.5)");
    check(expt(&h, p("16"), p("1/4")), "2.0", "(expt 16 1/4)");
    check(expt(&h, p("inf"), p("0")), "1", "(expt +inf.0 0)");
    check(expt(&h, p("nan"), p("0.0")), "1.0", "(expt +nan.0 0.0)");
    check(expt(&h, p("1.0"), p("nan")), "1.0", "(expt 1.0 +nan.0)");
    check(expt(&h, p("0"), p("nan")), "+nan.0", "(expt 0 +nan.0)");
    check(expt(&h, p("0.0"), p("-1")), "+inf.0", "(expt 0.0 -1)");
    check(expt(&h, p("-0.0"), p("-3")), "-inf.0", "(expt -0.0 -3)");
    check(add(&h, add(&h, p("1.0"), p("2|3")).unwrap(), p("5")), "8.0+3.0i", "(+ 1.0 2+3i 5)");
    check(rectangular(&h, real_part(&h, p("3")), real_part(&h, p("4.0"))), "3.0+4.0i", "(make-rectangular 3 4.0)");
    check(polar(&h, real_part(&h, p("10")), real_part(&h, pi_half)), "6.123233995736766e-16+10.0i", "(make-polar 10 pi/2)");
    let real = |x: Result<TestReal, TestError>| TestNumber::Real(x.unwrap());
    check(Ok(real(magnitude(&h, p("3|4")))), "5", "(magnitude 3+4i)");
    check(Ok(real(magnitude(&h, p("-3")))), "3", "(magnitude -3)");
    check(Ok(real(magnitude(&h, p("3.0")))), "3.0", "(magnitude 3.0)");
    check(Ok(real(angle(&h, p("-3")))), "3.141592653589793", "(angle -3)");
    check(Ok(real(angle(&h, p("3.0")))), "0", "(angle 3.0)");
    check(Ok(real(angle(&h, p("3|4")))), "0.9272952180016122", "(angle 3+4i)");
    check(Ok(real(angle(&h, p("inf|inf")))), "0.7853981633974483", "(angle +inf.0+inf.0i)");
    check(Ok(real(imag_part(&h, p("5.0")))), "0", "(imag-part 5.0)");
    let inf = |s| TestReal::Flonum(s);
    check(Ok(real(atan2(&h, inf(f64::INFINITY), inf(f64::NEG_INFINITY)))), "2.356194490192345", "(atan +inf.0 -inf.0)");
    let div0 = Err(TestError::Num(NumError::DivideByZero));
    assert_eq!(log(&h, p("0")), div0, "(log 0)");
    assert_eq!(angle(&h, p("0")).map(TestNumber::Real), div0, "(angle 0)");
    assert_eq!(atan(&h, p("0|1")), div0, "(atan +i)");
    assert_eq!(atan(&h, p("0|-1")), div0, "(atan -i)");
    assert_eq!(log_base(&h, p("2"), p("1")), div0, "(log 2 1)");
    assert_eq!(expt(&h, p("0"), p("-1")), div0, "(expt 0 -1)");
    assert_eq!(expt(&h, p("0"), p("-1|1")), div0, "(expt 0 -1+i)");
    assert_eq!(expt(&h, p("0"), p("0|1")), div0, "(expt 0 +i)");
    check(expt(&h, p("0"), p("1|1")), "0", "(expt 0 1+i)");
    check(expt(&h, p("0"), p("0.0")), "1.0", "(expt 0 0.0)");
}

impl PartialEq for TestNumber {
    fn eq(&self, other: &Self) -> bool {
        format!("{self:?}") == format!("{other:?}")
    }
}

#[test]
fn eqv_needs_matching_parts() {
    let h = TestHost::new(64);
    let p = |s| parse(&h, s);
    assert!(eqv(&h, p("1|2"), p("1|2")));
    assert!(!eqv(&h, p("1|2"), p("1.0|2.0")));
    assert!(!eqv(&h, p("0|2.0"), p("0.0|2.0")));
    assert!(!eqv(&h, p("1.0|0.0"), p("1.0|-0.0")));
    assert!(!eqv(&h, p("1.0|0.0"), p("1.0")));
    assert!(equal(&h, p("1.0|0.0"), p("1")).unwrap());
    assert!(eqv(&h, p("nan|1.0"), p("nan|1.0")));
    let hash_of = |z| {
        let mut state = std::hash::DefaultHasher::new();
        hash(&h, z, &mut state);
        std::hash::Hasher::finish(&state)
    };
    assert_eq!(hash_of(p("3/4|-2")), hash_of(mul(&h, p("3/8|-1"), p("2")).unwrap()));
}

#[test]
fn huge_exact_powers_fail_like_running_out_of_memory() {
    let h = TestHost::new(64);
    let huge = int::arithmetic_shift(&h, int::from_i64(&h, 1).unwrap(), 70).unwrap();
    let huge = TestNumber::Real(TestReal::Exact(TestRational::Int(huge)));
    let p = |s| parse(&h, s);
    assert_eq!(expt(&h, p("2"), huge), Err(TestError::TooBig));
    assert_eq!(expt(&h, p("1|1"), huge), Err(TestError::TooBig));
    assert_eq!(racket(&h, expt(&h, p("-1"), huge).unwrap()), "1");
}

/// A ratio whose parts have up to `max_len` digits, so it can be far outside what doubles hold.
fn spread(h: &TestHost, rng: &mut Rng, max_len: usize) -> TestReal {
    let num = int::from_digits(h, rng.bool(), crate::bigint::Digits::new(&rng.nonzero(max_len))).unwrap();
    let den = int::from_digits(h, false, crate::bigint::Digits::new(&rng.nonzero(max_len))).unwrap();
    TestReal::Exact(rational::from_parts(h, num, den).unwrap())
}

/// Exact numbers whose doubles would overflow or underflow still get roots, logs and angles
/// as good as those of numbers in range.
#[test]
fn exact_numbers_beyond_the_range_of_doubles() {
    let (mut rng, mut oracle) = (Rng(55), Oracle::default());
    let mut h = TestHost::new(64);
    // Few, as numbers this size are slow in debug builds.
    for i in 0..ROUNDS / 16 {
        // A host holds only so many bignums.
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

/// Parts big enough that `exp` and `cosh` overflow, or small enough to be subnormal.
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
