//! Test helpers. Answers are checked against Python's integers: each test runs its cases, then
//! has `oracle.py` answer all of them in one batch. Under Miri the cases still run, unchecked.

use std::cell::{Cell, OnceCell};
use std::fmt::Write as _;
use std::io::Write as _;
use std::process::{Command, Stdio};

use crate::bigint::{Digit, Digits, RWDigits};
use crate::int::*;

pub const ROUNDS: usize = if cfg!(miri) { 30 } else { 4000 };

/// splitmix64
pub struct Rng(pub u64);

impl Rng {
    pub fn u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ z >> 30).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ z >> 27).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ z >> 31
    }

    pub fn below(&mut self, n: u64) -> u64 {
        self.u64() % n
    }

    pub fn bool(&mut self) -> bool {
        self.u64() & 1 == 1
    }

    /// Up to `max_len` digits that often sit at the edges: all ones, zero, a lone top bit.
    pub fn digits(&mut self, max_len: usize) -> Vec<Digit> {
        let len = self.below(max_len as u64 + 1) as usize;
        let mut x: Vec<Digit> = (0..len)
            .map(|_| match self.below(6) {
                0 => 0,
                1 => Digit::MAX,
                2 => 1 << 63,
                3 => self.below(4),
                _ => self.u64(),
            })
            .collect();
        if let Some(top) = x.last_mut()
            && *top == 0
        {
            *top = self.u64().max(1);
        }
        x
    }

    pub fn nonzero(&mut self, max_len: usize) -> Vec<Digit> {
        loop {
            let x = self.digits(max_len);
            if !x.is_empty() {
                return x;
            }
        }
    }
}

pub fn hex(x: Digits<'_>) -> String {
    let x = x.normalize();
    let mut s = format!("{:x}", x.msd());
    for i in (0..x.len().saturating_sub(1)).rev() {
        write!(s, "{:016x}", x[i]).unwrap();
    }
    s
}

pub fn signed(x: Digits<'_>, negative: bool) -> String {
    if negative && !x.is_zero() { format!("-{}", hex(x)) } else { hex(x) }
}

#[derive(Default)]
pub struct Oracle {
    input: String,
    ours: Vec<String>,
}

impl Oracle {
    pub fn case(&mut self, op: &str, args: &[String], ours: String) {
        writeln!(self.input, "{op} {}", args.join(" ")).unwrap();
        self.ours.push(ours);
    }

    pub fn check(self) {
        if cfg!(miri) {
            return;
        }
        let mut child = Command::new("python3")
            .args(["-I", "-c", include_str!("oracle.py")])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("the bigint tests check their answers with python3");
        let mut stdin = child.stdin.take().unwrap();
        let input = self.input.clone();
        let writer = std::thread::spawn(move || stdin.write_all(input.as_bytes()));
        let output = child.wait_with_output().unwrap();
        let written = writer.join().unwrap();
        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
        written.unwrap();
        let expected = String::from_utf8(output.stdout).unwrap();
        assert_eq!(expected.lines().count(), self.ours.len());
        for ((case, want), ours) in self.input.lines().zip(expected.lines()).zip(&self.ours) {
            assert_eq!(ours, want, "{case}");
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum TestInt {
    Small(i64),
    Big { negative: bool, at: usize },
}

#[derive(Debug, PartialEq)]
pub enum TestError {
    Num(NumError),
    TooBig,
}

impl From<NumError> for TestError {
    fn from(e: NumError) -> Self {
        Self::Num(e)
    }
}

/// Holds small integers in `bits` bits, so narrow hosts take the big paths more often. Big
/// ones go in cells that are set once, so views can borrow them while more are added.
pub struct TestHost {
    bits: u32,
    bigs: Box<[OnceCell<Box<[Digit]>>]>,
    used: Cell<usize>,
}

pub const CAPACITY: usize = if cfg!(miri) { 1 << 12 } else { 1 << 16 };

impl TestHost {
    pub fn new(bits: u32) -> Self {
        Self { bits, bigs: (0..CAPACITY).map(|_| OnceCell::new()).collect(), used: Cell::new(0) }
    }

    pub fn digits(&self, at: usize) -> &[Digit] {
        self.bigs[at].get().expect("made by this host")
    }
}

impl Host for TestHost {
    type Int = TestInt;
    type Error = TestError;

    fn view(&self, x: TestInt) -> IntView<'_> {
        match x {
            TestInt::Small(n) => IntView::Small(n),
            TestInt::Big { negative, at } => IntView::Big { negative, digits: Digits::new(self.digits(at)) },
        }
    }

    fn small(&self, n: i64) -> Option<TestInt> {
        let fits = self.bits >= 64 || (-(1i64 << (self.bits - 1))..1i64 << (self.bits - 1)).contains(&n);
        fits.then_some(TestInt::Small(n))
    }

    fn big(&self, negative: bool, len: usize, init: impl FnOnce(RWDigits<'_>) -> usize) -> Result<TestInt, TestError> {
        if len > 1 << 12 {
            return Err(TestError::TooBig);
        }
        let mut digits = vec![0; len];
        let kept = init(RWDigits::new(&mut digits));
        digits.truncate(kept);
        let at = self.used.get();
        self.bigs.get(at).expect("test host is full").set(digits.into_boxed_slice()).expect("cells are set once");
        self.used.set(at + 1);
        Ok(TestInt::Big { negative, at })
    }
}

pub const WIDTHS: [u32; 4] = [64, 63, 9, 2];

pub fn hex_i64(n: i64) -> String {
    let sign = if n < 0 { "-" } else { "" };
    format!("{sign}{:x}", n.unsigned_abs())
}

impl TestHost {
    /// Asserts the result is normalized, and shows it as Python reads it.
    pub fn show(&self, x: TestInt) -> String {
        if let TestInt::Big { negative, at } = x {
            let digits = self.digits(at);
            assert!(!digits.is_empty() && *digits.last().unwrap() != 0, "big zero or high zero digits");
            let value = (digits.len() == 1).then(|| if negative { (digits[0] as i64).wrapping_neg() } else { digits[0] as i64 });
            let small = value.filter(|&v| (v < 0) == negative && v != 0).and_then(|v| self.small(v));
            assert!(small.is_none(), "{x:?} should be small");
        }
        to_string(self, x, 16).unwrap()
    }

    /// A random integer, often near the edges of the small range and of digits.
    pub fn random(&self, rng: &mut Rng, max_len: usize) -> TestInt {
        let edges = [0, 1, -1, i64::MAX, i64::MIN, 1 << 62, -(1 << 62), (1 << 62) - 1, 255, 256, -256, -257, 2, -2];
        match rng.below(4) {
            0 => {
                let n = edges[rng.below(edges.len() as u64) as usize];
                let n = n.wrapping_add(rng.below(3) as i64 - 1);
                from_i64(self, if self.bits < 64 && rng.bool() { n >> (64 - self.bits) } else { n }).unwrap()
            }
            1 => from_i64(self, rng.u64() as i64 >> rng.below(64)).unwrap(),
            _ => from_digits(self, rng.bool(), Digits::new(&rng.digits(max_len))).unwrap(),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum TestRational {
    Int(TestInt),
    Ratio(TestInt, TestInt),
}

impl crate::RationalHost for TestHost {
    type Rational = TestRational;

    fn rational_view(&self, x: TestRational) -> crate::RationalView<TestInt> {
        match x {
            TestRational::Int(n) => crate::RationalView::Integer(n),
            TestRational::Ratio(num, den) => crate::RationalView::Ratio { num, den },
        }
    }

    fn of_int(&self, x: TestInt) -> TestRational {
        TestRational::Int(x)
    }

    fn ratio(&self, num: TestInt, den: TestInt) -> Result<TestRational, TestError> {
        let one = from_i64(self, 1).unwrap();
        assert_eq!(compare(self, den, one), std::cmp::Ordering::Greater, "denominator {}", self.show(den));
        let g = gcd(self, num, den).unwrap();
        assert_eq!(compare(self, g, one), std::cmp::Ordering::Equal, "{}/{} isn't reduced", self.show(num), self.show(den));
        Ok(TestRational::Ratio(num, den))
    }
}

impl TestHost {
    /// Shows a rational as the oracle reads it, checking its parts.
    pub fn show_rational(&self, x: TestRational) -> String {
        match x {
            TestRational::Int(n) => self.show(n),
            TestRational::Ratio(num, den) => format!("{}/{}", self.show(num), self.show(den)),
        }
    }

    pub fn random_rational(&self, rng: &mut Rng, max_len: usize) -> TestRational {
        if rng.below(4) == 0 {
            return TestRational::Int(self.random(rng, max_len));
        }
        let num = self.random(rng, max_len);
        let den = loop {
            let den = self.random(rng, max_len);
            if sign(self, den) != std::cmp::Ordering::Equal {
                break den;
            }
        };
        crate::rational::from_parts(self, num, den).unwrap()
    }
}

#[derive(Clone, Copy, Debug)]
pub enum TestReal {
    Exact(TestRational),
    Flonum(f64),
}

#[derive(Clone, Copy, Debug)]
pub enum TestNumber {
    Real(TestReal),
    Complex(TestReal, TestReal),
}

impl crate::RealHost for TestHost {
    type Real = TestReal;

    fn real_view(&self, x: TestReal) -> crate::RealView<TestRational> {
        match x {
            TestReal::Exact(r) => crate::RealView::Exact(r),
            TestReal::Flonum(f) => crate::RealView::Flonum(f),
        }
    }

    fn of_rational(&self, x: TestRational) -> TestReal {
        TestReal::Exact(x)
    }

    fn flonum(&self, f: f64) -> Result<TestReal, TestError> {
        Ok(TestReal::Flonum(f))
    }
}

impl crate::ComplexHost for TestHost {
    type Number = TestNumber;

    fn complex_view(&self, x: TestNumber) -> crate::ComplexView<TestReal> {
        match x {
            TestNumber::Real(r) => crate::ComplexView::Real(r),
            TestNumber::Complex(re, im) => crate::ComplexView::Complex { re, im },
        }
    }

    fn of_real(&self, x: TestReal) -> TestNumber {
        TestNumber::Real(x)
    }

    fn complex(&self, re: TestReal, im: TestReal) -> Result<TestNumber, TestError> {
        use crate::real::{is_exact, is_exact_zero};
        assert!(!is_exact_zero(self, im), "complex with an exact zero imaginary part");
        let shape = is_exact(self, re) == is_exact(self, im) || is_exact_zero(self, re) && !is_exact(self, im);
        assert!(shape, "complex of mixed exactness: {} {}", self.show_real(re), self.show_real(im));
        Ok(TestNumber::Complex(re, im))
    }
}

/// Doubles that sit on the edges: zeros, infinities, NaN, the ends of the range, powers of
/// two around where integers stop being exact, and fractions that are exact in binary.
const FLONUM_EDGES: [f64; 22] = [
    0.0,
    -0.0,
    1.0,
    -1.0,
    0.5,
    -2.5,
    3.0,
    f64::INFINITY,
    f64::NEG_INFINITY,
    f64::NAN,
    f64::MAX,
    -f64::MAX,
    f64::MIN_POSITIVE,
    5e-324,
    9007199254740992.0,
    9007199254740993.0,
    -9223372036854775808.0,
    1e300,
    1e-300,
    0.1,
    -7.0,
    1.25,
];

impl TestHost {
    pub fn show_real(&self, x: TestReal) -> String {
        match x {
            TestReal::Exact(r) => self.show_rational(r),
            TestReal::Flonum(f) => format!("fl{:x}", f.to_bits()),
        }
    }

    pub fn show_number(&self, x: TestNumber) -> String {
        match x {
            TestNumber::Real(r) => self.show_real(r),
            TestNumber::Complex(re, im) => format!("cx{}|{}", self.show_real(re), self.show_real(im)),
        }
    }

    pub fn random_flonum(&self, rng: &mut Rng) -> f64 {
        match rng.below(4) {
            0 => FLONUM_EDGES[rng.below(FLONUM_EDGES.len() as u64) as usize],
            1 => f64::from_bits(rng.u64()),
            // Small integers and halves, which meet exact numbers and each other often.
            2 => (rng.below(41) as f64 - 20.0) / if rng.bool() { 1.0 } else { 2.0 },
            _ => (rng.u64() as i64 >> rng.below(64)) as f64 * if rng.bool() { 1.0 } else { 1e-3 },
        }
    }

    pub fn random_real(&self, rng: &mut Rng, max_len: usize) -> TestReal {
        match rng.below(3) {
            0 => TestReal::Flonum(self.random_flonum(rng)),
            // The double nearest an exact number, so the two compare closely.
            1 if rng.bool() => {
                let r = self.random_rational(rng, max_len);
                TestReal::Flonum(crate::rational::to_f64(self, r).unwrap())
            }
            _ => TestReal::Exact(self.random_rational(rng, max_len)),
        }
    }

    /// Reals, and complex numbers of each shape Racket has.
    pub fn random_number(&self, rng: &mut Rng, max_len: usize) -> TestNumber {
        let exact = |rng: &mut Rng| TestReal::Exact(self.random_rational(rng, max_len));
        let flonum = |rng: &mut Rng| TestReal::Flonum(self.random_flonum(rng));
        let (re, im) = match rng.below(4) {
            0 => return TestNumber::Real(self.random_real(rng, max_len)),
            1 => (exact(rng), exact(rng)),
            2 => (flonum(rng), flonum(rng)),
            _ => (TestReal::Exact(TestRational::Int(TestInt::Small(0))), flonum(rng)),
        };
        crate::complex::rectangular(self, re, im).unwrap()
    }
}

/// An error as the oracle names it.
pub fn error_token(e: TestError) -> String {
    match e {
        TestError::Num(NumError::DivideByZero) => "div0",
        TestError::Num(NumError::NoExactValue) => "noexact",
        TestError::Num(NumError::NotInteger) => "notint",
        TestError::TooBig => "toobig",
    }
    .to_string()
}
