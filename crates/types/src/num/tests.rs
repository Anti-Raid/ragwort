use ragwort_gc::{Arena, GcVec, Rootable};

use super::*;

struct Ints;
impl Rootable for Ints {
    type Root<'gc> = GcVec<'gc, Value<'gc>>;
}

fn parse<'gc>(h: &Nums<'_, 'gc>, text: &str) -> Integer<'gc> {
    let (negative, digits) = text.strip_prefix('-').map_or((false, text), |rest| (true, rest));
    int::parse(h, digits.as_bytes(), 10, negative).unwrap().unwrap()
}

#[test]
fn arithmetic_crosses_the_fixnum_edge() {
    let mut arena = Arena::<Ints>::new(4 << 20, |_| Ok(GcVec::new())).unwrap();
    arena.mutate(|mc, _| {
        let h = Nums::new(mc).unwrap();
        let max = int::from_i64(&h, Value::MAX_FIXNUM).unwrap();
        let one = int::from_i64(&h, 1).unwrap();
        let past = int::add(&h, max, one).unwrap();
        assert!(!past.value().is_fixnum(), "the first bignum");
        assert_eq!(int::to_string(&h, past, 10).unwrap(), "4611686018427387904");
        let back = int::sub(&h, past, one).unwrap();
        assert!(back.value().is_fixnum(), "results in range are fixnums");
        assert_eq!(back, max);
        let min = int::from_i64(&h, Value::MIN_FIXNUM).unwrap();
        assert!(min.value().is_fixnum());
        assert!(!int::neg(&h, min).unwrap().value().is_fixnum());
        let big = parse(&h, "-340282366920938463463374607431768211456");
        let two = int::from_i64(&h, 2).unwrap();
        assert_eq!(int::compare(&h, int::neg(&h, int::expt(&h, two, 128).unwrap()).unwrap(), big), std::cmp::Ordering::Equal);
        assert_eq!(int::quotient(&h, two, int::from_i64(&h, 0).unwrap()), Err(Error::Num(NumError::DivideByZero)));
        assert_eq!(h.integer(Value::TRUE), None);
        assert_eq!(h.integer(big.value()), Some(big));
    }).unwrap();
}

#[test]
fn bignums_survive_collections_that_move_them() {
    let mut arena = Arena::<Ints>::new(16 << 20, |_| Ok(GcVec::new())).unwrap();
    arena.set_evacuate_all(true);
    let expected: Vec<String> = arena.mutate(|mc, root| {
        let h = Nums::new(mc).unwrap();
        let mut x = parse(&h, "-12345678901234567890123456789");
        (0..200)
            .map(|i| {
                let k = int::from_i64(&h, 1_000_003 * i + 7).unwrap();
                x = int::add(&h, int::mul(&h, x, k).unwrap(), k).unwrap();
                // Garbage between the survivors.
                int::expt(&h, k, 9).unwrap();
                root.push(mc, x.value()).unwrap();
                int::to_string(&h, x, 10).unwrap()
            })
            .collect()
    }).unwrap();
    arena.collect();
    arena.collect();
    arena.mutate(|mc, root| {
        let h = Nums::new(mc).unwrap();
        for (i, want) in expected.iter().enumerate() {
            let x = h.integer(root.get(mc, i).unwrap()).unwrap();
            assert_eq!(&int::to_string(&h, x, 10).unwrap(), want);
        }
    }).unwrap();
}

#[test]
fn ratios_live_in_the_arena() {
    let mut arena = Arena::<Ints>::new(4 << 20, |_| Ok(GcVec::new())).unwrap();
    arena.set_evacuate_all(true);
    let expected = arena.mutate(|mc, root| {
        let h = Nums::new(mc).unwrap();
        let (one, three) = (int::from_i64(&h, 1).unwrap(), int::from_i64(&h, 3).unwrap());
        let third = rational::from_parts(&h, one, three).unwrap();
        let half = rational::from_parts(&h, one, int::from_i64(&h, 2).unwrap()).unwrap();
        let sum = rational::add(&h, third, half).unwrap();
        assert_eq!(rational::to_string(&h, sum, 10).unwrap(), "5/6");
        let whole = rational::add(&h, sum, rational::from_parts(&h, one, int::from_i64(&h, 6).unwrap()).unwrap()).unwrap();
        assert!(whole.value().is_fixnum(), "5/6 + 1/6 is the fixnum 1");
        // A ratio of bignums.
        let big = int::expt(&h, three, 100).unwrap();
        let x = rational::from_parts(&h, big, int::expt(&h, int::from_i64(&h, 2).unwrap(), 100).unwrap()).unwrap();
        assert_eq!(h.rational(x.value()), Some(x));
        assert_eq!(h.integer(x.value()), None);
        root.push(mc, sum.value()).unwrap();
        root.push(mc, x.value()).unwrap();
        [rational::to_string(&h, sum, 10).unwrap(), rational::to_string(&h, x, 10).unwrap()]
    }).unwrap();
    arena.collect();
    arena.mutate(|mc, root| {
        let h = Nums::new(mc).unwrap();
        for (i, want) in expected.iter().enumerate() {
            let x = h.rational(root.get(mc, i).unwrap()).unwrap();
            assert_eq!(&rational::to_string(&h, x, 10).unwrap(), want);
        }
    }).unwrap();
}

#[test]
fn running_out_of_memory_is_an_error() {
    let mut arena = Arena::<Ints>::new(1 << 20, |_| Ok(GcVec::new())).unwrap();
    arena.mutate(|mc, _| {
        let h = Nums::new(mc).unwrap();
        let two = int::from_i64(&h, 2).unwrap();
        assert_eq!(int::expt(&h, two, 1 << 24), Err(Error::OutOfMemory));
        assert_eq!(int::arithmetic_shift(&h, two, i64::MAX), Err(Error::OutOfMemory));
        let ten = int::from_i64(&h, 10).unwrap();
        let x = int::expt(&h, ten, 20_000).unwrap();
        let y = int::add(&h, x, two).unwrap();
        int::gcd(&h, x, y).unwrap();
    }).unwrap();
}

fn number<'gc>(h: &Nums<'_, 'gc>, re: f64, im: f64) -> Number<'gc> {
    complex::rectangular(h, h.flonum(re).unwrap(), h.flonum(im).unwrap()).unwrap()
}

fn exact<'gc>(h: &Nums<'_, 'gc>, n: i64) -> Number<'gc> {
    h.of_real(real::from_i64(h, n).unwrap())
}

fn parts<'gc>(h: &Nums<'_, 'gc>, z: Number<'gc>) -> (String, String) {
    let show = |x: Real<'gc>| match h.real_view(x) {
        RealView::Exact(r) => rational::to_string(h, r, 10).unwrap(),
        RealView::Flonum(f) => format!("{f:?}"),
    };
    (show(complex::real_part(h, z)), show(complex::imag_part(h, z).unwrap()))
}

#[test]
fn flonums_and_complex_numbers_live_in_the_arena() {
    let mut arena = Arena::<Ints>::new(4 << 20, |_| Ok(GcVec::new())).unwrap();
    arena.set_evacuate_all(true);
    let expected = arena.mutate(|mc, root| {
        let h = Nums::new(mc).unwrap();
        let root_i = exact(&h, -4);
        let two_i = complex::sqrt(&h, root_i).unwrap();
        assert!(complex::is_exact(&h, two_i), "(sqrt -4) is exact");
        assert_eq!(parts(&h, two_i), ("0".into(), "2".into()));
        let squared = complex::mul(&h, two_i, two_i).unwrap();
        assert!(squared.value().is_fixnum(), "(* +2i +2i) is the fixnum -4");
        // 1e300 doesn't fit in the word, so its part is boxed.
        let huge = number(&h, 1e300, -0.5);
        let ComplexView::Complex { re, .. } = h.complex_view(huge) else { panic!() };
        assert!(Value::inline_flonum(1e300).is_none() && re.value().is_flonum());
        let sum = complex::add(&h, huge, exact(&h, 3)).unwrap();
        let w = complex::exp(&h, number(&h, 2.0, 3.0)).unwrap();
        assert_eq!(parts(&h, w), ("-7.315110094901103".into(), "1.0427436562359045".into()));
        let half = complex::div(&h, exact(&h, 1), exact(&h, 2)).unwrap();
        assert_eq!(h.number(half.value()), Some(half));
        assert_eq!(h.real(two_i.value()), None);
        assert_eq!(h.number(Value::TRUE), None);
        assert!(h.real(Value::inline_flonum(0.5).unwrap()).is_some());
        let kept = [two_i, sum, w];
        for z in kept {
            root.push(mc, z.value()).unwrap();
        }
        kept.map(|z| parts(&h, z))
    }).unwrap();
    arena.collect();
    arena.collect();
    arena.mutate(|mc, root| {
        let h = Nums::new(mc).unwrap();
        for (i, want) in expected.iter().enumerate() {
            let z = h.number(root.get(mc, i).unwrap()).unwrap();
            assert_eq!(&parts(&h, z), want);
        }
    }).unwrap();
}
