use super::*;

#[test]
fn an_arity_with_gaps_survives_its_encoding() {
    // Clauses for 1 and 3 arguments: one required, two optional, and 2 is refused.
    let shape = Shape { required: 1, optional: 2, rest: false, refused: 0b01 };
    assert_eq!(Shape::of(shape.encode().unwrap()), shape);
    assert_eq!((0..5).map(|count| shape.takes(count)).collect::<Vec<_>>(), [false, true, false, true, false]);
    // With a rest parameter, every count past the optional ones is taken.
    let rest = Shape { required: 0, optional: 4, rest: true, refused: 0b0101 };
    assert_eq!(Shape::of(rest.encode().unwrap()), rest);
    assert_eq!((0..7).map(|count| rest.takes(count)).collect::<Vec<_>>(), [true, false, true, false, true, true, true]);
    // A shape without gaps is encoded as before.
    let plain = Shape { required: 2, optional: 1, rest: false, refused: 0 };
    assert_eq!(Shape::of(plain.encode().unwrap()), plain);
    assert_eq!(Shape { required: 3, optional: 0, rest: false, refused: 0 }.encode(), Some(3));
    assert_eq!(Shape { required: 3, optional: 0, rest: true, refused: 0 }.encode(), Some(-4));
    // The mask has `Shape::GAPS` bits, and gaps need optional parameters to be between.
    assert_eq!(Shape { required: 0, optional: 16, rest: false, refused: 1 << Shape::GAPS }.encode(), None);
    assert_eq!(Shape { required: 3, optional: 0, rest: false, refused: 1 }.encode(), None);
}

#[test]
fn an_arity_with_gaps_is_described_by_its_counts() {
    fn described(shape: Shape) -> String {
        ExpectedArity::from(shape).to_string()
    }
    assert_eq!(described(Shape { required: 1, optional: 2, rest: false, refused: 0b01 }), "expected 1 or 3");
    assert_eq!(described(Shape { required: 0, optional: 4, rest: false, refused: 0b0101 }), "expected 0, 2 or 4");
    assert_eq!(described(Shape { required: 0, optional: 4, rest: true, refused: 0b0101 }), "expected 0, 2 or at least 4");
    assert_eq!(described(Shape { required: 2, optional: 3, rest: true, refused: 0b001 }), "expected 2 or at least 4");
    // Without gaps, the description is the one of an ordinary procedure.
    assert_eq!(described(Shape { required: 1, optional: 2, rest: false, refused: 0 }), "expected 1 to 3");
    let expected = ExpectedArity::from(Shape { required: 0, optional: 4, rest: true, refused: 0b0101 });
    assert_eq!((0..7).map(|count| expected.takes(count)).collect::<Vec<_>>(), [true, false, true, false, true, true, true]);
}
