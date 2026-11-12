use ragwort_types::Wire;

use super::{Reader, Writer};

mod narrow {
    use ragwort_types::Wire;

    #[derive(Wire)]
    pub struct Inner {
        pub x: u8,
    }

    #[derive(Wire)]
    pub struct Outer {
        pub inner: Inner,
        pub rest: Vec<Inner>,
    }
}

mod wide {
    use ragwort_types::Wire;

    #[derive(Wire)]
    pub struct Inner {
        pub x: u16,
    }

    #[derive(Wire)]
    pub struct Outer {
        pub inner: Inner,
        pub rest: Vec<Inner>,
    }
}

#[derive(Wire, Debug, PartialEq)]
enum Tree {
    Leaf(u8),
    Node(Box<[Tree]>),
}

#[test]
fn a_shape_changes_when_the_shape_of_a_field_type_does() {
    assert_ne!(narrow::Inner::SHAPE, wide::Inner::SHAPE);
    assert_ne!(narrow::Outer::SHAPE, wide::Outer::SHAPE);
}

#[test]
fn a_type_that_holds_itself_has_a_shape_and_reads_back() {
    assert_ne!(Tree::SHAPE, 0);
    let tree = Tree::Node(Box::new([Tree::Leaf(1), Tree::Node(Box::new([Tree::Leaf(2)]))]));
    let mut out = Writer::new();
    tree.write(&mut out);
    let bytes = out.finish();
    assert_eq!(Tree::read(&mut Reader::new(&bytes, &())), Ok(tree));
}
