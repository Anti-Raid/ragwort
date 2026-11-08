use ragwort_types::gc::{Arena, Value};
use ragwort_types::string::Strings;
use ragwort_types::symbol::{Symbol, Symbols};

use super::{BoxFields, Bytecode, BytecodeFields, Vm};
use crate::{Capture, Op};

#[test]
fn objects_live_beside_the_types_crates() {
    let mut arena = Arena::new(1 << 20, 3);
    arena.mutate(|mc| {
        let symbols = Symbols::with_seed(mc, 1).unwrap();
        let name = symbols.intern_str(&Strings::new(mc), "x").unwrap();
        let ops = mc.frozen(Box::from([Op::LoadConst { dst: 0, index: 0 }, Op::Return { src: 0 }])).unwrap();
        mc.set_root(0, symbols.value(mc));
        let captures = mc.frozen(Box::<[Capture]>::from([])).unwrap();
        mc.set_root(1, Value::object(mc, Bytecode::new(mc, ops, name.value(mc), captures, 0, None).unwrap()));
        mc.set_root(2, Value::object(mc, super::Box::new(mc, Value::fixnum(7).unwrap()).unwrap()));
    });
    arena.collect();
    arena.mutate(|mc| {
        let code = mc.root(1).downcast::<Bytecode>(mc).unwrap();
        assert_eq!(code.ops(mc).unwrap()[1], Op::Return { src: 0 });
        assert!(Symbol::of(code.constants(mc)).is_some());
        let cell = mc.root(2).downcast::<super::Box>(mc).unwrap();
        cell.set_value(mc, Value::NIL);
        assert_eq!(cell.value(mc), Value::NIL);
        assert!(matches!(Vm::of(mc.root(2)), Some(Vm::Box(_))));
    });
}
