//! What an image needs to hold the VM's objects: see [`ragwort_types::gc::image`].
//!
//! - [`descs`]: the VM's object types.
//! - [`kinds`]: the frozen values they hold, such as a function's instructions.
//! - [`Hosts`]: the host functions a loaded image's code can call. A module's host functions
//!   are saved by name, and found again among these.

use std::cell::RefCell;

use ragwort_types::gc::Desc;
use ragwort_types::gc::image::Kind;
use ragwort_types::wire::{Malformed, Reader, Wire, Writer, mix, shape_of};

use crate::objects::Vm;
use crate::syntax_case::{Item, Pattern, PatternShape, Repeat, Template, TemplateShape};
use crate::{Capture, Fault, HostDef, Intrinsic, Op, Request};

/// A number that changes when the form of anything the VM saves does, for an image's stamp.
pub const SHAPE: u64 = {
    let shapes = [
        Op::SHAPE,
        Intrinsic::SHAPE,
        Request::SHAPE,
        Capture::SHAPE,
        Fault::SHAPE,
        <&'static HostDef>::SHAPE,
        PatternShape::SHAPE,
        Pattern::SHAPE,
        Repeat::SHAPE,
        TemplateShape::SHAPE,
        Template::SHAPE,
        Item::SHAPE,
    ];
    let (mut shape, mut i) = (0, 0);
    while i < shapes.len() {
        shape = mix(shape, shapes[i]);
        i += 1;
    }
    shape
};

/// The host functions an image is loaded with, which a [`Reader`] is given to find those the
/// image names.
pub struct Hosts {
    hosts: Vec<&'static HostDef>,
    missing: RefCell<Option<String>>,
}

impl Hosts {
    pub fn new(hosts: impl IntoIterator<Item = &'static HostDef>) -> Self {
        Self { hosts: hosts.into_iter().collect(), missing: RefCell::new(None) }
    }

    /// The name of a host function the image named that isn't among these, if a load failed
    /// for that.
    pub fn missing(&self) -> Option<String> {
        self.missing.borrow().clone()
    }
}

/// A host function is saved as its name and how many arguments it takes.
impl Wire for &'static HostDef {
    const SHAPE: u64 = shape_of("HostDef name arity");

    fn write(&self, out: &mut Writer) {
        out.bytes(self.name.as_bytes());
        self.arity.write(out);
    }

    fn read(input: &mut Reader<'_>) -> Result<Self, Malformed> {
        let name = std::str::from_utf8(input.bytes()?).map_err(|_| Malformed)?;
        let arity = i64::read(input)?;
        let hosts = input.context::<Hosts>()?;
        let found = hosts.hosts.iter().find(|host| host.name == name && host.arity == arity).copied();
        if found.is_none() {
            hosts.missing.borrow_mut().get_or_insert_with(|| name.to_string());
        }
        found.ok_or(Malformed)
    }
}

/// The VM's object types.
pub fn descs() -> &'static [&'static Desc] {
    Vm::DESCS
}

/// The kinds of frozen value the VM's objects hold, but a module's interface, which is its
/// compiler's.
pub fn kinds() -> Vec<Kind> {
    vec![
        Kind::of::<Box<[Op]>>(),
        Kind::of::<Box<[Capture]>>(),
        Kind::of::<Box<[&'static HostDef]>>(),
        Kind::of::<Fault>(),
        Kind::of::<Box<PatternShape>>(),
        Kind::of::<Box<TemplateShape>>(),
    ]
}
