//! Defines the metadata and registries required to serialize and deserialize VM objects in heap images (see [`ragwort_types::gc::image`]).
//!
//! - [`descs`]: Garbage collector descriptors for all VM object types.
//! - [`kinds`]: Registrations for frozen value types embedded within VM objects (such as compiled instruction buffers).
//! - [`Hosts`]: Registry of host functions callable by code in a loaded image. When serialized, host functions are referenced by module path and re-resolved against this table upon deserialization.

use std::cell::RefCell;

use ragwort_types::gc::Desc;
use ragwort_types::gc::image::Kind;
use ragwort_types::wire::{Malformed, Reader, Wire, Writer, mix, shape_of};

use crate::objects::Vm;
use crate::syntax_case::{Item, Pattern, PatternShape, Repeat, Template, TemplateShape};
use crate::report::{Failure, Table};
use crate::{Capture, HostDef, Intrinsic, Op, Request};

/// A combined hash of the serialized layout (wire shape) of all VM structures, used as a schema stamp to validate image compatibility upon loading.
pub const SHAPE: u64 = {
    let shapes = [
        Op::SHAPE,
        Intrinsic::SHAPE,
        Request::SHAPE,
        Capture::SHAPE,
        Failure::SHAPE,
        Table::SHAPE,
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

/// Registry of available host functions provided when loading an image, used by the image [`Reader`] to resolve host function references by path.
pub struct Hosts {
    hosts: Vec<&'static HostDef>,
    missing: RefCell<Option<String>>,
}

impl Hosts {
    /// Creates a host function registry from an iterator of [`HostDef`] definitions. Returns an error containing the colliding path if multiple distinct host functions share the same [`HostDef::path`].
    pub fn new(given: impl IntoIterator<Item = &'static HostDef>) -> Result<Self, &'static str> {
        let mut hosts: Vec<&'static HostDef> = Vec::new();
        for host in given {
            match hosts.iter().find(|other| other.path == host.path) {
                Some(other) if other.id == host.id => {}
                Some(_) => return Err(host.path),
                None => hosts.push(host),
            }
        }
        Ok(Self { hosts, missing: RefCell::new(None) })
    }

    /// Returns the name of the missing host function if image deserialization failed due to an unresolved host function reference.
    pub fn missing(&self) -> Option<String> {
        self.missing.borrow().clone()
    }
}

/// Serializes a host function reference by its module path, function name, and expected arity. When deserialized, these attributes must match an entry registered in [`Hosts`].
impl Wire for &'static HostDef {
    const SHAPE: u64 = shape_of("HostDef path name arity");

    fn write(&self, out: &mut Writer) {
        out.bytes(self.path.as_bytes());
        out.bytes(self.name.as_bytes());
        self.arity.write(out);
    }

    fn read(input: &mut Reader<'_>) -> Result<Self, Malformed> {
        let path = std::str::from_utf8(input.bytes()?).map_err(|_| Malformed)?;
        let name = std::str::from_utf8(input.bytes()?).map_err(|_| Malformed)?;
        let arity = i64::read(input)?;
        let hosts = input.context::<Hosts>()?;
        let found = hosts.hosts.iter().find(|host| host.path == path && host.name == name && host.arity == arity).copied();
        if found.is_none() {
            hosts.missing.borrow_mut().get_or_insert_with(|| name.to_string());
        }
        found.ok_or(Malformed)
    }
}

/// Returns the slice of garbage collector descriptors ([`Desc`]) for all VM object types.
pub fn descs() -> &'static [&'static Desc] {
    Vm::DESCS
}

/// Returns the list of [`Kind`] registrations for all frozen value types stored inside VM objects, excluding the module interface (which is defined by the compiler).
pub fn kinds() -> Vec<Kind> {
    vec![
        Kind::of::<Box<[Op]>>(),
        Kind::of::<Box<[Capture]>>(),
        Kind::of::<Box<[&'static HostDef]>>(),
        Kind::of::<Failure>(),
        Kind::of::<Table>(),
        Kind::of::<Box<PatternShape>>(),
        Kind::of::<Box<TemplateShape>>(),
    ]
}
