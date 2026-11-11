//! The code a `struct` form defines, shared by every front end. The struct types themselves are
//! in [`ragwort_vm::structs`].
//!
//! A form defines, in this order:
//!
//! - the struct type;
//! - a constructor with the struct's name;
//! - a predicate;
//! - an accessor for each field the form declares;
//! - a mutator for each of those fields that is mutable.
//!
//! # Top-level forms
//!
//! A top-level form's type is created when the form is declared, before any of the module's code
//! is compiled, so the code holds the type as a constant. A call to one of the form's procedures
//! is compiled to the operation itself, with no procedure call. That holds in every language of
//! the module and in the modules that require it.
//!
//! A call can be in code that runs before the form has. Such a call first reads the procedure's
//! variable, with the usual check that it is defined, so it fails the way a call to an undefined
//! procedure does.

use ragwort_types::gc::{Mutation, OutOfMemory, Value};
use ragwort_types::pair::Pairs;
use ragwort_vm::structs::{self, FieldFlags, TypeFlags};
use ragwort_vm::{Fault, Intrinsic};

use crate::keyword::Fresh;
use crate::module::{Field, Inline, ModuleBuilder, Operand, StructDef};
use crate::{Core, Lambda, Place, Prim, Var};

/// What a variable a struct form defines is: the type, or a procedure that makes one of it, says
/// whether a value is one, or reads or sets a field of one.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Member {
    Type,
    Make,
    Is,
    Ref(u32),
    Set(u32),
}

/// What a struct form named `name` defines, each with its name: the type, the constructor, the
/// predicate, an accessor for each of `fields`, its own, which come after `inherited` of its
/// supertype's, and a mutator for each of them that's mutable. `None` if that's more fields than
/// a type has.
pub fn members(name: &str, fields: &[Field], inherited: usize) -> Option<Vec<(String, Member)>> {
    let mut members = vec![(format!("struct:{name}"), Member::Type), (name.to_string(), Member::Make), (format!("{name}?"), Member::Is)];
    let mut mutators = Vec::new();
    for (i, field) in fields.iter().enumerate() {
        let k = u32::try_from(inherited + i).ok()?;
        members.push((format!("{name}-{}", field.name), Member::Ref(k)));
        if field.mutable {
            mutators.push((format!("set-{name}-{}!", field.name), Member::Set(k)));
        }
    }
    members.extend(mutators);
    Some(members)
}

/// A field a struct form declares: its name, a symbol, and what the form says of it.
#[derive(Clone, Copy)]
pub struct Declaration<'gc> {
    pub name: Value<'gc>,
    pub mutable: bool,
}

/// The lists a type is made of: the names of `fields`, the ones its form declares, and the bits
/// of each one's flags.
fn listed<'gc>(mc: &Mutation<'gc>, fields: &[Declaration<'gc>]) -> Result<(Value<'gc>, Value<'gc>), OutOfMemory> {
    let pairs = Pairs::new(mc);
    let names: Vec<Value<'gc>> = fields.iter().map(|field| field.name).collect();
    let flags = fields.iter().map(|field| {
        let mut flags = FieldFlags::empty();
        flags.set(FieldFlags::MUTABLE, field.mutable);
        Value::fixnum(i64::from(flags.bits())).expect("flags are a fixnum")
    });
    Ok((pairs.list(&names)?, pairs.list(&flags.collect::<Vec<_>>())?))
}

fn bits<'gc>(flags: TypeFlags) -> Value<'gc> {
    Value::fixnum(i64::from(flags.bits())).expect("flags are a fixnum")
}

/// A new type named by the symbol `name`, with the fields `fields` after those of its supertype
/// `parent`, or `#f`, and the flags its form declares.
pub fn make_type<'gc>(mc: &Mutation<'gc>, name: Value<'gc>, parent: Value<'gc>, fields: &[Declaration<'gc>], flags: TypeFlags) -> Result<Value<'gc>, Fault> {
    let (names, field_flags) = listed(mc, fields)?;
    structs::make_type(mc, name, parent, names, field_flags, bits(flags)).map(|kind| Value::object(mc, kind))
}

/// Code that makes such a type each time it runs, as a form in a body does.
pub fn type_maker<'gc>(mc: &Mutation<'gc>, name: Value<'gc>, parent: Core<'gc>, fields: &[Declaration<'gc>], flags: TypeFlags) -> Result<Core<'gc>, OutOfMemory> {
    let (names, field_flags) = listed(mc, fields)?;
    let args = vec![Core::Quote(name), parent, Core::Quote(names), Core::Quote(field_flags), Core::Quote(bits(flags))];
    Ok(Core::Intrinsic(Prim::Intrinsic(Intrinsic::MakeStructType), args))
}

fn index<'gc>(k: u32) -> Core<'gc> {
    Core::Quote(Value::fixnum(i64::from(k)).expect("an index is a fixnum"))
}

/// What a call of the procedure `member` of a struct type of `fields` fields does, the type
/// being in variable `kind` of its module. `None` for the type itself, which isn't called.
pub fn inline(member: Member, kind: u32, fields: u32) -> Option<Inline> {
    let kind = Operand::Slot(kind);
    Some(match member {
        Member::Type => return None,
        Member::Make => Inline::of_call(Intrinsic::MakeStruct, fields, &std::iter::once(kind).chain((0..fields).map(Operand::Param)).collect::<Vec<_>>()),
        Member::Is => Inline::of_call(Intrinsic::IsStructDerivedFrom, 1, &[Operand::Param(0), kind]),
        Member::Ref(k) => Inline::of_call(Intrinsic::StructRef, 1, &[Operand::Param(0), kind, Operand::Index(k)]),
        Member::Set(k) => Inline::of_call(Intrinsic::StructSet, 2, &[Operand::Param(0), kind, Operand::Index(k), Operand::Param(1)]),
    })
}

/// The value of the variable a struct form defines as `member` of the type `kind` evaluates to,
/// which has `fields` fields: the type, or a procedure of it.
pub fn value<'gc>(member: Member, kind: Core<'gc>, fields: u32, fresh: &mut impl Fresh) -> Core<'gc> {
    let local = |var: &Var| Core::Ref(Place::Local(*var));
    let (params, prim, args) = match member {
        Member::Type => return kind,
        Member::Make => {
            let params: Vec<Var> = (0..fields).map(|_| fresh.var()).collect();
            let args = std::iter::once(kind).chain(params.iter().map(local)).collect();
            (params, Intrinsic::MakeStruct, args)
        }
        Member::Is => {
            let v = fresh.var();
            (vec![v], Intrinsic::IsStructDerivedFrom, vec![local(&v), kind])
        }
        Member::Ref(k) => {
            let s = fresh.var();
            (vec![s], Intrinsic::StructRef, vec![local(&s), kind, index(k)])
        }
        Member::Set(k) => {
            let (s, v) = (fresh.var(), fresh.var());
            (vec![s, v], Intrinsic::StructSet, vec![local(&s), kind, index(k), local(&v)])
        }
    };
    let body = Box::new(Core::Intrinsic(Prim::Intrinsic(prim), args));
    Core::Lambda(Lambda { id: fresh.lambda(), optional: 0, params, rest: None, body })
}

/// A call of a procedure of a struct type, which does what the procedure does itself.
pub struct Call<'gc> {
    inline: Inline,
    kind: Core<'gc>,
    check: Option<Place>,
}

impl<'gc> Call<'gc> {
    /// A call that does what `inline` does, `kind` being the type. If the procedure is in a
    /// variable that may not be defined yet where the call is, `check` is the variable, which
    /// the call reads first, as a call of the procedure would, so it fails as that would.
    pub fn new(inline: Inline, kind: Core<'gc>, check: Option<Place>) -> Self {
        Self { inline, kind, check }
    }

    /// Whether the procedure takes `n` arguments. A call it doesn't take is left to it.
    pub fn takes(&self, n: usize) -> bool {
        self.inline.inlines(n)
    }

    /// The call, on `args`, which it takes, with new locals from `fresh`.
    pub fn core(self, args: Vec<Core<'gc>>, fresh: &mut dyn FnMut() -> Var) -> Core<'gc> {
        let Self { inline, kind, check } = self;
        let call = inline.call(args, fresh, &|_| kind.clone());
        match check {
            Some(place) => Core::Let(vec![(fresh(), Core::Ref(place))], Box::new(call)),
            None => call,
        }
    }
}

/// A struct form at a module's top level, once it's declared: the module's variable for each
/// thing it defines.
pub struct Declared {
    constructor: u32,
    members: Vec<(u32, Member)>,
    fields: u32,
}

impl Declared {
    /// Notes in `builder` what a struct form of the module's defines.
    ///
    /// - `kind`: the form's type.
    /// - `fields`: all the type's fields, its supertype's first.
    /// - `sealed`: whether the form says the type is sealed.
    /// - `members`: the variables the form defines: the type's, then the constructor's that has
    ///   the struct's name, then the rest.
    pub fn new<'gc>(builder: &mut ModuleBuilder<'gc>, kind: Value<'gc>, fields: Vec<Field>, sealed: bool, members: Vec<(u32, Member)>) -> Self {
        let (holder, constructor) = (members[0].0, members[1].0);
        let count = u32::try_from(fields.len()).expect("a type's fields are counted");
        for &(slot, member) in &members {
            if let Some(inline) = inline(member, holder, count) {
                builder.struct_procedure(slot, inline, kind);
            }
        }
        builder.define_struct(constructor, StructDef { kind: holder, fields: fields.into(), sealed }, kind, members.iter().map(|&(slot, _)| slot).collect());
        Self { constructor, members, fields: count }
    }

    /// The constructor that has the struct's name, which the module's builder has the type by.
    pub fn constructor(&self) -> u32 {
        self.constructor
    }

    /// The code of the form, which defines each of its variables, `kind` being its type.
    pub fn define<'gc>(self, kind: Value<'gc>, fresh: &mut impl Fresh) -> Core<'gc> {
        let mut binds = Vec::with_capacity(self.members.len());
        for (slot, member) in self.members {
            let value = value(member, Core::Quote(kind), self.fields, fresh);
            binds.push((fresh.var(), Core::Set(Place::Slot { slot, checked: false }, Box::new(value))));
        }
        Core::Let(binds, Box::new(Core::Quote(Value::VOID)))
    }
}
