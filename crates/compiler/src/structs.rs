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
//!
//! # Guards
//!
//! A guarded field has a guard: a procedure that must return true for every value the field is
//! given. The form's code evaluates the guard expressions and installs the guards in the type
//! before it defines anything. A constructor calls the guard of each guarded field, inherited
//! ones included, and a mutator calls its field's guard. A call to such a procedure is compiled
//! to the guard calls and the operation, unless it has too many guards, in which case it is an
//! ordinary procedure call.

use ragwort_types::gc::{Mutation, OutOfMemory, Value};
use ragwort_types::pair::Pairs;
use ragwort_vm::structs::{self, FieldFlags, TypeFlags};
use ragwort_vm::{Fault, Intrinsic, Request};

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
    pub guarded: bool,
}

/// The lists a type is made of: the names of `fields`, the ones its form declares, and the bits
/// of each one's flags.
fn listed<'gc>(mc: &Mutation<'gc>, fields: &[Declaration<'gc>]) -> Result<(Value<'gc>, Value<'gc>), OutOfMemory> {
    let pairs = Pairs::new(mc);
    let names: Vec<Value<'gc>> = fields.iter().map(|field| field.name).collect();
    let flags = fields.iter().map(|field| {
        let mut flags = FieldFlags::empty();
        flags.set(FieldFlags::MUTABLE, field.mutable);
        flags.set(FieldFlags::GUARDED, field.guarded);
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

/// Code that installs the procedure `guard` evaluates to as the guard of field `k` of the type
/// `kind` evaluates to.
pub fn guard_installer<'gc>(kind: Core<'gc>, k: u32, guard: Core<'gc>) -> Core<'gc> {
    Core::Intrinsic(Prim::Intrinsic(Intrinsic::SetStructFieldGuard), vec![kind, index(k), guard])
}

/// Code that calls the guard of field `k` of the type `kind` evaluates to on the value of `v`,
/// and raises the guard's error if it returns false.
fn guarded<'gc>(kind: &Core<'gc>, k: u32, v: Var) -> Core<'gc> {
    let value = || Core::Ref(Place::Local(v));
    let guard = Core::Intrinsic(Prim::Intrinsic(Intrinsic::StructFieldGuard), vec![kind.clone(), index(k)]);
    let error = Core::Intrinsic(Prim::Intrinsic(Intrinsic::MakeStructGuardError), vec![kind.clone(), index(k), value()]);
    let raise = Core::Intrinsic(Prim::Request(Request::Raise), vec![error]);
    Core::If(Box::new(Core::App(Box::new(guard), vec![value()])), Box::new(Core::Quote(Value::VOID)), Box::new(raise))
}

/// How many forms the inlined body of a procedure that calls guards can have. Each guard is
/// about a dozen, so a constructor with a few guards is inlined, and one with many is called.
const MAX_GUARDED: usize = 64;

/// Numbers the variables and the lambda of one procedure, for its template.
struct Numbering(u32);

impl Fresh for Numbering {
    fn var(&mut self) -> Var {
        self.0 += 1;
        Var(self.0)
    }

    fn lambda(&mut self) -> u32 {
        0
    }
}

/// What a call of the procedure `member` of a struct type with the fields `fields` does, the
/// type being in variable `kind` of its module. `None` for the type itself, which isn't called,
/// and for a procedure that calls too many guards to inline, which is called as it is.
pub fn inline(member: Member, kind: u32, fields: &[Field]) -> Option<Inline> {
    let calls_guard = match member {
        Member::Make => fields.iter().any(|field| field.guarded),
        Member::Set(k) => fields.get(k as usize).is_some_and(|field| field.guarded),
        Member::Type | Member::Is | Member::Ref(_) => false,
    };
    if calls_guard {
        let holder = Core::Ref(Place::Slot { slot: kind, checked: false });
        let made = value(member, holder, fields, &mut Numbering(0));
        let Core::Lambda(lambda) = &made else { return None };
        return Inline::of_at_most(lambda, MAX_GUARDED);
    }
    let kind = Operand::Slot(kind);
    let count = u32::try_from(fields.len()).ok()?;
    Some(match member {
        Member::Type => return None,
        Member::Make => Inline::of_call(Intrinsic::MakeStruct, count, &std::iter::once(kind).chain((0..count).map(Operand::Param)).collect::<Vec<_>>()),
        Member::Is => Inline::of_call(Intrinsic::IsStructDerivedFrom, 1, &[Operand::Param(0), kind]),
        Member::Ref(k) => Inline::of_call(Intrinsic::StructRef, 1, &[Operand::Param(0), kind, Operand::Index(k)]),
        Member::Set(k) => Inline::of_call(Intrinsic::StructSet, 2, &[Operand::Param(0), kind, Operand::Index(k), Operand::Param(1)]),
    })
}

/// The value of the variable a struct form defines as `member` of the type `kind` evaluates to,
/// which has the fields `fields`: the type, or a procedure of it. A constructor calls the guard
/// of each guarded field first, in order, and a mutator its field's.
pub fn value<'gc>(member: Member, kind: Core<'gc>, fields: &[Field], fresh: &mut impl Fresh) -> Core<'gc> {
    let local = |var: &Var| Core::Ref(Place::Local(*var));
    let is_guarded = |k: usize| fields.get(k).is_some_and(|field| field.guarded);
    let mut checks = Vec::new();
    let (params, prim, args) = match member {
        Member::Type => return kind,
        Member::Make => {
            let params: Vec<Var> = fields.iter().map(|_| fresh.var()).collect();
            checks.extend(params.iter().enumerate().filter(|&(k, _)| is_guarded(k)).map(|(k, &v)| guarded(&kind, k as u32, v)));
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
            if is_guarded(k as usize) {
                checks.push(guarded(&kind, k, v));
            }
            (vec![s, v], Intrinsic::StructSet, vec![local(&s), kind, index(k), local(&v)])
        }
    };
    let mut body = Core::Intrinsic(Prim::Intrinsic(prim), args);
    if !checks.is_empty() {
        body = Core::Let(checks.into_iter().map(|check| (fresh.var(), check)).collect(), Box::new(body));
    }
    Core::Lambda(Lambda { id: fresh.lambda(), optional: 0, params, rest: None, body: Box::new(body) })
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
        for &(slot, member) in &members {
            if let Some(inline) = inline(member, holder, &fields) {
                builder.struct_procedure(slot, inline, kind);
            } else if member != Member::Type {
                builder.struct_variable(slot);
            }
        }
        builder.define_struct(constructor, StructDef { kind: holder, fields: fields.into(), sealed }, kind, members.iter().map(|&(slot, _)| slot).collect());
        Self { constructor, members }
    }

    /// The constructor that has the struct's name, which the module's builder has the type by.
    pub fn constructor(&self) -> u32 {
        self.constructor
    }

    /// The code of the form.
    ///
    /// - `kind`: the form's type.
    /// - `fields`: all the type's fields, its supertype's first.
    /// - `guards`: the guard expression of each guarded field the form declares, with the
    ///   field's index, in the order the form has them.
    ///
    /// It evaluates the guards and installs them, then defines each of the form's variables.
    pub fn define<'gc>(self, kind: Value<'gc>, fields: &[Field], guards: Vec<(u32, Core<'gc>)>, fresh: &mut impl Fresh) -> Core<'gc> {
        let mut binds = Vec::with_capacity(guards.len() + self.members.len());
        for (k, guard) in guards {
            binds.push((fresh.var(), guard_installer(Core::Quote(kind), k, guard)));
        }
        for (slot, member) in self.members {
            let value = value(member, Core::Quote(kind), fields, fresh);
            binds.push((fresh.var(), Core::Set(Place::Slot { slot, checked: false }, Box::new(value))));
        }
        Core::Let(binds, Box::new(Core::Quote(Value::VOID)))
    }
}
