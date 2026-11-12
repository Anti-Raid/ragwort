//! Compiler representations and builder infrastructure for modules.
//!
//! This module provides:
//! - [`ModuleBuilder`]: Used by language front ends to lower source files into compiled top-level forms
//!   that assemble a [`Module`].
//! - [`Interface`]: Specifies a compiled module's exported definitions for downstream consumers.
//!
//! A module's top-level variables occupy numbered slots in its runtime storage. Variable accesses are emitted
//! as unchecked loads when the front end can verify prior initialization (for instance, when defined in an earlier
//! top-level form, or when referenced self-recursively inside its own initializing lambda). Exports that are never
//! mutated within the module are treated as immutable: importing modules may directly embed (quote) their values or,
//! for small lambdas capturing only parameters and other immutable module slots, inline their call sites directly.
//! Mutable exports are accessed dynamically at runtime via `module-ref`.

use crate::hash::{HashMap, HashSet};

use ragwort_types::Wire;
use ragwort_types::gc::image::{Kind, LoadError, freeze};
use ragwort_types::gc::{Gc, Immediate, Mutation, OutOfMemory, Value};
use ragwort_types::wire::{Malformed, Reader, Writer, mix, shape_of};
use ragwort_types::string::{Strings, chars};
use ragwort_types::symbol::{Symbol, Symbols};
use ragwort_vm::objects::{Module, ModuleFields};
use ragwort_vm::{HostDef, Intrinsic};

use crate::keyword::CallShape;
use crate::structs::{Call, Member};
use crate::{CompileError, Core, Lambda, Place, Prim, Var, compile};

/// Maximum number of AST nodes permitted in the body of an inlined export.
const MAX_INLINE: usize = 16;
/// Maximum length of a rest-argument list generated during inlining, where each element introduces a nested `cons`.
const MAX_REST: usize = 16;

/// The export table of a compiled module, mapping public export names to their export descriptors.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Interface {
    exports: HashMap<Box<str>, Export>,
}

impl Interface {
    pub fn get(&self, name: &str) -> Option<&Export> {
        self.exports.get(name)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&str, &Export)> {
        self.exports.iter().map(|(name, export)| (&**name, export))
    }
}

/// Serializes module exports sorted lexicographically by export name.
impl Wire for Interface {
    const SHAPE: u64 = shape_of("Interface");

    fn write(&self, out: &mut Writer) {
        let mut exports: Vec<(&Box<str>, &Export)> = self.exports.iter().collect();
        exports.sort_by_key(|&(name, _)| name);
        out.length(exports.len());
        for (name, export) in exports {
            name.write(out);
            export.write(out);
        }
    }

    fn read(input: &mut Reader<'_>) -> Result<Self, Malformed> {
        let mut exports = HashMap::default();
        for _ in 0..input.length()? {
            let name = Box::<str>::read(input)?;
            exports.insert(name, Export::read(input)?);
        }
        Ok(Self { exports })
    }
}

/// Serializes a module's compiler interface into a heap image, writing the [`Interface`] if compilation succeeded, or an empty record if the module is incomplete. Unrecognized user data is ignored.
fn save_interface(value: &dyn std::any::Any, out: &mut Writer) -> bool {
    let Some(held) = value.downcast_ref::<Box<dyn std::any::Any>>() else { return false };
    if let Some(interface) = held.downcast_ref::<Interface>() {
        out.u8(1);
        interface.write(out);
        true
    } else if held.is::<()>() {
        out.u8(0);
        true
    } else {
        false
    }
}

fn load_interface<'gc>(mc: &Mutation<'gc>, input: &mut Reader<'_>, cost: usize) -> Result<u64, LoadError> {
    let held: Box<dyn std::any::Any> = match input.u8()? {
        0 => Box::new(()),
        1 => Box::new(Interface::read(input)?),
        _ => return Err(LoadError::Malformed),
    };
    Ok(freeze(mc, held, cost)?)
}

/// The GC image serialization descriptor for frozen module interfaces; see [`ragwort_types::gc::image`].
pub const INTERFACE: Kind = Kind { save: save_interface, load: load_interface, shape: SHAPE };

/// Type shape hash for [`Interface`], updated whenever the binary wire format of any interface type changes.
const SHAPE: u64 = {
    let shapes = [Interface::SHAPE, Export::SHAPE, StructDef::SHAPE, Field::SHAPE, Inline::SHAPE, Template::SHAPE, Prim::SHAPE, crate::SlotOp::SHAPE];
    let (mut shape, mut i) = (0, 0);
    while i < shapes.len() {
        shape = mix(shape, shapes[i]);
        i += 1;
    }
    shape
};

/// Describes an exported module variable and its inlining/structure metadata.
#[derive(Clone, Debug, PartialEq, Eq, Wire)]
pub struct Export {
    pub slot: u32,
    /// Indicates whether this variable is mutated within the defining module, requiring dynamic reads via `module-ref`.
    pub mutable: bool,
    /// Optional inlining template used when calls to this export can be inlined directly at call sites.
    pub inline: Option<Inline>,
    /// For keyword procedures, points to the underlying core procedure that statically matched keyword calls can invoke directly.
    pub core: Option<Box<Export>>,
    /// Type definition metadata associated with this export when it represents a struct constructor or type name.
    pub structure: Option<Box<StructDef>>,
}

/// A field definition within a struct type as exposed to client modules.
#[derive(Clone, Debug, PartialEq, Eq, Wire)]
pub struct Field {
    pub name: Box<str>,
    pub mutable: bool,
}

/// The structural definition and capabilities of an exported struct type.
#[derive(Clone, Debug, PartialEq, Eq, Wire)]
pub struct StructDef {
    /// The module slot index holding the struct type descriptor object.
    pub kind: u32,
    /// The struct's fields, ordered with supertype fields preceding subtype fields.
    pub fields: Box<[Field]>,
    /// Whether the struct type is sealed against further subtyping.
    pub sealed: bool,
    /// Indicates that the struct identifier is imported exclusively for pattern matching (e.g. when exported without its constructor); the name cannot be evaluated as a runtime value and the type is sealed.
    pub match_only: bool,
}

/// Retrieves the compiled [`Interface`] of `module`, if compilation has completed.
pub fn interface<'gc>(mc: &Mutation<'gc>, module: Gc<'gc, Module>) -> Option<&'gc Interface> {
    ragwort_vm::module::interface(mc, module)
}

/// Resolves imported module names to compiled [`Module`] instances.
pub trait Resolver<'gc> {
    /// Resolves module `name` imported by `from`. The target module must have already executed so that its immutable exports are fully initialized; circular dependencies return `None`.
    fn resolve(&mut self, mc: &Mutation<'gc>, name: &str, from: Value<'gc>) -> Option<Gc<'gc, Module>>;
}

/// A dummy [`Resolver`] that resolves no modules, suitable for standalone modules with no dependencies.
pub struct NoModules;

impl<'gc> Resolver<'gc> for NoModules {
    fn resolve(&mut self, _: &Mutation<'gc>, _: &str, _: Value<'gc>) -> Option<Gc<'gc, Module>> {
        None
    }
}

/// A compiled module and its sequence of top-level zero-argument initialization thunks, which must be executed in order before the module can be resolved by downstream modules.
#[derive(Clone, Debug)]
pub struct Loaded<'gc> {
    pub module: Gc<'gc, Module>,
    pub thunks: Vec<Value<'gc>>,
}

/// A specific export imported from a required module.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Import<'gc> {
    pub module: Gc<'gc, Module>,
    pub export: &'gc Export,
}

/// Explains why an imported identifier cannot be evaluated as an expression value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Unusable {
    /// The imported identifier is an immutable export that was never initialized by its defining module.
    Uninitialized,
    /// The imported identifier is a struct name exported without a constructor, usable only within `match` patterns.
    MatchOnly,
}

impl<'gc> Import<'gc> {
    fn same(self, other: Self) -> bool {
        self.module == other.module && self.export.slot == other.export.slot && self.export.structure == other.export.structure
    }

    /// Emits a reference to the imported binding: either an inlined constant quote for immutable slots, or a dynamic `module-ref` intrinsic for mutable slots.
    pub fn reference(self, mc: &Mutation<'gc>) -> Result<Core<'gc>, Unusable> {
        if self.export.structure.as_deref().is_some_and(|def| def.match_only) {
            return Err(Unusable::MatchOnly);
        }
        let slot = self.export.slot;
        if self.export.mutable {
            let k = Value::fixnum(i64::from(slot)).expect("slots are fixnums");
            let read = vec![Core::Quote(Value::object(mc, self.module)), Core::Quote(k)];
            return Ok(Core::Intrinsic(Prim::Intrinsic(Intrinsic::ModuleRef), read));
        }
        self.variable(mc, slot).map(Core::Quote).ok_or(Unusable::Uninitialized)
    }

    /// Returns an [`Import`] pointing to the underlying core procedure if this import represents a keyword procedure.
    pub fn keyword_core(self) -> Option<Self> {
        Some(Self { module: self.module, export: self.export.core.as_deref()? })
    }

    /// Returns the struct definition metadata and runtime type descriptor if this import represents a struct constructor or type name.
    pub fn struct_def(self, mc: &Mutation<'gc>) -> Option<(&'gc StructDef, Value<'gc>)> {
        let def = self.export.structure.as_deref()?;
        Some((def, self.variable(mc, def.kind)?))
    }

    /// Retrieves the value stored in the module's variable `slot`, returning `None` if the slot is out of bounds or still undefined.
    fn variable(self, mc: &Mutation<'gc>, slot: u32) -> Option<Value<'gc>> {
        let items = self.module.items(mc);
        (slot as usize).lt(&items.len()).then(|| items.get(slot as usize)).filter(|&v| v != Value::UNDEFINED)
    }

    /// Generates an invocation of the imported procedure with `args`, inlining the call if an inline template is available and valid.
    pub fn call(self, mc: &Mutation<'gc>, args: Vec<Core<'gc>>, fresh: &mut dyn FnMut() -> Var) -> Result<Core<'gc>, Unusable> {
        let quoted = |slot: u32| self.variable(mc, slot).map(Core::Quote);
        match &self.export.inline {
            Some(inline) if inline.inlines(args.len()) && inline.slots().all(|slot| quoted(slot).is_some()) => {
                Ok(inline.call(args, fresh, &|slot| quoted(slot).expect("its variables are defined")))
            }
            _ => Ok(Core::App(Box::new(self.reference(mc)?), args)),
        }
    }
}

/// A collection of resolved imports mapped to local binding names, transformed by import filters (such as `only`, `except`, `prefix`, and `rename`).
#[derive(Clone, Debug, Default)]
pub struct Imports<'gc>(pub Vec<(String, Import<'gc>)>);

impl<'gc> Imports<'gc> {
    /// Imports all public definitions exported by `module` under their original export names.
    pub fn all(mc: &Mutation<'gc>, module: Gc<'gc, Module>) -> Option<Self> {
        let interface = interface(mc, module)?;
        let mut imports: Vec<_> = interface.iter().map(|(name, export)| (name.to_owned(), Import { module, export })).collect();
        imports.sort_by(|a, b| a.0.cmp(&b.0));
        Some(Self(imports))
    }

    /// Filters imports to retain only those matching `names`, returning an error identifying the first unrecognized name if any are missing.
    pub fn only(self, names: &[String]) -> Result<Self, String> {
        self.has(names)?;
        Ok(Self(self.0.into_iter().filter(|(n, _)| names.contains(n)).collect()))
    }

    /// Filters imports to exclude `names`, returning an error identifying the first unrecognized name if any specified name was not present.
    pub fn except(self, names: &[String]) -> Result<Self, String> {
        self.has(names)?;
        Ok(Self(self.0.into_iter().filter(|(n, _)| !names.contains(n)).collect()))
    }

    pub fn prefix(self, prefix: &str) -> Self {
        Self(self.0.into_iter().map(|(n, import)| (format!("{prefix}{n}"), import)).collect())
    }

    /// Renames imported bindings according to `renames`, returning an error identifying the first missing original name if any cannot be found.
    pub fn rename(self, renames: &[(String, String)]) -> Result<Self, String> {
        let olds: Vec<String> = renames.iter().map(|(old, _)| old.clone()).collect();
        self.has(&olds)?;
        let renamed = self.0.into_iter().map(|(n, import)| match renames.iter().find(|(old, _)| *old == n) {
            Some((_, new)) => (new.clone(), import),
            None => (n, import),
        });
        Ok(Self(renamed.collect()))
    }

    fn has(&self, names: &[String]) -> Result<(), String> {
        match names.iter().find(|name| !self.0.iter().any(|(n, _)| n == *name)) {
            Some(missing) => Err(missing.clone()),
            None => Ok(()),
        }
    }
}

/// An import specification parsed by a language front end, annotated with source locations `L`.
/// Applies nested import filters sequentially from innermost to outermost (e.g. `(prefix-in p: (only-in m a))` applies `only-in` prior to `prefix-in`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RequireSpec<L> {
    pub module: String,
    pub at: L,
    pub filters: Vec<Filter<L>>,
}

/// Filtering or renaming operations applied to an imported module's export set.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Filter<L> {
    Only(Vec<(String, L)>),
    Except(Vec<(String, L)>),
    Prefix(String),
    /// Renames imported identifiers from `(old_name, new_name, source_location)`.
    Rename(Vec<(String, String, L)>),
}

/// Errors encountered while evaluating an import specification, paired with source locations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpecError<L> {
    /// The requested module could not be found by the resolver or was never constructed.
    Resolve(L),
    /// The specified identifier is not exported by the target module.
    NotProvided(L),
}

impl<L: Copy> RequireSpec<L> {
    /// Resolves and filters the module imports for a requiring module named `from` using `resolver`.
    pub fn imports<'gc>(&self, mc: &Mutation<'gc>, resolver: &mut dyn Resolver<'gc>, from: Value<'gc>) -> Result<Imports<'gc>, SpecError<L>> {
        let at = |names: &[(String, L)], missing: String| names.iter().find(|(n, _)| *n == missing).map(|&(_, at)| SpecError::NotProvided(at));
        let module = resolver.resolve(mc, &self.module, from).ok_or(SpecError::Resolve(self.at))?;
        let mut imports = Imports::all(mc, module).ok_or(SpecError::Resolve(self.at))?;
        for filter in &self.filters {
            imports = match filter {
                Filter::Only(names) | Filter::Except(names) => {
                    let just: Vec<String> = names.iter().map(|(n, _)| n.clone()).collect();
                    let kept = if matches!(filter, Filter::Only(..)) { imports.only(&just) } else { imports.except(&just) };
                    kept.map_err(|missing| at(names, missing).expect("a missing name is one of the spec's"))?
                }
                Filter::Prefix(prefix) => imports.prefix(prefix),
                Filter::Rename(renames) => {
                    let pairs: Vec<(String, String)> = renames.iter().map(|(old, new, _)| (old.clone(), new.clone())).collect();
                    let olds: Vec<(String, L)> = renames.iter().map(|(old, _, at)| (old.clone(), *at)).collect();
                    imports.rename(&pairs).map_err(|missing| at(&olds, missing).expect("a missing name is one of the spec's"))?
                }
            };
        }
        Ok(imports)
    }
}

/// Inline expansion template for an exported procedure. Represents a lambda body whose constants are immediate values,
/// and whose variable references are restricted to parameters, local `let` bindings, and immutable module slots whose
/// values can be constant-quoted at inline sites. Inlined bodies invoke intrinsics, requests, or procedure values.
#[derive(Clone, Debug, PartialEq, Eq, Wire)]
pub struct Inline {
    params: u32,
    /// The number of trailing optional parameters that callers may omit, which default to unsupplied values.
    optional: u32,
    rest: bool,
    /// The number of local variables bound in the template body, allocated freshly for each inlined call site.
    locals: u32,
    body: Template,
    /// Indicates whether every parameter is referenced exactly once and in evaluation order prior to any other side effects,
    /// allowing argument expressions to be directly substituted without introducing temporary variables.
    linear: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Wire)]
enum Template {
    Param(u32),
    /// References a local variable introduced in the template body, indexed by binding order.
    Local(u32),
    /// A `let` binding form introducing consecutive local variables initialized to the given values around the body.
    Let(u32, Vec<Template>, Box<Template>),
    Immediate(Immediate),
    /// References an immutable slot from the defining module, resolved to a constant quote upon inlining.
    Slot(u32),
    If(Box<[Template; 3]>),
    Prim(Prim, Vec<Template>),
    Apply(Prim, Vec<Template>),
    /// Invokes the procedure produced by evaluating the first expression with the remaining expressions as arguments.
    Call(Vec<Template>),
}

/// Tracks evaluation events in a template body: either referencing a formal parameter or performing an operation with potential side effects.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Event {
    Param(u32),
    Other,
}

/// Represents the substitution target for a parameter in an inlined call: either an expression directly inlined or a local variable holding the argument.
enum Arg<'gc> {
    Core(Option<Core<'gc>>),
    Var(Var),
}

impl Arg<'_> {
    /// Returns true if `core` is a pure constant (such as a quote) that can be duplicated at every reference without changing semantics.
    fn is_trivial(core: &Core<'_>) -> bool {
        matches!(core, Core::Quote(_))
    }
}

/// An operand supplied to a struct accessor or constructor intrinsic: a parameter index, a module slot holding the struct type, or a constant field index.
#[derive(Clone, Copy, Debug)]
pub enum Operand {
    Param(u32),
    Slot(u32),
    Index(u32),
}

impl Inline {
    /// Generates an [`Inline`] template from `lambda` if its body meets inlining size and purity constraints.
    pub fn of(lambda: &Lambda<'_>) -> Option<Self> {
        let params: Vec<Var> = lambda.params.iter().copied().chain(lambda.rest).collect();
        let (mut left, mut locals) = (MAX_INLINE, Vec::new());
        let body = Template::of(&lambda.body, &params, &mut locals, &mut left)?;
        let (params, locals) = (u32::try_from(lambda.params.len()).ok()?, u32::try_from(locals.len()).ok()?);
        Some(Self::new(params, lambda.optional, lambda.rest.is_some(), locals, body))
    }

    /// Constructs an [`Inline`] template for a procedure with `params` parameters that delegates directly to `intrinsic` with `operands` (e.g. struct getters/setters/constructors).
    pub fn of_call(intrinsic: Intrinsic, params: u32, operands: &[Operand]) -> Self {
        let operand = |operand: &Operand| match *operand {
            Operand::Param(i) => Template::Param(i),
            Operand::Slot(slot) => Template::Slot(slot),
            Operand::Index(k) => Template::Immediate(Value::fixnum(i64::from(k)).and_then(Value::immediate).expect("an index is a fixnum")),
        };
        Self::new(params, 0, false, 0, Template::Prim(Prim::Intrinsic(intrinsic), operands.iter().map(operand).collect()))
    }

    fn new(params: u32, optional: u32, rest: bool, locals: u32, body: Template) -> Self {
        let mut events = Vec::new();
        body.events(&mut events);
        let uses: Vec<u32> = events.iter().filter_map(|e| if let Event::Param(i) = *e { Some(i) } else { None }).collect();
        let last_use = events.iter().rposition(|e| matches!(e, Event::Param(_)));
        let first_other = events.iter().position(|e| *e == Event::Other);
        let in_order = uses.iter().copied().eq(0..params + u32::from(rest));
        let linear = in_order && last_use.zip(first_other).is_none_or(|(used, other)| used < other);
        Self { params, optional, rest, locals, body, linear }
    }

    /// Returns an iterator over all module slot indices referenced by the inline template.
    pub fn slots(&self) -> impl Iterator<Item = u32> {
        let mut slots = Vec::new();
        self.body.slots(&mut slots);
        slots.into_iter()
    }

    pub fn takes(&self, n: usize) -> bool {
        n >= (self.params - self.optional) as usize && (self.rest || n <= self.params as usize)
    }

    /// Determines whether a call with `n` arguments can be inlined: checks arity compatibility and verifies that any rest-argument list does not exceed `MAX_REST`.
    pub fn inlines(&self, n: usize) -> bool {
        let rest = n.saturating_sub(self.params as usize);
        self.takes(n) && (!self.rest || rest <= MAX_REST || !self.body.uses_list(self.params, rest))
    }

    /// Expands the inline template with the given `args`, generating fresh local variable IDs via `fresh` and resolving referenced module slots via `slot`. Gathers excess arguments into a rest list or flattens them into apply operations.
    pub fn call<'gc>(&self, mut args: Vec<Core<'gc>>, fresh: &mut dyn FnMut() -> Var, slot: &dyn Fn(u32) -> Core<'gc>) -> Core<'gc> {
        if args.len() < self.params as usize {
            args.resize(self.params as usize, Core::Quote(Value::UNSUPPLIED));
        }
        let locals: Vec<Var> = (0..self.locals).map(|_| fresh()).collect();
        let mut binds = Vec::new();
        let mut args: Vec<Arg<'gc>> = args
            .into_iter()
            .map(|arg| {
                if self.linear || Arg::is_trivial(&arg) {
                    Arg::Core(Some(arg))
                } else {
                    let var = fresh();
                    binds.push((var, arg));
                    Arg::Var(var)
                }
            })
            .collect();
        let rest = args.split_off(self.params as usize);
        let mut inner = None;
        let body = if self.rest {
            let mut rest = rest;
            let list_uses = self.body.list_uses(self.params, rest.len());
            let mut cx = Instance { params: args, rest: Some(&mut rest), list: None, locals: &locals, slot };
            if list_uses > 0 {
                // Construct the rest list once from individual arguments. If referenced at only a single site, instantiate it at the use site to avoid constructing unused lists on alternate code branches.
                let items: Vec<Core<'gc>> = cx.rest.as_deref_mut().into_iter().flatten().map(|a| a.take()).collect();
                let list = items.into_iter().rfold(Core::Quote(Value::NIL), |tail, item| Core::Intrinsic(Prim::Intrinsic(Intrinsic::Cons), vec![item, tail]));
                if self.linear || list_uses == 1 {
                    cx.list = Some(Arg::Core(Some(list)));
                } else {
                    let var = fresh();
                    inner = Some((var, list));
                    cx.list = Some(Arg::Var(var));
                }
            }
            self.body.core(&mut cx, self.params)
        } else {
            self.body.core(&mut Instance { params: args, rest: None, list: None, locals: &locals, slot }, self.params)
        };
        // Wrap the body in a `Let` binding for the rest list, located inside the scope of the rest argument temporaries.
        let body = match inner {
            Some(list) => Core::Let(vec![list], Box::new(body)),
            None => body,
        };
        if binds.is_empty() { body } else { Core::Let(binds, Box::new(body)) }
    }
}

/// Context maintained while instantiating an inlined template into concrete AST nodes.
struct Instance<'r, 'gc> {
    params: Vec<Arg<'gc>>,
    rest: Option<&'r mut Vec<Arg<'gc>>>,
    list: Option<Arg<'gc>>,
    locals: &'r [Var],
    slot: &'r dyn Fn(u32) -> Core<'gc>,
}

impl<'gc> Arg<'gc> {
    /// Extracts the expression for this argument: duplicates trivial constant arguments, but yields non-trivial expressions only once.
    fn take(&mut self) -> Core<'gc> {
        match self {
            Arg::Var(var) => Core::Ref(Place::Local(*var)),
            Arg::Core(core) => match core {
                Some(c) if Arg::is_trivial(c) => c.clone(),
                _ => core.take().expect("a linear template uses each argument once"),
            },
        }
    }
}

/// Checks whether the primitive `prim` accepts an argument count of `n`.
fn takes(prim: Prim, n: usize) -> bool {
    match prim {
        Prim::Intrinsic(i) => i.arity().is_none_or(|a| usize::from(a) == n),
        Prim::Request(r) => r.takes(n),
        Prim::Host(h) => h.takes(n),
        Prim::Slot(op, _) => op.arity() == n,
    }
}

impl Template {
    /// Converts `core` into a `Template` given formal parameters `params` and visible `locals`, returning `None` if AST complexity exceeds the remaining quota in `left`.
    fn of(mut core: &Core<'_>, params: &[Var], locals: &mut Vec<Var>, left: &mut usize) -> Option<Self> {
        // A template keeps no positions: code inlined from it reports the position of the call it replaces.
        while let Core::At(_, inner) = core {
            core = inner;
        }
        *left = left.checked_sub(1)?;
        // Host functions are transitively propagated into the host table of any requiring module, so they may be safely inlined.
        let closed = |prim: &Prim| !matches!(prim, Prim::Slot(..));
        let mut all = |args: &[Core<'_>], locals: &mut Vec<Var>| args.iter().map(|a| Self::of(a, params, locals, left)).collect::<Option<Vec<_>>>();
        Some(match core {
            Core::Ref(Place::Local(v)) => match params.iter().position(|p| p == v) {
                Some(i) => Self::Param(i as u32),
                None => Self::Local(locals.iter().position(|l| l == v)? as u32),
            },
            // Module variable reference: retained for inlining only if verified to be immutable.
            Core::Ref(Place::Slot { slot, .. }) => Self::Slot(*slot),
            Core::App(f, args) => {
                let f = Self::of(f, params, locals, left)?;
                Self::Call(std::iter::once(Some(f)).chain(args.iter().map(|a| Self::of(a, params, locals, left))).collect::<Option<Vec<_>>>()?)
            }
            Core::Quote(v) => Self::Immediate(v.immediate()?),
            Core::If(a, b, c) => {
                let (a, b) = (Self::of(a, params, locals, left)?, Self::of(b, params, locals, left)?);
                Self::If(Box::new([a, b, Self::of(c, params, locals, left)?]))
            }
            Core::Intrinsic(prim, args) if closed(prim) => Self::Prim(*prim, all(args, locals)?),
            Core::ApplyIntrinsic(prim, args) if closed(prim) => Self::Apply(*prim, all(args, locals)?),
            Core::Let(binds, body) => {
                let values = binds.iter().map(|(_, value)| Self::of(value, params, locals, left)).collect::<Option<Vec<_>>>()?;
                let first = u32::try_from(locals.len()).ok()?;
                locals.extend(binds.iter().map(|&(var, _)| var));
                Self::Let(first, values, Box::new(Self::of(body, params, locals, left)?))
            }
            _ => return None,
        })
    }

    /// Records the sequence of parameter references and effectful operations performed by the template. Conditional branches are marked as non-linear operations following the test expression.
    fn events(&self, out: &mut Vec<Event>) {
        match self {
            Self::Param(i) => out.push(Event::Param(*i)),
            Self::Immediate(_) | Self::Local(_) | Self::Slot(_) => {}
            Self::Let(_, values, body) => {
                for value in values {
                    value.events(out);
                }
                body.events(out);
            }
            Self::If(parts) => {
                parts[0].events(out);
                // Mark subsequent uses as non-linear because branch evaluation is conditional.
                out.push(Event::Other);
                for branch in &parts[1..] {
                    branch.events(out);
                }
            }
            Self::Prim(_, args) | Self::Apply(_, args) | Self::Call(args) => {
                for arg in args {
                    arg.events(out);
                }
                out.push(Event::Other);
            }
        }
    }

    /// Appends all module slot indices referenced by this template to `out`.
    fn slots(&self, out: &mut Vec<u32>) {
        match self {
            Self::Slot(slot) => out.push(*slot),
            Self::Param(_) | Self::Immediate(_) | Self::Local(_) => {}
            Self::Let(_, values, body) => values.iter().chain([&**body]).for_each(|p| p.slots(out)),
            Self::If(parts) => parts.iter().for_each(|p| p.slots(out)),
            Self::Prim(_, args) | Self::Apply(_, args) | Self::Call(args) => args.iter().for_each(|a| a.slots(out)),
        }
    }

    /// Determines whether a call with `count` excess arguments uses the rest parameter as a materialized list rather than spreading it into an `apply` primitive.
    fn uses_list(&self, rest: u32, count: usize) -> bool {
        self.list_uses(rest, count) > 0
    }

    /// Counts the number of occurrences where the rest parameter `rest` is used as a materialized list when called with `count` excess arguments.
    fn list_uses(&self, rest: u32, count: usize) -> usize {
        let of = |parts: &[Template]| parts.iter().map(|p| p.list_uses(rest, count)).sum::<usize>();
        match self {
            Self::Param(i) => usize::from(*i == rest),
            Self::Immediate(_) | Self::Local(_) | Self::Slot(_) => 0,
            Self::Let(_, values, body) => of(values) + body.list_uses(rest, count),
            Self::If(parts) => of(&parts[..]),
            Self::Prim(_, args) | Self::Call(args) => of(args),
            Self::Apply(prim, args) => match args.split_last() {
                Some((Self::Param(i), fixed)) if *i == rest => usize::from(!takes(*prim, fixed.len() + count)) + of(fixed),
                _ => of(args),
            },
        }
    }

    /// Instantiates the template into a concrete [`Core`] AST expression using the substitution bindings in `cx` and rest parameter index `rest`.
    fn core<'gc>(&self, cx: &mut Instance<'_, 'gc>, rest: u32) -> Core<'gc> {
        match self {
            Self::Param(i) if *i == rest && cx.rest.is_some() => cx.list.as_mut().expect("the rest's list is made when it's used").take(),
            Self::Param(i) => cx.params[*i as usize].take(),
            Self::Immediate(v) => Core::Quote(v.value()),
            Self::Slot(slot) => (cx.slot)(*slot),
            Self::Local(k) => Core::Ref(Place::Local(cx.locals[*k as usize])),
            Self::Let(first, values, body) => {
                let binds = values.iter().zip(*first..).map(|(value, k)| (cx.locals[k as usize], value.core(cx, rest))).collect();
                Core::Let(binds, Box::new(body.core(cx, rest)))
            }
            Self::If(parts) => {
                let [a, b, c] = &**parts;
                Core::If(Box::new(a.core(cx, rest)), Box::new(b.core(cx, rest)), Box::new(c.core(cx, rest)))
            }
            Self::Prim(prim, args) => Core::Intrinsic(*prim, args.iter().map(|a| a.core(cx, rest)).collect()),
            Self::Call(parts) => {
                let mut parts = parts.iter().map(|part| part.core(cx, rest));
                let f = parts.next().expect("a call has a procedure");
                Core::App(Box::new(f), parts.collect())
            }
            Self::Apply(prim, args) => match args.split_last() {
                Some((Self::Param(i), fixed)) if *i == rest && cx.rest.is_some() => {
                    let count = cx.rest.as_ref().map_or(0, |r| r.len());
                    let fixed: Vec<Core<'gc>> = fixed.iter().map(|a| a.core(cx, rest)).collect();
                    if takes(*prim, fixed.len() + count) {
                        let spread: Vec<Core<'gc>> = cx.rest.as_deref_mut().into_iter().flatten().map(|a| a.take()).collect();
                        Core::Intrinsic(*prim, fixed.into_iter().chain(spread).collect())
                    } else {
                        let list = cx.list.as_mut().expect("the rest's list is made when it's used").take();
                        Core::ApplyIntrinsic(*prim, fixed.into_iter().chain([list]).collect())
                    }
                }
                _ => Core::ApplyIntrinsic(*prim, args.iter().map(|a| a.core(cx, rest)).collect()),
            },
        }
    }
}

/// Errors encountered during module construction, reported with source locations by the language front end.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ModuleError {
    /// An identifier was defined multiple times or exported multiple times.
    Duplicate,
    /// Identifier collision: an identifier was both defined and imported, or imported from conflicting sources.
    Conflict,
    /// Attempted to export an identifier that is not defined in the module.
    NotDefined,
    /// Attempted to mutate an immutable definition, such as a keyword procedure core or a struct type descriptor.
    Immutable,
    OutOfMemory,
}

impl From<OutOfMemory> for ModuleError {
    fn from(_: OutOfMemory) -> Self {
        Self::OutOfMemory
    }
}

/// The top-level resolution of an identifier in a module.
#[derive(Clone, Copy, Debug)]
pub enum Binding<'gc> {
    /// A variable slot defined locally within this module.
    Slot(u32),
    Import(Import<'gc>),
}

/// The kind of definition exported under an export name.
#[derive(Clone, Copy)]
enum Provided {
    /// Exports a module variable slot.
    Variable(u32),
    /// Exports the struct type descriptor for pattern matching only, omitting its constructor.
    Matching(u32),
}

/// Incremental module builder for language front ends.
/// Front ends first declare imports, definitions, and exports; call [`ModuleBuilder::start`] to allocate the module;
/// sequentially lower and compile top-level forms via [`ModuleBuilder::compile`]; and finally call [`ModuleBuilder::finish`]
/// to publish the module's [`Interface`].
pub struct ModuleBuilder<'gc> {
    name: Value<'gc>,
    hosts: &'static [HostDef],
    /// Names of module variables and the index of the top-level form that defines each.
    names: Vec<Value<'gc>>,
    defined_by: Vec<u32>,
    /// Top-level bindings declared by definitions and explicit imports, as well as fallback implicit imports shadowed by them.
    bindings: HashMap<u64, Binding<'gc>>,
    implicit: HashMap<u64, Import<'gc>>,
    exports: Vec<(Box<str>, Provided)>,
    assigned: HashSet<u32>,
    inlines: HashMap<u32, Inline>,
    /// Maps keyword procedure slots to their underlying core implementation slot and keyword call shape.
    cores: HashMap<u32, (u32, CallShape<'gc>)>,
    /// Maps struct type descriptor slots to their type object and member slots, and maps constructor slots to their struct definitions.
    kinds: HashMap<u32, (Value<'gc>, Vec<(u32, Member)>)>,
    structs: HashMap<u32, StructDef>,
    /// Maps struct procedure slots to their inline templates and associated struct type objects.
    procedures: HashMap<u32, (Inline, Value<'gc>)>,
    module: Option<Gc<'gc, Module>>,
}

impl<'gc> ModuleBuilder<'gc> {
    /// Creates a new `ModuleBuilder` for a module named `name` with host function bindings `hosts`.
    pub fn new(name: Value<'gc>, hosts: &'static [HostDef]) -> Self {
        Self {
            name,
            hosts,
            names: Vec::new(),
            defined_by: Vec::new(),
            bindings: HashMap::default(),
            implicit: HashMap::default(),
            exports: Vec::new(),
            assigned: HashSet::default(),
            inlines: HashMap::default(),
            cores: HashMap::default(),
            kinds: HashMap::default(),
            structs: HashMap::default(),
            procedures: HashMap::default(),
            module: None,
        }
    }

    pub fn name(&self) -> Value<'gc> {
        self.name
    }

    pub fn hosts(&self) -> &'static [HostDef] {
        self.hosts
    }

    /// Declares a module variable named `name` in top-level form `form`, returning its assigned slot index.
    pub fn define(&mut self, name: Value<'gc>, form: u32) -> Result<u32, ModuleError> {
        match self.bindings.get(&name.to_bits()) {
            Some(Binding::Slot(_)) => return Err(ModuleError::Duplicate),
            Some(Binding::Import(_)) => return Err(ModuleError::Conflict),
            None => {}
        }
        let slot = self.define_private(name, form)?;
        self.bindings.insert(name.to_bits(), Binding::Slot(slot));
        Ok(slot)
    }

    /// Declares an anonymous or hygienic module variable (such as one generated by a macro) with display name `name`, returning its assigned slot index.
    pub fn define_private(&mut self, name: Value<'gc>, form: u32) -> Result<u32, ModuleError> {
        let slot = u32::try_from(self.names.len()).map_err(|_| ModuleError::OutOfMemory)?;
        self.names.push(name);
        self.defined_by.push(form);
        Ok(slot)
    }

    /// Binds symbol `name` to an imported definition.
    pub fn import(&mut self, name: Value<'gc>, import: Import<'gc>) -> Result<(), ModuleError> {
        match self.bindings.get(&name.to_bits()) {
            Some(&Binding::Import(other)) if other.same(import) => Ok(()),
            Some(_) => Err(ModuleError::Conflict),
            None => {
                self.bindings.insert(name.to_bits(), Binding::Import(import));
                Ok(())
            }
        }
    }

    /// Binds all exported names in `imports` into the module's top-level scope.
    pub fn require(&mut self, mc: &Mutation<'gc>, symbols: Symbols<'gc>, imports: Imports<'gc>) -> Result<(), ModuleError> {
        let strings = Strings::new(mc);
        for (name, import) in imports.0 {
            let symbol = symbols.intern_str(&strings, &name).map_err(|_| ModuleError::OutOfMemory)?;
            self.import(symbol.value(mc), import)?;
        }
        Ok(())
    }

    /// Implicitly imports all exports of `module` (such as a base language prelude), allowing explicit definitions and imports to shadow them.
    pub fn require_implicitly(&mut self, mc: &Mutation<'gc>, symbols: Symbols<'gc>, module: Gc<'gc, Module>) -> Result<(), ModuleError> {
        let strings = Strings::new(mc);
        for (name, import) in Imports::all(mc, module).unwrap_or_default().0 {
            let symbol = symbols.intern_str(&strings, &name).map_err(|_| ModuleError::OutOfMemory)?;
            self.implicit.insert(symbol.value(mc).to_bits(), import);
        }
        Ok(())
    }

    /// Exports the module variable named `name` under public export name `external`.
    pub fn provide(&mut self, external: &str, name: Value<'gc>) -> Result<(), ModuleError> {
        let Some(&Binding::Slot(slot)) = self.bindings.get(&name.to_bits()) else { return Err(ModuleError::NotDefined) };
        self.provide_as(external, Provided::Variable(slot))
    }

    fn provide_as(&mut self, external: &str, provided: Provided) -> Result<(), ModuleError> {
        if self.exports.iter().any(|(n, _)| **n == *external) {
            return Err(ModuleError::Duplicate);
        }
        self.exports.push((external.into(), provided));
        Ok(())
    }

    /// Exports all identifiers defined by the struct form associated with `constructor`.
    ///
    /// If `constructors` is false, constructors are omitted from exports and the struct name is exported solely for pattern matching
    /// (see [`StructDef::match_only`]). Client modules can then destructure instances via `match`, but can only instantiate them
    /// through custom constructor procedures exported by this module.
    pub fn provide_struct(&mut self, mc: &Mutation<'gc>, constructor: u32, constructors: bool) -> Result<(), ModuleError> {
        let members = self.structs.get(&constructor).and_then(|def| self.kinds.get(&def.kind)).ok_or(ModuleError::NotDefined)?.1.clone();
        let strings = Strings::new(mc);
        for (slot, member) in members {
            let symbol = Symbol::of(self.names[slot as usize]).expect("variables are named by symbols");
            let external: String = chars(&strings, symbol.name(mc)).collect();
            if constructors || member != Member::Make {
                self.provide_as(&external, Provided::Variable(slot))?;
            } else if slot == constructor {
                self.provide_as(&external, Provided::Matching(slot))?;
            }
        }
        Ok(())
    }

    /// Exports all uniquely named top-level module variables under their respective symbol names.
    pub fn provide_all(&mut self, mc: &Mutation<'gc>) -> Result<(), ModuleError> {
        let strings = Strings::new(mc);
        let public = self.names.iter().enumerate().filter(|&(slot, name)| matches!(self.bindings.get(&name.to_bits()), Some(&Binding::Slot(s)) if s as usize == slot));
        for name in public.map(|(_, &name)| name).collect::<Vec<_>>() {
            let symbol = Symbol::of(name).expect("variables are named by symbols");
            let external: String = chars(&strings, symbol.name(mc)).collect();
            self.provide(&external, name)?;
        }
        Ok(())
    }

    /// Resolves symbol `name` in the module's top-level scope, checking explicit definitions/imports first, then implicit imports.
    pub fn binding(&self, name: Value<'gc>) -> Option<Binding<'gc>> {
        let k = name.to_bits();
        self.bindings.get(&k).copied().or_else(|| self.implicit.get(&k).copied().map(Binding::Import))
    }

    /// Allocates and initializes the runtime [`Module`] once all definitions are declared. Combines the module's own host functions
    /// with all host functions transitively required by imported modules, ensuring host calls in inlined functions resolve correctly.
    pub fn start(&mut self, mc: &Mutation<'gc>) -> Result<Gc<'gc, Module>, OutOfMemory> {
        let mut hosts: Vec<&'static HostDef> = self.hosts.iter().collect();
        let imported = self.bindings.values().filter_map(|b| if let Binding::Import(i) = b { Some(i) } else { None }).chain(self.implicit.values());
        let mut seen = Vec::new();
        for import in imported {
            if seen.contains(&import.module) {
                continue;
            }
            seen.push(import.module);
            for &def in import.module.hosts(mc).map_or(&[][..], |h| &h[..]) {
                if !hosts.contains(&def) {
                    hosts.push(def);
                }
            }
        }
        let module = ragwort_vm::module::new(mc, self.name, &self.names, hosts)?;
        self.module = Some(module);
        Ok(module)
    }

    /// Returns the [`Place`] for accessing variable `slot` within top-level form `form`, optionally within the initializing lambda `defining`.
    /// Emits an unchecked access if the slot is guaranteed to have already been defined.
    pub fn place(&self, slot: u32, form: u32, defining: Option<u32>) -> Place {
        let defined = self.defined_by.get(slot as usize).is_some_and(|&by| by < form) || defining == Some(slot);
        Place::Slot { slot, checked: !defined }
    }

    /// Registers `procedure` as a keyword procedure with shape `shape` implemented by underlying core procedure `core`, allowing language front ends to bypass wrapper dispatch when keywords match.
    pub fn keyword_core(&mut self, procedure: u32, core: u32, shape: CallShape<'gc>) {
        self.cores.insert(procedure, (core, shape));
    }

    /// Retrieves the core procedure slot and call shape for keyword procedure `slot`, if registered.
    pub fn keyword_def(&self, slot: u32) -> Option<(u32, &CallShape<'gc>)> {
        self.cores.get(&slot).map(|(core, shape)| (*core, shape))
    }

    /// Registers struct type metadata: associates type descriptor slot `def.kind` with runtime object `kind` and member slots `members`, and associates constructor slot `constructor` with `def`.
    pub fn define_struct(&mut self, constructor: u32, def: StructDef, kind: Value<'gc>, members: Vec<(u32, Member)>) {
        self.kinds.insert(def.kind, (kind, members));
        self.structs.insert(constructor, def);
    }

    /// Registers `slot` as an accessor or constructor for struct type `kind` with inlining template `inline`.
    pub fn struct_procedure(&mut self, slot: u32, inline: Inline, kind: Value<'gc>) {
        self.procedures.insert(slot, (inline, kind));
    }

    /// Retrieves the struct definition and runtime type object associated with constructor slot `slot`.
    pub fn struct_def(&self, slot: u32) -> Option<(&StructDef, Value<'gc>)> {
        let def = self.structs.get(&slot)?;
        Some((def, self.kinds.get(&def.kind)?.0))
    }

    /// Generates a struct procedure call for `slot` within form `form`, checking for slot initialization if the defining form has not yet executed.
    pub fn struct_call(&self, slot: u32, form: u32) -> Option<Call<'gc>> {
        let (inline, kind) = self.procedures.get(&slot)?;
        let defined = self.defined_by.get(slot as usize).is_some_and(|&by| by < form);
        Some(Call::new(inline.clone(), Core::Quote(*kind), (!defined).then_some(Place::Slot { slot, checked: true })))
    }

    /// Returns the constant value of variable `slot` in form `form` if it has already been initialized (such as a struct type descriptor defined in an earlier form).
    pub fn constant(&self, slot: u32, form: u32) -> Option<Value<'gc>> {
        let (kind, _) = self.kinds.get(&slot)?;
        self.defined_by.get(slot as usize).is_some_and(|&by| by < form).then_some(*kind)
    }

    /// Marks variable `slot` as mutated. Returns an error if `slot` represents an immutable keyword procedure core or struct procedure.
    pub fn assign(&mut self, slot: u32) -> Result<(), ModuleError> {
        if self.cores.contains_key(&slot) || self.procedures.contains_key(&slot) || self.kinds.contains_key(&slot) {
            return Err(ModuleError::Immutable);
        }
        self.assigned.insert(slot);
        Ok(())
    }

    /// Records `value` as the initializing expression for `slot`, analyzing it for potential inlining if it is a lambda.
    pub fn defined(&mut self, slot: u32, value: &Core<'gc>) {
        if let Core::Lambda(lambda) = value
            && let Some(inline) = Inline::of(lambda)
        {
            self.inlines.insert(slot, inline);
        }
    }

    /// Compiles top-level form `core` in the context of the active module.
    pub fn compile(&self, mc: &Mutation<'gc>, core: &Core<'gc>) -> Result<Value<'gc>, CompileError> {
        compile(mc, self.module, core)
    }

    /// Finalizes the module after all top-level forms are compiled, publishing its [`Interface`] and returning the module instance.
    pub fn finish(mut self, mc: &Mutation<'gc>) -> Result<Gc<'gc, Module>, OutOfMemory> {
        let module = match self.module {
            Some(module) => module,
            None => self.start(mc)?,
        };
        let export = |slot: u32| {
            let mutable = self.assigned.contains(&slot);
            // Do not inline procedures that read mutated module slots; otherwise callers would observe stale values captured at import time.
            let fixed = |inline: &&Inline| inline.slots().all(|read| !self.assigned.contains(&read));
            let inline = if mutable { None } else { self.procedures.get(&slot).map(|(inline, _)| inline).or(self.inlines.get(&slot)).filter(fixed).cloned() };
            Export { slot, mutable, inline, core: None, structure: self.structs.get(&slot).cloned().map(Box::new) }
        };
        let mut exports = HashMap::default();
        for &(ref name, provided) in &self.exports {
            let out = match provided {
                Provided::Variable(slot) => {
                    let mut out = export(slot);
                    if !out.mutable {
                        out.core = self.cores.get(&slot).map(|&(core, _)| Box::new(export(core)));
                    }
                    out
                }
                // Bind the export to the struct type descriptor slot rather than the constructor, restricting use to pattern matching.
                Provided::Matching(constructor) => {
                    let def = self.structs.get(&constructor).expect("a struct's constructor").clone();
                    let mut out = export(def.kind);
                    out.structure = Some(Box::new(StructDef { sealed: true, match_only: true, ..def }));
                    out
                }
            };
            exports.insert(name.clone(), out);
        }
        ragwort_vm::module::set_interface(mc, module, Interface { exports })?;
        Ok(module)
    }
}
