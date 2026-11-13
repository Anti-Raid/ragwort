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

use std::cell::RefCell;

use crate::hash::{HashMap, HashSet};

use ragwort_types::Wire;
use ragwort_types::gc::image::{Kind, LoadError, freeze};
use ragwort_types::gc::{Gc, Immediate, Mutation, OutOfMemory, Value};
use ragwort_types::wire::{Malformed, Reader, Writer, mix, shape_of};
use ragwort_types::string::{Strings, chars};
use ragwort_types::symbol::{Symbol, Symbols};
use ragwort_types::syntax::{SyntaxSource, SyntaxSpan};
use ragwort_vm::objects::{Module, ModuleFields};
use ragwort_vm::{HostDef, Intrinsic, Request};

use crate::ir::Sites;
use crate::ir::l1::{Fun, Id, L1, Node, Span};
use crate::keyword::{self, CallShape};
use crate::structs::{self, Call, Declared, Member};
use crate::{CompileError, Core, GlobalError, Place, Position, Prim, SlotOp, Var, compile_in};

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
    /// The name the module exports the binding under.
    pub name: &'gc str,
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
            return Ok(Core::Intrinsic(Prim::Intrinsic(Intrinsic::ModuleRef), read, None));
        }
        self.variable(mc, slot).map(Core::Quote).ok_or(Unusable::Uninitialized)
    }

    /// Returns an [`Import`] pointing to the underlying core procedure if this import represents a keyword procedure.
    pub fn keyword_core(self) -> Option<Self> {
        Some(Self { module: self.module, export: self.export.core.as_deref()?, name: self.name })
    }

    /// Checks that the import can be used as a value: a front end calls this to report an unusable import at its source position before emitting [`Core::Import`].
    pub fn usable(self, mc: &Mutation<'gc>) -> Result<(), Unusable> {
        self.reference(mc).map(|_| ())
    }

    /// Checks that a call of the import with `args` arguments can be compiled: either the call is inlined, or the import is usable as a value.
    pub fn callable(self, mc: &Mutation<'gc>, args: usize) -> Result<(), Unusable> {
        if self.inlined(mc, args).is_some() { Ok(()) } else { self.usable(mc) }
    }

    /// Returns the inline template that a call of the import with `args` arguments expands to, if it has one that accepts them, and the procedure's own variable and every module variable the template reads are defined.
    ///
    /// The procedure's variable is undefined only when its module stopped before defining it, as an input to the REPL that raised an error does. A call then fails as a reference to the name does.
    pub(crate) fn inlined(self, mc: &Mutation<'gc>, args: usize) -> Option<&'gc Inline> {
        let inline = self.export.inline.as_ref()?;
        let defined = |slot: u32| self.variable(mc, slot).is_some();
        let fits = inline.inlines(args) && defined(self.export.slot) && inline.slots().all(defined);
        fits.then_some(inline)
    }

    /// Returns the struct definition metadata and runtime type descriptor if this import represents a struct constructor or type name.
    pub fn struct_def(self, mc: &Mutation<'gc>) -> Option<(&'gc StructDef, Value<'gc>)> {
        let def = self.export.structure.as_deref()?;
        Some((def, self.variable(mc, def.kind)?))
    }

    /// Retrieves the value stored in the module's variable `slot`, returning `None` if the slot is out of bounds or still undefined.
    pub(crate) fn variable(self, mc: &Mutation<'gc>, slot: u32) -> Option<Value<'gc>> {
        let items = self.module.items(mc);
        (slot as usize).lt(&items.len()).then(|| items.get(slot as usize)).filter(|&v| v != Value::UNDEFINED)
    }
}

/// A collection of resolved imports mapped to local binding names, transformed by import filters (such as `only`, `except`, `prefix`, and `rename`).
#[derive(Clone, Debug, Default)]
pub struct Imports<'gc>(pub Vec<(String, Import<'gc>)>);

impl<'gc> Imports<'gc> {
    /// Imports all public definitions exported by `module` under their original export names.
    pub fn all(mc: &Mutation<'gc>, module: Gc<'gc, Module>) -> Option<Self> {
        let interface = interface(mc, module)?;
        let mut imports: Vec<_> = interface.iter().map(|(name, export)| (name.to_owned(), Import { module, export, name })).collect();
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
    /// The name of the source that defines the procedure and the line its definition starts on, when known. An error report shows them for a call inlined from this template.
    origin: Option<(Box<str>, u32)>,
    /// The module variables the body reads, each once. A call expands from the template only while all of them are defined.
    slots: Box<[u32]>,
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
    /// An operation on the given operands. The last field of this variant and of the next two is the line the operation is written on, in the source that [`Inline::origin`] names, or 0 if the line is not known. An error raised in code expanded from the template reports that line.
    Prim(Prim, Vec<Template>, u32),
    Apply(Prim, Vec<Template>, u32),
    /// Invokes the procedure produced by evaluating the first expression with the remaining expressions as arguments.
    Call(Vec<Template>, u32),
}

/// Finds the line that an operation of a procedure is written on, while a template is made from the procedure.
struct Lines<'x, 'gc> {
    mc: &'x Mutation<'gc>,
    sites: &'x Sites<'gc>,
    /// The source that the procedure is defined in, which the template's lines count in.
    source: Option<Value<'gc>>,
}

impl Lines<'_, '_> {
    /// Returns the line of the code at `site`, or 0 if it has no position, or is not written in the procedure's own source: code that a macro wrote, or that was itself expanded from another procedure's template.
    fn of(&self, site: u32) -> u32 {
        let line = || {
            let site = self.sites.get(site).filter(|site| site.inlined == 0 && Some(site.at.source) == self.source)?;
            Some(SyntaxSource::of(site.at.source)?.location(self.mc, site.at.offset)?.line)
        };
        line().unwrap_or(0)
    }
}

/// Tracks evaluation events in a template body: either referencing a formal parameter or performing an operation with potential side effects.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Event {
    Param(u32),
    Other,
}

/// Builds the code that an inline template expands to, in one representation of code. The compiler's first pass implements it for its node table.
pub(crate) trait Target<'gc> {
    type Expr;

    fn fresh(&mut self) -> Var;
    /// Tells the target that the operation built next is written on `line` of the source the template comes from, or that its line is not known if `line` is 0.
    fn line(&mut self, line: u32);
    fn quote(&mut self, value: Value<'gc>) -> Self::Expr;
    fn local(&mut self, var: Var) -> Self::Expr;
    /// Builds the value of variable `slot` of the module the template belongs to.
    fn slot(&mut self, slot: u32) -> Self::Expr;
    fn bind(&mut self, binds: Vec<(Var, Self::Expr)>, body: Self::Expr) -> Self::Expr;
    fn branch(&mut self, test: Self::Expr, then: Self::Expr, other: Self::Expr) -> Self::Expr;
    fn prim(&mut self, prim: Prim, args: Vec<Self::Expr>) -> Self::Expr;
    fn apply(&mut self, prim: Prim, args: Vec<Self::Expr>) -> Self::Expr;
    fn call(&mut self, f: Self::Expr, args: Vec<Self::Expr>) -> Self::Expr;
    /// Returns whether `expr` is a constant, which an expansion may use any number of times.
    fn is_constant(&self, expr: &Self::Expr) -> bool;
    /// Builds another copy of the constant `expr`.
    fn copy(&mut self, expr: &Self::Expr) -> Self::Expr;
}

/// Represents the substitution target for a parameter in an inlined call: either an expression directly inlined or a local variable holding the argument.
enum Arg<E> {
    Expr(Option<E>),
    Var(Var),
}

/// An operand supplied to a struct accessor or constructor intrinsic: a parameter index, a module slot holding the struct type, or a constant field index.
#[derive(Clone, Copy, Debug)]
pub enum Operand {
    Param(u32),
    Slot(u32),
    Index(u32),
}

impl Inline {
    /// Generates an [`Inline`] template from the lowered lambda `fun` of `tree` if its body meets inlining size and purity constraints. `at` is the position of the lambda's definition.
    ///
    /// The template is made from the lowered form, in which calls of imports are expanded, struct and keyword procedures of the module are resolved, and a parameter with a default is bound by a `let` around the body.
    pub(crate) fn of_function<'id, 'gc>(mc: &Mutation<'gc>, tree: &L1<'id, 'gc>, sites: &Sites<'gc>, fun: Fun<'id>, at: Option<Position<'gc>>) -> Option<Self> {
        let fun = tree[fun];
        let params: Vec<Var> = tree[fun.params].iter().copied().chain(fun.rest).collect();
        let (mut left, mut locals) = (MAX_INLINE, Vec::new());
        let lines = Lines { mc, sites, source: at.map(|at| at.source) };
        let body = Template::of(tree, fun.body, &params, &mut locals, &mut left, &lines)?;
        let (params, locals) = (u32::try_from(tree[fun.params].len()).ok()?, u32::try_from(locals.len()).ok()?);
        Some(Self::new(params, fun.optional, fun.rest.is_some(), locals, body).defined_at(mc, at))
    }

    /// Records the source and line of the position `at`, where the procedure is defined.
    fn defined_at<'gc>(mut self, mc: &Mutation<'gc>, at: Option<Position<'gc>>) -> Self {
        self.origin = at.and_then(|at| {
            let source = SyntaxSource::of(at.source)?;
            let name = String::from_utf8_lossy(source.name(mc)?.bytes(mc)).into_owned();
            Some((name.into_boxed_str(), source.location(mc, at.offset)?.line))
        });
        self
    }

    /// Returns the name of the source that defines the procedure and the line its definition starts on, when known.
    pub(crate) fn origin(&self) -> Option<(&str, u32)> {
        self.origin.as_ref().map(|(file, line)| (&**file, *line))
    }

    /// Returns whether an expansion of the template may need fresh variables: for its own locals, or to hold arguments it uses more than once or out of order.
    pub(crate) fn needs_vars(&self) -> bool {
        !self.linear || self.locals > 0
    }

    /// Returns whether a call inlined from the template is reported as the operation itself, not as a call of the procedure. That holds for two kinds of template:
    ///
    /// - a single built-in operation applied to parameters and constants, as the prelude's wrappers around intrinsics are;
    /// - a procedure whose outermost operation raises its argument, such as `error`, because the error belongs to the caller.
    pub(crate) fn is_wrapper(&self) -> bool {
        let simple = |part: &Template| matches!(part, Template::Param(_) | Template::Immediate(_) | Template::Slot(_));
        match &self.body {
            Template::Prim(Prim::Request(Request::Raise | Request::RaiseContinuable), ..) => true,
            Template::Prim(_, args, _) | Template::Apply(_, args, _) => args.iter().all(simple),
            _ => false,
        }
    }

    /// Constructs an [`Inline`] template for a procedure with `params` parameters that delegates directly to `intrinsic` with `operands` (e.g. struct getters/setters/constructors).
    pub fn of_call(intrinsic: Intrinsic, params: u32, operands: &[Operand]) -> Self {
        let operand = |operand: &Operand| match *operand {
            Operand::Param(i) => Template::Param(i),
            Operand::Slot(slot) => Template::Slot(slot),
            Operand::Index(k) => Template::Immediate(Value::fixnum(i64::from(k)).and_then(Value::immediate).expect("an index is a fixnum")),
        };
        Self::new(params, 0, false, 0, Template::Prim(Prim::Intrinsic(intrinsic), operands.iter().map(operand).collect(), 0))
    }

    fn new(params: u32, optional: u32, rest: bool, locals: u32, body: Template) -> Self {
        let mut events = Vec::new();
        body.events(&mut events);
        let uses: Vec<u32> = events.iter().filter_map(|e| if let Event::Param(i) = *e { Some(i) } else { None }).collect();
        let last_use = events.iter().rposition(|e| matches!(e, Event::Param(_)));
        let first_other = events.iter().position(|e| *e == Event::Other);
        let in_order = uses.iter().copied().eq(0..params + u32::from(rest));
        let linear = in_order && last_use.zip(first_other).is_none_or(|(used, other)| used < other);
        let mut slots = Vec::new();
        body.slots(&mut slots);
        slots.sort_unstable();
        slots.dedup();
        Self { params, optional, rest, locals, body, linear, origin: None, slots: slots.into() }
    }

    /// Returns an iterator over all module slot indices referenced by the inline template.
    pub fn slots(&self) -> impl Iterator<Item = u32> {
        self.slots.iter().copied()
    }

    pub fn takes(&self, n: usize) -> bool {
        n >= (self.params - self.optional) as usize && (self.rest || n <= self.params as usize)
    }

    /// Determines whether a call with `n` arguments can be inlined: checks arity compatibility and verifies that any rest-argument list does not exceed `MAX_REST`.
    pub fn inlines(&self, n: usize) -> bool {
        let rest = n.saturating_sub(self.params as usize);
        self.takes(n) && (!self.rest || rest <= MAX_REST || !self.body.uses_list(self.params, rest))
    }

    /// Expands the template for a call with the arguments `args`, building the expansion with `target`. Arguments past the parameters are gathered into a rest list or spread into the operation that takes them.
    pub(crate) fn expand<'gc, T: Target<'gc>>(&self, target: &mut T, mut args: Vec<T::Expr>) -> T::Expr {
        while args.len() < self.params as usize {
            args.push(target.quote(Value::UNSUPPLIED));
        }
        let locals: Vec<Var> = (0..self.locals).map(|_| target.fresh()).collect();
        let mut binds = Vec::new();
        let mut held = Vec::with_capacity(args.len());
        for arg in args {
            if self.linear || target.is_constant(&arg) {
                held.push(Arg::Expr(Some(arg)));
            } else {
                let var = target.fresh();
                binds.push((var, arg));
                held.push(Arg::Var(var));
            }
        }
        let rest = held.split_off(self.params as usize);
        let mut cx = Instance { params: held, rest: None, list: None, locals };
        let mut inner = None;
        if self.rest {
            let list_uses = self.body.list_uses(self.params, rest.len());
            cx.rest = Some(rest);
            if list_uses > 0 {
                // Construct the rest list once from individual arguments. If referenced at only a single site, instantiate it at the use site to avoid constructing unused lists on alternate code branches.
                let mut items = Vec::new();
                for arg in cx.rest.iter_mut().flatten() {
                    items.push(arg.take(target));
                }
                let mut list = target.quote(Value::NIL);
                for item in items.into_iter().rev() {
                    list = target.prim(Prim::Intrinsic(Intrinsic::Cons), vec![item, list]);
                }
                if self.linear || list_uses == 1 {
                    cx.list = Some(Arg::Expr(Some(list)));
                } else {
                    let var = target.fresh();
                    inner = Some((var, list));
                    cx.list = Some(Arg::Var(var));
                }
            }
        }
        let mut body = self.body.build(target, &mut cx, self.params);
        // Wrap the body in a `Let` binding for the rest list, located inside the scope of the rest argument temporaries.
        if let Some(list) = inner {
            body = target.bind(vec![list], body);
        }
        if binds.is_empty() { body } else { target.bind(binds, body) }
    }
}

/// Context maintained while instantiating an inlined template.
struct Instance<E> {
    params: Vec<Arg<E>>,
    rest: Option<Vec<Arg<E>>>,
    list: Option<Arg<E>>,
    locals: Vec<Var>,
}

impl<E> Arg<E> {
    /// Extracts the expression for this argument: duplicates constant arguments, but yields other expressions only once.
    fn take<'gc, T: Target<'gc, Expr = E>>(&mut self, target: &mut T) -> E {
        match self {
            Arg::Var(var) => target.local(*var),
            Arg::Expr(expr) => match expr {
                Some(constant) if target.is_constant(constant) => target.copy(constant),
                _ => expr.take().expect("a linear template uses each argument once"),
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
    /// Converts the node `id` of `tree` into a `Template` given the formal parameters `params` and the visible `locals`, returning `None` if the node cannot be part of a template or the template grows past the remaining quota in `left`.
    fn of<'id, 'gc>(tree: &L1<'id, 'gc>, id: Id<'id>, params: &[Var], locals: &mut Vec<Var>, left: &mut usize, lines: &Lines<'_, 'gc>) -> Option<Self> {
        *left = left.checked_sub(1)?;
        // Host functions are transitively propagated into the host table of any requiring module, so they may be safely inlined.
        let closed = |prim: Prim| !matches!(prim, Prim::Slot(..));
        let mut all = |ids: Span<'id, Id<'id>>, locals: &mut Vec<Var>| tree[ids].iter().map(|&id| Self::of(tree, id, params, locals, left, lines)).collect::<Option<Vec<_>>>();
        let line = lines.of(tree.site(id));
        Some(match tree[id] {
            Node::Ref(v) => match params.iter().position(|&p| p == v) {
                Some(i) => Self::Param(i as u32),
                None => Self::Local(locals.iter().position(|&l| l == v)? as u32),
            },
            // Module variable reference: retained for inlining only if verified to be immutable.
            Node::Intrinsic(Prim::Slot(SlotOp::Load | SlotOp::LoadChecked, slot), _) => Self::Slot(slot),
            Node::App(f, args) => {
                let mut parts = Vec::with_capacity(tree[args].len() + 1);
                parts.push(Self::of(tree, f, params, locals, left, lines)?);
                for &arg in &tree[args] {
                    parts.push(Self::of(tree, arg, params, locals, left, lines)?);
                }
                Self::Call(parts, line)
            }
            Node::Quote(v) => Self::Immediate(v.immediate()?),
            Node::If(a, b, c) => {
                let (a, b) = (Self::of(tree, a, params, locals, left, lines)?, Self::of(tree, b, params, locals, left, lines)?);
                Self::If(Box::new([a, b, Self::of(tree, c, params, locals, left, lines)?]))
            }
            Node::Intrinsic(prim, args) if closed(prim) => Self::Prim(prim, all(args, locals)?, line),
            Node::ApplyIntrinsic(prim, args) if closed(prim) => Self::Apply(prim, all(args, locals)?, line),
            Node::Let(binds, body) => {
                let mut values = Vec::with_capacity(tree[binds].len());
                for &(_, value) in &tree[binds] {
                    values.push(Self::of(tree, value, params, locals, left, lines)?);
                }
                let first = u32::try_from(locals.len()).ok()?;
                locals.extend(tree[binds].iter().map(|&(var, _)| var));
                Self::Let(first, values, Box::new(Self::of(tree, body, params, locals, left, lines)?))
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
            Self::Prim(_, args, _) | Self::Apply(_, args, _) | Self::Call(args, _) => {
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
            Self::Prim(_, args, _) | Self::Apply(_, args, _) | Self::Call(args, _) => args.iter().for_each(|a| a.slots(out)),
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
            Self::Prim(_, args, _) | Self::Call(args, _) => of(args),
            Self::Apply(prim, args, _) => match args.split_last() {
                Some((Self::Param(i), fixed)) if *i == rest => usize::from(!takes(*prim, fixed.len() + count)) + of(fixed),
                _ => of(args),
            },
        }
    }

    /// Builds the code this template stands for with `target`, substituting the arguments held in `cx`. `rest` is the index of the rest parameter.
    fn build<'gc, T: Target<'gc>>(&self, target: &mut T, cx: &mut Instance<T::Expr>, rest: u32) -> T::Expr {
        match self {
            Self::Param(i) if *i == rest && cx.rest.is_some() => cx.list.as_mut().expect("the rest's list is made when it's used").take(target),
            Self::Param(i) => cx.params[*i as usize].take(target),
            Self::Immediate(v) => target.quote(v.value()),
            Self::Slot(slot) => target.slot(*slot),
            Self::Local(k) => target.local(cx.locals[*k as usize]),
            Self::Let(first, values, body) => {
                let mut binds = Vec::with_capacity(values.len());
                for (value, k) in values.iter().zip(*first..) {
                    binds.push((cx.locals[k as usize], value.build(target, cx, rest)));
                }
                let body = body.build(target, cx, rest);
                target.bind(binds, body)
            }
            Self::If(parts) => {
                let [a, b, c] = &**parts;
                let (a, b, c) = (a.build(target, cx, rest), b.build(target, cx, rest), c.build(target, cx, rest));
                target.branch(a, b, c)
            }
            Self::Prim(prim, args, line) => {
                let args = args.iter().map(|a| a.build(target, cx, rest)).collect();
                target.line(*line);
                target.prim(*prim, args)
            }
            Self::Call(parts, line) => {
                let mut built: Vec<T::Expr> = parts.iter().map(|part| part.build(target, cx, rest)).collect();
                let args = built.split_off(1);
                let f = built.pop().expect("a call has a procedure");
                target.line(*line);
                target.call(f, args)
            }
            Self::Apply(prim, args, line) => match args.split_last() {
                Some((Self::Param(i), fixed)) if *i == rest && cx.rest.is_some() => {
                    let count = cx.rest.as_ref().map_or(0, |r| r.len());
                    let mut all: Vec<T::Expr> = fixed.iter().map(|a| a.build(target, cx, rest)).collect();
                    if takes(*prim, all.len() + count) {
                        for arg in cx.rest.iter_mut().flatten() {
                            all.push(arg.take(target));
                        }
                        target.line(*line);
                        target.prim(*prim, all)
                    } else {
                        all.push(cx.list.as_mut().expect("the rest's list is made when it's used").take(target));
                        target.line(*line);
                        target.apply(*prim, all)
                    }
                }
                _ => {
                    let args = args.iter().map(|a| a.build(target, cx, rest)).collect();
                    target.line(*line);
                    target.apply(*prim, args)
                }
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
    /// A required module could not be found.
    Resolve,
    /// A required module does not export a name that the requirement asks for.
    NotProvided,
    /// The supertype named by a struct declaration is not a struct type that can be extended.
    Supertype,
    /// A struct declaration whose type cannot be made, for example because it has too many fields.
    Struct,
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

/// Supplies the local variables and lambda IDs of a module's code, numbered apart across the whole module.
///
/// A variable made with [`Locals::named`] gives its name to a lambda that a `let` or `letrec` binds it to, so that error reports show the procedure by that name. A front end therefore makes each variable for the identifier it binds, and does not name procedures itself.
#[derive(Default)]
pub struct Locals<'gc> {
    /// The name each variable was made for, indexed by the variable's number, or `#f` for a variable without one.
    names: Vec<Value<'gc>>,
    lambdas: u32,
}

impl<'gc> Locals<'gc> {
    /// Makes a variable that stands for no name in the source.
    pub fn fresh(&mut self) -> Var {
        self.named(Value::FALSE)
    }

    /// Makes a variable for the identifier `name`, a symbol.
    pub fn named(&mut self, name: Value<'gc>) -> Var {
        let var = Var(u32::try_from(self.names.len()).expect("fewer than 2^32 variables"));
        self.names.push(name);
        var
    }

    /// Makes the ID of a lambda.
    pub fn lambda(&mut self) -> u32 {
        let id = self.lambdas;
        self.lambdas = self.lambdas.checked_add(1).expect("fewer than 2^32 lambdas");
        id
    }

    fn name(&self, var: Var) -> Option<Value<'gc>> {
        self.names.get(var.0 as usize).copied().filter(|&name| name != Value::FALSE)
    }
}

/// A top-level form of a module, as [`ModuleBuilder::compile`] takes it.
pub enum Form<'gc> {
    /// Defines the module variable in the slot as the value of the expression.
    Define(u32, Core<'gc>),
    /// An expression evaluated for its effects.
    Expr(Core<'gc>),
}

/// A top-level form of a module whose names the compiler resolves, as [`ModuleBuilder::declare`] and [`ModuleBuilder::compile_item`] take it.
///
/// A front end that keeps no table of the module's bindings lowers each form to an item: its expressions refer to every name that is not a local variable with [`Core::Global`]. The items of a whole module make a [`Description`], which builds the module. A module whose forms come from more than one front end is built from its items one at a time instead:
///
/// ```text
/// for each form:  builder.declare(mc, resolver, index, &item)
/// builder.provide_items(mc)
/// builder.start(mc)
/// for each form:  builder.compile_item(mc, index, item)
/// builder.finish(mc)
/// ```
pub enum Item<'gc> {
    /// Defines the module variable named by the symbol as the value of the expression. The span locates the name in the source.
    Define(Value<'gc>, SyntaxSpan<'gc>, Core<'gc>),
    /// Declares a struct type, and defines the variables of its type, constructors, predicate, accessors and mutators.
    Struct(structs::Form<'gc>),
    /// An expression evaluated for its effects.
    Expr(Core<'gc>),
    /// Imports what other modules export.
    Require(Vec<Require<'gc>>),
    /// Exports variables of the module. The names may be defined by any form of the module, before or after this one.
    Provide(Vec<Provide<'gc>>),
}

/// One module that an [`Item::Require`] imports from: the module and the filters on its exports, located by spans, and the span of the whole specification.
pub struct Require<'gc> {
    pub spec: RequireSpec<SyntaxSpan<'gc>>,
    pub span: SyntaxSpan<'gc>,
}

/// What an [`Item::Provide`] exports. Each span locates the specification in the source.
#[derive(Clone)]
pub enum Provide<'gc> {
    /// Exports the module variable named by the symbol `name` under the name `external`.
    Variable { name: Value<'gc>, external: String, span: SyntaxSpan<'gc> },
    /// Exports every variable that the module defines, under its own name.
    AllDefined(SyntaxSpan<'gc>),
    /// Exports everything that the struct declaration for `name` defines. Without `constructors`, the constructors are left out, and the struct's name is exported for `match` patterns only.
    Struct { name: Value<'gc>, constructors: bool, span: SyntaxSpan<'gc> },
}

/// A whole module whose names the compiler resolves: its name, the host functions its code can call, and its top-level forms in order.
///
/// A front end makes the supply of local variables, lowers every form of the module to an [`Item`] with it, and builds the description:
///
/// ```text
/// let mut locals = Locals::default();
/// let items = forms.map(|form| lower(&mut locals, form));
/// Description { name, hosts, locals, items }.build(mc, resolver)
/// ```
pub struct Description<'gc> {
    /// The module's name, a symbol.
    pub name: Value<'gc>,
    pub hosts: &'static [HostDef],
    /// The supply that the local variables and lambda IDs in `items` were made from.
    pub locals: Locals<'gc>,
    pub items: Vec<Item<'gc>>,
}

/// Why a [`Description`] does not build.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BuildError<'gc> {
    /// A declaration, a `require` or a `provide` is wrong, at the span of the name at fault.
    Declare(ModuleError, SyntaxSpan<'gc>),
    Compile(CompileError),
}

impl From<CompileError> for BuildError<'_> {
    fn from(e: CompileError) -> Self {
        Self::Compile(e)
    }
}

impl<'gc> From<(ModuleError, SyntaxSpan<'gc>)> for BuildError<'gc> {
    fn from((e, span): (ModuleError, SyntaxSpan<'gc>)) -> Self {
        Self::Declare(e, span)
    }
}

impl<'gc> Description<'gc> {
    /// Builds the module, which requires the modules that `resolver` finds: declares every item, compiles each one, and returns the module with the thunks that run its forms in order.
    pub fn build(self, mc: &Mutation<'gc>, resolver: &mut dyn Resolver<'gc>) -> Result<Loaded<'gc>, BuildError<'gc>> {
        let mut builder = ModuleBuilder::new(self.name, self.hosts);
        builder.locals = self.locals;
        let index = |i: usize| u32::try_from(i).map_err(|_| CompileError::OutOfMemory);
        for (i, item) in self.items.iter().enumerate() {
            builder.declare(mc, resolver, index(i)?, item)?;
        }
        builder.provide_items(mc)?;
        builder.start(mc).map_err(CompileError::from)?;
        let mut thunks = Vec::with_capacity(self.items.len());
        for (i, item) in self.items.into_iter().enumerate() {
            thunks.extend(builder.compile_item(mc, index(i)?, item)?);
        }
        let module = builder.finish(mc).map_err(CompileError::from)?;
        Ok(Loaded { module, thunks })
    }
}

/// The module that a top-level form is compiled in: the declarations of the module, the index of the form, and the variable that the form defines as a procedure, if it does. Lowering resolves calls of the module's struct procedures and keyword procedures from it.
pub(crate) struct Unit<'b, 'gc> {
    builder: &'b ModuleBuilder<'gc>,
    form: u32,
    defining: Option<u32>,
    /// The module variables that the form assigns by name, which the builder marks as assigned once the form is compiled.
    assigned: RefCell<Vec<u32>>,
}

impl<'gc> Unit<'_, 'gc> {
    /// Returns where the core of the keyword procedure in the variable `slot` is read from, and the procedure's shape, if the module defines `slot` as a keyword procedure.
    pub(crate) fn keyword_core(&self, slot: u32) -> Option<(Place, &CallShape<'gc>)> {
        let (core, shape) = self.builder.keyword_def(slot)?;
        Some((self.builder.place(core, self.form, self.defining), shape))
    }

    /// Returns the slot that holds the core of the keyword procedure that the form defines in `slot`, and the place the procedure built around the core reads it from.
    pub(crate) fn keyword_definition(&self, slot: u32) -> Option<(u32, Place, &CallShape<'gc>)> {
        let (core, shape) = self.builder.keyword_def(slot)?;
        Some((core, self.builder.place(core, self.form, self.defining), shape))
    }

    /// Returns the name that the local variable `var` was made for, if it was made for one.
    pub(crate) fn local_name(&self, var: Var) -> Option<Value<'gc>> {
        self.builder.locals.name(var)
    }

    /// Returns what `name` is bound to at the top level of the module.
    pub(crate) fn binding(&self, name: Value<'gc>) -> Option<Binding<'gc>> {
        self.builder.binding(name)
    }

    /// Returns the value of the variable `slot` if it is a constant by the time the form runs, as a struct's type object is after its declaration.
    pub(crate) fn constant(&self, slot: u32) -> Option<Value<'gc>> {
        self.builder.constant(slot, self.form)
    }

    /// Returns the place that the form reads or writes the variable `slot` through, checked unless the variable is defined by the time the form runs.
    pub(crate) fn place(&self, slot: u32) -> Place {
        self.builder.place(slot, self.form, self.defining)
    }

    /// Records that the form assigns the variable `slot`, or returns false if the variable cannot change.
    pub(crate) fn assign(&self, slot: u32) -> bool {
        let assignable = self.builder.assignable(slot);
        if assignable {
            self.assigned.borrow_mut().push(slot);
        }
        assignable
    }

    /// Returns the variable that the form defines as a procedure, whose lowered lambda becomes its inline template: the variable of the core, for a keyword procedure.
    pub(crate) fn defining(&self) -> Option<u32> {
        self.defining
    }

    /// Returns the expansion of a call of the struct procedure in the variable `slot` with `args` arguments, if `slot` holds one that takes them.
    pub(crate) fn struct_call(&self, slot: u32, args: usize) -> Option<Call<'gc>> {
        self.builder.struct_call(slot, self.form).filter(|call| call.takes(args))
    }
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
    /// The struct items declared, by the index of the top-level form each one is, until the form is compiled.
    declared: HashMap<u32, Declared>,
    /// What the declared provide items export, until [`ModuleBuilder::provide_items`] exports it.
    provides: Vec<Provide<'gc>>,
    locals: Locals<'gc>,
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
            declared: HashMap::default(),
            provides: Vec::new(),
            locals: Locals::default(),
            module: None,
        }
    }

    pub fn name(&self) -> Value<'gc> {
        self.name
    }

    pub fn hosts(&self) -> &'static [HostDef] {
        self.hosts
    }

    /// Returns the supply of local variables and lambda IDs for the module's code.
    pub fn locals(&mut self) -> &mut Locals<'gc> {
        &mut self.locals
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
    fn struct_call(&self, slot: u32, form: u32) -> Option<Call<'gc>> {
        let (inline, kind) = self.procedures.get(&slot)?;
        let defined = self.defined_by.get(slot as usize).is_some_and(|&by| by < form);
        Some(Call::new(inline.clone(), *kind, (!defined).then_some(Place::Slot { slot, checked: true })))
    }

    /// Returns the constant value of variable `slot` in form `form` if it has already been initialized (such as a struct type descriptor defined in an earlier form).
    pub fn constant(&self, slot: u32, form: u32) -> Option<Value<'gc>> {
        let (kind, _) = self.kinds.get(&slot)?;
        self.defined_by.get(slot as usize).is_some_and(|&by| by < form).then_some(*kind)
    }

    /// Marks variable `slot` as mutated. Returns an error if `slot` represents an immutable keyword procedure core or struct procedure.
    pub fn assign(&mut self, slot: u32) -> Result<(), ModuleError> {
        if !self.assignable(slot) {
            return Err(ModuleError::Immutable);
        }
        self.assigned.insert(slot);
        Ok(())
    }

    /// Returns whether the variable `slot` can be assigned: a keyword procedure and the bindings of a struct declaration cannot.
    fn assignable(&self, slot: u32) -> bool {
        !(self.cores.contains_key(&slot) || self.procedures.contains_key(&slot) || self.kinds.contains_key(&slot))
    }

    /// Declares what `item`, the top-level form of the module with index `form`, defines. A definition whose value is a lambda with keyword parameters is declared as a keyword procedure, so that calls anywhere in the module reach its core.
    ///
    /// An error comes with the span of the name at fault.
    pub fn declare(&mut self, mc: &Mutation<'gc>, resolver: &mut dyn Resolver<'gc>, form: u32, item: &Item<'gc>) -> Result<(), (ModuleError, SyntaxSpan<'gc>)> {
        match item {
            Item::Expr(_) => {}
            Item::Require(requires) => {
                for require in requires {
                    let imports = require.spec.imports(mc, resolver, self.name).map_err(|e| match e {
                        SpecError::Resolve(span) => (ModuleError::Resolve, span),
                        SpecError::NotProvided(span) => (ModuleError::NotProvided, span),
                    })?;
                    let symbols = Symbols::of_arena(mc).map_err(|e| (e.into(), require.span))?;
                    self.require(mc, symbols, imports).map_err(|e| (e, require.span))?;
                }
            }
            // Exports wait for `provide_items`, since a later form may define what this one provides.
            Item::Provide(provides) => self.provides.extend(provides.iter().cloned()),
            Item::Struct(declaration) => {
                let declared = Declared::of_form(mc, self, form, declaration)?;
                self.declared.insert(form, declared);
            }
            Item::Define(name, span, value) => {
                let slot = self.define(*name, form).map_err(|e| (e, *span))?;
                if let Core::OptionalLambda(lambda) = value
                    && lambda.params.iter().any(|formal| formal.keyword.is_some())
                {
                    let params: Vec<keyword::Param<'gc>> = lambda.params.iter().map(|formal| keyword::Param { keyword: formal.keyword, optional: formal.default.is_some() }).collect();
                    let core = self.define_private(*name, form).map_err(|e| (e, *span))?;
                    self.keyword_core(slot, core, CallShape::of(mc, &params, lambda.rest.is_some()));
                }
            }
        }
        Ok(())
    }

    /// Exports what the declared [`Item::Provide`]s name, once every form of the module is declared. An error comes with the span of the specification at fault.
    pub fn provide_items(&mut self, mc: &Mutation<'gc>) -> Result<(), (ModuleError, SyntaxSpan<'gc>)> {
        for provide in std::mem::take(&mut self.provides) {
            match provide {
                Provide::Variable { name, external, span } => self.provide(&external, name).map_err(|e| (e, span))?,
                Provide::AllDefined(span) => self.provide_all(mc).map_err(|e| (e, span))?,
                Provide::Struct { name, constructors, span } => {
                    let Some(Binding::Slot(constructor)) = self.binding(name) else { return Err((ModuleError::NotDefined, span)) };
                    self.provide_struct(mc, constructor, constructors).map_err(|e| (e, span))?;
                }
            }
        }
        Ok(())
    }

    /// Compiles `item`, the top-level form of the module with index `form`, which [`ModuleBuilder::declare`] declared, as [`ModuleBuilder::compile`] compiles a form. Returns `None` for an item that has no code to run.
    pub fn compile_item(&mut self, mc: &Mutation<'gc>, form: u32, item: Item<'gc>) -> Result<Option<Value<'gc>>, CompileError> {
        let top = match item {
            Item::Require(_) | Item::Provide(_) => return Ok(None),
            Item::Expr(core) => Form::Expr(core),
            Item::Struct(_) => {
                let declared = self.declared.remove(&form).expect("a struct item is declared before it is compiled");
                let (_, kind) = self.struct_def(declared.constructor()).expect("a declared struct has its definition");
                Form::Expr(declared.define(kind, &mut self.locals))
            }
            Item::Define(name, span, value) => match self.binding(name) {
                Some(Binding::Slot(slot)) => Form::Define(slot, value),
                _ => return Err(CompileError::Global { kind: GlobalError::Unbound, start: span.start(), end: span.end() }),
            },
        };
        self.compile(mc, form, top).map(Some)
    }

    /// Compiles `top`, the top-level form of the module with index `form`, into a thunk that runs it.
    ///
    /// A definition whose value is a lambda records the procedure's inline template for modules that require this one. If the variable was declared as a keyword procedure with [`ModuleBuilder::keyword_core`], the definition also sets the variable of the core.
    pub fn compile(&mut self, mc: &Mutation<'gc>, form: u32, top: Form<'gc>) -> Result<Value<'gc>, CompileError> {
        let (core, defining) = match top {
            Form::Expr(core) => (core, None),
            Form::Define(slot, value) => {
                // The lambda that defines a keyword procedure is lowered to the procedure's core, which has a variable of its own.
                let procedure = matches!(value, Core::Lambda(_) | Core::OptionalLambda(_));
                let defined = self.cores.get(&slot).map_or(slot, |&(core, _)| core);
                (Core::Set(Place::Slot { slot, checked: false }, Box::new(value)), procedure.then_some(defined))
            }
        };
        let unit = Unit { builder: self, form, defining, assigned: RefCell::default() };
        let (thunk, inline) = compile_in(mc, self.module, &core, Some(&unit))?;
        let assigned = unit.assigned.into_inner();
        self.assigned.extend(assigned);
        if let (Some(slot), Some(inline)) = (defining, inline) {
            self.inlines.insert(slot, inline);
        }
        Ok(thunk)
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
