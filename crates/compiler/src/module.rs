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
            let index = Value::fixnum(i64::from(slot)).expect("slots are fixnums");
            let read = vec![Core::Quote(Value::object(mc, self.module)), Core::Quote(index)];
            return Ok(Core::Intrinsic(Prim::Intrinsic(Intrinsic::ModuleRef), read, None));
        }
        self.variable(mc, slot).map(Core::Quote).ok_or(Unusable::Uninitialized)
    }

    /// Returns an [`Import`] pointing to the underlying core procedure if this import represents a keyword procedure.
    pub fn keyword_core(self) -> Option<Self> {
        Some(Self { module: self.module, export: self.export.core.as_deref()?, name: self.name })
    }

    /// Checks that the import can be used as a value. A front end calls this before it emits [`Core::Import`], so that it can report the error at the right source position.
    pub fn usable(self, mc: &Mutation<'gc>) -> Result<(), Unusable> {
        self.reference(mc).map(|_| ())
    }

    /// Checks that a call of the import with `args` arguments can be compiled. The call is valid if it can be inlined, or if the import is usable as a value.
    pub fn callable(self, mc: &Mutation<'gc>, args: usize) -> Result<(), Unusable> {
        if self.inlined(mc, args).is_some() { Ok(()) } else { self.usable(mc) }
    }

    /// Returns the inline template for a call of the import with `args` arguments, or `None` if the call cannot be inlined.
    ///
    /// A call is inlined only if all of these hold:
    /// - The export has a template, and the template accepts `args` arguments.
    /// - The procedure's own variable is defined.
    /// - Every module variable that the template reads is defined.
    ///
    /// A variable can be undefined if its module stopped early. This happens in the REPL when an input raises an error partway through.
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
        (slot as usize).lt(&items.len()).then(|| items.get(slot as usize)).filter(|&value| value != Value::UNDEFINED)
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
        imports.sort_by(|left, right| left.0.cmp(&right.0));
        Some(Self(imports))
    }

    /// Filters imports to retain only those matching `names`, returning an error identifying the first unrecognized name if any are missing.
    pub fn only(self, names: &[String]) -> Result<Self, String> {
        self.has(names)?;
        Ok(Self(self.0.into_iter().filter(|(name, _)| names.contains(name)).collect()))
    }

    /// Filters imports to exclude `names`, returning an error identifying the first unrecognized name if any specified name was not present.
    pub fn except(self, names: &[String]) -> Result<Self, String> {
        self.has(names)?;
        Ok(Self(self.0.into_iter().filter(|(name, _)| !names.contains(name)).collect()))
    }

    pub fn prefix(self, prefix: &str) -> Self {
        Self(self.0.into_iter().map(|(name, import)| (format!("{prefix}{name}"), import)).collect())
    }

    /// Renames imported bindings according to `renames`, returning an error identifying the first missing original name if any cannot be found.
    pub fn rename(self, renames: &[(String, String)]) -> Result<Self, String> {
        let olds: Vec<String> = renames.iter().map(|(old, _)| old.clone()).collect();
        self.has(&olds)?;
        let renamed = self.0.into_iter().map(|(name, import)| match renames.iter().find(|(old, _)| *old == name) {
            Some((_, new)) => (new.clone(), import),
            None => (name, import),
        });
        Ok(Self(renamed.collect()))
    }

    fn has(&self, names: &[String]) -> Result<(), String> {
        match names.iter().find(|name| !self.0.iter().any(|(imported, _)| imported == *name)) {
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
        let at = |names: &[(String, L)], missing: String| names.iter().find(|(name, _)| *name == missing).map(|&(_, at)| SpecError::NotProvided(at));
        let module = resolver.resolve(mc, &self.module, from).ok_or(SpecError::Resolve(self.at))?;
        let mut imports = Imports::all(mc, module).ok_or(SpecError::Resolve(self.at))?;
        for filter in &self.filters {
            imports = match filter {
                Filter::Only(names) | Filter::Except(names) => {
                    let just: Vec<String> = names.iter().map(|(name, _)| name.clone()).collect();
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
    /// The file that defines the procedure and the line where its definition starts, if known. Error reports show both for calls inlined from this template.
    origin: Option<(Box<str>, u32)>,
    /// The slots of the module variables that the body reads, without duplicates. A call is inlined only while all of them are defined.
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
    /// Applies a primitive to operands. The last field is the source line of the operation, or 0 if the line is unknown. `Apply` and `Call` have the same field. The line refers to the file named by [`Inline::origin`], and error reports use it.
    Prim(Prim, Vec<Template>, u32),
    Apply(Prim, Vec<Template>, u32),
    /// Invokes the procedure produced by evaluating the first expression with the remaining expressions as arguments.
    Call(Vec<Template>, u32),
}

/// Looks up source lines while a template is being built from a procedure.
struct Lines<'x, 'gc> {
    mc: &'x Mutation<'gc>,
    sites: &'x Sites<'gc>,
    /// The source file that defines the procedure. Lines stored in the template refer to this file.
    source: Option<Value<'gc>>,
}

impl Lines<'_, '_> {
    /// Returns the line of the code at `site`, or 0 if the line is unknown. The line is unknown for code that has no position, and for code from another source: code written by a macro, or code expanded from another procedure's template.
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

/// Builds the expansion of an inline template. The compiler's first pass implements this trait to build nodes of its tree.
pub(crate) trait Target<'gc> {
    type Expr;

    fn fresh(&mut self) -> Var;
    /// Sets the source line of the next operation. A `line` of 0 means that the line is unknown.
    fn line(&mut self, line: u32);
    fn quote(&mut self, value: Value<'gc>) -> Self::Expr;
    fn local(&mut self, var: Var) -> Self::Expr;
    /// Builds a read of module variable `slot`. The variable belongs to the module that defines the template.
    fn slot(&mut self, slot: u32) -> Self::Expr;
    fn bind(&mut self, binds: Vec<(Var, Self::Expr)>, body: Self::Expr) -> Self::Expr;
    fn branch(&mut self, test: Self::Expr, then: Self::Expr, other: Self::Expr) -> Self::Expr;
    fn prim(&mut self, prim: Prim, args: Vec<Self::Expr>) -> Self::Expr;
    fn apply(&mut self, prim: Prim, args: Vec<Self::Expr>) -> Self::Expr;
    fn call(&mut self, procedure: Self::Expr, args: Vec<Self::Expr>) -> Self::Expr;
    /// Returns whether `expr` is a constant. An expansion may copy a constant, but it uses any other argument only once.
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
    /// Builds an [`Inline`] template from the lowered lambda `fun`. Returns `None` if the body is too large, or if it contains a form that a template cannot hold. `at` is the position of the lambda's definition.
    ///
    /// The template is built after lowering. By then calls of imports are expanded, calls of the module's struct and keyword procedures are resolved, and each default value is a `let` around the body.
    pub(crate) fn of_function<'id, 'gc>(mc: &Mutation<'gc>, tree: &L1<'id, 'gc>, sites: &Sites<'gc>, fun: Fun<'id>, at: Option<Position<'gc>>) -> Option<Self> {
        let fun = tree[fun];
        let params: Vec<Var> = tree[fun.params].iter().copied().chain(fun.rest).collect();
        let (mut left, mut locals) = (MAX_INLINE, Vec::new());
        let lines = Lines { mc, sites, source: at.map(|at| at.source) };
        let body = Template::of(tree, fun.body, &params, &mut locals, &mut left, &lines)?;
        let (params, locals) = (u32::try_from(tree[fun.params].len()).ok()?, u32::try_from(locals.len()).ok()?);
        Some(Self::new(params, fun.optional, fun.rest.is_some(), locals, body).defined_at(mc, at))
    }

    /// Records the file and line of `at`, which is the position of the procedure's definition.
    fn defined_at<'gc>(mut self, mc: &Mutation<'gc>, at: Option<Position<'gc>>) -> Self {
        self.origin = at.and_then(|at| {
            let source = SyntaxSource::of(at.source)?;
            let name = String::from_utf8_lossy(source.name(mc)?.bytes(mc)).into_owned();
            Some((name.into_boxed_str(), source.location(mc, at.offset)?.line))
        });
        self
    }

    /// Returns the file that defines the procedure and the line where its definition starts, if known.
    pub(crate) fn origin(&self) -> Option<(&str, u32)> {
        self.origin.as_ref().map(|(file, line)| (&**file, *line))
    }

    /// Returns whether expanding the template may need fresh variables. It needs them for its own locals, and for arguments that it uses more than once or out of order.
    pub(crate) fn needs_vars(&self) -> bool {
        !self.linear || self.locals > 0
    }

    /// Returns whether an inlined call of this template gets no traceback entry of its own. An error in it is reported as part of the caller. Two kinds of template are wrappers:
    ///
    /// - A single built-in operation on parameters and constants. The prelude's thin wrappers around intrinsics have this shape.
    /// - A procedure whose outermost operation raises its argument, such as `error`. The error belongs to the caller.
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
            Operand::Param(param) => Template::Param(param),
            Operand::Slot(slot) => Template::Slot(slot),
            Operand::Index(index) => Template::Immediate(Value::fixnum(i64::from(index)).and_then(Value::immediate).expect("an index is a fixnum")),
        };
        Self::new(params, 0, false, 0, Template::Prim(Prim::Intrinsic(intrinsic), operands.iter().map(operand).collect(), 0))
    }

    fn new(params: u32, optional: u32, rest: bool, locals: u32, body: Template) -> Self {
        let mut events = Vec::new();
        body.events(&mut events);
        let uses: Vec<u32> = events.iter().filter_map(|event| if let Event::Param(param) = *event { Some(param) } else { None }).collect();
        let last_use = events.iter().rposition(|event| matches!(event, Event::Param(_)));
        let first_other = events.iter().position(|event| *event == Event::Other);
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

    pub fn takes(&self, count: usize) -> bool {
        count >= (self.params - self.optional) as usize && (self.rest || count <= self.params as usize)
    }

    /// Determines whether a call with `count` arguments can be inlined: checks arity compatibility and verifies that any rest-argument list does not exceed `MAX_REST`.
    pub fn inlines(&self, count: usize) -> bool {
        let rest = count.saturating_sub(self.params as usize);
        self.takes(count) && (!self.rest || rest <= MAX_REST || !self.body.uses_list(self.params, rest))
    }

    /// Expands the template for a call with arguments `args`, and builds the result with `target`. Extra arguments go to the rest parameter: they are spread into the operation that takes them, or gathered into a list.
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

/// Checks whether the primitive `prim` accepts an argument count of `count`.
fn takes(prim: Prim, count: usize) -> bool {
    match prim {
        Prim::Intrinsic(intrinsic) => intrinsic.arity().is_none_or(|arity| usize::from(arity) == count),
        Prim::Request(request) => request.takes(count),
        Prim::Host(host) => host.takes(count),
        Prim::Slot(op, _) => op.arity() == count,
    }
}

impl Template {
    /// Converts node `id` of `tree` into a `Template`. `params` are the lambda's parameters, and `locals` are the variables bound so far. Returns `None` if the node cannot be part of a template, or if the template would exceed the remaining size budget `left`.
    fn of<'id, 'gc>(tree: &L1<'id, 'gc>, id: Id<'id>, params: &[Var], locals: &mut Vec<Var>, left: &mut usize, lines: &Lines<'_, 'gc>) -> Option<Self> {
        *left = left.checked_sub(1)?;
        // Host functions are transitively propagated into the host table of any requiring module, so they may be safely inlined.
        let closed = |prim: Prim| !matches!(prim, Prim::Slot(..));
        let mut all = |ids: Span<'id, Id<'id>>, locals: &mut Vec<Var>| tree[ids].iter().map(|&id| Self::of(tree, id, params, locals, left, lines)).collect::<Option<Vec<_>>>();
        let line = lines.of(tree.site(id));
        Some(match tree[id] {
            Node::Ref(var) => match params.iter().position(|&param| param == var) {
                Some(index) => Self::Param(index as u32),
                None => Self::Local(locals.iter().position(|&local| local == var)? as u32),
            },
            // Module variable reference: retained for inlining only if verified to be immutable.
            Node::Intrinsic(Prim::Slot(SlotOp::Load | SlotOp::LoadChecked, slot), _) => Self::Slot(slot),
            Node::App(function, args) => {
                let mut parts = Vec::with_capacity(tree[args].len() + 1);
                parts.push(Self::of(tree, function, params, locals, left, lines)?);
                for &arg in &tree[args] {
                    parts.push(Self::of(tree, arg, params, locals, left, lines)?);
                }
                Self::Call(parts, line)
            }
            Node::Quote(value) => Self::Immediate(value.immediate()?),
            Node::If(test, consequent, other) => {
                let (test, consequent) = (Self::of(tree, test, params, locals, left, lines)?, Self::of(tree, consequent, params, locals, left, lines)?);
                Self::If(Box::new([test, consequent, Self::of(tree, other, params, locals, left, lines)?]))
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
            Self::Param(param) => out.push(Event::Param(*param)),
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
            Self::Let(_, values, body) => values.iter().chain([&**body]).for_each(|part| part.slots(out)),
            Self::If(parts) => parts.iter().for_each(|part| part.slots(out)),
            Self::Prim(_, args, _) | Self::Apply(_, args, _) | Self::Call(args, _) => args.iter().for_each(|arg| arg.slots(out)),
        }
    }

    /// Determines whether a call with `count` excess arguments uses the rest parameter as a materialized list rather than spreading it into an `apply` primitive.
    fn uses_list(&self, rest: u32, count: usize) -> bool {
        self.list_uses(rest, count) > 0
    }

    /// Counts the number of occurrences where the rest parameter `rest` is used as a materialized list when called with `count` excess arguments.
    fn list_uses(&self, rest: u32, count: usize) -> usize {
        let of = |parts: &[Template]| parts.iter().map(|part| part.list_uses(rest, count)).sum::<usize>();
        match self {
            Self::Param(param) => usize::from(*param == rest),
            Self::Immediate(_) | Self::Local(_) | Self::Slot(_) => 0,
            Self::Let(_, values, body) => of(values) + body.list_uses(rest, count),
            Self::If(parts) => of(&parts[..]),
            Self::Prim(_, args, _) | Self::Call(args, _) => of(args),
            Self::Apply(prim, args, _) => match args.split_last() {
                Some((Self::Param(param), fixed)) if *param == rest => usize::from(!takes(*prim, fixed.len() + count)) + of(fixed),
                _ => of(args),
            },
        }
    }

    /// Builds the code this template stands for with `target`, substituting the arguments held in `cx`. `rest` is the index of the rest parameter.
    fn build<'gc, T: Target<'gc>>(&self, target: &mut T, cx: &mut Instance<T::Expr>, rest: u32) -> T::Expr {
        match self {
            Self::Param(param) if *param == rest && cx.rest.is_some() => cx.list.as_mut().expect("the rest's list is made when it's used").take(target),
            Self::Param(param) => cx.params[*param as usize].take(target),
            Self::Immediate(value) => target.quote(value.value()),
            Self::Slot(slot) => target.slot(*slot),
            Self::Local(local) => target.local(cx.locals[*local as usize]),
            Self::Let(first, values, body) => {
                let mut binds = Vec::with_capacity(values.len());
                for (value, local) in values.iter().zip(*first..) {
                    binds.push((cx.locals[local as usize], value.build(target, cx, rest)));
                }
                let body = body.build(target, cx, rest);
                target.bind(binds, body)
            }
            Self::If(parts) => {
                let [test, consequent, other] = &**parts;
                let (test, consequent, other) = (test.build(target, cx, rest), consequent.build(target, cx, rest), other.build(target, cx, rest));
                target.branch(test, consequent, other)
            }
            Self::Prim(prim, args, line) => {
                let args = args.iter().map(|arg| arg.build(target, cx, rest)).collect();
                target.line(*line);
                target.prim(*prim, args)
            }
            Self::Call(parts, line) => {
                let mut built: Vec<T::Expr> = parts.iter().map(|part| part.build(target, cx, rest)).collect();
                let args = built.split_off(1);
                let procedure = built.pop().expect("a call has a procedure");
                target.line(*line);
                target.call(procedure, args)
            }
            Self::Apply(prim, args, line) => match args.split_last() {
                Some((Self::Param(param), fixed)) if *param == rest && cx.rest.is_some() => {
                    let count = cx.rest.as_ref().map_or(0, |extras| extras.len());
                    let mut all: Vec<T::Expr> = fixed.iter().map(|arg| arg.build(target, cx, rest)).collect();
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
                    let args = args.iter().map(|arg| arg.build(target, cx, rest)).collect();
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

/// Allocates local variables and lambda IDs for a module. The numbers are unique across the whole module.
///
/// A front end calls [`Locals::named`] for each identifier that it binds. When a `let` or `letrec` binds that variable to a lambda, the lambda takes the variable's name, and error reports show it. The front end does not name procedures itself.
#[derive(Default)]
pub struct Locals<'gc> {
    /// The name of each variable, indexed by variable number. The entry is `#f` for a variable without a name.
    names: Vec<Value<'gc>>,
    lambdas: u32,
}

impl<'gc> Locals<'gc> {
    /// Allocates a variable that has no name in the source.
    pub fn fresh(&mut self) -> Var {
        self.named(Value::FALSE)
    }

    /// Allocates a variable for the identifier `name`, which is a symbol.
    pub fn named(&mut self, name: Value<'gc>) -> Var {
        let var = Var(u32::try_from(self.names.len()).expect("fewer than 2^32 variables"));
        self.names.push(name);
        var
    }

    /// Allocates a lambda ID.
    pub fn lambda(&mut self) -> u32 {
        let id = self.lambdas;
        self.lambdas = self.lambdas.checked_add(1).expect("fewer than 2^32 lambdas");
        id
    }

    fn name(&self, var: Var) -> Option<Value<'gc>> {
        self.names.get(var.0 as usize).copied().filter(|&name| name != Value::FALSE)
    }
}

/// A top-level form whose names are already resolved to slots. [`ModuleBuilder::compile`] compiles it.
pub enum Form<'gc> {
    /// Defines the module variable in the given slot. The expression computes its value.
    Define(u32, Core<'gc>),
    /// An expression evaluated for its effects.
    Expr(Core<'gc>),
}

/// A top-level form that refers to module-level bindings by name. The compiler resolves the names.
///
/// A front end lowers each top-level form to one item. Inside an item, every name that is not a local variable is a [`Core::Global`], so the front end needs no table of the module's bindings.
///
/// There are two ways to build a module from items:
/// - Put all the items in a [`Description`] and call [`Description::build`].
/// - Pass the items to a [`ModuleBuilder`] one at a time, as shown below. A module that mixes forms from several front ends is built this way.
///
/// ```text
/// for each form:  builder.declare(mc, resolver, index, &item)
/// builder.provide_items(mc)
/// builder.start(mc)
/// for each form:  builder.compile_item(mc, index, item)
/// builder.finish(mc)
/// ```
pub enum Item<'gc> {
    /// Defines a module variable. The fields are the variable's name (a symbol), the span of the name in the source, and the expression that computes the value.
    Define(Value<'gc>, SyntaxSpan<'gc>, Core<'gc>),
    /// Declares a struct type. This defines module variables for the type, its constructors, its predicate, and its accessors and mutators.
    Struct(structs::Form<'gc>),
    /// An expression evaluated for its effects.
    Expr(Core<'gc>),
    /// Imports bindings from other modules.
    Require(Vec<Require<'gc>>),
    /// Exports module variables. A name may be defined by any form of the module, including a later one.
    Provide(Vec<Provide<'gc>>),
}

/// One entry of an [`Item::Require`]. `spec` names the module and the filters on its exports. `span` covers the whole entry in the source.
pub struct Require<'gc> {
    pub spec: RequireSpec<SyntaxSpan<'gc>>,
    pub span: SyntaxSpan<'gc>,
}

/// One entry of an [`Item::Provide`]. Each `span` covers the entry in the source.
#[derive(Clone)]
pub enum Provide<'gc> {
    /// Exports the module variable named by the symbol `name` under the name `external`.
    Variable { name: Value<'gc>, external: String, span: SyntaxSpan<'gc> },
    /// Exports every variable that the module defines, under its own name.
    AllDefined(SyntaxSpan<'gc>),
    /// Exports every binding of the struct declared as `name`. If `constructors` is false, the constructors are not exported, and the struct's name can be used only in `match` patterns.
    Struct { name: Value<'gc>, constructors: bool, span: SyntaxSpan<'gc> },
}

/// A whole module, described by its top-level items. The compiler resolves all names.
///
/// To build a module, a front end creates a [`Locals`], lowers every top-level form to an [`Item`] with it, and calls [`Description::build`]:
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
    /// The allocator that produced the local variables and lambda IDs used in `items`.
    pub locals: Locals<'gc>,
    pub items: Vec<Item<'gc>>,
}

/// An error from [`Description::build`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BuildError<'gc> {
    /// A definition, struct declaration, `require` or `provide` is invalid. The span covers the name at fault.
    Declare(ModuleError, SyntaxSpan<'gc>),
    Compile(CompileError),
}

impl From<CompileError> for BuildError<'_> {
    fn from(error: CompileError) -> Self {
        Self::Compile(error)
    }
}

impl<'gc> From<(ModuleError, SyntaxSpan<'gc>)> for BuildError<'gc> {
    fn from((error, span): (ModuleError, SyntaxSpan<'gc>)) -> Self {
        Self::Declare(error, span)
    }
}

impl<'gc> Description<'gc> {
    /// Builds the module. `resolver` finds the modules that it requires. Returns the module and the thunks of its forms, in order. Running the thunks in order initializes the module.
    pub fn build(self, mc: &Mutation<'gc>, resolver: &mut dyn Resolver<'gc>) -> Result<Loaded<'gc>, BuildError<'gc>> {
        let mut builder = ModuleBuilder::new(self.name, self.hosts);
        builder.locals = self.locals;
        let index = |position: usize| u32::try_from(position).map_err(|_| CompileError::OutOfMemory);
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

/// The context for compiling one top-level form of a module. Lowering uses it to resolve names, calls of the module's struct procedures, and calls of its keyword procedures.
pub(crate) struct Unit<'b, 'gc> {
    builder: &'b ModuleBuilder<'gc>,
    form: u32,
    defining: Option<u32>,
    /// Slots that the form assigns with [`Core::SetGlobal`]. The builder marks them as assigned after the form is compiled.
    assigned: RefCell<Vec<u32>>,
}

impl<'gc> Unit<'_, 'gc> {
    /// Returns the place of the core procedure and the call shape, if `slot` holds a keyword procedure of this module. A call that matches the shape can call the core directly.
    pub(crate) fn keyword_core(&self, slot: u32) -> Option<(Place, &CallShape<'gc>)> {
        let (core, shape) = self.builder.keyword_def(slot)?;
        Some((self.builder.place(core, self.form, self.defining), shape))
    }

    /// Returns what the definition of keyword procedure `slot` needs: the slot of the core procedure, the place to read the core from, and the call shape. Returns `None` if `slot` was not declared as a keyword procedure.
    pub(crate) fn keyword_definition(&self, slot: u32) -> Option<(u32, Place, &CallShape<'gc>)> {
        let (core, shape) = self.builder.keyword_def(slot)?;
        Some((core, self.builder.place(core, self.form, self.defining), shape))
    }

    /// Returns the name of local variable `var`, if it has one.
    pub(crate) fn local_name(&self, var: Var) -> Option<Value<'gc>> {
        self.builder.locals.name(var)
    }

    /// Returns the module-level binding of `name`: a slot of this module, or an import.
    pub(crate) fn binding(&self, name: Value<'gc>) -> Option<Binding<'gc>> {
        self.builder.binding(name)
    }

    /// Returns the value of variable `slot` if it is a known constant when the form runs. A struct's type object is a constant after its declaration.
    pub(crate) fn constant(&self, slot: u32) -> Option<Value<'gc>> {
        self.builder.constant(slot, self.form)
    }

    /// Returns the place for reading or writing variable `slot` in this form. The access is checked unless the variable is certainly defined when the form runs.
    pub(crate) fn place(&self, slot: u32) -> Place {
        self.builder.place(slot, self.form, self.defining)
    }

    /// Records that the form assigns variable `slot`. Returns `false` if the variable is immutable.
    pub(crate) fn assign(&self, slot: u32) -> bool {
        let assignable = self.builder.assignable(slot);
        if assignable {
            self.assigned.borrow_mut().push(slot);
        }
        assignable
    }

    /// Returns the slot of the procedure that this form defines, if it defines one. For a keyword procedure, this is the slot of its core. The lambda lowered for this slot becomes the procedure's inline template.
    pub(crate) fn defining(&self) -> Option<u32> {
        self.defining
    }

    /// Returns the inline expansion for a call of struct procedure `slot` with `args` arguments. Returns `None` if `slot` is not a struct procedure, or if it does not accept `args` arguments.
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
    /// Declared struct items, keyed by the index of their top-level form. An entry is removed when its form is compiled.
    declared: HashMap<u32, Declared>,
    /// Pending exports from declared [`Item::Provide`]s. [`ModuleBuilder::provide_items`] applies them.
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

    /// Returns the allocator of local variables and lambda IDs for this module.
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
        if self.exports.iter().any(|(name, _)| **name == *external) {
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
        let public = self.names.iter().enumerate().filter(|&(slot, name)| matches!(self.bindings.get(&name.to_bits()), Some(&Binding::Slot(bound)) if bound as usize == slot));
        for name in public.map(|(_, &name)| name).collect::<Vec<_>>() {
            let symbol = Symbol::of(name).expect("variables are named by symbols");
            let external: String = chars(&strings, symbol.name(mc)).collect();
            self.provide(&external, name)?;
        }
        Ok(())
    }

    /// Resolves symbol `name` in the module's top-level scope, checking explicit definitions/imports first, then implicit imports.
    pub fn binding(&self, name: Value<'gc>) -> Option<Binding<'gc>> {
        let key = name.to_bits();
        self.bindings.get(&key).copied().or_else(|| self.implicit.get(&key).copied().map(Binding::Import))
    }

    /// Allocates and initializes the runtime [`Module`] once all definitions are declared. Combines the module's own host functions
    /// with all host functions transitively required by imported modules, ensuring host calls in inlined functions resolve correctly.
    pub fn start(&mut self, mc: &Mutation<'gc>) -> Result<Gc<'gc, Module>, OutOfMemory> {
        let mut hosts: Vec<&'static HostDef> = self.hosts.iter().collect();
        let imported = self.bindings.values().filter_map(|binding| if let Binding::Import(import) = binding { Some(import) } else { None }).chain(self.implicit.values());
        let mut seen = Vec::new();
        for import in imported {
            if seen.contains(&import.module) {
                continue;
            }
            seen.push(import.module);
            for &def in import.module.hosts(mc).map_or(&[][..], |defs| &defs[..]) {
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

    /// Returns whether variable `slot` can be assigned. Keyword procedures and the bindings of a struct declaration are immutable.
    fn assignable(&self, slot: u32) -> bool {
        !(self.cores.contains_key(&slot) || self.procedures.contains_key(&slot) || self.kinds.contains_key(&slot))
    }

    /// Declares the bindings of `item`, which is top-level form number `form`. Every item must be declared before the module starts.
    ///
    /// - A definition declares its variable. If the value is a lambda with keyword parameters, the variable is declared as a keyword procedure, so that calls anywhere in the module can call its core directly.
    /// - A struct item declares the type and all its bindings.
    /// - A require imports the bindings that `resolver` finds.
    /// - A provide is recorded, and [`ModuleBuilder::provide_items`] applies it later.
    ///
    /// An error is returned with the span of the name at fault.
    pub fn declare(&mut self, mc: &Mutation<'gc>, resolver: &mut dyn Resolver<'gc>, form: u32, item: &Item<'gc>) -> Result<(), (ModuleError, SyntaxSpan<'gc>)> {
        match item {
            Item::Expr(_) => {}
            Item::Require(requires) => {
                for require in requires {
                    let imports = require.spec.imports(mc, resolver, self.name).map_err(|error| match error {
                        SpecError::Resolve(span) => (ModuleError::Resolve, span),
                        SpecError::NotProvided(span) => (ModuleError::NotProvided, span),
                    })?;
                    let symbols = Symbols::of_arena(mc).map_err(|error| (error.into(), require.span))?;
                    self.require(mc, symbols, imports).map_err(|error| (error, require.span))?;
                }
            }
            // Exports are applied later, because a later form may define the provided name.
            Item::Provide(provides) => self.provides.extend(provides.iter().cloned()),
            Item::Struct(declaration) => {
                let declared = Declared::of_form(mc, self, form, declaration)?;
                self.declared.insert(form, declared);
            }
            Item::Define(name, span, value) => {
                let slot = self.define(*name, form).map_err(|error| (error, *span))?;
                if let Core::OptionalLambda(lambda) = value
                    && lambda.params.iter().any(|formal| formal.keyword.is_some())
                {
                    let params: Vec<keyword::Param<'gc>> = lambda.params.iter().map(|formal| keyword::Param { keyword: formal.keyword, optional: formal.default.is_some() }).collect();
                    let core = self.define_private(*name, form).map_err(|error| (error, *span))?;
                    self.keyword_core(slot, core, CallShape::of(mc, &params, lambda.rest.is_some()));
                }
            }
        }
        Ok(())
    }

    /// Applies the exports of all declared [`Item::Provide`]s. Call this after every form is declared. An error is returned with the span of the entry at fault.
    pub fn provide_items(&mut self, mc: &Mutation<'gc>) -> Result<(), (ModuleError, SyntaxSpan<'gc>)> {
        for provide in std::mem::take(&mut self.provides) {
            match provide {
                Provide::Variable { name, external, span } => self.provide(&external, name).map_err(|error| (error, span))?,
                Provide::AllDefined(span) => self.provide_all(mc).map_err(|error| (error, span))?,
                Provide::Struct { name, constructors, span } => {
                    let Some(Binding::Slot(constructor)) = self.binding(name) else { return Err((ModuleError::NotDefined, span)) };
                    self.provide_struct(mc, constructor, constructors).map_err(|error| (error, span))?;
                }
            }
        }
        Ok(())
    }

    /// Compiles `item`, which is top-level form number `form` and was declared with [`ModuleBuilder::declare`]. Returns the thunk that runs the form, or `None` for an item with no code (a require or a provide).
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

    /// Compiles `top`, which is top-level form number `form`, and returns the thunk that runs it.
    ///
    /// For a definition whose value is a lambda, this also records the procedure's inline template, which modules that require this one use. If the variable was declared with [`ModuleBuilder::keyword_core`], the compiled code sets the core's variable too.
    pub fn compile(&mut self, mc: &Mutation<'gc>, form: u32, top: Form<'gc>) -> Result<Value<'gc>, CompileError> {
        let (core, defining) = match top {
            Form::Expr(core) => (core, None),
            Form::Define(slot, value) => {
                // For a keyword procedure, the lambda is lowered to the core procedure, and the core has its own slot.
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
