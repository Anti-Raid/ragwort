//! Modules as the compiler sees them: a [`ModuleBuilder`] for the front ends, which lower a
//! module's files to forms it compiles into one [`Module`], and the [`Interface`] that tells code
//! requiring a module what each of its exports is.
//!
//! A module's variables are its slots. A reference to one the front end knows is defined where
//! it runs is unchecked: one defined by an earlier top-level form, or the variable itself inside
//! the lambda that's directly its definition. An export no code of its module assigns is
//! immutable, so a module requiring it quotes its value, and if its definition is a closed lambda,
//! inlines its calls. Code reads an export its module assigns with `module-ref`.

use std::collections::{HashMap, HashSet};

use ragwort_types::gc::{Gc, Immediate, Mutation, OutOfMemory, Value};
use ragwort_types::string::{Strings, chars};
use ragwort_types::symbol::{Symbol, Symbols};
use ragwort_vm::objects::{Module, ModuleFields};
use ragwort_vm::{HostDef, Intrinsic};

use crate::{CompileError, Core, Lambda, Place, Prim, Var, compile};

/// How many forms an inlined export's body can have.
const MAX_INLINE: usize = 16;

/// What a module exports, by the names other modules require them by.
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

/// One of a module's variables, as it exports it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Export {
    pub slot: u32,
    /// Whether its module assigns it, so it's read as it is when code reads it.
    pub mutable: bool,
    /// What a call of it inlines to, if its definition is a closed lambda.
    pub inline: Option<Inline>,
}

/// The interface of `module`, once it's built.
pub fn interface<'gc>(mc: &Mutation<'gc>, module: Gc<'gc, Module>) -> Option<&'gc Interface> {
    ragwort_vm::module::interface(mc, module)
}

/// Finds the modules code requires.
pub trait Resolver<'gc> {
    /// The module named `name`, which the module named `from` requires, once it's run: its
    /// immutable exports must be defined. A module that requires itself, or one that requires it,
    /// isn't one this can give.
    fn resolve(&mut self, mc: &Mutation<'gc>, name: &str, from: Value<'gc>) -> Option<Gc<'gc, Module>>;
}

/// A [`Resolver`] that has no modules, for a module that requires none.
pub struct NoModules;

impl<'gc> Resolver<'gc> for NoModules {
    fn resolve(&mut self, _: &Mutation<'gc>, _: &str, _: Value<'gc>) -> Option<Gc<'gc, Module>> {
        None
    }
}

/// A module a front end built, and a procedure of no arguments for each of its top-level forms
/// with code to run, to run in order. Once they have, a resolver can give it to code that
/// requires it.
#[derive(Clone, Debug)]
pub struct Loaded<'gc> {
    pub module: Gc<'gc, Module>,
    pub thunks: Vec<Value<'gc>>,
}

/// An export of a module that code requires.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Import<'gc> {
    pub module: Gc<'gc, Module>,
    pub export: &'gc Export,
}

/// A reference to an immutable export of a module that hasn't defined it, which the module's
/// resolver shouldn't have given.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Uninitialized;

impl<'gc> Import<'gc> {
    fn same(self, other: Self) -> bool {
        self.module == other.module && self.export.slot == other.export.slot
    }

    /// A reference to it: its value, or for a mutable export, a read of it.
    pub fn reference(self, mc: &Mutation<'gc>) -> Result<Core<'gc>, Uninitialized> {
        let slot = self.export.slot;
        if self.export.mutable {
            let k = Value::fixnum(i64::from(slot)).expect("slots are fixnums");
            let read = vec![Core::Quote(Value::object(mc, self.module)), Core::Quote(k)];
            return Ok(Core::Intrinsic(Prim::Intrinsic(Intrinsic::ModuleRef), read));
        }
        let items = self.module.items(mc);
        let value = (slot as usize).lt(&items.len()).then(|| items.get(slot as usize)).filter(|&v| v != Value::UNDEFINED);
        value.map(Core::Quote).ok_or(Uninitialized)
    }

    /// A call of it on `args`, inlined if it can be, with new locals from `fresh`.
    pub fn call(self, mc: &Mutation<'gc>, args: Vec<Core<'gc>>, fresh: &mut dyn FnMut() -> Var) -> Result<Core<'gc>, Uninitialized> {
        match &self.export.inline {
            Some(inline) if inline.takes(args.len()) => Ok(inline.call(args, fresh)),
            _ => Ok(Core::App(Box::new(self.reference(mc)?), args)),
        }
    }
}

/// The exports of the modules a module requires, by the names it gives them, which a require
/// spec's parts take from and rename.
#[derive(Clone, Debug, Default)]
pub struct Imports<'gc>(pub Vec<(String, Import<'gc>)>);

impl<'gc> Imports<'gc> {
    /// All of what `module` exports, by the names it exports them by.
    pub fn all(mc: &Mutation<'gc>, module: Gc<'gc, Module>) -> Option<Self> {
        let interface = interface(mc, module)?;
        let mut imports: Vec<_> = interface.iter().map(|(name, export)| (name.to_owned(), Import { module, export })).collect();
        imports.sort_by(|a, b| a.0.cmp(&b.0));
        Some(Self(imports))
    }

    /// Just `names`, or the first of them not among these.
    pub fn only(self, names: &[String]) -> Result<Self, String> {
        self.has(names)?;
        Ok(Self(self.0.into_iter().filter(|(n, _)| names.contains(n)).collect()))
    }

    /// All but `names`, or the first of them not among these.
    pub fn except(self, names: &[String]) -> Result<Self, String> {
        self.has(names)?;
        Ok(Self(self.0.into_iter().filter(|(n, _)| !names.contains(n)).collect()))
    }

    pub fn prefix(self, prefix: &str) -> Self {
        Self(self.0.into_iter().map(|(n, import)| (format!("{prefix}{n}"), import)).collect())
    }

    /// These, with each name in `renames` given its new name, or the first not among these.
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

/// A require spec, with where each part of it is written, `L`: what a front end reads one as.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RequireSpec<L> {
    /// All of what the module of this name exports.
    Module(String, L),
    Only(Box<Self>, Vec<(String, L)>),
    Except(Box<Self>, Vec<(String, L)>),
    Prefix(String, Box<Self>),
    /// Each old name, renamed to the new.
    Rename(Box<Self>, Vec<(String, String, L)>),
}

/// What's wrong with a require spec, and where.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpecError<L> {
    /// A module the resolver doesn't have, or one that no [`ModuleBuilder`] built.
    Resolve(L),
    /// A name the spec it's in doesn't import.
    NotProvided(L),
}

impl<L: Copy> RequireSpec<L> {
    /// What it imports, of the modules `resolver` finds for the module named `from`.
    pub fn imports<'gc>(&self, mc: &Mutation<'gc>, resolver: &mut dyn Resolver<'gc>, from: Value<'gc>) -> Result<Imports<'gc>, SpecError<L>> {
        let at = |names: &[(String, L)], missing: String| names.iter().find(|(n, _)| *n == missing).map(|&(_, at)| SpecError::NotProvided(at));
        Ok(match self {
            Self::Module(name, at) => {
                let module = resolver.resolve(mc, name, from).ok_or(SpecError::Resolve(*at))?;
                Imports::all(mc, module).ok_or(SpecError::Resolve(*at))?
            }
            Self::Only(inner, names) | Self::Except(inner, names) => {
                let imports = inner.imports(mc, resolver, from)?;
                let just: Vec<String> = names.iter().map(|(n, _)| n.clone()).collect();
                let kept = if matches!(self, Self::Only(..)) { imports.only(&just) } else { imports.except(&just) };
                kept.map_err(|missing| at(names, missing).expect("a missing name is one of the spec's"))?
            }
            Self::Prefix(prefix, inner) => inner.imports(mc, resolver, from)?.prefix(prefix),
            Self::Rename(inner, renames) => {
                let pairs: Vec<(String, String)> = renames.iter().map(|(old, new, _)| (old.clone(), new.clone())).collect();
                let olds: Vec<(String, L)> = renames.iter().map(|(old, _, at)| (old.clone(), *at)).collect();
                let imports = inner.imports(mc, resolver, from)?;
                imports.rename(&pairs).map_err(|missing| at(&olds, missing).expect("a missing name is one of the spec's"))?
            }
        })
    }
}

/// What a module export's call inlines to: the body of a lambda of no variables but its
/// parameters, whose constants are immediates and whose calls are of intrinsics, reads and
/// requests, which mean the same in any module.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Inline {
    params: u32,
    rest: bool,
    body: Template,
    /// Whether the body uses each parameter once, in order, before it calls anything, so its
    /// arguments go in its place, evaluated as they would be for the call.
    linear: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Template {
    Param(u32),
    Immediate(Immediate),
    If(Box<[Template; 3]>),
    Prim(Prim, Vec<Template>),
    Apply(Prim, Vec<Template>),
}

/// What a template does as it's evaluated: uses a parameter, or anything else that isn't just a
/// value.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Event {
    Param(u32),
    Other,
}

/// What an inlined call's parameter stands for: an argument that goes in its place, or the
/// local it's bound to.
enum Arg<'gc> {
    Core(Option<Core<'gc>>),
    Var(Var),
}

impl Arg<'_> {
    /// Whether `core` can go wherever it's used, as often: a constant. A local can't, as a call
    /// before a use could assign it.
    fn is_trivial(core: &Core<'_>) -> bool {
        matches!(core, Core::Quote(_))
    }
}

impl Inline {
    /// What `lambda`'s calls inline to, if it can be inlined.
    pub fn of(lambda: &Lambda<'_>) -> Option<Self> {
        let params: Vec<Var> = lambda.params.iter().copied().chain(lambda.rest).collect();
        let mut size = 0;
        let body = Template::of(&lambda.body, &params, &mut size)?;
        let mut events = Vec::new();
        body.events(&mut events);
        let uses: Vec<u32> = events.iter().filter_map(|e| if let Event::Param(i) = *e { Some(i) } else { None }).collect();
        let last_use = events.iter().rposition(|e| matches!(e, Event::Param(_)));
        let first_other = events.iter().position(|e| *e == Event::Other);
        let in_order = uses.iter().copied().eq(0..params.len() as u32);
        let linear = in_order && last_use.zip(first_other).is_none_or(|(used, other)| used < other);
        Some(Self { params: u32::try_from(lambda.params.len()).ok()?, rest: lambda.rest.is_some(), body, linear })
    }

    pub fn takes(&self, n: usize) -> bool {
        if self.rest { n >= self.params as usize } else { n == self.params as usize }
    }

    /// The body, with its parameters standing for `args`, which it takes, and the rest in a
    /// list. An `apply` of the rest list calls its primitive on them, if it takes that many.
    fn call<'gc>(&self, args: Vec<Core<'gc>>, fresh: &mut dyn FnMut() -> Var) -> Core<'gc> {
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
            let uses_list = self.body.uses_list(self.params, rest.len());
            let mut cx = Instance { params: args, rest: Some(&mut rest), list: None };
            if uses_list {
                // The rest's list, made once, of the rest, each bound once.
                let items: Vec<Core<'gc>> = cx.rest.as_deref_mut().into_iter().flatten().map(|a| a.take()).collect();
                let list = items.into_iter().rfold(Core::Quote(Value::NIL), |tail, item| Core::Intrinsic(Prim::Intrinsic(Intrinsic::Cons), vec![item, tail]));
                if self.linear {
                    cx.list = Some(Arg::Core(Some(list)));
                } else {
                    let var = fresh();
                    inner = Some((var, list));
                    cx.list = Some(Arg::Var(var));
                }
            }
            self.body.core(&mut cx, self.params)
        } else {
            self.body.core(&mut Instance { params: args, rest: None, list: None }, self.params)
        };
        // The list is of the rest's locals, so it's bound inside them.
        let body = match inner {
            Some(list) => Core::Let(vec![list], Box::new(body)),
            None => body,
        };
        if binds.is_empty() { body } else { Core::Let(binds, Box::new(body)) }
    }
}

/// What an inlined call's parameters stand for, as its template is made into code.
struct Instance<'r, 'gc> {
    params: Vec<Arg<'gc>>,
    rest: Option<&'r mut Vec<Arg<'gc>>>,
    list: Option<Arg<'gc>>,
}

impl<'gc> Arg<'gc> {
    /// What it stands for: a trivial argument as often as it's used, any other only once.
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

/// Whether `prim` takes `n` arguments.
fn takes(prim: Prim, n: usize) -> bool {
    match prim {
        Prim::Intrinsic(i) => i.arity().is_none_or(|a| usize::from(a) == n),
        Prim::Read(r) => usize::from(r.arity()) == n,
        Prim::Request(r) => r.takes(n),
        Prim::Host(h) => h.takes(n),
        Prim::Slot(op, _) => op.arity() == n,
    }
}

impl Template {
    fn of(core: &Core<'_>, params: &[Var], size: &mut usize) -> Option<Self> {
        *size += 1;
        if *size > MAX_INLINE {
            return None;
        }
        let closed = |prim: &Prim| !matches!(prim, Prim::Slot(..) | Prim::Host(_));
        let all = |args: &[Core<'_>], size: &mut usize| args.iter().map(|a| Self::of(a, params, size)).collect::<Option<Vec<_>>>();
        Some(match core {
            Core::Ref(Place::Local(v)) => Self::Param(params.iter().position(|p| p == v)? as u32),
            Core::Quote(v) => Self::Immediate(v.immediate()?),
            Core::If(a, b, c) => Self::If(Box::new([Self::of(a, params, size)?, Self::of(b, params, size)?, Self::of(c, params, size)?])),
            Core::Intrinsic(prim, args) if closed(prim) => Self::Prim(*prim, all(args, size)?),
            Core::ApplyIntrinsic(prim, args) if closed(prim) => Self::Apply(*prim, all(args, size)?),
            _ => return None,
        })
    }

    /// What it does, in the order it does it. An `if` counts as anything, after its test.
    fn events(&self, out: &mut Vec<Event>) {
        match self {
            Self::Param(i) => out.push(Event::Param(*i)),
            Self::Immediate(_) => {}
            Self::If(parts) => {
                parts[0].events(out);
                out.push(Event::Other);
                for branch in &parts[1..] {
                    let mut inner = Vec::new();
                    branch.events(&mut inner);
                    // A parameter used in a branch might not be, so the call isn't linear.
                    out.extend(inner.into_iter().map(|_| Event::Other));
                }
            }
            Self::Prim(_, args) | Self::Apply(_, args) => {
                for arg in args {
                    arg.events(out);
                }
                out.push(Event::Other);
            }
        }
    }

    /// Whether a call with `count` arguments past the parameters uses the rest parameter,
    /// `rest`, as a list, rather than as arguments an `apply` spreads.
    fn uses_list(&self, rest: u32, count: usize) -> bool {
        match self {
            Self::Param(i) => *i == rest,
            Self::Immediate(_) => false,
            Self::If(parts) => parts.iter().any(|p| p.uses_list(rest, count)),
            Self::Prim(_, args) => args.iter().any(|a| a.uses_list(rest, count)),
            Self::Apply(prim, args) => match args.split_last() {
                Some((Self::Param(i), fixed)) if *i == rest => {
                    !takes(*prim, fixed.len() + count) || fixed.iter().any(|a| a.uses_list(rest, count))
                }
                _ => args.iter().any(|a| a.uses_list(rest, count)),
            },
        }
    }

    /// This, with its parameters as `cx` has them, and `rest` the index of the rest parameter.
    fn core<'gc>(&self, cx: &mut Instance<'_, 'gc>, rest: u32) -> Core<'gc> {
        match self {
            Self::Param(i) if *i == rest && cx.rest.is_some() => cx.list.as_mut().expect("the rest's list is made when it's used").take(),
            Self::Param(i) => cx.params[*i as usize].take(),
            Self::Immediate(v) => Core::Quote(v.value()),
            Self::If(parts) => {
                let [a, b, c] = &**parts;
                Core::If(Box::new(a.core(cx, rest)), Box::new(b.core(cx, rest)), Box::new(c.core(cx, rest)))
            }
            Self::Prim(prim, args) => Core::Intrinsic(*prim, args.iter().map(|a| a.core(cx, rest)).collect()),
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

/// What went wrong building a module, which the front end says where.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ModuleError {
    /// A name the module defines twice, or provides twice.
    Duplicate,
    /// A name the module both defines and requires, or requires as two different things.
    Conflict,
    /// A provide of a name the module doesn't define.
    NotDefined,
    OutOfMemory,
}

impl From<OutOfMemory> for ModuleError {
    fn from(_: OutOfMemory) -> Self {
        Self::OutOfMemory
    }
}

/// What a name refers to at a module's top level.
#[derive(Clone, Copy, Debug)]
pub enum Binding<'gc> {
    /// The module's own variable.
    Slot(u32),
    Import(Import<'gc>),
}

/// A module as its front ends build it. First they declare its definitions, requires and
/// provides, then [`ModuleBuilder::start`] makes it, and they lower and [`ModuleBuilder::compile`]
/// each of its forms, in order, and [`ModuleBuilder::finish`] gives it its [`Interface`].
pub struct ModuleBuilder<'gc> {
    name: Value<'gc>,
    hosts: &'static [HostDef],
    /// Each variable's name, and the form that defines it.
    names: Vec<Value<'gc>>,
    defined_by: Vec<u32>,
    /// What the module's definitions and requires bind, by name, and what it requires
    /// implicitly, which they shadow.
    bindings: HashMap<u64, Binding<'gc>>,
    implicit: HashMap<u64, Import<'gc>>,
    exports: Vec<(Box<str>, u32)>,
    assigned: HashSet<u32>,
    inlines: HashMap<u32, Inline>,
    module: Option<Gc<'gc, Module>>,
}

impl<'gc> ModuleBuilder<'gc> {
    /// A module named `name`, whose native code calls `hosts`.
    pub fn new(name: Value<'gc>, hosts: &'static [HostDef]) -> Self {
        Self {
            name,
            hosts,
            names: Vec::new(),
            defined_by: Vec::new(),
            bindings: HashMap::new(),
            implicit: HashMap::new(),
            exports: Vec::new(),
            assigned: HashSet::new(),
            inlines: HashMap::new(),
            module: None,
        }
    }

    pub fn name(&self) -> Value<'gc> {
        self.name
    }

    pub fn hosts(&self) -> &'static [HostDef] {
        self.hosts
    }

    /// Defines the variable `name`, a symbol, in top-level form `form`, and gives its slot.
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

    /// Defines a variable that no name refers to at the top level, such as one a macro defines
    /// hygienically, named `name` for what it's shown as, and gives its slot.
    pub fn define_private(&mut self, name: Value<'gc>, form: u32) -> Result<u32, ModuleError> {
        let slot = u32::try_from(self.names.len()).map_err(|_| ModuleError::OutOfMemory)?;
        self.names.push(name);
        self.defined_by.push(form);
        Ok(slot)
    }

    /// Binds `name`, a symbol, to `import`.
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

    /// Binds what `imports` names, as a require of them does.
    pub fn require(&mut self, mc: &Mutation<'gc>, symbols: Symbols<'gc>, imports: Imports<'gc>) -> Result<(), ModuleError> {
        let strings = Strings::new(mc);
        for (name, import) in imports.0 {
            let symbol = symbols.intern_str(&strings, &name).map_err(|_| ModuleError::OutOfMemory)?;
            self.import(symbol.value(mc), import)?;
        }
        Ok(())
    }

    /// Requires all of what `module` exports implicitly, as a language does what it's built on:
    /// what the module defines or requires shadows it, as it does what's implicitly required
    /// before it.
    pub fn require_implicitly(&mut self, mc: &Mutation<'gc>, symbols: Symbols<'gc>, module: Gc<'gc, Module>) -> Result<(), ModuleError> {
        let strings = Strings::new(mc);
        for (name, import) in Imports::all(mc, module).unwrap_or_default().0 {
            let symbol = symbols.intern_str(&strings, &name).map_err(|_| ModuleError::OutOfMemory)?;
            self.implicit.insert(symbol.value(mc).to_bits(), import);
        }
        Ok(())
    }

    /// Exports the variable `name`, a symbol, as `external`.
    pub fn provide(&mut self, external: &str, name: Value<'gc>) -> Result<(), ModuleError> {
        let Some(&Binding::Slot(slot)) = self.bindings.get(&name.to_bits()) else { return Err(ModuleError::NotDefined) };
        if self.exports.iter().any(|(n, _)| **n == *external) {
            return Err(ModuleError::Duplicate);
        }
        self.exports.push((external.into(), slot));
        Ok(())
    }

    /// Exports each of the module's variables that a name refers to, by that name.
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

    /// What `name`, a symbol, refers to at the top level, if anything.
    pub fn binding(&self, name: Value<'gc>) -> Option<Binding<'gc>> {
        let k = name.to_bits();
        self.bindings.get(&k).copied().or_else(|| self.implicit.get(&k).copied().map(Binding::Import))
    }

    /// Makes the module, once all its definitions are known.
    pub fn start(&mut self, mc: &Mutation<'gc>) -> Result<Gc<'gc, Module>, OutOfMemory> {
        let module = ragwort_vm::module::new(mc, self.name, &self.names, self.hosts)?;
        self.module = Some(module);
        Ok(module)
    }

    /// The place of variable `slot` in code of top-level form `form`, inside the definition of
    /// `defining`'s lambda, if it is: unchecked if it's defined there.
    pub fn place(&self, slot: u32, form: u32, defining: Option<u32>) -> Place {
        let defined = self.defined_by.get(slot as usize).is_some_and(|&by| by < form) || defining == Some(slot);
        Place::Slot { slot, checked: !defined }
    }

    /// Notes that code assigns variable `slot`, so it isn't immutable.
    pub fn assign(&mut self, slot: u32) {
        self.assigned.insert(slot);
    }

    /// Notes that `value` defines variable `slot`, for what its calls can inline to.
    pub fn defined(&mut self, slot: u32, value: &Core<'gc>) {
        if let Core::Lambda(lambda) = value
            && let Some(inline) = Inline::of(lambda)
        {
            self.inlines.insert(slot, inline);
        }
    }

    /// Compiles `core`, a top-level form of the module, once it's started.
    pub fn compile(&self, mc: &Mutation<'gc>, core: &Core<'gc>) -> Result<Value<'gc>, CompileError> {
        compile(mc, self.module, core)
    }

    /// The module, with what it exports, once each of its forms is compiled.
    pub fn finish(mut self, mc: &Mutation<'gc>) -> Result<Gc<'gc, Module>, OutOfMemory> {
        let module = match self.module {
            Some(module) => module,
            None => self.start(mc)?,
        };
        let exports = self.exports.iter().map(|(name, slot)| {
            let mutable = self.assigned.contains(slot);
            let inline = if mutable { None } else { self.inlines.get(slot).cloned() };
            (name.clone(), Export { slot: *slot, mutable, inline })
        });
        ragwort_vm::module::set_interface(mc, module, Interface { exports: exports.collect() })?;
        Ok(module)
    }
}
