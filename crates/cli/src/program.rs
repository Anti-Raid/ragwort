//! Loads and runs the files and modules that the command line names.
//!
//! A [`Program`] owns an arena that holds the libraries of Scheme and the `repl` module. It loads a module
//! from its folder the first time that code requires the module, and runs the module at once. The code that
//! requires the module is compiled against the module's definitions, so the module must run first.
//!
//! # Loading what a module requires
//!
//! A module is built in one step of the arena, and every module that it requires must have run by then.
//! So a build stops at a `require` of a module that is not loaded. That module is then built
//! and run, and the first module is built again from the start. This repeats once for each
//! module that the first module is the first to require.
//!
//! The code of every module, including the libraries of Scheme, runs one step at a time between builds. So the
//! collector keeps up with the module's allocation, as it does for the entry point.
//!
//! # Images
//!
//! [`Program::save_image`] saves the symbol table, the `scheme` module and every loaded module with its name. The libraries of Scheme are among the loaded modules.
//! [`Program::from_image`] starts a program from that state. See [`ragwort_modules_core::image`]. The
//! modules of an image have already run, so they are not loaded from their folders again.
//!
//! # The REPL
//!
//! Each input is a module of its own. It provides everything that it defines, and it implicitly requires
//! `repl` and every earlier input. So:
//!
//! - A definition is visible to the inputs after it. A later definition of the same name replaces
//!   it for the inputs after that.
//! - A module that an input requires by its name alone, as in `(require lib/text)`, is visible to
//!   the inputs after it too. A module required through `only-in` or another filter is visible only to that input.
//! - An input cannot `set!` a variable that an earlier input defined, because no module can assign a variable that it imports.
//! - A macro is visible only in the input that defines it.

#[cfg(test)]
#[path = "tests/program.rs"]
mod tests;

use std::hash::{BuildHasher, Hasher, RandomState};
use std::path::{Path, PathBuf};

use ragwort_compiler::module::{Loaded, Resolver};
use ragwort_modules_core::image::{self, ImageError};
use ragwort_modules_core::{Error, File, Language, Located, Source, library_of, load_located, scheme};
use ragwort_printer_scheme::{Mode, render, to_string};
use ragwort_reader_scheme::{ErrorKind, Reader};
use ragwort_types::gc::image::{LoadError, SaveError};
use ragwort_types::gc::{Arena, Gc, Mutation, REGION, Root, Value, ValueRoot};
use ragwort_types::pair::Pairs;
use ragwort_types::string::{Strings, chars, from_str};
use ragwort_types::symbol::{Symbol, Symbols};
use ragwort_types::syntax::{Syntax, SyntaxKind, SyntaxSession};
use ragwort_vm::objects::Module;
use ragwort_vm::report::Report;
use ragwort_vm::{Fault, HostDef, MIN_SEGMENT, Machine, Outcome};

use crate::args::{ModuleDir, language};
use crate::{hosts, listing};

/// The default memory limit of a program, in bytes: the capacity of the object region.
pub const HEAP: usize = REGION;
/// The maximum length, in bytes, of the text shown for a result or a raised value.
const SHOWN: usize = 1 << 16;
const OUT_OF_MEMORY: &str = "out of memory";

/// A file of a module: its path, its text and its language.
struct SourceFile {
    path: PathBuf,
    text: String,
    language: Language,
}

/// The modules that the command line names, and their loading state.
struct Modules {
    dirs: Vec<ModuleDir>,
    /// The modules that are loaded and have run, each with its name.
    loaded: Vec<(String, Root<Module>)>,
    /// The name of a module that the current build required and that is not loaded yet. The build stopped at that `require`.
    wanted: Option<String>,
    /// The error messages collected so far, in order.
    errors: Vec<String>,
    /// The bytecode listing of each module loaded since [`Program::list`] was called, or `None` if listings are not kept.
    listing: Option<String>,
}

/// A module that is built but has not run yet. `thunks` holds the code of its forms, which run in order.
struct Built {
    thunks: Vec<ValueRoot>,
    module: Root<Module>,
}

/// The reason a module was not built.
enum Missed {
    /// The module requires the module named by the first field, which is not loaded. The second field is the error message that locates the `require`.
    Needs(String, String),
    /// The build failed. The error messages are in `Modules::errors`.
    Failed,
}

/// A module that is being loaded: its name and its files. `asked` is the error message that locates the `require` in the module that asked for it, if a module did.
struct Pending {
    name: String,
    files: Vec<SourceFile>,
    asked: Option<String>,
}


pub struct Program {
    arena: Arena,
    symbols: ValueRoot,
    scheme_module: Root<Module>,
    modules: Modules,
    /// The modules that a REPL input requires implicitly: `repl`, then each earlier input, and
    /// each module that an earlier input required by name. `required` holds the names of those modules.
    inputs: Vec<Root<Module>>,
    required: Vec<String>,
}

/// Returns the text of `node` if `node` is an identifier or a string literal, and `None` otherwise.
fn name_of<'gc>(mc: &Mutation<'gc>, node: Syntax<'gc>) -> Option<String> {
    let (strings, datum) = (Strings::new(mc), node.datum(mc));
    let name = match node.kind(mc)? {
        SyntaxKind::Identifier => Symbol::of(datum)?.name(mc),
        SyntaxKind::Literal => strings.string(datum)?,
        _ => return None,
    };
    Some(chars(&strings, name).collect())
}

/// The words that start a filter in a require spec. A list that starts with any other word is a group of specs.
const FILTERS: [&str; 4] = ["only-in", "except-in", "prefix-in", "rename-in"];

/// Returns the names of the modules that the forms of `text` require by name alone, in order. `(require lib/text "other")`
/// requires two modules in that way, and so does `(require [lib/text "other"])`. A module inside a filter is not one of them.
fn required_by<'gc>(mc: &Mutation<'gc>, symbols: Symbols<'gc>, text: &str) -> Vec<String> {
    let mut names = Vec::new();
    let Ok(session) = SyntaxSession::new(mc, text) else { return names };
    let Ok(reader) = Reader::new(mc, symbols, &session) else { return names };
    for node in reader.flatten() {
        if node.kind(mc) != Some(SyntaxKind::List) {
            continue;
        }
        let mut items = Pairs::new(mc).elements(node.datum(mc)).filter_map(Syntax::of);
        if items.next().and_then(|head| name_of(mc, head)).as_deref() != Some("require") {
            continue;
        }
        // The specs still to look at, with the next one last.
        let mut specs: Vec<Syntax<'gc>> = items.collect();
        specs.reverse();
        while let Some(spec) = specs.pop() {
            if let Some(name) = name_of(mc, spec) {
                names.push(name);
                continue;
            }
            if spec.kind(mc) != Some(SyntaxKind::List) {
                continue;
            }
            let members: Vec<Syntax<'gc>> = Pairs::new(mc).elements(spec.datum(mc)).filter_map(Syntax::of).collect();
            let filter = members.first().is_some_and(|&head| head.kind(mc) == Some(SyntaxKind::Identifier) && name_of(mc, head).is_some_and(|word| FILTERS.contains(&word.as_str())));
            if !filter {
                specs.extend(members.into_iter().rev());
            }
        }
    }
    names
}

/// Returns whether a `require` or `%require` form of `files` names `library` or the `scheme` module anywhere, also inside a filter or a group.
fn requires<'gc>(mc: &Mutation<'gc>, symbols: Symbols<'gc>, files: &[SourceFile], library: &str) -> bool {
    for file in files {
        let Ok(session) = SyntaxSession::new(mc, &file.text) else { continue };
        let Ok(reader) = Reader::new(mc, symbols, &session) else { continue };
        for node in reader.flatten() {
            if node.kind(mc) != Some(SyntaxKind::List) {
                continue;
            }
            let mut items = Pairs::new(mc).elements(node.datum(mc)).filter_map(Syntax::of);
            if !items.next().and_then(|head| name_of(mc, head)).is_some_and(|head| head == "require" || head == "%require") {
                continue;
            }
            let mut parts: Vec<Syntax<'gc>> = items.collect();
            while let Some(part) = parts.pop() {
                if name_of(mc, part).is_some_and(|name| name == library || name == "scheme") {
                    return true;
                }
                if part.kind(mc) == Some(SyntaxKind::List) {
                    parts.extend(Pairs::new(mc).elements(part.datum(mc)).filter_map(Syntax::of));
                }
            }
        }
    }
    false
}

/// Returns a note for the error `failed` of a module with the files `files`, if the error is an unbound name that a library of Scheme
/// provides and the module requires neither that library nor `scheme`. The note names the library.
fn missing_library<'gc>(mc: &Mutation<'gc>, symbols: Symbols<'gc>, files: &[SourceFile], failed: &Located) -> Option<String> {
    let (start, end) = failed.error.unbound()?;
    let file = match failed.file {
        Some(index) => files.get(index),
        None => files.first().filter(|_| files.len() == 1),
    }?;
    let name = file.text.get(start as usize..end as usize)?;
    let library = library_of(name)?;
    if requires(mc, symbols, files, library) {
        return None;
    }
    Some(format!("`{name}` is in `{library}`, which is not required"))
}

/// Returns the one-based line and column of byte `offset` in `text`.
fn place(text: &str, offset: u32) -> (usize, usize) {
    let before = &text.as_bytes()[..(offset as usize).min(text.len())];
    let line = before.iter().filter(|&&byte| byte == b'\n').count() + 1;
    let column = before.iter().rev().take_while(|&&byte| byte != b'\n').count() + 1;
    (line, column)
}

/// Formats the error `failed` of the module `name`, whose files are `files`, as `file:line:column: message`.
fn describe(name: &str, files: &[SourceFile], failed: &Located) -> String {
    let (what, start) = match failed.error {
        Error::Read(error) => (error.kind.to_string(), Some(error.start)),
        Error::Expand(error) => (error.kind.to_string(), Some(error.start)),
        Error::Lower(error) => (error.kind.to_string(), Some(error.start)),
        Error::Compile(error) => (error.to_string(), None),
    };
    let file = match failed.file {
        Some(index) => files.get(index),
        None => files.first().filter(|_| files.len() == 1),
    };
    match (file, start) {
        (Some(file), Some(start)) => {
            let (line, column) = place(&file.text, start);
            format!("{}:{line}:{column}: {what}", file.path.display())
        }
        (Some(file), None) => format!("{}: {what}", file.path.display()),
        (None, _) => format!("module {name}: {what}"),
    }
}

fn shown<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> String {
    to_string(mc, value, Mode::Write, SHOWN).unwrap_or_else(|_| "...".to_string())
}

fn fault(fault: Fault) -> String {
    format!("error: {}", Fault::KINDS[fault.kind()])
}

/// The outcome of running a machine.
enum Ran<'gc> {
    More,
    Done(Value<'gc>),
    Failed(String),
}

fn ran<'gc>(mc: &Mutation<'gc>, outcome: Result<Outcome<'gc>, Fault>) -> Ran<'gc> {
    match outcome {
        Ok(Outcome::Paused) => Ran::More,
        Ok(Outcome::Done(value)) => Ran::Done(value),
        Ok(Outcome::Raised(raised)) => Ran::Failed(render(mc, &Report::of(mc, raised), SHOWN)),
        Ok(Outcome::Yielded(_)) => Ran::Failed("error: a yield with nothing to resume it".to_string()),
        Ok(Outcome::Deferred(_)) => Ran::Failed("error: a host call that's never answered".to_string()),
        Err(error) => Ran::Failed(fault(error)),
    }
}

/// Reads the source files in `folder`, in the order of their paths.
fn read_folder(folder: &Path) -> Result<Vec<SourceFile>, String> {
    let mut paths = Vec::new();
    for entry in std::fs::read_dir(folder).map_err(|error| format!("{}: {error}", folder.display()))? {
        let path = entry.map_err(|error| format!("{}: {error}", folder.display()))?.path();
        if path.is_file() && language(&path).is_some() {
            paths.push(path);
        }
    }
    paths.sort();
    if paths.is_empty() {
        return Err(format!("{}: no .rg or .rgn files", folder.display()));
    }
    paths.iter().map(|path| read_file(path)).collect()
}

fn read_file(path: &Path) -> Result<SourceFile, String> {
    let language = language(path).ok_or_else(|| format!("{}: not a .rg or .rgn file", path.display()))?;
    let text = std::fs::read_to_string(path).map_err(|error| format!("{}: {error}", path.display()))?;
    Ok(SourceFile { path: path.to_path_buf(), text, language })
}

/// Builds the module `name` from `files`. An error is added to `modules.errors`. The exception is a `require`
/// of a module that is not loaded yet, which is returned as `Missed::Needs`.
fn load_module<'gc>(
    mc: &Mutation<'gc>,
    symbols: Symbols<'gc>,
    modules: &mut Modules,
    name: &str,
    hosts: &'static [HostDef],
    files: &[SourceFile],
    implicit: &[Gc<'gc, Module>],
) -> Result<Loaded<'gc>, Missed> {
    let mut sessions = Vec::with_capacity(files.len());
    for file in files {
        let Ok(session) = SyntaxSession::named(mc, &file.path.to_string_lossy(), &file.text) else {
            modules.errors.push(OUT_OF_MEMORY.to_string());
            return Err(Missed::Failed);
        };
        sessions.push(session);
    }
    let mut parts = Vec::with_capacity(files.len());
    for (file, session) in files.iter().zip(&sessions) {
        parts.push(File { language: file.language, session });
    }
    let source = Source { name, hosts, files: &parts, implicit, internals: false };
    modules.wanted = None;
    match load_located(mc, symbols, &source, &mut Finder { modules }) {
        Ok(loaded) => {
            if let Some(listing) = &mut modules.listing {
                listing::list(mc, name, &loaded.thunks, listing);
            }
            Ok(loaded)
        }
        Err(failed) => {
            let mut message = describe(name, files, &failed);
            // A procedure of Scheme is unbound in a module that does not require its library. A module with implicit modules, such
            // as a REPL input, has every library already.
            if implicit.is_empty()
                && let Some(note) = missing_library(mc, symbols, files, &failed)
            {
                message = format!("{message}: {note}");
            }
            match modules.wanted.take() {
                Some(module) => Err(Missed::Needs(module, message)),
                None => {
                    modules.errors.push(message);
                    Err(Missed::Failed)
                }
            }
        }
    }
}

/// Roots the thunks and the module of `loaded`, so that they stay alive across arena steps until the module has run. Returns `None` if allocation fails.
fn rooted<'gc>(mc: &Mutation<'gc>, loaded: &Loaded<'gc>) -> Option<Built> {
    let mut thunks = Vec::with_capacity(loaded.thunks.len());
    for &thunk in &loaded.thunks {
        thunks.push(ValueRoot::new(mc, thunk).ok()?);
    }
    Some(Built { thunks, module: Root::new(mc, loaded.module).ok()? })
}

/// A `Resolver` that finds required modules among the loaded modules. If a required module is not loaded but the command line gives it a folder,
/// its name is recorded in `Modules::wanted`. The build is then tried again once that module is loaded.
struct Finder<'m> {
    modules: &'m mut Modules,
}

impl<'gc> Resolver<'gc> for Finder<'_> {
    fn resolve(&mut self, mc: &Mutation<'gc>, name: &str, _: Value<'gc>) -> Option<Gc<'gc, Module>> {
        if let Some((_, module)) = self.modules.loaded.iter().find(|(loaded, _)| loaded == name) {
            return module.get(mc).ok();
        }
        if self.modules.dirs.iter().any(|dir| dir.name == name) {
            self.modules.wanted = Some(name.to_string());
        }
        None
    }
}

/// Creates the symbol table and builds the libraries of Scheme, in the first step of a new arena. Adds each library to `modules.loaded` under its
/// name, so code can require it. Returns the `scheme` module, which passes them all on, with the thunks of the libraries.
fn start<'gc>(mc: &Mutation<'gc>, modules: &mut Modules) -> Result<(ValueRoot, Built), String> {
    let symbols = Symbols::with_seed(mc, RandomState::new().build_hasher().finish()).map_err(|_| OUT_OF_MEMORY.to_string())?;
    let libraries = scheme(mc, symbols).map_err(|error| format!("the libraries of Scheme: {error:?}"))?;
    for &(name, module) in &libraries.modules {
        if modules.dirs.iter().any(|dir| dir.name == name) {
            return Err(format!("module `{name}` is already a library of Scheme"));
        }
        modules.loaded.push((name.to_string(), Root::new(mc, module).map_err(|_| OUT_OF_MEMORY.to_string())?));
    }
    let loaded = Loaded { module: libraries.all(), thunks: libraries.thunks };
    let built = rooted(mc, &loaded).ok_or_else(|| OUT_OF_MEMORY.to_string())?;
    Ok((ValueRoot::new(mc, symbols.value(mc)).map_err(|_| OUT_OF_MEMORY.to_string())?, built))
}

/// Loads the image `bytes`, in the first step of a new arena. An image holds the symbol table, the `scheme` module, and each
/// module with its name, the libraries of Scheme among them. Returns the symbol table and the `scheme` module, and adds the modules to `modules.loaded`. Fails if the command line also gives a folder for a module in the image.
fn restore<'gc>(mc: &Mutation<'gc>, bytes: &[u8], modules: &mut Modules) -> Result<(ValueRoot, Root<Module>), String> {
    fn damaged() -> String {
        "image does not contain valid module data".to_string()
    }
    let roots = image::load(mc, bytes, hosts::HOSTS.iter()).map_err(|error| match error {
        ImageError::Host(name) => format!("image requires unknown host function `{name}`"),
        ImageError::SameHost(path) => format!("duplicate host function `{path}`"),
        ImageError::Load(LoadError::Stamp) => "image was created by a different build of ragwort".to_string(),
        ImageError::Load(LoadError::OutOfMemory) => OUT_OF_MEMORY.to_string(),
        ImageError::Load(_) => "invalid or corrupted ragwort image".to_string(),
    })?;
    let [symbols, scheme_module, named @ ..] = roots.as_slice() else { return Err(damaged()) };
    let scheme_module = scheme_module.downcast::<Module>(mc).ok_or_else(damaged)?;
    let strings = Strings::new(mc);
    for pair in named.chunks(2) {
        let &[name, module] = pair else { return Err(damaged()) };
        let name: String = chars(&strings, strings.string(name).ok_or_else(damaged)?).collect();
        if modules.dirs.iter().any(|dir| dir.name == name) {
            return Err(format!("module `{name}` is already present in the image"));
        }
        let module = module.downcast::<Module>(mc).ok_or_else(damaged)?;
        modules.loaded.push((name, Root::new(mc, module).map_err(|_| OUT_OF_MEMORY.to_string())?));
    }
    Ok((ValueRoot::new(mc, *symbols).map_err(|_| OUT_OF_MEMORY.to_string())?, Root::new(mc, scheme_module).map_err(|_| OUT_OF_MEMORY.to_string())?))
}

/// Calls `thunk` and runs it to completion, one arena step at a time, so the collector keeps up. The written form of its
/// value is passed to `out`, unless the value is void.
fn run(arena: &mut Arena, thunk: &ValueRoot, mut out: Option<&mut dyn FnMut(&str)>) -> Result<(), String> {
    let mut machine = arena.mutate(|mc| {
        let thunk = thunk.get(mc).map_err(|_| "value belongs to another arena".to_string())?;
        Machine::new(mc, MIN_SEGMENT, thunk, &[]).map_err(fault)
    })?;
    loop {
        let step = arena.step(|mc| match ran(mc, machine.run(mc)) {
            Ran::More => None,
            Ran::Done(value) => {
                let text = if value != Value::VOID {
                    Some(shown(mc, value))
                } else {
                    None
                };
                Some(Ok(text))
            }
            Ran::Failed(message) => Some(Err(message)),
        });
        match step {
            Err(_) => return Err(format!("error: {OUT_OF_MEMORY}")),
            Ok(None) => {}
            Ok(Some(Err(message))) => return Err(message),
            Ok(Some(Ok(text))) => {
                if let (Some(out), Some(text)) = (&mut out, text) {
                    out(&text);
                }
                return Ok(());
            }
        }
    }
}

impl Program {
    /// Creates a program with a memory limit of `heap` bytes. Its code can require the modules of `dirs`, and none of them is loaded yet.
    pub fn new(heap: usize, dirs: Vec<ModuleDir>) -> Result<Self, Vec<String>> {
        let mut arena = Arena::new(heap, 0);
        let mut modules = Modules { dirs, loaded: Vec::new(), wanted: None, errors: Vec::new(), listing: None };
        let (symbols, built) = arena.mutate(|mc| start(mc, &mut modules)).map_err(|message| vec![message])?;
        for thunk in &built.thunks {
            run(&mut arena, thunk, None).map_err(|message| vec![format!("the libraries of Scheme: {message}")])?;
        }
        let mut program = Self { arena, symbols, scheme_module: built.module, modules, inputs: Vec::new(), required: Vec::new() };
        let files = [SourceFile { path: "repl.rgn".into(), text: hosts::SOURCE.to_string(), language: Language::Native }];
        let Some(built) = program.build(hosts::NAME, &hosts::HOSTS, &files, false) else { return Err(program.take_errors()) };
        program.inputs.push(built.module.clone());
        program.finish(hosts::NAME, built).map_err(|message| vec![message])?;
        Ok(program)
    }

    fn take_errors(&mut self) -> Vec<String> {
        std::mem::take(&mut self.modules.errors)
    }

    /// Makes one attempt to build the module `name` from `files`. The attempt stops at a `require` of a module
    /// that is not loaded. If `input` is true, the module is a REPL input. It implicitly requires the `scheme` module, then the modules in `inputs`.
    /// Any other module starts with no procedure and requires what it uses.
    fn attempt(&mut self, name: &str, hosts: &'static [HostDef], files: &[SourceFile], input: bool) -> Result<Built, Missed> {
        let Self { arena, symbols, scheme_module, modules, inputs, .. } = self;
        let implicit: &[Root<Module>] = if input {
            inputs
        } else {
            &[]
        };
        let built = arena.mutate(|mc| {
            let symbols = symbols.get(mc).ok().and_then(Symbols::of);
            let (Some(symbols), Ok(scheme_module)) = (symbols, scheme_module.get(mc)) else { return Ok(None) };
            let mut required = Vec::with_capacity(implicit.len() + 1);
            if input {
                required.push(scheme_module);
            }
            for module in implicit {
                let Ok(module) = module.get(mc) else { return Ok(None) };
                required.push(module);
            }
            let loaded = load_module(mc, symbols, modules, name, hosts, files, &required)?;
            Ok(rooted(mc, &loaded))
        })?;
        built.ok_or_else(|| {
            modules.errors.push(OUT_OF_MEMORY.to_string());
            Missed::Failed
        })
    }

    /// Builds the module `name` from `files`. Each module that it requires and that is not
    /// loaded yet is loaded first.
    fn build(&mut self, name: &str, hosts: &'static [HostDef], files: &[SourceFile], input: bool) -> Option<Built> {
        loop {
            match self.attempt(name, hosts, files, input) {
                Ok(built) => return Some(built),
                Err(Missed::Failed) => return None,
                Err(Missed::Needs(module, asked)) => self.ensure(module, Some(asked))?,
            }
        }
    }

    /// Runs the built module `name` and records it as loaded, so that later code can require it.
    fn finish(&mut self, name: &str, built: Built) -> Result<(), String> {
        for thunk in &built.thunks {
            run(&mut self.arena, thunk, None).map_err(|message| format!("module {name}: {message}"))?;
        }
        self.modules.loaded.push((name.to_string(), built.module));
        Ok(())
    }

    /// Loads the module `name` from its folder and runs it. Every module that it requires, directly or indirectly,
    /// and that is not loaded yet is loaded and run first. `asked` is the error message that locates the `require` in the
    /// requiring code. If the module cannot be loaded, that message is reported as an error in the requiring code.
    fn ensure(&mut self, name: String, asked: Option<String>) -> Option<()> {
        let mut pending: Vec<Pending> = Vec::new();
        let mut next = Some((name, asked));
        // The loop yields the `asked` message of the module that could not be loaded, if that module was not added to `pending`.
        let asked = loop {
            if let Some((name, asked)) = next.take() {
                if pending.iter().any(|module| module.name == name) {
                    let through: Vec<&str> = pending.iter().map(|module| &*module.name).collect();
                    self.modules.errors.push(format!("module {name}: circular dependency via {}", through.join(", ")));
                    break asked;
                }
                let folder = self.modules.dirs.iter().find(|dir| dir.name == name).map(|dir| dir.folder.clone());
                match folder.as_deref().map(read_folder) {
                    Some(Ok(files)) => pending.push(Pending { name, files, asked }),
                    Some(Err(message)) => {
                        self.modules.errors.push(message);
                        break asked;
                    }
                    None => {
                        self.modules.errors.push(format!("module {name}: no directory configured"));
                        break asked;
                    }
                }
            }
            let Some(module) = pending.last() else { return Some(()) };
            match self.attempt(&module.name, &[], &module.files, false) {
                Ok(built) => {
                    if let Err(message) = self.finish(&module.name, built) {
                        self.modules.errors.push(message);
                        break None;
                    }
                    pending.pop();
                }
                Err(Missed::Failed) => break None,
                Err(Missed::Needs(module, asked)) => next = Some((module, Some(asked))),
            }
        };
        self.modules.errors.extend(asked);
        self.modules.errors.extend(pending.into_iter().rev().filter_map(|module| module.asked));
        None
    }

    /// Creates a program that starts from the state in the image `bytes`. Its code can also require the modules of
    /// `dirs`.
    pub fn from_image(heap: usize, dirs: Vec<ModuleDir>, bytes: &[u8]) -> Result<Self, Vec<String>> {
        let mut arena = Arena::new(heap, 0);
        let mut modules = Modules { dirs, loaded: Vec::new(), wanted: None, errors: Vec::new(), listing: None };
        let (symbols, scheme_module) = arena.mutate(|mc| restore(mc, bytes, &mut modules)).map_err(|message| vec![message])?;
        let repl = modules.loaded.iter().find(|(name, _)| name == hosts::NAME).map(|(_, module)| module.clone());
        let Some(repl) = repl else { return Err(vec![format!("an image without the `{}` module", hosts::NAME)]) };
        Ok(Self { arena, symbols, scheme_module, modules, inputs: vec![repl], required: Vec::new() })
    }

    /// Saves the symbol table, the `scheme` module and every loaded module as an image that
    /// [`Program::from_image`] accepts.
    pub fn save_image(&mut self) -> Result<Vec<u8>, Vec<String>> {
        let Self { arena, symbols, scheme_module, modules, .. } = self;
        arena.collect();
        let saved = arena.mutate(|mc| {
            let strings = Strings::new(mc);
            let mut roots = vec![symbols.get(mc).ok()?, Value::object(mc, scheme_module.get(mc).ok()?)];
            for (name, module) in &modules.loaded {
                roots.push(from_str(&strings, name).ok()?.value());
                roots.push(Value::object(mc, module.get(mc).ok()?));
            }
            Some(image::save(mc, &roots))
        });
        match saved {
            None => Err(vec![OUT_OF_MEMORY.to_string()]),
            Some(Ok(bytes)) => Ok(bytes),
            Some(Err(SaveError::Host(_) | SaveError::Frozen(_))) => Err(vec!["a module holds a value of the host's, which an image can't hold".to_string()]),
            Some(Err(SaveError::Unnumbered | SaveError::Busy)) => Err(vec!["a module holds a value that an image can't hold".to_string()]),
        }
    }

    /// Starts keeping the bytecode listing of each module that is loaded from now on. [`Program::take_listing`] returns the listing.
    pub fn list(&mut self) {
        self.modules.listing = Some(String::new());
    }

    pub fn take_listing(&mut self) -> String {
        self.modules.listing.take().unwrap_or_default()
    }

    /// Loads every module that the command line names and that is not loaded yet.
    pub fn load_all(&mut self) -> Result<(), Vec<String>> {
        let names: Vec<String> = self.modules.dirs.iter().map(|dir| dir.name.clone()).collect();
        for name in names {
            let loaded = self.modules.loaded.iter().any(|(loaded, _)| *loaded == name);
            if !loaded && self.ensure(name, None).is_none() {
                return Err(self.take_errors());
            }
        }
        Ok(())
    }

    /// Loads the file at `path` as a module named after the file's stem, and runs it if `running` is true.
    pub fn run_file(&mut self, path: &Path, running: bool) -> Result<(), Vec<String>> {
        let file = read_file(path).map_err(|message| vec![message])?;
        let name = path.file_stem().map_or_else(|| "main".to_string(), |stem| stem.to_string_lossy().into_owned());
        let Some(built) = self.build(&name, &[], &[file], false) else { return Err(self.take_errors()) };
        if running {
            for thunk in &built.thunks {
                run(&mut self.arena, thunk, None).map_err(|message| vec![message])?;
            }
        }
        Ok(())
    }

    /// Returns whether `text` ends inside a list, a string or a block comment, so that more input is expected.
    pub fn unfinished(&mut self, text: &str) -> bool {
        let Self { arena, symbols, .. } = self;
        arena.mutate(|mc| {
            let Some(symbols) = symbols.get(mc).ok().and_then(Symbols::of) else { return false };
            let Ok(session) = SyntaxSession::new(mc, text) else { return false };
            let Ok(reader) = Reader::new(mc, symbols, &session) else { return false };
            for node in reader {
                if let Err(error) = node {
                    return error.kind == ErrorKind::Unclosed;
                }
            }
            false
        })
    }

    /// Runs `text` as the next REPL input. The written form of the value of each form is passed to `out`
    /// as soon as the form has run. A void value is not passed.
    pub fn eval(&mut self, text: &str, out: &mut dyn FnMut(&str)) -> Result<(), Vec<String>> {
        fn file(text: &str) -> SourceFile {
            SourceFile { path: "<input>".into(), text: text.to_string(), language: Language::Scheme }
        }
        let name = format!("input-{}", self.inputs.len());
        let files = [file(text), file("(provide (all-defined-out))")];
        let Some(built) = self.build(&name, &[], &files, true) else { return Err(self.take_errors()) };
        let Self { arena, symbols, modules, inputs, required, .. } = self;
        let names = arena.mutate(|mc| symbols.get(mc).ok().and_then(Symbols::of).map_or(Vec::new(), |symbols| required_by(mc, symbols, text)));
        for name in names {
            let found = modules.loaded.iter().find(|(loaded, _)| *loaded == name);
            if let Some((_, module)) = found.filter(|_| !required.contains(&name)) {
                inputs.push(module.clone());
                required.push(name);
            }
        }
        inputs.push(built.module);
        for thunk in &built.thunks {
            run(arena, thunk, Some(&mut *out)).map_err(|message| vec![message])?;
        }
        Ok(())
    }
}
