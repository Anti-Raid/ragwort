//! Loading and running what the command line names.
//!
//! A [`Program`] has an arena with the prelude and the `repl` module in it. It loads a module
//! from its folder the first time code requires it, and runs it then, since the code that
//! requires it is compiled against what it defines.
//!
//! # Loading what a module requires
//!
//! A module is built in one step of the arena, and what it requires has to have run by then.
//! So building stops at a `require` of a module that isn't loaded. That module is then built
//! and run, and the first is built again from the start, as often as it takes: once for each
//! module it's the first to require.
//!
//! Every module's code, the prelude's included, runs a step at a time between builds, so the
//! collector keeps up with what it allocates as it does for the entry point.
//!
//! # Images
//!
//! [`Program::save_image`] saves the symbols, the prelude and every module loaded, by name,
//! and [`Program::from_image`] starts from them: see [`ragwort_modules_core::image`]. The
//! modules of an image have run, so they aren't loaded from their folders again.
//!
//! # The REPL
//!
//! Each input is a module of its own that provides everything it defines, and requires
//! `repl` and every input before it implicitly. So:
//!
//! - A definition is there for the inputs after it, and one of the same name later takes its
//!   place for the inputs after that.
//! - A module an input requires by its name alone, as `(require lib/text)` does, is there for
//!   the inputs after it too. One required through `only-in` or the like is for that input.
//! - An input can't `set!` a variable an earlier one defined, as no module can one it requires.
//! - A macro lasts for the input that defines it.

#[cfg(test)]
#[path = "tests/program.rs"]
mod tests;

use std::hash::{BuildHasher, Hasher, RandomState};
use std::path::{Path, PathBuf};

use ragwort_compiler::module::{Loaded, Resolver};
use ragwort_modules_core::image::{self, ImageError};
use ragwort_modules_core::{Error, File, Language, Located, Source, load_located, prelude};
use ragwort_printer_scheme::{Mode, to_string};
use ragwort_reader_scheme::{ErrorKind, Reader};
use ragwort_types::gc::image::{LoadError, SaveError};
use ragwort_types::gc::{Arena, Gc, Mutation, Root, Value, ValueRoot};
use ragwort_types::pair::Pairs;
use ragwort_types::string::{Strings, chars, from_str};
use ragwort_types::symbol::{Symbol, Symbols};
use ragwort_types::syntax::{Syntax, SyntaxKind, SyntaxSession};
use ragwort_vm::objects::Module;
use ragwort_vm::{Fault, HostDef, MIN_SEGMENT, Machine, Outcome};

use crate::args::{ModuleDir, language};
use crate::{hosts, listing};

/// The most bytes the arena takes.
const HEAP: usize = 1 << 28;
/// The most characters a result or a raised value is shown in.
const SHOWN: usize = 1 << 16;
const OUT_OF_MEMORY: &str = "out of memory";

/// A file of a module: where it's from, its text and its language.
struct SourceFile {
    path: PathBuf,
    text: String,
    language: Language,
}

/// The modules the command line names, and what's become of them.
struct Modules {
    dirs: Vec<ModuleDir>,
    /// Those loaded and run, by name.
    loaded: Vec<(String, Root<Module>)>,
    /// The module the build under way asked for that isn't loaded, which it stopped at.
    wanted: Option<String>,
    /// What went wrong, in order.
    errors: Vec<String>,
    /// The bytecode of each module loaded since [`Program::list`], if it's kept.
    listing: Option<String>,
}

/// A module that's built and hasn't run: the code of each of its forms, to run in order.
struct Built {
    thunks: Vec<ValueRoot>,
    module: Root<Module>,
}

/// Why a module wasn't built.
enum Missed {
    /// It requires this module, which isn't loaded: the message says where.
    Needs(String, String),
    /// Something's wrong, which `Modules::errors` says.
    Failed,
}

/// A module being loaded: its files, and where the module that asked for it requires it.
struct Pending {
    name: String,
    files: Vec<SourceFile>,
    asked: Option<String>,
}

/// What every module is built on.
#[derive(Clone, Copy)]
struct Base<'gc> {
    symbols: Symbols<'gc>,
    prelude: Gc<'gc, Module>,
}

pub struct Program {
    arena: Arena,
    symbols: ValueRoot,
    prelude: Root<Module>,
    modules: Modules,
    /// The modules a REPL input requires implicitly: `repl`, then each input before it, and
    /// each module one of them required by name, which are `required`.
    inputs: Vec<Root<Module>>,
    required: Vec<String>,
}

/// The text of `node`, if it's an identifier or a string.
fn name_of<'gc>(mc: &Mutation<'gc>, node: Syntax<'gc>) -> Option<String> {
    let (strings, datum) = (Strings::new(mc), node.datum(mc));
    let name = match node.kind(mc)? {
        SyntaxKind::Identifier => Symbol::of(datum)?.name(mc),
        SyntaxKind::Literal => strings.string(datum)?,
        _ => return None,
    };
    Some(chars(&strings, name).collect())
}

/// The modules that `text`'s forms require by name alone, as `(require lib/text "other")`
/// does two.
fn required_by<'gc>(mc: &Mutation<'gc>, symbols: Symbols<'gc>, text: &str) -> Vec<String> {
    let mut names = Vec::new();
    let Ok(session) = SyntaxSession::new(mc, text) else { return names };
    let Ok(reader) = Reader::new(mc, symbols, &session) else { return names };
    for node in reader.flatten() {
        if node.kind(mc) != Some(SyntaxKind::List) {
            continue;
        }
        let mut items = Pairs::new(mc).elements(node.datum(mc)).filter_map(Syntax::of);
        if items.next().and_then(|head| name_of(mc, head)).as_deref() == Some("require") {
            names.extend(items.filter_map(|spec| name_of(mc, spec)));
        }
    }
    names
}

/// The one-based line and column of byte `offset` of `text`.
fn place(text: &str, offset: u32) -> (usize, usize) {
    let before = &text.as_bytes()[..(offset as usize).min(text.len())];
    let line = before.iter().filter(|&&byte| byte == b'\n').count() + 1;
    let column = before.iter().rev().take_while(|&&byte| byte != b'\n').count() + 1;
    (line, column)
}

/// What's wrong with the module `name`, whose files are `files`, as `file:line:column: what`.
fn describe(name: &str, files: &[SourceFile], failed: &Located) -> String {
    let (what, start) = match failed.error {
        Error::Read(e) => (e.kind.to_string(), Some(e.start)),
        Error::Expand(e) => (e.kind.to_string(), Some(e.start)),
        Error::Lower(e) => (e.kind.to_string(), Some(e.start)),
        Error::Compile(e) => (e.to_string(), None),
    };
    let file = match failed.file {
        Some(k) => files.get(k),
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

/// What a run of a machine came to.
enum Ran<'gc> {
    More,
    Done(Value<'gc>),
    Failed(String),
}

fn ran<'gc>(mc: &Mutation<'gc>, outcome: Result<Outcome<'gc>, Fault>) -> Ran<'gc> {
    match outcome {
        Ok(Outcome::Paused) => Ran::More,
        Ok(Outcome::Done(value)) => Ran::Done(value),
        Ok(Outcome::Raised(raised)) => Ran::Failed(format!("uncaught: {}", shown(mc, raised))),
        Ok(Outcome::Yielded(_)) => Ran::Failed("error: a yield with nothing to resume it".to_string()),
        Ok(Outcome::Deferred(_)) => Ran::Failed("error: a host call that's never answered".to_string()),
        Err(e) => Ran::Failed(fault(e)),
    }
}

/// The source files in `folder`, in the order of their names.
fn read_folder(folder: &Path) -> Result<Vec<SourceFile>, String> {
    let wrong = |e: std::io::Error| format!("{}: {e}", folder.display());
    let mut paths = Vec::new();
    for entry in std::fs::read_dir(folder).map_err(wrong)? {
        let path = entry.map_err(wrong)?.path();
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
    let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    Ok(SourceFile { path: path.to_path_buf(), text, language })
}

/// Builds the module `name` of `files`. What's wrong with it goes to `modules.errors`, unless
/// it's that it requires a module that isn't loaded yet.
fn load_module<'gc>(
    mc: &Mutation<'gc>,
    base: Base<'gc>,
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
    match load_located(mc, base.symbols, base.prelude, &source, &mut Finder { modules }) {
        Ok(loaded) => {
            if let Some(listing) = &mut modules.listing {
                listing::list(mc, name, &loaded.thunks, listing);
            }
            Ok(loaded)
        }
        Err(failed) => {
            let message = describe(name, files, &failed);
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

/// `loaded`, kept across steps till it has run.
fn rooted<'gc>(mc: &Mutation<'gc>, loaded: &Loaded<'gc>) -> Option<Built> {
    let mut thunks = Vec::with_capacity(loaded.thunks.len());
    for &thunk in &loaded.thunks {
        thunks.push(ValueRoot::new(mc, thunk).ok()?);
    }
    Some(Built { thunks, module: Root::new(mc, loaded.module).ok()? })
}

/// Finds the modules code requires among those loaded. One the command line gives a folder
/// that isn't loaded yet is noted, for the build to be tried again once it is.
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

/// The symbol table and the prelude, built, in a new arena's first step.
fn start<'gc>(mc: &Mutation<'gc>) -> Result<(ValueRoot, Built), String> {
    let oom = |_| OUT_OF_MEMORY.to_string();
    let symbols = Symbols::with_seed(mc, RandomState::new().build_hasher().finish()).map_err(oom)?;
    let loaded = prelude(mc, symbols).map_err(|e| format!("the prelude: {e:?}"))?;
    let built = rooted(mc, &loaded).ok_or_else(|| OUT_OF_MEMORY.to_string())?;
    Ok((ValueRoot::new(mc, symbols.value(mc)).map_err(oom)?, built))
}

/// What an image holds, in a new arena's first step: the symbol table, the prelude, and each
/// module with its name. A module the command line gives a folder too is an error.
fn restore<'gc>(mc: &Mutation<'gc>, bytes: &[u8], modules: &mut Modules) -> Result<(ValueRoot, Root<Module>), String> {
    let oom = |_| OUT_OF_MEMORY.to_string();
    let roots = image::load(mc, bytes, hosts::HOSTS.iter()).map_err(|e| match e {
        ImageError::Host(name) => format!("the image calls the host function `{name}`, which this ragwort doesn't have"),
        ImageError::SameHost(path) => format!("two host functions are both `{path}`"),
        ImageError::Load(LoadError::Stamp) => "the image was made by another build of ragwort".to_string(),
        ImageError::Load(LoadError::OutOfMemory) => OUT_OF_MEMORY.to_string(),
        ImageError::Load(_) => "not a ragwort image, or one that's damaged".to_string(),
    })?;
    let damaged = || "an image that holds something other than modules".to_string();
    let [symbols, prelude, named @ ..] = roots.as_slice() else { return Err(damaged()) };
    let prelude = prelude.downcast::<Module>(mc).ok_or_else(damaged)?;
    let strings = Strings::new(mc);
    for pair in named.chunks(2) {
        let &[name, module] = pair else { return Err(damaged()) };
        let name: String = chars(&strings, strings.string(name).ok_or_else(damaged)?).collect();
        if modules.dirs.iter().any(|dir| dir.name == name) {
            return Err(format!("the module `{name}` is in the image already"));
        }
        let module = module.downcast::<Module>(mc).ok_or_else(damaged)?;
        modules.loaded.push((name, Root::new(mc, module).map_err(oom)?));
    }
    Ok((ValueRoot::new(mc, *symbols).map_err(oom)?, Root::new(mc, prelude).map_err(oom)?))
}

/// Calls `thunk` and runs it to its end, a step at a time, so the collector keeps up. Its
/// value goes to `out`, written out, unless it's void.
fn run(arena: &mut Arena, thunk: &ValueRoot, mut out: Option<&mut dyn FnMut(&str)>) -> Result<(), String> {
    let mut machine = arena.mutate(|mc| {
        let thunk = thunk.get(mc).map_err(|_| "a value of another arena".to_string())?;
        Machine::new(mc, MIN_SEGMENT, thunk, &[]).map_err(fault)
    })?;
    loop {
        let step = arena.step(|mc| match ran(mc, machine.run(mc)) {
            Ran::More => None,
            Ran::Done(value) => Some(Ok((value != Value::VOID).then(|| shown(mc, value)))),
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
    /// A program whose code can require the modules of `dirs`, none of them loaded yet.
    pub fn new(dirs: Vec<ModuleDir>) -> Result<Self, Vec<String>> {
        let mut arena = Arena::new(HEAP, 0);
        let modules = Modules { dirs, loaded: Vec::new(), wanted: None, errors: Vec::new(), listing: None };
        let (symbols, built) = arena.mutate(start).map_err(|message| vec![message])?;
        for thunk in &built.thunks {
            run(&mut arena, thunk, None).map_err(|message| vec![format!("the prelude: {message}")])?;
        }
        let mut program = Self { arena, symbols, prelude: built.module, modules, inputs: Vec::new(), required: Vec::new() };
        let files = [SourceFile { path: "repl.rgn".into(), text: hosts::SOURCE.to_string(), language: Language::Native }];
        let Some(built) = program.build(hosts::NAME, &hosts::HOSTS, &files, false) else { return Err(program.take_errors()) };
        program.inputs.push(built.module.clone());
        program.finish(hosts::NAME, built).map_err(|message| vec![message])?;
        Ok(program)
    }

    fn take_errors(&mut self) -> Vec<String> {
        std::mem::take(&mut self.modules.errors)
    }

    /// One try at building the module `name` of `files`, which stops at a module it requires
    /// that isn't loaded. A REPL input requires what the inputs before it defined implicitly.
    fn attempt(&mut self, name: &str, hosts: &'static [HostDef], files: &[SourceFile], input: bool) -> Result<Built, Missed> {
        let Self { arena, symbols, prelude, modules, inputs, .. } = self;
        let implicit: &[Root<Module>] = if input { inputs } else { &[] };
        let built = arena.mutate(|mc| {
            let symbols = symbols.get(mc).ok().and_then(Symbols::of);
            let (Some(symbols), Ok(prelude)) = (symbols, prelude.get(mc)) else { return Ok(None) };
            let mut required = Vec::with_capacity(implicit.len());
            for module in implicit {
                let Ok(module) = module.get(mc) else { return Ok(None) };
                required.push(module);
            }
            let loaded = load_module(mc, Base { symbols, prelude }, modules, name, hosts, files, &required)?;
            Ok(rooted(mc, &loaded))
        })?;
        built.ok_or_else(|| {
            modules.errors.push(OUT_OF_MEMORY.to_string());
            Missed::Failed
        })
    }

    /// Builds the module `name` of `files`, after loading each module it requires that isn't
    /// loaded yet.
    fn build(&mut self, name: &str, hosts: &'static [HostDef], files: &[SourceFile], input: bool) -> Option<Built> {
        loop {
            match self.attempt(name, hosts, files, input) {
                Ok(built) => return Some(built),
                Err(Missed::Failed) => return None,
                Err(Missed::Needs(module, asked)) => self.ensure(module, Some(asked))?,
            }
        }
    }

    /// Runs the module `name`, which is built, and keeps it for the code that requires it.
    fn finish(&mut self, name: &str, built: Built) -> Result<(), String> {
        for thunk in &built.thunks {
            run(&mut self.arena, thunk, None).map_err(|message| format!("module {name}: {message}"))?;
        }
        self.modules.loaded.push((name.to_string(), built.module));
        Ok(())
    }

    /// Loads the module `name` from its folder and runs it, after each module it requires
    /// that isn't loaded yet, and each that those require. `asked` is where the code that
    /// requires it does, which is what's wrong with that code if the module can't be loaded.
    fn ensure(&mut self, name: String, asked: Option<String>) -> Option<()> {
        let mut pending: Vec<Pending> = Vec::new();
        let mut next = Some((name, asked));
        // Where the module that can't be loaded was asked for, if it isn't one of `pending`.
        let asked = loop {
            if let Some((name, asked)) = next.take() {
                if pending.iter().any(|module| module.name == name) {
                    let through: Vec<&str> = pending.iter().map(|module| &*module.name).collect();
                    self.modules.errors.push(format!("module {name}: it requires itself, through {}", through.join(", ")));
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
                        self.modules.errors.push(format!("module {name}: no folder is given for it"));
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

    /// A program that starts from what the image `bytes` holds, and can require the modules of
    /// `dirs` besides.
    pub fn from_image(dirs: Vec<ModuleDir>, bytes: &[u8]) -> Result<Self, Vec<String>> {
        let mut arena = Arena::new(HEAP, 0);
        let mut modules = Modules { dirs, loaded: Vec::new(), wanted: None, errors: Vec::new(), listing: None };
        let (symbols, prelude) = arena.mutate(|mc| restore(mc, bytes, &mut modules)).map_err(|message| vec![message])?;
        let repl = modules.loaded.iter().find(|(name, _)| name == hosts::NAME).map(|(_, module)| module.clone());
        let Some(repl) = repl else { return Err(vec![format!("an image without the `{}` module", hosts::NAME)]) };
        Ok(Self { arena, symbols, prelude, modules, inputs: vec![repl], required: Vec::new() })
    }

    /// The symbols, the prelude and every module loaded, as an image for
    /// [`Program::from_image`].
    pub fn save_image(&mut self) -> Result<Vec<u8>, Vec<String>> {
        let Self { arena, symbols, prelude, modules, .. } = self;
        arena.collect();
        let saved = arena.mutate(|mc| {
            let strings = Strings::new(mc);
            let mut roots = vec![symbols.get(mc).ok()?, Value::object(mc, prelude.get(mc).ok()?)];
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

    /// Keeps the bytecode of each module loaded from here on, for [`Program::take_listing`].
    pub fn list(&mut self) {
        self.modules.listing = Some(String::new());
    }

    pub fn take_listing(&mut self) -> String {
        self.modules.listing.take().unwrap_or_default()
    }

    /// Loads every module the command line names that isn't loaded yet.
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

    /// Loads the file at `path` as a module named for it, and runs it if `running`.
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

    /// Whether `text` ends inside a list, string or comment, so there's more of it to come.
    pub fn unfinished(&mut self, text: &str) -> bool {
        let Self { arena, symbols, .. } = self;
        arena.mutate(|mc| {
            let Some(symbols) = symbols.get(mc).ok().and_then(Symbols::of) else { return false };
            let Ok(session) = SyntaxSession::new(mc, text) else { return false };
            let Ok(reader) = Reader::new(mc, symbols, &session) else { return false };
            for node in reader {
                if let Err(e) = node {
                    return e.kind == ErrorKind::Unclosed;
                }
            }
            false
        })
    }

    /// Runs `text` as the REPL's next input, giving `out` the value of each of its forms,
    /// written out, as it's made.
    pub fn eval(&mut self, text: &str, out: &mut dyn FnMut(&str)) -> Result<(), Vec<String>> {
        let name = format!("input-{}", self.inputs.len());
        let file = |text: &str| SourceFile { path: "<input>".into(), text: text.to_string(), language: Language::Scheme };
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
