//! Ragwort's languages together: modules whose files are in any of them, and the prelude, which
//! Scheme is built on.
//!
//! A module's files, each in the language the embedder says, are one body: each file's code
//! refers to what the others define at the top level by name, but for what a Scheme macro defines
//! hygienically, and a module provides what any of them define.

#[cfg(test)]
#[path = "tests/modules.rs"]
mod tests;

use ragwort_compiler::CompileError;
use ragwort_compiler::module::{Loaded, NoModules, Resolver};
use ragwort_native::{LowerError, Lowerer};
use ragwort_reader_scheme::{ReadError, Reader};
use ragwort_scheme::{ExpandError, Expander, PRELUDE, PRELUDE_NAME, Top};
use ragwort_types::gc::{Gc, Mutation, OutOfMemory};
use ragwort_types::symbol::Symbols;
use ragwort_types::syntax::{Syntax, SyntaxSession};
use ragwort_vm::HostDef;
use ragwort_vm::objects::Module;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Read(ReadError),
    /// What's wrong with a Scheme file's code.
    Expand(ExpandError),
    /// What's wrong with a native file's code.
    Lower(LowerError),
    Compile(CompileError),
}

impl From<ReadError> for Error {
    fn from(e: ReadError) -> Self {
        Error::Read(e)
    }
}

impl From<ExpandError> for Error {
    fn from(e: ExpandError) -> Self {
        Error::Expand(e)
    }
}

impl From<LowerError> for Error {
    fn from(e: LowerError) -> Self {
        Error::Lower(e)
    }
}

impl From<CompileError> for Error {
    fn from(e: CompileError) -> Self {
        Error::Compile(e)
    }
}

impl From<OutOfMemory> for Error {
    fn from(e: OutOfMemory) -> Self {
        Error::Expand(e.into())
    }
}

impl From<ragwort_native::Error> for Error {
    fn from(e: ragwort_native::Error) -> Self {
        match e {
            ragwort_native::Error::Read(e) => Error::Read(e),
            ragwort_native::Error::Lower(e) => Error::Lower(e),
            ragwort_native::Error::Compile(e) => Error::Compile(e),
        }
    }
}

/// Builds the [`PRELUDE`]'s module, whose forms are to run before any Scheme is loaded.
pub fn prelude<'gc>(mc: &Mutation<'gc>, symbols: Symbols<'gc>) -> Result<Loaded<'gc>, Error> {
    let session = SyntaxSession::named(mc, "prelude", PRELUDE).map_err(|e| LowerError::from(ragwort_types::Error::from(e)))?;
    Ok(ragwort_native::load(mc, symbols, PRELUDE_NAME, &[], &[&session], &mut NoModules)?)
}

/// The language a file of a module is written in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Language {
    Scheme,
    Native,
}

/// A file of a module, and its language, which only the embedder says.
#[derive(Clone, Copy)]
pub struct File<'s> {
    pub language: Language,
    pub session: &'s SyntaxSession,
}

/// A module to build.
///
/// - `name`: the module's name.
/// - `hosts`: the host functions its native files call.
/// - `files`: its files, in order.
/// - `implicit`: the modules it requires implicitly, after the prelude. What each of them
///   exports shadows what those before it do, and what the module defines or requires shadows
///   them all.
/// - `internals`: whether its native files can name
///   [internal intrinsics](ragwort_vm::Intrinsic::is_internal) in an `%intrinsic`. Leave it
///   `false` unless the embedder wrote the module itself: see [`Lowerer::new`].
pub struct Source<'a, 'gc> {
    pub name: &'a str,
    pub hosts: &'static [HostDef],
    pub files: &'a [File<'a>],
    pub implicit: &'a [Gc<'gc, Module>],
    pub internals: bool,
}

/// A top-level form of a module, from a file in either language.
enum Form<'gc> {
    Scheme(Top),
    Native(Syntax<'gc>),
}

/// A [`load`] that failed: what's wrong, and which of the module's files it's in, by its place in
/// [`Source::files`]. There's no file for what's wrong with what the module provides as a whole.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Located {
    pub error: Error,
    pub file: Option<usize>,
}

/// Builds the module `source` describes, interning names in `symbols`, and compiles each of its
/// forms. It requires the `prelude` module, which has run, implicitly, and the modules `resolver`
/// finds as it says.
pub fn load<'gc>(
    mc: &Mutation<'gc>,
    symbols: Symbols<'gc>,
    prelude: Gc<'gc, Module>,
    source: &Source<'_, 'gc>,
    resolver: &mut dyn Resolver<'gc>,
) -> Result<Loaded<'gc>, Error> {
    load_located(mc, symbols, prelude, source, resolver).map_err(|failed| failed.error)
}

/// As [`load`], saying which file an error is in.
pub fn load_located<'gc>(
    mc: &Mutation<'gc>,
    symbols: Symbols<'gc>,
    prelude: Gc<'gc, Module>,
    source: &Source<'_, 'gc>,
    resolver: &mut dyn Resolver<'gc>,
) -> Result<Loaded<'gc>, Located> {
    let mut file = None;
    load_from(mc, symbols, prelude, source, resolver, &mut file).map_err(|error| Located { error, file })
}

/// [`load`], keeping in `at` the file whose code it's working on.
fn load_from<'gc>(
    mc: &Mutation<'gc>,
    symbols: Symbols<'gc>,
    prelude: Gc<'gc, Module>,
    source: &Source<'_, 'gc>,
    resolver: &mut dyn Resolver<'gc>,
    at: &mut Option<usize>,
) -> Result<Loaded<'gc>, Error> {
    let mut expander = Expander::new(mc, symbols, prelude, source.name, source.hosts, source.implicit)?;
    let mut lowerer = None;
    let mut forms = Vec::new();
    let mut tops = Vec::new();
    for (k, file) in source.files.iter().enumerate() {
        *at = Some(k);
        for node in Reader::new(mc, symbols, file.session)? {
            let node = node?;
            let first = u32::try_from(forms.len()).map_err(|_| OutOfMemory)?;
            match file.language {
                Language::Scheme => {
                    expander.declare(node, first, &mut tops, resolver)?;
                    forms.extend(tops.drain(..).map(|top| (k, Form::Scheme(top))));
                }
                Language::Native => {
                    let lowerer = match &mut lowerer {
                        Some(lowerer) => lowerer,
                        None => lowerer.insert(Lowerer::new(mc, symbols, source.hosts, source.internals).map_err(LowerError::from)?),
                    };
                    lowerer.declare(expander.builder(), node, first, resolver)?;
                    forms.push((k, Form::Native(node)));
                }
            }
        }
    }
    *at = None;
    expander.provide()?;
    if let Some(lowerer) = &mut lowerer {
        lowerer.provide(expander.builder())?;
    }
    expander.builder().start(mc)?;
    let mut thunks = Vec::with_capacity(forms.len());
    for (i, (k, form)) in forms.into_iter().enumerate() {
        *at = Some(k);
        let i = u32::try_from(i).map_err(|_| OutOfMemory)?;
        let core = match form {
            Form::Scheme(top) => Some(expander.lower(top, i)?),
            Form::Native(node) => lowerer.as_mut().expect("native forms are declared").lower(expander.builder(), node, i)?,
        };
        if let Some(core) = core {
            thunks.push(expander.builder().compile(mc, &core)?);
        }
    }
    *at = None;
    let module = expander.finish()?;
    Ok(Loaded { module, thunks })
}
