//! Combines ragwort's languages. This crate builds modules whose files can be written in different
//! languages, and it builds the libraries that hold Scheme's procedures.
//!
//! The embedder states the language of each file. The files of a module make up one body:
//!
//! - Code in one file can refer by name to the top-level definitions of the other files.
//! - The exception is a definition that a macro introduces hygienically. Other files cannot refer to it.
//! - A macro of native ragwort is known to the module's files of every language, once the form that defines it is declared. A Scheme macro is known only to the module's Scheme files.
//! - A module can provide a definition from any of its files.

pub mod image;
pub mod libraries;

#[cfg(test)]
#[path = "tests/modules.rs"]
mod tests;

use ragwort_compiler::CompileError;
use ragwort_compiler::module::{Item, Loaded, NoModules, Resolver};
use ragwort_types::gc::Value;
use ragwort_native::{LowerError, Lowerer};
use ragwort_reader_scheme::{ReadError, Reader};
pub use ragwort_scheme::library_of;
use ragwort_scheme::{ExpandError, Expander, Top};
use ragwort_types::gc::{Gc, Mutation, OutOfMemory};
use ragwort_types::symbol::Symbols;
use ragwort_types::syntax::SyntaxSession;
use ragwort_vm::HostDef;
use ragwort_vm::objects::Module;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Read(ReadError),
    /// An error in the code of a Scheme file.
    Expand(ExpandError),
    /// An error in the code of a native file.
    Lower(LowerError),
    Compile(CompileError),
}

impl Error {
    /// Returns the byte range of the name, if the error is a name that nothing defines. If the name is a procedure of Scheme,
    /// [`library_of`] gives the library that the module would have to require.
    pub fn unbound(&self) -> Option<(u32, u32)> {
        match self {
            Error::Expand(error) if error.kind == ragwort_scheme::ExpandErrorKind::Unbound => Some((error.start, error.end)),
            Error::Lower(error) if error.kind == ragwort_native::LowerErrorKind::Unbound => Some((error.start, error.end)),
            _ => None,
        }
    }
}

impl From<ReadError> for Error {
    fn from(error: ReadError) -> Self {
        Error::Read(error)
    }
}

impl From<ExpandError> for Error {
    fn from(error: ExpandError) -> Self {
        Error::Expand(error)
    }
}

impl From<LowerError> for Error {
    fn from(error: LowerError) -> Self {
        Error::Lower(error)
    }
}

impl From<CompileError> for Error {
    fn from(error: CompileError) -> Self {
        // The compiler resolves the top-level names of native forms. Its error about a misused name is reported as a lowering error.
        match LowerError::located(error) {
            Some(lower) => Error::Lower(lower),
            None => Error::Compile(error),
        }
    }
}

impl From<OutOfMemory> for Error {
    fn from(error: OutOfMemory) -> Self {
        Error::Expand(error.into())
    }
}

impl From<ragwort_native::Error> for Error {
    fn from(error: ragwort_native::Error) -> Self {
        match error {
            ragwort_native::Error::Read(error) => Error::Read(error),
            ragwort_native::Error::Lower(error) => Error::Lower(error),
            ragwort_native::Error::Compile(error) => Error::Compile(error),
        }
    }
}

/// The modules of Scheme's libraries, built in one arena. See [`scheme`].
pub struct Scheme<'gc> {
    /// The name and the module of each library of [`ragwort_scheme::LIBRARIES`], then of the `scheme` module, which passes them all on.
    pub modules: Vec<(&'static str, Gc<'gc, Module>)>,
    /// The thunks of the libraries' forms. They must run, in order, before code that requires a library is loaded.
    pub thunks: Vec<Value<'gc>>,
}

impl<'gc> Scheme<'gc> {
    /// Returns the `scheme` module. A module that requires it, or that is given it as an implicit module, has every procedure of the language.
    pub fn all(&self) -> Gc<'gc, Module> {
        self.modules.last().expect("the `scheme` module").1
    }
}

/// Finds a module of Scheme's libraries by its name, for the `scheme` module that requires them.
struct Built<'m, 'gc>(&'m [(&'static str, Gc<'gc, Module>)]);

impl<'gc> Resolver<'gc> for Built<'_, 'gc> {
    fn resolve(&mut self, _: &Mutation<'gc>, name: &str, _: Value<'gc>) -> Option<Gc<'gc, Module>> {
        self.0.iter().find(|(built, _)| *built == name).map(|&(_, module)| module)
    }
}

/// Builds the modules of Scheme's libraries, and the `scheme` module that passes them all on. A program that does not use a set of
/// [`libraries`] builds them this way.
pub fn scheme<'gc>(mc: &Mutation<'gc>, symbols: Symbols<'gc>) -> Result<Scheme<'gc>, Error> {
    let mut built = Scheme { modules: Vec::with_capacity(ragwort_scheme::LIBRARIES.len() + 1), thunks: Vec::new() };
    for (name, source) in ragwort_scheme::LIBRARIES {
        let session = SyntaxSession::named(mc, name, source).map_err(|error| LowerError::from(ragwort_types::Error::from(error)))?;
        let loaded = ragwort_native::load(mc, symbols, name, &[], &[&session], &mut NoModules)?;
        built.modules.push((name, loaded.module));
        built.thunks.extend(loaded.thunks);
    }
    let (name, source) = ragwort_scheme::SCHEME;
    let session = SyntaxSession::named(mc, name, source).map_err(|error| LowerError::from(ragwort_types::Error::from(error)))?;
    let loaded = ragwort_native::load(mc, symbols, name, &[], &[&session], &mut Built(&built.modules))?;
    built.modules.push((name, loaded.module));
    built.thunks.extend(loaded.thunks);
    Ok(built)
}

/// The language a file of a module is written in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Language {
    Scheme,
    Native,
}

/// A file of a module and its language. Only the embedder decides the language.
#[derive(Clone, Copy)]
pub struct File<'s> {
    pub language: Language,
    pub session: &'s SyntaxSession,
}

/// A module to build.
///
/// - `name`: the module's name.
/// - `hosts`: the host functions that its native files can call.
/// - `files`: its files, in order.
/// - `implicit`: the modules that it requires implicitly. They must have run. Without any, the module starts with no procedure. The exports of each
///   module shadow the exports of the modules before it. The module's own definitions and
///   requires shadow all of them.
/// - `internals`: whether its native files can name
///   [internal intrinsics](ragwort_vm::Intrinsic::is_internal) in an `%intrinsic`. Leave it
///   `false` unless the embedder wrote the module itself. See [`Lowerer::new`].
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
    Native(Item<'gc>),
}

/// The error of a failed [`load`], and the file that the error is in. `file` is an index into
/// [`Source::files`]. It is `None` for an error that belongs to no single file, such as an error in the module's exports.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Located {
    pub error: Error,
    pub file: Option<usize>,
}

/// Builds the module that `source` describes and compiles each of its forms. Names are interned in `symbols`.
/// `resolver` finds the modules
/// that the code requires explicitly.
pub fn load<'gc>(
    mc: &Mutation<'gc>,
    symbols: Symbols<'gc>,
    source: &Source<'_, 'gc>,
    resolver: &mut dyn Resolver<'gc>,
) -> Result<Loaded<'gc>, Error> {
    load_located(mc, symbols, source, resolver).map_err(|failed| failed.error)
}

/// Works like [`load`], but the error also says which file it is in.
pub fn load_located<'gc>(
    mc: &Mutation<'gc>,
    symbols: Symbols<'gc>,
    source: &Source<'_, 'gc>,
    resolver: &mut dyn Resolver<'gc>,
) -> Result<Loaded<'gc>, Located> {
    let mut file = None;
    load_from(mc, symbols, source, resolver, &mut file).map_err(|error| Located { error, file })
}

/// Implements [`load`]. While it works on the code of one file, `at` holds that file's index. Otherwise `at` is `None`.
fn load_from<'gc>(
    mc: &Mutation<'gc>,
    symbols: Symbols<'gc>,
    source: &Source<'_, 'gc>,
    resolver: &mut dyn Resolver<'gc>,
    at: &mut Option<usize>,
) -> Result<Loaded<'gc>, Error> {
    let mut expander = Expander::new(mc, symbols, source.name, source.hosts, source.implicit)?;
    let mut lowerer = None;
    let mut forms = Vec::new();
    let mut tops = Vec::new();
    for (file_index, file) in source.files.iter().enumerate() {
        *at = Some(file_index);
        for node in Reader::new(mc, symbols, file.session)? {
            let node = node?;
            let first = u32::try_from(forms.len()).map_err(|_| OutOfMemory)?;
            match file.language {
                Language::Scheme => {
                    expander.declare(node, first, &mut tops, resolver)?;
                    forms.extend(tops.drain(..).map(|top| (file_index, Form::Scheme(top))));
                }
                Language::Native => {
                    let lowerer = match &mut lowerer {
                        Some(lowerer) => lowerer,
                        None => lowerer.insert(Lowerer::new(mc, symbols, source.internals)?),
                    };
                    let items = lowerer.declare(expander.builder(), resolver, node, first)?;
                    forms.extend(items.into_iter().map(|item| (file_index, Form::Native(item))));
                }
            }
        }
    }
    *at = None;
    expander.provide()?;
    expander.builder().provide_items(mc).map_err(|(error, span)| LowerError::declared(error, span))?;
    expander.builder().start(mc)?;
    let mut thunks = Vec::with_capacity(forms.len());
    for (i, (file_index, form)) in forms.into_iter().enumerate() {
        *at = Some(file_index);
        let i = u32::try_from(i).map_err(|_| OutOfMemory)?;
        match form {
            Form::Scheme(top) => {
                let form = expander.lower(top, i)?;
                thunks.push(expander.builder().compile(mc, i, form)?);
            }
            Form::Native(item) => thunks.extend(expander.builder().compile_item(mc, i, item)?),
        }
    }
    *at = None;
    let sealed = lowerer.as_mut().map(|lowerer| lowerer.seal(expander.builder()));
    let module = expander.finish()?;
    if let Some(sealed) = sealed {
        sealed.patch(mc, module);
    }
    Ok(Loaded { module, thunks })
}
