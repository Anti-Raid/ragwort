//! Libraries: modules that are built once and shared by many arenas.
//!
//! A [`Library`] describes a module in the program's own code: its name, its source files and the host functions that it calls. A
//! [`Libraries`] is a set of libraries that has been built. An arena that starts from the set gets a library when it first needs it,
//! and pays nothing for a library that it never needs.
//!
//! ```text
//! static QUEUE: Library = Library { name: "std/queue", base: Some(&PRELUDE), files: &[LibraryFile::scheme("queue.rg", QUEUE_SOURCE)], hosts: &[], requires: &[], internals: false };
//!
//! // Once, when the program starts:
//! let libraries = Libraries::build(&[&QUEUE], 64 << 20)?;
//! // In each new arena:
//! let shelf = arena.mutate(|mc| libraries.start(mc))?;
//! // To compile Scheme code in the arena: its base library, and a resolver that loads what the code requires.
//! let prelude = libraries.require(mc, shelf, PRELUDE.name)?;
//! let mut resolver = libraries.resolver(shelf, None);
//! ```
//!
//! # Base libraries
//!
//! The code of a language is compiled against that language's base library, which it uses without requiring it. For Scheme this is the
//! prelude, [`PRELUDE`]. A base library is a library like any other in the set: it is built once, shared, and loaded into an arena
//! when the arena first needs it. So an arena that runs no Scheme code does not hold the prelude.
//!
//! A library names its base in [`Library::base`]. A base library has none. It is written in native ragwort, which needs nothing
//! beneath it.
//!
//! # What the arenas share
//!
//! The set holds one image of each library. The arenas share the frozen values of the images, such as the instructions of the code.
//! Each arena has its own copy of the objects of the images that it loaded, and its own hash seed. See [`image::Template`].
//!
//! A library's image refers to the objects of its base and of the libraries that it uses. It does not hold copies of them. So an arena
//! that loads a library loads those first.
//!
//! # What a library can do
//!
//! A library runs once, when the set is built. Its image holds the state that it has then: its definitions and the values of its
//! variables. So:
//!
//! - Its top level must not depend on anything outside the arena, such as the time. Every arena gets the same result.
//! - Its variables must not hold values that the host owns after it has run, because an image cannot hold them. Its procedures can
//!   make such values when they are called.
//! - It must not change objects of another library while it runs, for example by adding to a table of theirs. The change is not
//!   part of any image, so an arena that loads the library does not see it.
//!
//! # Which libraries a program sees
//!
//! The embedder chooses. A set holds only the libraries that it was built with, and [`Libraries::resolver`] takes the names that one
//! arena's code is allowed to require.

use ragwort_compiler::module::Resolver;
use ragwort_types::gc::image::{Exports, Known, SaveError};
use ragwort_types::gc::{Arena, Gc, Mutation, OutOfMemory, Value};
use ragwort_types::symbol::Symbols;
use ragwort_types::syntax::SyntaxSession;
use ragwort_types::vector::{ImmutableVector, Vector, Vectors};
use ragwort_vm::objects::{Condition, ConditionFields, Module};
use ragwort_vm::{Fault, HostDef, Machine, Outcome, SEGMENT};

use crate::image::{self, ImageError, Template};
use crate::{File, Language, Located, Source, load_located};

#[cfg(test)]
#[path = "tests/libraries.rs"]
mod tests;

/// One source file of a [`Library`]. `path` names the file in error messages.
#[derive(Clone, Copy, Debug)]
pub struct LibraryFile {
    pub language: Language,
    pub path: &'static str,
    pub text: &'static str,
}

impl LibraryFile {
    pub const fn scheme(path: &'static str, text: &'static str) -> Self {
        Self { language: Language::Scheme, path, text }
    }

    pub const fn native(path: &'static str, text: &'static str) -> Self {
        Self { language: Language::Native, path, text }
    }
}

/// A module of the program's own that arenas share. See the [module docs](self).
///
/// - `name`: the name that code requires it by, such as `std/queue`.
/// - `base`: the base library of the language that it is written in, which its code is compiled against. `None` for a base library
///   itself. Its files are then all native.
/// - `files`: its files, in order. They make up one body.
/// - `hosts`: the host functions that its native files can call.
/// - `requires`: the libraries that its code requires. They are built before it, and are part of every set that it is part of.
/// - `internals`: whether its native files can name internal intrinsics. See [`Source::internals`].
#[derive(Debug)]
pub struct Library {
    pub name: &'static str,
    pub base: Option<&'static Library>,
    pub files: &'static [LibraryFile],
    pub hosts: &'static [HostDef],
    pub requires: &'static [&'static Library],
    pub internals: bool,
}

/// The base library of Scheme: the prelude. Scheme code is compiled against it.
pub static PRELUDE: Library = Library {
    name: ragwort_scheme::PRELUDE_NAME,
    base: None,
    files: &[LibraryFile::native("prelude", ragwort_scheme::PRELUDE)],
    hosts: &[],
    requires: &[],
    internals: false,
};

/// The reason why [`Libraries::build`] failed. `library` is the name of the library that the error is in.
#[derive(Debug)]
pub enum BuildError {
    OutOfMemory,
    /// The library has no base, and one of its files is not native.
    Base(&'static str),
    /// Two libraries of the set have this name.
    SameName(&'static str),
    /// The library requires itself, directly or through other libraries.
    Cycle(&'static str),
    /// The library's code has an error.
    Load { library: &'static str, error: Located },
    /// The library raised an error while it ran. `fault` is the fault, if the error was one.
    Raised { library: &'static str, fault: Option<Fault> },
    /// The library cannot be saved. See [`SaveError`].
    Save { library: &'static str, error: SaveError },
    Image(ImageError),
}

impl From<OutOfMemory> for BuildError {
    fn from(_: OutOfMemory) -> Self {
        Self::OutOfMemory
    }
}

/// One image of a set: a template, and the positions of its objects that later images refer to.
struct Linked {
    template: Template,
    exports: Vec<u32>,
}

/// A library of a set. `needs` are the positions of the libraries that an arena must hold before it loads this one, in ascending
/// order. The number of a library's image is its position in the set.
struct Built {
    name: &'static str,
    image: Linked,
    needs: Vec<usize>,
}

/// A set of libraries that has been built. See the [module docs](self).
pub struct Libraries {
    libraries: Vec<Built>,
}

/// The objects of earlier images that an image refers to, each as the number of its image and its position in that image.
type Imports = Vec<(u32, u32)>;

/// The roots of the arena that builds a set.
const SYMBOLS: usize = 0;
/// A list of the objects of each image saved so far, the newest first. Each entry is a vector.
const SAVED: usize = 1;
/// A list of the modules built so far, the newest first.
const MODULES: usize = 2;
/// The thunks of the module that is running, as a vector.
const THUNKS: usize = 3;
const ROOTS: usize = 4;

impl Libraries {
    /// Builds the libraries in `libraries`, their bases and the libraries that they require, in an arena with a limit of `limit`
    /// bytes that is dropped afterwards. Each library is built and run once, after its base and the libraries that it requires.
    pub fn build(libraries: &[&'static Library], limit: usize) -> Result<Self, BuildError> {
        let order = ordered(libraries)?;
        let hosts: Vec<&'static HostDef> = order.iter().flat_map(|library| library.hosts.iter()).collect();
        let mut arena = Arena::new(limit, ROOTS);
        arena.mutate(|mc| {
            mc.set_root(SYMBOLS, Symbols::of_arena(mc)?.value(mc));
            Ok::<(), BuildError>(())
        })?;
        let mut saved = Vec::with_capacity(order.len());
        // The imports of each image: the images and positions that it refers to.
        let mut imports: Vec<Imports> = Vec::with_capacity(order.len());
        for (position, library) in order.iter().enumerate() {
            let thunks = arena.mutate(|mc| compile(mc, library, &order[..position]))?;
            run(&mut arena, thunks, library.name)?;
            let (bytes, imported) = save(&mut arena, library.name)?;
            saved.push(bytes);
            imports.push(imported);
        }
        let mut built: Vec<Built> = Vec::with_capacity(order.len());
        for (position, library) in order.iter().enumerate() {
            let mut exports: Vec<u32> = imports.iter().flatten().filter(|&&(image, _)| image as usize == position).map(|&(_, place)| place).collect();
            exports.sort_unstable();
            exports.dedup();
            let image = Linked { template: Template::new(&saved[position], hosts.iter().copied()).map_err(BuildError::Image)?, exports };
            // The libraries that this one refers to, and those that they need. An earlier library's needs are complete already.
            let mut needs: Vec<usize> = imports[position].iter().map(|&(image, _)| image as usize).collect();
            for required in library.requires.iter().chain(library.base.iter()) {
                needs.extend(order.iter().position(|other| other.name == required.name));
            }
            let mut index = 0;
            while index < needs.len() {
                let further = built[needs[index]].needs.clone();
                needs.extend(further);
                index += 1;
            }
            needs.sort_unstable();
            needs.dedup();
            built.push(Built { name: library.name, image, needs });
        }
        Ok(Self { libraries: built })
    }

    /// Returns the names of the libraries of the set, in the order in which they were built.
    pub fn names(&self) -> impl Iterator<Item = &'static str> + '_ {
        self.libraries.iter().map(|library| library.name)
    }

    /// Makes the [`Shelf`] of a new arena, which holds no library yet. Keep the shelf alive, for example in a root.
    pub fn start<'gc>(&self, mc: &Mutation<'gc>) -> Result<Shelf<'gc>, OutOfMemory> {
        let symbols = Symbols::of_arena(mc)?;
        let slots = Vectors::new(mc).make(Shelf::IMAGES + 2 * self.libraries.len(), Value::FALSE)?;
        slots.items(mc).set(mc, Shelf::SYMBOLS, symbols.value(mc));
        Ok(Shelf(slots))
    }

    /// Returns the module of the library `name`. Loads the library into the arena first, and the libraries that it needs, if the arena
    /// does not hold them yet. Returns `None` if the set has no library of that name.
    ///
    /// The library has run already, when the set was built. So its module is ready at once, and this can be called while code that
    /// requires the library is being compiled.
    pub fn require<'gc>(&self, mc: &Mutation<'gc>, shelf: Shelf<'gc>, name: &str) -> Result<Option<Gc<'gc, Module>>, ImageError> {
        let Some(position) = self.libraries.iter().position(|library| library.name == name) else { return Ok(None) };
        for &needed in &self.libraries[position].needs {
            self.load(mc, shelf, needed)?;
        }
        self.load(mc, shelf, position).map(Some)
    }

    /// Returns the module of the library at `position`. Loads its image if the arena does not hold it. The arena holds the
    /// libraries that this one needs.
    fn load<'gc>(&self, mc: &Mutation<'gc>, shelf: Shelf<'gc>, position: usize) -> Result<Gc<'gc, Module>, ImageError> {
        let malformed = ImageError::Load(ragwort_types::gc::image::LoadError::Malformed);
        let items = shelf.0.items(mc);
        if let Some(module) = items.get(Shelf::IMAGES + 2 * position + 1).downcast::<Module>(mc) {
            return Ok(module);
        }
        let mut links = Vec::with_capacity(position);
        for (earlier, library) in self.libraries.iter().enumerate().take(position) {
            links.push(ImmutableVector::of(items.get(Shelf::IMAGES + 2 * earlier)).map(|objects| Exports { places: &library.image.exports, objects }));
        }
        let image = &self.libraries[position].image;
        let loaded = image.template.load_linked(mc, &links, &image.exports)?;
        let &[module] = loaded.roots.as_slice() else { return Err(malformed) };
        let Some(module) = module.downcast::<Module>(mc) else { return Err(malformed) };
        items.set(mc, Shelf::IMAGES + 2 * position, Vectors::new(mc).immutable_from_slice(&loaded.exported).map_err(out_of_memory)?.value(mc));
        items.set(mc, Shelf::IMAGES + 2 * position + 1, Value::object(mc, module));
        Ok(module)
    }

    /// Returns a resolver for the code of the arena that `shelf` belongs to. It finds the libraries of the set, and loads one when
    /// code first requires it. `allowed` are the names that this code can require. `None` allows every library of the set.
    pub fn resolver<'a, 'gc>(&'a self, shelf: Shelf<'gc>, allowed: Option<&'a [&'a str]>) -> Requires<'a, 'gc> {
        Requires { libraries: self, shelf, allowed, failed: None }
    }
}

fn out_of_memory(_: OutOfMemory) -> ImageError {
    ImageError::Load(ragwort_types::gc::image::LoadError::OutOfMemory)
}

/// What one arena holds of a set of libraries: its symbol table, and the libraries that it has loaded so far.
///
/// It is a vector in the arena. Slot 0 holds the symbol table. Then come two slots for each library of the set: the objects that
/// later images refer to, and the library's module. Both are `#f` until the arena loads the library.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Shelf<'gc>(Vector<'gc>);

impl<'gc> Shelf<'gc> {
    const SYMBOLS: usize = 0;
    const IMAGES: usize = 1;

    /// Returns `value` as a shelf, if it is the value of one.
    pub fn of(mc: &Mutation<'gc>, value: Value<'gc>) -> Option<Self> {
        let slots = Vector::of(value)?;
        let items = slots.items(mc);
        if items.len() >= Self::IMAGES && Symbols::of(items.get(Self::SYMBOLS)).is_some() { Some(Self(slots)) } else { None }
    }

    pub fn value(self, mc: &Mutation<'gc>) -> Value<'gc> {
        self.0.value(mc)
    }

    pub fn symbols(self, mc: &Mutation<'gc>) -> Symbols<'gc> {
        Symbols::of(self.0.items(mc).get(Self::SYMBOLS)).expect("a shelf holds the symbol table")
    }

    /// Returns the number of libraries that the arena has loaded, base libraries included.
    pub fn loaded(self, mc: &Mutation<'gc>) -> usize {
        let items = self.0.items(mc);
        (Self::IMAGES..items.len()).step_by(2).filter(|&slot| items.get(slot + 1).downcast::<Module>(mc).is_some()).count()
    }
}

/// A [`Resolver`] that finds the libraries of a set and loads each one when code first requires it. See [`Libraries::resolver`].
pub struct Requires<'a, 'gc> {
    libraries: &'a Libraries,
    shelf: Shelf<'gc>,
    allowed: Option<&'a [&'a str]>,
    failed: Option<ImageError>,
}

impl Requires<'_, '_> {
    /// Returns the error of a library that could not be loaded, if there was one. The code that required the library then failed to
    /// compile, with an error about a module that was not found.
    pub fn failed(&self) -> Option<&ImageError> {
        self.failed.as_ref()
    }
}

impl<'gc> Resolver<'gc> for Requires<'_, 'gc> {
    fn resolve(&mut self, mc: &Mutation<'gc>, name: &str, _: Value<'gc>) -> Option<Gc<'gc, Module>> {
        if self.allowed.is_some_and(|allowed| !allowed.contains(&name)) {
            return None;
        }
        match self.libraries.require(mc, self.shelf, name) {
            Ok(module) => module,
            Err(error) => {
                self.failed = Some(error);
                None
            }
        }
    }
}

/// Returns `libraries`, their bases and the libraries that they require, each after its base and the libraries that it requires.
fn ordered(libraries: &[&'static Library]) -> Result<Vec<&'static Library>, BuildError> {
    /// A library that is being placed, and the number of its requirements that have been dealt with.
    struct Visit {
        library: &'static Library,
        next: usize,
    }
    let mut order: Vec<&'static Library> = Vec::new();
    for &library in libraries {
        let mut path = vec![Visit { library, next: 0 }];
        while let Some(visit) = path.last_mut() {
            let library = visit.library;
            if let Some(placed) = order.iter().find(|placed| placed.name == library.name) {
                // Two different libraries with one name cannot both be required by that name.
                if !same(placed, library) {
                    return Err(BuildError::SameName(library.name));
                }
                path.pop();
                continue;
            }
            // A library's base comes before the libraries that it requires.
            let wanted = library.base.iter().chain(library.requires.iter()).nth(visit.next).copied();
            match wanted {
                Some(required) => {
                    visit.next += 1;
                    if path.iter().any(|earlier| earlier.library.name == required.name) {
                        return Err(BuildError::Cycle(required.name));
                    }
                    path.push(Visit { library: required, next: 0 });
                }
                None => {
                    if library.base.is_none() && library.files.iter().any(|file| file.language != Language::Native) {
                        return Err(BuildError::Base(library.name));
                    }
                    order.push(library);
                    path.pop();
                }
            }
        }
    }
    Ok(order)
}

/// Returns whether two descriptions are of the same library: the same files, in the same languages.
fn same(first: &Library, second: &Library) -> bool {
    first.files.len() == second.files.len() && first.files.iter().zip(second.files).all(|(one, other)| one.language == other.language && one.path == other.path && one.text == other.text)
}

/// Compiles `library` in the building arena. `built` are the libraries built so far, in order, whose modules are in the `MODULES`
/// root with the newest first. Stores the thunks of the library's forms in the `THUNKS` root and returns their number. The module
/// joins the `MODULES` root.
fn compile<'gc>(mc: &Mutation<'gc>, library: &'static Library, built: &[&'static Library]) -> Result<usize, BuildError> {
    let symbols = Symbols::of(mc.root(SYMBOLS)).expect("the symbol table");
    let mut sessions = Vec::with_capacity(library.files.len());
    for file in library.files {
        sessions.push(SyntaxSession::named(mc, file.path, file.text)?);
    }
    let mut resolver = Earlier { built, required: library.requires };
    let loaded = match library.base {
        // A base library is native code with nothing beneath it.
        None => {
            let files: Vec<&SyntaxSession> = sessions.iter().collect();
            let loaded = ragwort_native::load(mc, symbols, library.name, library.hosts, &files, &mut resolver);
            loaded.map_err(|error| BuildError::Load { library: library.name, error: Located { error: error.into(), file: None } })?
        }
        Some(base) => {
            let base = module_of(mc, built, base.name).expect("a library's base is built before it");
            let files: Vec<File> = library.files.iter().zip(&sessions).map(|(file, session)| File { language: file.language, session }).collect();
            let source = Source { name: library.name, hosts: library.hosts, files: &files, implicit: &[], internals: library.internals };
            load_located(mc, symbols, base, &source, &mut resolver).map_err(|error| BuildError::Load { library: library.name, error })?
        }
    };
    let pairs = ragwort_types::pair::Pairs::new(mc);
    mc.set_root(MODULES, pairs.cons(Value::object(mc, loaded.module), mc.root(MODULES))?.value(mc));
    mc.set_root(THUNKS, Vectors::new(mc).from_slice(&loaded.thunks)?.value(mc));
    Ok(loaded.thunks.len())
}

/// Returns the module of the library `name` among the libraries built so far. Their modules are in the `MODULES` root, the newest first.
fn module_of<'gc>(mc: &Mutation<'gc>, built: &[&'static Library], name: &str) -> Option<Gc<'gc, Module>> {
    let position = built.iter().position(|library| library.name == name)?;
    let pairs = ragwort_types::pair::Pairs::new(mc);
    pairs.elements(mc.root(MODULES)).nth(built.len() - 1 - position)?.downcast::<Module>(mc)
}

/// The resolver for a library that is being built. It finds the libraries that the library says it requires, among those built so far.
struct Earlier<'a> {
    built: &'a [&'static Library],
    required: &'static [&'static Library],
}

impl<'gc> Resolver<'gc> for Earlier<'_> {
    fn resolve(&mut self, mc: &Mutation<'gc>, name: &str, _: Value<'gc>) -> Option<Gc<'gc, Module>> {
        if !self.required.iter().any(|library| library.name == name) {
            return None;
        }
        module_of(mc, self.built, name)
    }
}

/// Runs the thunks in the `THUNKS` root in order, one step of the arena at a time, and then collects. `library` names what is running.
fn run(arena: &mut Arena, thunks: usize, library: &'static str) -> Result<(), BuildError> {
    for index in 0..thunks {
        let mut machine = arena.mutate(|mc| {
            let thunk = Vector::of(mc.root(THUNKS)).expect("the thunks").items(mc).get(index);
            Machine::new(mc, SEGMENT, thunk, &[])
        });
        loop {
            let Ok(running) = &mut machine else { return Err(BuildError::Raised { library, fault: machine.err() }) };
            let step = arena.step(|mc| match running.run(mc) {
                Ok(Outcome::Paused) => Ok(false),
                Ok(Outcome::Done(_)) => Ok(true),
                Ok(Outcome::Raised(raised)) => Err(raised.downcast::<Condition>(mc).and_then(|condition| condition.failure(mc)).map(|failure| failure.fault)),
                Ok(_) => Err(Some(Fault::Malformed)),
                Err(fault) => Err(Some(fault)),
            });
            match step {
                Ok(Ok(true)) => break,
                Ok(Ok(false)) => {}
                Ok(Err(fault)) => return Err(BuildError::Raised { library, fault }),
                Err(OutOfMemory) => return Err(BuildError::OutOfMemory),
            }
        }
    }
    arena.mutate(|mc| mc.set_root(THUNKS, Value::NULL));
    arena.collect();
    Ok(())
}

/// Saves an image of the module that was built last. The image refers to the objects of the images saved before it. Returns the
/// image's bytes and its imports. `name` is the library's name.
fn save(arena: &mut Arena, name: &'static str) -> Result<(Vec<u8>, Imports), BuildError> {
    arena.mutate(|mc| {
        let (pairs, vectors) = (ragwort_types::pair::Pairs::new(mc), Vectors::new(mc));
        // The newest image is first in the list, and the first library's image is number 0.
        let earlier: Vec<Value> = pairs.elements(mc.root(SAVED)).collect();
        let mut known = Known::default();
        for (back, objects) in earlier.iter().enumerate() {
            let objects = Vector::of(*objects).expect("the objects of an image").items(mc);
            known.add((earlier.len() - 1 - back) as u32, (0..objects.len()).map(|at| objects.get(at)));
        }
        let module = pairs.elements(mc.root(MODULES)).next().expect("the module that was built");
        let saved = image::save_linked(mc, &[module], &known).map_err(|error| BuildError::Save { library: name, error })?;
        let objects = vectors.from_slice(&saved.objects)?;
        mc.set_root(SAVED, pairs.cons(objects.value(mc), mc.root(SAVED))?.value(mc));
        Ok((saved.bytes, saved.imports))
    })
}
