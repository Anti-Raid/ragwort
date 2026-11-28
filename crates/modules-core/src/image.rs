//! Saves loaded modules as an image, so that a later run can load them without compiling or running them again.
//!
//! An image holds a set of root values and every object reachable from them. For modules that have run, that includes their code
//! and the values of their variables. Loading an image into a new arena reproduces the state of the arena that
//! saved it. Code loaded afterwards is compiled against the image's modules exactly as it would be
//! against newly built modules.
//!
//! ```text
//! let bytes = arena.mutate(|mc| image::save(mc, &[symbols, scheme, library]))?;
//! // In another arena, or another run of the program:
//! let roots = arena.mutate(|mc| image::load(mc, &bytes, HOSTS.iter()))?;
//! ```
//!
//! # Many arenas
//!
//! A program that makes many arenas with the same modules makes a [`Template`] of the image once, and loads the template into each arena.
//! The arenas then share the instructions and the other read-only data of the modules, and each holds only its own objects.
//!
//! ```text
//! let template = image::Template::new(&bytes, HOSTS.iter())?;
//! let roots = arena.mutate(|mc| template.load(mc))?;
//! ```
//!
//! # What an image is good for
//!
//! - A module in an image does not run again when the image is loaded. Its variables hold the values that they
//!   held when the image was saved. Effects that the module had outside the arena while it ran,
//!   such as calls of host functions, are not repeated either.
//! - An image is valid only for the build that saved it. [`load`] rejects an image from another build. A build is identified by its source. See
//!   [`BUILD`].
//! - An image must be one that the program itself wrote, because an image is trusted. See [`ragwort_types::gc::image`].

use ragwort_compiler::module::INTERFACE;
use ragwort_types::gc::image::{self, Exports, Kind, Known, LoadError, Loaded, SaveError, Saved};
use ragwort_types::gc::{Desc, Mutation, Value};
use ragwort_types::wire::{mix, shape_of};
use ragwort_vm::HostDef;
use ragwort_vm::image::Hosts;

/// The reason an image could not be loaded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ImageError {
    Load(LoadError),
    /// The image's code calls a host function with this name, and that function is not among the host functions given to [`load`].
    Host(String),
    /// Two different host functions given to [`load`] have this same [`HostDef::path`],
    /// so an image could not identify which of them it means.
    SameHost(&'static str),
}

fn descs() -> Vec<&'static Desc> {
    let mut descs = image::descs();
    descs.extend(ragwort_vm::image::descs());
    descs
}

fn kinds() -> Vec<Kind> {
    let mut kinds = image::KINDS.to_vec();
    kinds.extend(ragwort_vm::image::kinds());
    kinds.push(INTERFACE);
    kinds
}

/// A stamp that identifies this build of ragwort. The build script computes it as a hash of the
/// source of every ragwort crate, the crate version and the build target.
pub const BUILD: &str = env!("RAGWORT_BUILD");

/// Returns the stamp that identifies the images of this build. It combines [`BUILD`] with the shape of every
/// type that an image saves.
///
/// The shapes alone are not enough. Two builds can lay out saved data in the same way and still differ in what an image means.
/// `BUILD` does not cover the program that ragwort is built into. If that program changes what its host functions do,
/// it must keep its old and new images apart itself.
pub fn stamp() -> u64 {
    let shape = mix(image::shape(&descs(), &kinds()), ragwort_vm::image::SHAPE);
    mix(shape, shape_of(BUILD))
}

/// Serializes every object reachable from `roots` into bytes that [`load`] accepts. Run a collection first, so that dead objects are not saved.
pub fn save<'gc>(mc: &Mutation<'gc>, roots: &[Value<'gc>]) -> Result<Vec<u8>, SaveError> {
    image::save(mc, stamp(), roots, &kinds())
}

/// Works like [`save`], for an image that builds on images saved earlier. See [`image::save_linked`].
pub fn save_linked<'gc>(mc: &Mutation<'gc>, roots: &[Value<'gc>], known: &Known) -> Result<Saved<'gc>, SaveError> {
    image::save_linked(mc, stamp(), roots, &kinds(), known)
}

/// Deserializes the image in `bytes` into the arena and returns the roots that the image was
/// saved with. `hosts` are the host functions that the image's code can call.
///
/// The arena hashes with its own seed, which is random in a new arena. The image holds no seed, so two arenas that load one image do
/// not share one.
pub fn load<'gc>(mc: &Mutation<'gc>, bytes: &[u8], hosts: impl IntoIterator<Item = &'static HostDef>) -> Result<Vec<Value<'gc>>, ImageError> {
    let hosts = Hosts::new(hosts).map_err(ImageError::SameHost)?;
    image::load(mc, stamp(), bytes, &descs(), &kinds(), &hosts).map_err(|error| match hosts.missing() {
        Some(name) => ImageError::Host(name),
        None => ImageError::Load(error),
    })
}

/// An image that is ready to be loaded into many arenas of one thread. The arenas share the frozen values of the image, such as the
/// instructions of its code. See [`ragwort_types::gc::image::Template`].
pub struct Template(image::Template);

impl Template {
    /// Reads the image in `bytes`, which [`save`] wrote. `hosts` are the host functions that the image's code can call.
    pub fn new(bytes: &[u8], hosts: impl IntoIterator<Item = &'static HostDef>) -> Result<Self, ImageError> {
        let hosts = Hosts::new(hosts).map_err(ImageError::SameHost)?;
        match image::Template::new(stamp(), bytes, &kinds(), &hosts) {
            Ok(template) => Ok(Self(template)),
            Err(error) => Err(match hosts.missing() {
                Some(name) => ImageError::Host(name),
                None => ImageError::Load(error),
            }),
        }
    }

    /// Rebuilds the image's objects in the arena and returns the roots that the image was saved with. The arena must be new: a load into
    /// an arena that holds frozen values already fails. Each arena gets a hash seed of its own, as with [`load`].
    pub fn load<'gc>(&self, mc: &Mutation<'gc>) -> Result<Vec<Value<'gc>>, ImageError> {
        self.0.load(mc, &descs()).map_err(ImageError::Load)
    }

    /// Works like [`Template::load`], for an image that [`save_linked`] wrote. See [`image::Template::load_linked`].
    pub fn load_linked<'gc>(&self, mc: &Mutation<'gc>, links: &[Option<Exports<'_, 'gc>>], wanted: &[u32]) -> Result<Loaded<'gc>, ImageError> {
        self.0.load_linked(mc, &descs(), links, wanted).map_err(ImageError::Load)
    }

    /// Returns the number of frozen values that the arenas loading the template share.
    pub fn frozen_values(&self) -> usize {
        self.0.frozen_values()
    }
}

