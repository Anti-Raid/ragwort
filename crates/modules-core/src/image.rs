//! Saving what's loaded, to load it again without compiling or running it.
//!
//! An image holds values and everything they reach: modules that have run, with their code
//! and what their variables hold. Loading one into a new arena leaves it as the arena that
//! saved it was, so code loaded after is compiled against the image's modules as it would be
//! against ones just built.
//!
//! ```text
//! let bytes = arena.mutate(|mc| image::save(mc, &[symbols, prelude, library]))?;
//! // In another arena, or another run of the program:
//! let roots = arena.mutate(|mc| image::load(mc, &bytes, HOSTS.iter()))?;
//! ```
//!
//! # What an image is good for
//!
//! - A module in it isn't run again when it's loaded: what its variables hold is what they
//!   held when it was saved. What the module did to the world outside the arena as it ran,
//!   such as a call of a host function, isn't done again either.
//! - It's for the build that saved it: [`load`] refuses another's. A build is its source: see
//!   [`BUILD`].
//! - It's to be one the program wrote itself: see [`ragwort_types::gc::image`].

use ragwort_compiler::module::INTERFACE;
use ragwort_types::gc::image::{self, Kind, LoadError, SaveError};
use ragwort_types::gc::{Desc, Mutation, Value};
use ragwort_types::wire::{mix, shape_of};
use ragwort_vm::HostDef;
use ragwort_vm::image::Hosts;

/// Why an image can't be loaded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ImageError {
    Load(LoadError),
    /// Its code calls a host function of this name that isn't among the ones given.
    Host(String),
    /// Two different host functions among the ones given are at this one place in the program,
    /// so an image couldn't say which it means: see [`HostDef::path`].
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

/// What tells this build of ragwort from any other: a number its build script makes of the
/// source of every ragwort crate and what the build is for.
pub const BUILD: &str = env!("RAGWORT_BUILD");

/// What tells this build's images from another's: [`BUILD`], with the shape of everything
/// that's saved.
///
/// The shapes alone would let through a build whose source differs in what an image means
/// and not in how it's laid out. `BUILD` doesn't know of the program ragwort is built into:
/// one whose host functions change what they do keeps its own images apart.
pub fn stamp() -> u64 {
    let shape = mix(image::shape(&descs(), &kinds()), ragwort_vm::image::SHAPE);
    mix(shape, shape_of(BUILD))
}

/// Everything `roots` reach, as bytes for [`load`]. Collect first, so what's dead isn't saved.
pub fn save<'gc>(mc: &Mutation<'gc>, roots: &[Value<'gc>]) -> Result<Vec<u8>, SaveError> {
    image::save(mc, stamp(), roots, &kinds())
}

/// Makes what `bytes` hold, in an arena with no symbols yet, and gives the roots they were
/// saved with. `hosts` are the host functions the image's code can call.
pub fn load<'gc>(mc: &Mutation<'gc>, bytes: &[u8], hosts: impl IntoIterator<Item = &'static HostDef>) -> Result<Vec<Value<'gc>>, ImageError> {
    let hosts = Hosts::new(hosts).map_err(ImageError::SameHost)?;
    image::load(mc, stamp(), bytes, &descs(), &kinds(), &hosts).map_err(|e| match hosts.missing() {
        Some(name) => ImageError::Host(name),
        None => ImageError::Load(e),
    })
}
