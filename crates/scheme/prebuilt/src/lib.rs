//! The libraries of Scheme, built when this crate is built.
//!
//! [`scheme`](ragwort_modules_core::scheme) compiles the libraries from their source. A program that calls it at every start pays for that each time, in time and in
//! memory. This crate does the work once, in its build script:
//!
//! - The build script builds and runs the libraries, and saves them as one image.
//! - [`IMAGE`] is that image, included in the program.
//! - [`load`] puts the libraries into a new arena. They have run already, so code can require them at once.
//!
//! # Example
//!
//! ```
//! use ragwort_types::gc::Arena;
//!
//! let mut arena = Arena::new(1 << 24, 0);
//! let libraries = arena.mutate(|mc| {
//!     let (_symbols, libraries) = ragwort_prebuilt_scheme::load(mc).expect("the image of this build");
//!     libraries.modules.len()
//! });
//! assert!(libraries > 1);
//! ```
//!
//! # When the image does not load
//!
//! An image loads only in a build of the same source. See [`ragwort_modules_core::image::stamp`]. The target does not matter, as long as
//! its pointers have the same width: a build script on one machine can make the image of a program for another. Between a 32-bit and a
//! 64-bit build, [`load`] fails with [`LoadError::Stamp`]. Such a program calls [`scheme`](ragwort_modules_core::scheme) instead, and runs the thunks that it returns.

#[cfg(test)]
#[path = "tests/image.rs"]
mod tests;

use ragwort_modules_core::image::{self, ImageError};
use ragwort_modules_core::Scheme;
use ragwort_types::gc::Mutation;
use ragwort_types::gc::image::LoadError;
use ragwort_types::symbol::Symbols;
use ragwort_vm::objects::Module;

/// The image of the libraries, which the build script made.
pub static IMAGE: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/scheme.img"));

/// Puts the libraries of [`IMAGE`] into the arena. Returns the arena's symbol table and the modules: each library of Scheme with its name, then
/// the `scheme` module, which passes them all on. The modules have run, so [`Scheme::thunks`] is empty.
///
/// Call this in the first step of a new arena, before anything makes a symbol table for it.
pub fn load<'gc>(mc: &Mutation<'gc>) -> Result<(Symbols<'gc>, Scheme<'gc>), ImageError> {
    read(mc, IMAGE)
}

/// Puts the libraries of the image `bytes` into the arena, as [`load`] does for [`IMAGE`]. The image holds the symbol table, then each module in the order of [`Scheme::modules`].
fn read<'gc>(mc: &Mutation<'gc>, bytes: &[u8]) -> Result<(Symbols<'gc>, Scheme<'gc>), ImageError> {
    let roots = image::load(mc, bytes, std::iter::empty())?;
    let names: Vec<&'static str> = ragwort_modules_core::libraries::scheme::LIBRARIES.iter().map(|library| library.name).chain(["scheme"]).collect();
    let [symbols, saved @ ..] = roots.as_slice() else { return Err(ImageError::Load(LoadError::Malformed)) };
    let symbols = Symbols::of(*symbols).ok_or(ImageError::Load(LoadError::Malformed))?;
    if saved.len() != names.len() {
        return Err(ImageError::Load(LoadError::Malformed));
    }
    let mut modules = Vec::with_capacity(names.len());
    for (name, value) in names.into_iter().zip(saved) {
        let module = value.downcast::<Module>(mc).ok_or(ImageError::Load(LoadError::Malformed))?;
        modules.push((name, module));
    }
    Ok((symbols, Scheme { modules, thunks: Vec::new() }))
}
