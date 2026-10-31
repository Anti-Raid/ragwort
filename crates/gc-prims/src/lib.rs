//! GC-backed buffers and table algorithms over host-owned storage.

pub mod map;
pub mod scratch;
pub mod vec;

pub use map::GcMap;
pub use scratch::ScratchVec;
pub use vec::GcVec;
