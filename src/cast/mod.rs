//! Type-erased, castable maps — the nightly-only `castable` feature.
//!
//! This whole module is gated behind the `castable` feature (see the crate
//! root) and requires a nightly compiler, so its submodules are not gated
//! individually. `stable_cast_map` is the safe entry point; `unsafe_cast_map`
//! is the low-level building block; `cast_key`, `map_id`, and `retype_ptr`
//! provide the supporting key, identity, and pointer-retyping machinery.

pub mod cast_key;
pub mod map_id;
pub mod retype_ptr;
pub mod stable_cast_map;
pub mod unsafe_cast_map;
