//! Type-erased, castable maps — the nightly-only `castable` feature.
//!
//! This whole module is gated behind the `castable` feature (see the crate
//! root) and requires a nightly compiler, so its submodules are not gated
//! individually. `stable_cast_map` is the safe entry point; `unsafe_cast_map`
//! is the low-level building block. `cast_key` provides the key, `any_haver`
//! the metadata→`TypeId` recovery used for safe lookups, `cast_box` the custom
//! owning box that carries each value's concrete type id, and `retype_ptr` the
//! pointer-retyping machinery.

pub mod any_haver;
pub mod cast_box;
pub mod cast_key;
pub mod retype_ptr;
pub mod stable_cast_map;
pub mod unsafe_cast_map;
