//! # stable_gen_map
//!
//! Single-threaded generational maps with `insert(&self)`, stable references
//! across growth, and smart-pointer support (`Box`/`Rc`/`Arc`/`&T`).
//!
//! The main types are:
//!
//! - [`StableMap`](stable_map::StableMap) — stores each value behind
//!   a `Box` for pointer stability. The `Box` allocation is reused across
//!   remove/insert cycles.
//! - [`StableDerefMap`](stable_deref_map::StableDerefMap) — stores a
//!   user-supplied smart pointer directly.
//! - **`StableCastMap`** *(requires the `castable` feature)* —
//!   wraps `StableDerefMap` with `CastKey`
//!   support for type-erased heterogeneous storage (e.g. `Box<dyn Any>`).
//!
//! All map types allow `insert(&self)` (shared-reference insertion) while
//! keeping existing `&T` references valid. `remove` and `clear` require
//! `&mut self`, so the borrow checker prevents freeing elements while
//! outstanding references exist.
//!
//! ## The `castable` feature (nightly only)
//!
//! The `CastKey` family and `StableCastMap` rely on the nightly features
//! `ptr_metadata`, `coerce_unsized`, and `unsize`. They are gated behind
//! the **`castable`** cargo feature, which is **not** enabled by default.
//!
//! To enable cast keys (requires nightly):
//!
//! ```toml
//! [dependencies]
//! stable_gen_map = { version = "0.12", features = ["castable"] }
//! ```

#![allow(warnings)]
#![cfg_attr(feature = "castable", feature(ptr_metadata))]
#![cfg_attr(feature = "castable", feature(coerce_unsized))]
#![cfg_attr(feature = "castable", feature(unsize))]

#[cfg(feature = "castable")]
pub mod cast_key;
pub mod gen_map;
pub mod key;
pub mod key_piece;
pub mod map_id;
pub mod slot_item;
#[cfg(feature = "castable")]
pub mod stable_cast_map;
pub mod stable_deref_map;
pub mod stable_map;

#[cfg(test)]
mod tests {
    #[cfg(test)]
    mod stable_deref_gen_retain_tests;

    #[cfg(test)]
    mod stable_gen_retain_tests;

    #[cfg(test)]
    mod stable_deref_gen_map_tests;
    #[cfg(test)]
    mod stable_gen_clone_tests;

    #[cfg(test)]
    mod stable_deref_gen_clone_tests;

    #[cfg(test)]
    mod stable_gen_map_tests;

    #[cfg(test)]
    mod stable_deref_gen_map_overflow_tests;

    #[cfg(test)]
    mod stable_gen_map_overflow_tests;

    #[cfg(test)]
    mod key_macro_tests;

    #[cfg(test)]
    mod stable_gen_snapshot_tests;

    #[cfg(test)]
    mod stable_deref_gen_snapshot_tests;

    #[cfg(test)]
    mod stable_gen_drain_tests;

    #[cfg(test)]
    mod stable_deref_gen_drain_tests;

    #[cfg(test)]
    mod map_id_tests;

    #[cfg(all(test, feature = "castable"))]
    mod castable_key_tests;

    #[cfg(all(test, feature = "castable"))]
    mod castable_map_tests;

    #[cfg(all(test, feature = "castable"))]
    mod castable_key_macro_tests;

    #[cfg(all(test, feature = "castable"))]
    mod custom_inner_key_tests;
}
