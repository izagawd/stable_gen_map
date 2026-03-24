//! # stable_gen_map
//!
//! Single-threaded generational maps with `insert(&self)`, stable references
//! across growth, and smart-pointer support (`Box`/`Rc`/`Arc`/`&T`).
//!
//! The main types are:
//!
//! - [`StableGenMap`](stable_gen_map::StableMap) — stores each value behind
//!   a `Box` for pointer stability. The `Box` allocation is reused across
//!   remove/insert cycles.
//! - [`StableDerefGenMap`](stable_deref_gen_map::StableDerefMap) — stores a
//!   user-supplied smart pointer directly.
//! - [`KeyCastableStableGenMap`](castable_map::StableCastMap) —
//!   wraps `StableDerefGenMap` with [`CastKey`](castable_key::CastKey)
//!   support for type-erased heterogeneous storage (e.g. `Box<dyn Any>`).
//!
//! All map types allow `insert(&self)` (shared-reference insertion) while
//! keeping existing `&T` references valid. `remove` and `clear` require
//! `&mut self`, so the borrow checker prevents freeing elements while
//! outstanding references exist.
//!
//! ## Nightly requirement
//!
//! The [`CastKey`](castable_key::CastKey) family and
//! [`KeyCastableStableGenMap`](castable_map::StableCastMap) rely on
//! the nightly features `ptr_metadata`, `coerce_unsized`, and `unsize`.
//! If you don't need castable keys, those features are still required at the
//! crate level but have no effect on the core map types.

#![allow(warnings)]
#![feature(ptr_metadata)]
#![feature(coerce_unsized)]
#![feature(unsize)]

pub mod castable_key;
pub mod castable_map;
pub mod gen_map;
pub mod key;
pub mod key_piece;
pub mod map_id;
pub mod slot_item;
pub mod stable_deref_gen_map;
pub mod stable_gen_map;

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

    #[cfg(test)]
    mod castable_key_tests;

    #[cfg(test)]
    mod castable_map_tests;
}
