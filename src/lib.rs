#![cfg_attr(feature = "castable", feature(ptr_metadata))]
#![cfg_attr(feature = "castable", feature(coerce_unsized))]
#![cfg_attr(feature = "castable", feature(unsize))]

// Module tree
// ===========
// The public module *paths* are deliberately kept flat (`stable_gen_map::key`,
// `stable_gen_map::gen_map`, `stable_gen_map::boxed_slot`, …) so that existing
// imports, the intra-doc links in this crate's docs, the `new_key_type!` macro
// (which expands to `$crate::key::…`), and downstream users all keep working
// unchanged. The source files are grouped into folders purely for navigation,
// and each module is pointed at its file with `#[path]`:
//
//   keys/     key types and the numeric key-piece trait (+ castable keys / map ids)
//   core/     the generational-map engine and its slot-storage abstraction
//   storage/  concrete per-slot storage strategies and the clone promise they use
//   cast/     the nightly `castable` layer: type-erased maps and pointer re-typing

// ─── keys ────────────────────────────────────────────────────────────────────
#[path = "keys/key_piece.rs"]
pub mod key_piece;
#[path = "keys/key.rs"]
pub mod key;
#[cfg(feature = "castable")]
#[path = "keys/cast_key.rs"]
pub mod cast_key;
#[cfg(feature = "castable")]
#[path = "keys/map_id.rs"]
pub mod map_id;

// ─── core engine ─────────────────────────────────────────────────────────────
#[path = "core/gen_map.rs"]
pub mod gen_map;
#[path = "core/slot_storage.rs"]
pub mod slot_storage;

// ─── storage strategies ──────────────────────────────────────────────────────
#[path = "storage/boxed_slot.rs"]
pub mod boxed_slot;
#[path = "storage/deref_slot.rs"]
pub mod deref_slot;
#[path = "storage/clone_gen_map_promise.rs"]
pub mod clone_gen_map_promise;

// ─── cast layer (nightly `castable` feature) ─────────────────────────────────
#[cfg(feature = "castable")]
#[path = "cast/stable_cast_map.rs"]
pub mod stable_cast_map;
#[cfg(feature = "castable")]
#[path = "cast/unsafe_cast_map.rs"]
pub mod unsafe_cast_map;
#[cfg(feature = "castable")]
#[path = "cast/retype_ptr.rs"]
pub mod retype_ptr;

pub use boxed_slot::{BoxedSlot, StableGenMap};
pub use deref_slot::{BoxStableDerefMap, DerefSlot, StableDerefMap};
pub use gen_map::{GenMap, Slot};
pub use key::{DefaultKey, Key, KeyData};

// `castable` feature (nightly only).
#[cfg(feature = "castable")]
pub use cast_key::{CastKey, StableCastKey};
#[cfg(feature = "castable")]
pub use map_id::MapId;
#[cfg(feature = "castable")]
pub use stable_cast_map::{StableBoxCastMap, StableCastMap};
#[cfg(feature = "castable")]
pub use unsafe_cast_map::{UnsafeBoxCastMap, UnsafeCastMap};

#[cfg(test)]
mod tests {
    // ─── StableGenMap (boxed-slot) tests ─────────────────────────────────────
    #[cfg(test)]
    #[path = "gen/stable_gen_map_tests.rs"]
    mod stable_gen_map_tests;

    #[cfg(test)]
    #[path = "gen/stable_gen_map_overflow_tests.rs"]
    mod stable_gen_map_overflow_tests;

    #[cfg(test)]
    #[path = "gen/stable_gen_clone_tests.rs"]
    mod stable_gen_clone_tests;

    #[cfg(test)]
    #[path = "gen/stable_gen_drain_tests.rs"]
    mod stable_gen_drain_tests;

    #[cfg(test)]
    #[path = "gen/stable_gen_retain_tests.rs"]
    mod stable_gen_retain_tests;

    #[cfg(test)]
    #[path = "gen/stable_gen_snapshot_tests.rs"]
    mod stable_gen_snapshot_tests;

    #[cfg(test)]
    #[path = "gen/gen_map_reset_tests.rs"]
    mod gen_map_reset_tests;

    // ─── StableDerefMap tests ────────────────────────────────────────────────
    #[cfg(test)]
    #[path = "deref/stable_deref_gen_map_tests.rs"]
    mod stable_deref_gen_map_tests;

    #[cfg(test)]
    #[path = "deref/stable_deref_gen_map_overflow_tests.rs"]
    mod stable_deref_gen_map_overflow_tests;

    #[cfg(test)]
    #[path = "deref/stable_deref_gen_clone_tests.rs"]
    mod stable_deref_gen_clone_tests;

    #[cfg(test)]
    #[path = "deref/stable_deref_gen_drain_tests.rs"]
    mod stable_deref_gen_drain_tests;

    #[cfg(test)]
    #[path = "deref/stable_deref_gen_retain_tests.rs"]
    mod stable_deref_gen_retain_tests;

    #[cfg(test)]
    #[path = "deref/stable_deref_gen_snapshot_tests.rs"]
    mod stable_deref_gen_snapshot_tests;

    // ─── cross-cutting tests ─────────────────────────────────────────────────
    #[cfg(test)]
    #[path = "common/pointer_stability_tests.rs"]
    mod pointer_stability_tests;

    #[cfg(test)]
    #[path = "common/key_macro_tests.rs"]
    mod key_macro_tests;

    #[cfg(test)]
    #[path = "common/unchecked_tests.rs"]
    mod unchecked_tests;

    // ─── castable-feature tests (nightly only) ───────────────────────────────
    #[cfg(all(test, feature = "castable"))]
    #[path = "castable/map_id_tests.rs"]
    mod map_id_tests;

    #[cfg(all(test, feature = "castable"))]
    #[path = "castable/castable_key_tests.rs"]
    mod castable_key_tests;

    #[cfg(all(test, feature = "castable"))]
    #[path = "castable/castable_map_tests.rs"]
    mod castable_map_tests;

    #[cfg(all(test, feature = "castable"))]
    #[path = "castable/castable_reset_tests.rs"]
    mod castable_reset_tests;

    #[cfg(all(test, feature = "castable"))]
    #[path = "castable/castable_insert_typed_tests.rs"]
    mod castable_insert_typed_tests;

    #[cfg(all(test, feature = "castable"))]
    #[path = "castable/castable_unchecked_tests.rs"]
    mod castable_unchecked_tests;

    #[cfg(all(test, feature = "castable"))]
    #[path = "castable/castable_pointer_stability_tests.rs"]
    mod castable_pointer_stability_tests;
}
