#![cfg_attr(feature = "castable", feature(ptr_metadata))]
#![cfg_attr(feature = "castable", feature(coerce_unsized))]
#![cfg_attr(feature = "castable", feature(unsize))]

pub mod boxed_slot;
#[cfg(feature = "castable")]
pub mod cast_key;
pub mod clone_gen_map_promise;
pub mod deref_slot;
pub mod gen_map;
pub mod key;
pub mod key_piece;
#[cfg(feature = "castable")]
pub mod map_id;
pub mod slot_storage;
#[cfg(feature = "castable")]
pub mod stable_cast_map;
#[cfg(feature = "castable")]
pub mod unsafe_cast_map;

#[cfg(feature = "castable")]
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

    #[cfg(all(test, feature = "castable"))]
    mod map_id_tests;

    #[cfg(all(test, feature = "castable"))]
    mod castable_key_tests;

    #[cfg(all(test, feature = "castable"))]
    mod castable_map_tests;

    #[cfg(all(test, feature = "castable"))]
    mod castable_reset_tests;

    #[cfg(test)]
    mod gen_map_reset_tests;

    #[cfg(all(test, feature = "castable"))]
    mod castable_insert_typed_tests;

    #[cfg(test)]
    mod unchecked_tests;

    #[cfg(all(test, feature = "castable"))]
    mod castable_unchecked_tests;

    #[cfg(test)]
    mod pointer_stability_tests;

    #[cfg(all(test, feature = "castable"))]
    mod castable_pointer_stability_tests;
}
