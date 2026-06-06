#![cfg_attr(feature = "castable", feature(ptr_metadata))]
#![cfg_attr(feature = "castable", feature(coerce_unsized))]
#![cfg_attr(feature = "castable", feature(unsize))]

// Module tree
// ===========
// Files are grouped into folders that mirror the public module hierarchy
// (folder == module), so the source layout and the module paths line up:
//
//   keys/     key types and the numeric key-piece trait
//   core/     the generational-map engine and the slot-storage trait
//   slots/    concrete per-slot storage strategies and the clone promise
//   cast/     the nightly `castable` layer (type-erased maps), gated as a whole
//
// The most commonly used types are re-exported at the crate root below, so the
// typical user can write `stable_gen_map::StableGenMap` / `DefaultKey` etc.

pub mod keys;
pub mod core;
pub mod slots;

// `castable` feature (nightly only). Gating the whole `cast` module here means
// its submodules need no individual `#[cfg]`.
#[cfg(feature = "castable")]
pub mod cast;

pub use slots::boxed_slot::{BoxedSlot, StableGenMap};
pub use slots::deref_slot::{BoxStableDerefMap, DerefSlot, StableDerefMap};
pub use core::gen_map::{GenMap, Slot};
pub use keys::key::{DefaultKey, Key, KeyData};

// `castable` feature (nightly only).
#[cfg(feature = "castable")]
pub use cast::cast_key::{CastKey, StableCastKey};
#[cfg(feature = "castable")]
pub use cast::map_id::MapId;
#[cfg(feature = "castable")]
pub use cast::stable_cast_map::{StableBoxCastMap, StableCastMap};
#[cfg(feature = "castable")]
pub use cast::unsafe_cast_map::{UnsafeBoxCastMap, UnsafeCastMap};

#[cfg(test)]
mod tests {
    mod gen;
    mod deref;
    mod common;

    #[cfg(feature = "castable")]
    mod castable;
}
