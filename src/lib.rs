// Module tree
// ===========
// Files are grouped into folders that mirror the public module hierarchy
// (folder == module), so the source layout and the module paths line up:
//
//   keys/     key types and the numeric key-piece trait
//   core/     the generational-map engine and the slot-storage trait
//   slots/    concrete per-slot storage strategies (boxed / deref)
//
// The most commonly used types are re-exported at the crate root below, so the
// typical user can write `stable_gen_map::StableGenMap` / `DefaultKey` etc.

pub mod core;
pub mod keys;
pub mod slots;

pub use core::gen_map::{GenMap, Slot};
pub use keys::key::{DefaultKey, Key, KeyData};
pub use slots::boxed_slot::{BoxedSlot, StableGenMap};
pub use slots::deref_slot::{BoxStableDerefMap, DerefSlot, StableDerefMap};

#[cfg(test)]
mod tests {
    mod common;
    mod deref;
    mod gen;
}
