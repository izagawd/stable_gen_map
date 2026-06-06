//! The generational-map engine, the slot-storage trait it is built on, and the
//! clone-soundness contract for stored values.
//!
//! `gen_map` contains `GenMap` (the core map) and `Slot`. `slot_storage`
//! contains the `SlotStorage` trait family that abstracts how each slot stores
//! its payload (concrete strategies live in the `slots` module).
//! `clone_gen_map_promise` holds the `CloneGenMapPromise` trait that stored
//! values implement so a `GenMap` can be cloned soundly.

pub mod clone_gen_map_promise;
pub mod gen_map;
pub mod slot_storage;
