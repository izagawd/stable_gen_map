//! The generational-map engine and the slot-storage trait it is built on.
//!
//! `gen_map` contains `GenMap` (the core map) and `Slot`. `slot_storage`
//! contains the `SlotStorage` trait family that abstracts how each slot stores
//! its payload; the concrete strategies live in the `slots` module.

pub mod gen_map;
pub mod slot_storage;
