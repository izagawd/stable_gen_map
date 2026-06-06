//! Concrete per-slot storage strategies and the clone promise they rely on.
//!
//! `boxed_slot` stores a sized payload in a `Box`; `deref_slot` stores a smart
//! pointer and exposes its `Deref` target. `clone_gen_map_promise` holds the
//! `CloneGenMapPromise` trait that stored values implement so a `GenMap` can be
//! cloned soundly.

pub mod boxed_slot;
pub mod deref_slot;
pub mod clone_gen_map_promise;
