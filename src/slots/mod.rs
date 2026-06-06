//! Concrete per-slot storage strategies.
//!
//! `boxed_slot` stores a sized payload in a `Box`; `deref_slot` stores a smart
//! pointer and exposes its `Deref` target.

pub mod boxed_slot;
pub mod deref_slot;
