//! Key types and the numeric key-piece trait.
//!
//! `key` holds the generational key types (`Key`, `KeyData`, `DefaultKey`) and
//! the `new_key_type!` macro. `key_piece` holds the `KeyPiece` trait, which
//! abstracts the unsigned-integer index and generation components a key is
//! built from.

pub mod key_piece;
pub mod key;
