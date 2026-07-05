//! The castable key type for [`UnsafeCastMap`](crate::cast::unsafe_cast_map::UnsafeCastMap)
//! and [`StableCastMap`](crate::cast::stable_cast_map::StableCastMap).
//!
//! [`CastKey<T, K>`] stores `T`'s pointer metadata alongside a generational
//! index. It is the only key type used by both maps: `UnsafeCastMap` exposes it
//! through `unsafe` lookups, while `StableCastMap` makes the same key safe by
//! checking each slot's stored [`TypeId`](std::any::TypeId) before trusting the
//! metadata. There is no separate "stable" key — the safety lives in the map.
//!
//! `CastKey` is not a [`Key`](crate::keys::key::Key); the cast maps convert at
//! the boundary via [`CastKey::inner_key`].
//!
//! # Sizes (64-bit)
//! - `CastKey<SizedType>`: 8 bytes (KeyData only, metadata is `()`)
//! - `CastKey<dyn Trait>`: 16 bytes (KeyData + vtable pointer)

use std::ptr::Pointee;

use crate::keys::key::{DefaultKey, Key, KeyData};

// ─── CastKey<T, K> ──────────────────────────────────────────────────────

/// A key parameterized over `T: ?Sized` that stores `T`'s pointer
/// metadata alongside a generational index.
///
/// The index and generation types default to `u32`.
///
/// `K` is the backing key type (defaults to [`DefaultKey`]).
pub struct CastKey<T: ?Sized + Pointee, K: Key = DefaultKey>
where
    <T as Pointee>::Metadata: Copy,
{
    pub(crate) key_data: KeyData<K::Idx, K::Gen>,
    pub(crate) metadata: <T as Pointee>::Metadata,
}

// ── Manual trait impls ──────────────────────────────────────────────────

impl<T: ?Sized + Pointee, K: Key> Clone for CastKey<T, K>
where
    <T as Pointee>::Metadata: Copy,
{
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized + Pointee, K: Key> Copy for CastKey<T, K> where <T as Pointee>::Metadata: Copy {}

impl<T: ?Sized + Pointee, K: Key> std::fmt::Debug for CastKey<T, K>
where
    <T as Pointee>::Metadata: Copy,
    KeyData<K::Idx, K::Gen>: std::fmt::Debug,
{
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CastKey")
            .field("key_data", &self.key_data)
            .finish()
    }
}

impl<T: ?Sized + Pointee, K: Key> PartialEq for CastKey<T, K>
where
    <T as Pointee>::Metadata: Copy,
    KeyData<K::Idx, K::Gen>: PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.key_data == other.key_data
    }
}

impl<T: ?Sized + Pointee, K: Key> Eq for CastKey<T, K>
where
    <T as Pointee>::Metadata: Copy,
    KeyData<K::Idx, K::Gen>: Eq,
{
}

impl<T: ?Sized + Pointee, K: Key> std::hash::Hash for CastKey<T, K>
where
    <T as Pointee>::Metadata: Copy,
    KeyData<K::Idx, K::Gen>: std::hash::Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.key_data.hash(state);
    }
}

// ── Methods ────────────────────────────────────────────────────────────

impl<T: ?Sized + Pointee, K: Key> CastKey<T, K>
where
    <T as Pointee>::Metadata: Copy,
{
    /// Returns the generational key data.
    #[inline]
    pub fn key_data(&self) -> KeyData<K::Idx, K::Gen> {
        self.key_data
    }

    /// Returns the pointer metadata for `T`.
    #[inline]
    pub fn metadata(&self) -> <T as Pointee>::Metadata {
        self.metadata
    }

    /// Strips pointer metadata, producing the backing [`Key`] used by
    /// the `GenMap`.
    #[inline]
    pub fn inner_key(&self) -> K {
        K::from(self.key_data)
    }

    /// Upcasts the key's metadata from `T` to `U` where `T: Unsize<U>`.
    ///
    /// This enables converting e.g. `CastKey<Dog>` to `CastKey<dyn Any>`
    /// without needing a data pointer.
    #[inline]
    pub fn upcast<U: ?Sized + Pointee>(self) -> CastKey<U, K>
    where
        T: std::marker::Unsize<U>,
        <U as Pointee>::Metadata: Copy,
    {
        let dummy: *const T = std::ptr::from_raw_parts(std::ptr::null::<()>(), self.metadata);
        let upcast: *const U = dummy;
        CastKey {
            key_data: self.key_data,
            metadata: std::ptr::metadata(upcast),
        }
    }

    /// Build a cast key from raw parts.
    ///
    /// # Safety
    /// - `metadata` must be valid for the allocation identified by the key.
    /// - `data`'s generation must be one that a map actually issued for an
    ///   occupied slot (i.e. odd/"live"). `StableCastMap` relies on a generation
    ///   match implying occupancy before it reads a slot's stored type id; a
    ///   forged even generation that collides with a vacant slot would make that
    ///   read unsound.
    #[inline]
    pub unsafe fn from_parts(
        data: KeyData<K::Idx, K::Gen>,
        metadata: <T as Pointee>::Metadata,
    ) -> Self {
        Self {
            key_data: data,
            metadata,
        }
    }
}