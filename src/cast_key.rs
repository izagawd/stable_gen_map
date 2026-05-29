//! Castable key types for use with [`UnsafeCastMap`](crate::unsafe_cast_map::UnsafeCastMap)
//! and [`StableCastMap`](crate::stable_cast_map::StableCastMap).
//!
//! - [`CastKey<T, K>`] stores pointer metadata alongside a generational index.
//!   It is the bare key used by `UnsafeCastMap`.
//! - [`StableCastKey<T, K>`] wraps a `CastKey` and adds a [`MapId`](crate::map_id::MapId),
//!   making it safe to use with `StableCastMap` (cross-map misuse returns `None`).
//!
//! Neither `CastKey` nor `StableCastKey` is a [`Key`](crate::key::Key).
//! The cast map wrappers handle conversion at the boundary.
//!
//! # Sizes (64-bit)
//! - `CastKey<SizedType>`: 8 bytes (KeyData only, metadata is `()`)
//! - `CastKey<dyn Trait>`: 16 bytes (KeyData + vtable pointer)
//! - `StableCastKey<T, K>`: `CastKey<T, K>` + 8 bytes (MapId)

use std::ptr::Pointee;

use crate::key::{DefaultKey, Key, KeyData};

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
    /// `metadata` must be valid for the allocation identified by the key.
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

// ─── StableCastKey<T, K> ─────────────────────────────────────────────────

/// A [`CastKey`] paired with a [`MapId`](crate::map_id::MapId) so that
/// cross-map misuse is caught at runtime rather than being UB.
pub struct StableCastKey<T: ?Sized + Pointee, K: Key = DefaultKey>
where
    <T as Pointee>::Metadata: Copy,
{
    pub(crate) inner: CastKey<T, K>,
    pub(crate) map_id: crate::map_id::MapId,
}

// ── Manual trait impls ──────────────────────────────────────────────────

impl<T: ?Sized + Pointee, K: Key> Clone for StableCastKey<T, K>
where
    <T as Pointee>::Metadata: Copy,
{
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized + Pointee, K: Key> Copy for StableCastKey<T, K> where <T as Pointee>::Metadata: Copy {}

impl<T: ?Sized + Pointee, K: Key> std::fmt::Debug for StableCastKey<T, K>
where
    <T as Pointee>::Metadata: Copy,
    KeyData<K::Idx, K::Gen>: std::fmt::Debug,
{
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StableCastKey")
            .field("key_data", &self.inner.key_data)
            .field("map_id", &self.map_id)
            .finish()
    }
}

impl<T: ?Sized + Pointee, K: Key> PartialEq for StableCastKey<T, K>
where
    <T as Pointee>::Metadata: Copy,
    KeyData<K::Idx, K::Gen>: PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.inner.key_data == other.inner.key_data && self.map_id == other.map_id
    }
}

impl<T: ?Sized + Pointee, K: Key> Eq for StableCastKey<T, K>
where
    <T as Pointee>::Metadata: Copy,
    KeyData<K::Idx, K::Gen>: Eq,
{
}

impl<T: ?Sized + Pointee, K: Key> std::hash::Hash for StableCastKey<T, K>
where
    <T as Pointee>::Metadata: Copy,
    KeyData<K::Idx, K::Gen>: std::hash::Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.inner.key_data.hash(state);
        self.map_id.hash(state);
    }
}

// ── Methods ────────────────────────────────────────────────────────────

impl<T: ?Sized + Pointee, K: Key> StableCastKey<T, K>
where
    <T as Pointee>::Metadata: Copy,
{
    /// Constructs a `StableCastKey` from its raw cast key and map id.
    ///
    /// # Safety
    /// The caller must ensure that `map_id` identifies the map that owns the slot
    /// addressed by `cast_key.inner_key()`, and that the metadata is valid for `T`.
    #[inline]
    pub unsafe fn from_parts(cast_key: CastKey<T, K>, map_id: crate::map_id::MapId) -> Self {
        StableCastKey {
            inner: cast_key,
            map_id,
        }
    }

    /// Returns the generational key data.
    #[inline]
    pub fn key_data(&self) -> KeyData<K::Idx, K::Gen> {
        self.inner.key_data
    }

    /// Returns the pointer metadata for `T`.
    #[inline]
    pub fn metadata(&self) -> <T as Pointee>::Metadata {
        self.inner.metadata
    }

    /// Returns the map identity this key is bound to.
    #[inline]
    pub fn map_id(&self) -> crate::map_id::MapId {
        self.map_id
    }

    /// Strips pointer metadata and map id, producing the backing [`Key`].
    #[inline]
    pub fn inner_key(&self) -> K {
        self.inner.inner_key()
    }

    /// Returns the underlying [`CastKey`] without the map id.
    #[inline]
    pub fn cast_key(&self) -> CastKey<T, K> {
        self.inner
    }

    /// Upcasts the key's metadata from `T` to `U` where `T: Unsize<U>`.
    ///
    /// The map id is preserved.
    #[inline]
    pub fn upcast<U: ?Sized + Pointee>(self) -> StableCastKey<U, K>
    where
        T: std::marker::Unsize<U>,
        <U as Pointee>::Metadata: Copy,
    {
        StableCastKey {
            inner: self.inner.upcast(),
            map_id: self.map_id,
        }
    }
}
