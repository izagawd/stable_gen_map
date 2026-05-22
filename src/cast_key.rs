//! Castable key type that is generic over `T: ?Sized`, storing
//! pointer metadata alongside a generational index.
//!
//! `CastKey` is **not** a [`Key`](crate::key::Key). The inner
//! `GenMap` uses a plain [`DefaultMapKey`]; the castable map wrapper
//! converts at the boundary.
//!
//! # Sizes (64-bit)
//! - `CastKey<SizedType>`: 8 bytes (KeyData only, metadata is `()`)
//! - `CastKey<dyn Trait>`: 16 bytes (KeyData + vtable pointer)

use std::ptr::Pointee;

use crate::key::{Key, KeyData};
use crate::key_piece::KeyPiece;

// ─── DefaultMapKey ──────────────────────────────────────────────────────────

/// A plain key used as the inner key for cast maps — just key_data.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct DefaultMapKey<Idx, Gen> {
    pub(crate) key_data: KeyData<Idx, Gen>,
}

impl<Idx: Copy + KeyPiece, Gen: Copy + KeyPiece> From<KeyData<Idx, Gen>>
    for DefaultMapKey<Idx, Gen>
{
    fn from(key_data: KeyData<Idx, Gen>) -> Self {
        Self { key_data }
    }
}

unsafe impl<Idx: Copy + KeyPiece, Gen: Copy + KeyPiece> Key for DefaultMapKey<Idx, Gen> {
    type Idx = Idx;
    type Gen = Gen;

    #[inline]
    fn data(&self) -> KeyData<Idx, Gen> {
        self.key_data
    }
}

// ─── CastKey<T, Idx, Gen> ──────────────────────────────────────────────

/// A key parameterised over `T: ?Sized` that stores `T`'s pointer
/// metadata alongside a generational index.
///
/// The index and generation types default to `u32`.
pub struct CastKey<T: ?Sized + Pointee, Idx = u32, Gen = u32>
where
    <T as Pointee>::Metadata: Copy,
{
    pub(crate) key_data: KeyData<Idx, Gen>,
    pub(crate) metadata: <T as Pointee>::Metadata,
}

// ── Manual trait impls ──────────────────────────────────────────────────

impl<T: ?Sized + Pointee, Idx: Copy, Gen: Copy> Clone for CastKey<T, Idx, Gen>
where
    <T as Pointee>::Metadata: Copy,
{
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized + Pointee, Idx: Copy, Gen: Copy> Copy for CastKey<T, Idx, Gen> where
    <T as Pointee>::Metadata: Copy
{
}

impl<T: ?Sized + Pointee, Idx, Gen> std::fmt::Debug for CastKey<T, Idx, Gen>
where
    <T as Pointee>::Metadata: Copy,
    KeyData<Idx, Gen>: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CastKey")
            .field("key_data", &self.key_data)
            .finish()
    }
}

impl<T: ?Sized + Pointee, Idx, Gen> PartialEq for CastKey<T, Idx, Gen>
where
    <T as Pointee>::Metadata: Copy,
    KeyData<Idx, Gen>: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.key_data == other.key_data
    }
}

impl<T: ?Sized + Pointee, Idx, Gen> Eq for CastKey<T, Idx, Gen>
where
    <T as Pointee>::Metadata: Copy,
    KeyData<Idx, Gen>: Eq,
{
}

impl<T: ?Sized + Pointee, Idx, Gen> std::hash::Hash for CastKey<T, Idx, Gen>
where
    <T as Pointee>::Metadata: Copy,
    KeyData<Idx, Gen>: std::hash::Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.key_data.hash(state);
    }
}

// ── Methods ────────────────────────────────────────────────────────────

impl<T: ?Sized + Pointee, Idx: Copy + KeyPiece, Gen: Copy + KeyPiece> CastKey<T, Idx, Gen>
where
    <T as Pointee>::Metadata: Copy,
{
    /// Returns the generational key data.
    #[inline]
    pub fn key_data(&self) -> KeyData<Idx, Gen> {
        self.key_data
    }

    /// Returns the pointer metadata for `T`.
    #[inline]
    pub fn metadata(&self) -> <T as Pointee>::Metadata {
        self.metadata
    }

    /// Strips pointer metadata, producing the inner key used by
    /// the backing `GenMap`.
    #[inline]
    pub fn inner_key(&self) -> DefaultMapKey<Idx, Gen> {
        DefaultMapKey {
            key_data: self.key_data,
        }
    }

    /// Upcasts the key's metadata from `T` to `U` where `T: Unsize<U>`.
    ///
    /// This enables converting e.g. `CastKey<Dog>` to `CastKey<dyn Any>`
    /// without needing a data pointer.
    #[inline]
    pub fn upcast<U: ?Sized + Pointee>(self) -> CastKey<U, Idx, Gen>
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
        data: KeyData<Idx, Gen>,
        metadata: <T as Pointee>::Metadata,
    ) -> Self {
        Self {
            key_data: data,
            metadata,
        }
    }

    /// Build a cast key from an inner key and pointer metadata.
    ///
    /// # Safety
    /// `metadata` must be valid for the allocation identified by `inner`.
    #[inline]
    pub unsafe fn from_inner_key_and_metadata(
        inner: DefaultMapKey<Idx, Gen>,
        metadata: <T as Pointee>::Metadata,
    ) -> Self {
        Self {
            key_data: inner.key_data,
            metadata,
        }
    }
}

// ─── StableCastKey<T, Idx, Gen> ────────────────────────────────────────

/// A [`CastKey`] paired with a [`MapId`](crate::map_id::MapId) so that
/// cross-map misuse is caught at runtime rather than being UB.
pub struct StableCastKey<T: ?Sized + Pointee, Idx = u32, Gen = u32>
where
    <T as Pointee>::Metadata: Copy,
{
    pub(crate) inner: CastKey<T, Idx, Gen>,
    pub(crate) map_id: crate::map_id::MapId,
}

// ── Manual trait impls ──────────────────────────────────────────────────

impl<T: ?Sized + Pointee, Idx: Copy, Gen: Copy> Clone for StableCastKey<T, Idx, Gen>
where
    <T as Pointee>::Metadata: Copy,
{
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized + Pointee, Idx: Copy, Gen: Copy> Copy for StableCastKey<T, Idx, Gen> where
    <T as Pointee>::Metadata: Copy
{
}

impl<T: ?Sized + Pointee, Idx, Gen> std::fmt::Debug for StableCastKey<T, Idx, Gen>
where
    <T as Pointee>::Metadata: Copy,
    KeyData<Idx, Gen>: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StableCastKey")
            .field("key_data", &self.inner.key_data)
            .field("map_id", &self.map_id)
            .finish()
    }
}

impl<T: ?Sized + Pointee, Idx, Gen> PartialEq for StableCastKey<T, Idx, Gen>
where
    <T as Pointee>::Metadata: Copy,
    KeyData<Idx, Gen>: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.inner.key_data == other.inner.key_data && self.map_id == other.map_id
    }
}

impl<T: ?Sized + Pointee, Idx, Gen> Eq for StableCastKey<T, Idx, Gen>
where
    <T as Pointee>::Metadata: Copy,
    KeyData<Idx, Gen>: Eq,
{
}

impl<T: ?Sized + Pointee, Idx, Gen> std::hash::Hash for StableCastKey<T, Idx, Gen>
where
    <T as Pointee>::Metadata: Copy,
    KeyData<Idx, Gen>: std::hash::Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.inner.hash(state);
        self.map_id.hash(state);
    }
}

// ── Methods ────────────────────────────────────────────────────────────

impl<T: ?Sized + Pointee, Idx: Copy + KeyPiece, Gen: Copy + KeyPiece> StableCastKey<T, Idx, Gen>
where
    <T as Pointee>::Metadata: Copy,
{
    /// Returns the generational key data.
    #[inline]
    pub fn key_data(&self) -> KeyData<Idx, Gen> {
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

    /// Strips pointer metadata and map id, producing the inner key used by
    /// the backing `GenMap`.
    #[inline]
    pub fn inner_key(&self) -> DefaultMapKey<Idx, Gen> {
        self.inner.inner_key()
    }

    /// Returns the underlying [`CastKey`] without the map id.
    #[inline]
    pub fn cast_key(&self) -> CastKey<T, Idx, Gen> {
        self.inner
    }

    /// Upcasts the key's metadata from `T` to `U` where `T: Unsize<U>`.
    ///
    /// The map id is preserved.
    #[inline]
    pub fn upcast<U: ?Sized + Pointee>(self) -> StableCastKey<U, Idx, Gen>
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
