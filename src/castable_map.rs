//! Map type that uses a castable key family, storing smart pointers
//! whose deref target is some base trait (e.g. `dyn Any`).
//!
//! Generic over the key type `K` so users can plug in
//! `DefaultCastableKey<D::Target>`, `MyCastableKey<D::Target>`, etc.

use std::ptr::Pointee;

use crate::key::Key;
use crate::key_castable::CastableKey;
use crate::map_id::MapId;
use crate::stable_deref_gen_map::{DerefGenMapPromise, StableDerefGenMap};

// ─── KeyCastableStableDerefGenMap ───────────────────────────────────────────

/// A [`StableDerefGenMap`] wrapper that supports typed lookups via castable
/// keys.
///
/// - `K`: the inner key type, e.g. `DefaultCastableKey<dyn Any>` or
///   `MyCastableKey<dyn Any>`. Must implement `Key<Extra = MapId>`.
/// - `D`: the smart pointer type, e.g. `Box<dyn Any>`.
///
/// You insert values as `D`, getting back a `K` (with real metadata patched
/// in). You can upcast/cross-cast that key to a different `T` and use
/// [`get_as`](Self::get_as) to get `Option<&T>`.
pub struct KeyCastableStableDerefGenMap<K, D>
where
    K: Key<Extra = MapId>,
    D: DerefGenMapPromise + 'static,
{
    inner: StableDerefGenMap<K, D>,
}

impl<K, D> KeyCastableStableDerefGenMap<K, D>
where
    K: Key<Extra = MapId>,
    D: DerefGenMapPromise + 'static,
{
    /// Creates a new, empty map.
    #[inline]
    pub fn new() -> Self {
        Self {
            inner: StableDerefGenMap::new(),
        }
    }

    /// Creates a new map with the given pre-allocated capacity.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: StableDerefGenMap::with_capacity(capacity),
        }
    }

    /// Returns the number of occupied elements.
    #[inline]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Empties the map.
    #[inline]
    pub fn clear(&mut self) {
        self.inner.clear();
    }
}

// ── Methods that require K: CastableKey<D::Target> ─────────────────────────
//
// These are the "native" operations that work with the base trait key.

impl<K, D> KeyCastableStableDerefGenMap<K, D>
where
    K: CastableKey<D::Target>,
    D: DerefGenMapPromise + 'static,
    <D::Target as Pointee>::Metadata: Copy,
{
    /// Inserts a smart pointer, returning a key (with real metadata) and a
    /// reference to the deref target.
    #[inline]
    pub fn insert(&self, value: D) -> (K, &D::Target) {
        let (raw_key, reference) = self.inner.insert(value);
        let metadata = std::ptr::metadata(reference as *const D::Target);
        let patched = K::from_castable_parts(
            raw_key.data(),
            raw_key.extra(),
            metadata,
        );
        (patched, reference)
    }

    /// Inserts via a closure that receives the key.
    ///
    /// Note: the key passed to `func` has zeroed metadata since the value
    /// hasn't been stored yet. The returned key will have correct metadata.
    #[inline]
    pub fn insert_with_key(
        &self,
        func: impl FnOnce(K) -> D,
    ) -> (K, &D::Target) {
        let (raw_key, reference) = self.inner.insert_with_key(func);
        let metadata = std::ptr::metadata(reference as *const D::Target);
        let patched = K::from_castable_parts(
            raw_key.data(),
            raw_key.extra(),
            metadata,
        );
        (patched, reference)
    }

    /// Shared-reference lookup returning `&D::Target` (the base trait).
    ///
    /// Use [`get_as`](Self::get_as) to look up with a differently-typed key.
    #[inline]
    pub fn get(&self, key: K) -> Option<&D::Target> {
        self.inner.get(key)
    }

    /// Mutable-reference lookup returning `&mut D::Target`.
    #[inline]
    pub fn get_mut(&mut self, key: K) -> Option<&mut D::Target>
    where
        D: std::ops::DerefMut,
    {
        self.inner.get_mut(key)
    }

    /// Removes an element by key, returning the owned smart pointer.
    #[inline]
    pub fn remove(&mut self, key: K) -> Option<D> {
        self.inner.remove(key)
    }

    /// Returns a snapshot of all `(key, &target)` pairs.
    #[inline]
    pub fn snapshot(&self) -> Vec<(K, &D::Target)> {
        let raw = self.inner.snapshot();
        raw.into_iter()
            .map(|(raw_key, reference)| {
                let metadata =
                    std::ptr::metadata(reference as *const D::Target);
                let patched = K::from_castable_parts(
                    raw_key.data(),
                    raw_key.extra(),
                    metadata,
                );
                (patched, reference)
            })
            .collect()
    }
}

// ── Cross-typed lookups ────────────────────────────────────────────────────
//
// These accept any CastableKey with matching Idx/Gen — the key might be
// parameterised over a *different* T than D::Target.

impl<K, D> KeyCastableStableDerefGenMap<K, D>
where
    K: Key<Extra = MapId>,
    D: DerefGenMapPromise + 'static,
{
    /// Shared-reference lookup with a key for a *different* type `T`.
    ///
    /// Converts the key to the inner key type (same key_data + map_id),
    /// looks up the slot to get the data pointer, then combines it with
    /// `key.metadata()` to produce `&T`.
    ///
    /// # Safety
    /// The metadata in `key` must be valid for the concrete type stored
    /// at this slot. This is the caller's responsibility (or will be
    /// enforced by the future cross-casting infrastructure).
    #[inline]
    pub unsafe fn get_as<T: ?Sized + Pointee, CK>(
        &self,
        key: CK,
    ) -> Option<&T>
    where
        CK: CastableKey<T, Idx = K::Idx, Gen = K::Gen>,
        <T as Pointee>::Metadata: Copy,
    {
        let inner_key = K::from_parts(key.data(), key.extra());
        let base_ref: &D::Target = self.inner.get(inner_key)?;

        let data_ptr: *const () = (base_ref as *const D::Target).cast();
        let fat_ptr: *const T = std::ptr::from_raw_parts(data_ptr, key.metadata());
        Some(&*fat_ptr)
    }

    /// Mutable-reference lookup with a differently-typed key.
    ///
    /// # Safety
    /// Same as [`get_as`](Self::get_as).
    #[inline]
    pub unsafe fn get_as_mut<T: ?Sized + Pointee, CK>(
        &mut self,
        key: CK,
    ) -> Option<&mut T>
    where
        CK: CastableKey<T, Idx = K::Idx, Gen = K::Gen>,
        <T as Pointee>::Metadata: Copy,
        D: std::ops::DerefMut,
    {
        let inner_key = K::from_parts(key.data(), key.extra());
        let base_ref: &mut D::Target = self.inner.get_mut(inner_key)?;

        let data_ptr: *mut () = (base_ref as *mut D::Target).cast();
        let fat_ptr: *mut T = std::ptr::from_raw_parts_mut(data_ptr, key.metadata());
        Some(&mut *fat_ptr)
    }

    /// Removes using a differently-typed key.
    #[inline]
    pub fn remove_by<T: ?Sized + Pointee, CK>(
        &mut self,
        key: CK,
    ) -> Option<D>
    where
        CK: CastableKey<T, Idx = K::Idx, Gen = K::Gen>,
        <T as Pointee>::Metadata: Copy,
    {
        let inner_key = K::from_parts(key.data(), key.extra());
        self.inner.remove(inner_key)
    }
}