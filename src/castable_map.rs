//! Map type that uses [`DefaultCastableKey<T>`] as its user-facing key,
//! storing smart pointers whose deref target is some base trait (e.g. `dyn Any`).
//!
//! Only the `StableDerefGenMap` variant exists — the value must be a trait
//! object behind a smart pointer so the key can carry its metadata.
//!
//! # How it works
//!
//! The inner `GenMap` is keyed by `DefaultCastableKey<D::Target>` (e.g.
//! `DefaultCastableKey<dyn Any>`).
//!
//! `get<T>` accepts a `DefaultCastableKey<T>` for *any* `T: ?Sized`, converts
//! it to the inner key type (same key_data + map_id), looks up the slot to
//! get the raw data pointer, then combines that pointer with `key.metadata()`
//! to reconstruct `&T`.

use std::ptr::Pointee;

use crate::key::Key;
use crate::key_castable::{CastableKey, DefaultCastableKey};
use crate::stable_deref_gen_map::{DerefGenMapPromise, StableDerefGenMap};

// ─── KeyCastableStableDerefGenMap ───────────────────────────────────────────

/// A [`StableDerefGenMap`] wrapper whose keys are
/// [`DefaultCastableKey<T>`].
///
/// `D` is the smart pointer type (e.g. `Box<dyn Any>`, `Rc<dyn Foo>`).
/// You insert values as `D`, getting back a `DefaultCastableKey<D::Target>`.
/// You can then look up with a `DefaultCastableKey<T>` for a *different* `T`
/// and get back `Option<&T>`, as long as the metadata in the key is valid.
pub struct KeyCastableStableDerefGenMap<D: DerefGenMapPromise + 'static>
where
    <D::Target as Pointee>::Metadata: Copy,
{
    inner: StableDerefGenMap<DefaultCastableKey<D::Target>, D>,
}

impl<D: DerefGenMapPromise + 'static> KeyCastableStableDerefGenMap<D>
where
    <D::Target as Pointee>::Metadata: Copy,
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

    /// Inserts a smart pointer, returning a key (with real metadata) and a
    /// reference to the deref target.
    #[inline]
    pub fn insert(&self, value: D) -> (DefaultCastableKey<D::Target>, &D::Target) {
        let (raw_key, reference) = self.inner.insert(value);
        // raw_key has zeroed metadata from GenMap's from_parts.
        // Patch it with the real metadata from the stored reference.
        let metadata = std::ptr::metadata(reference as *const D::Target);
        let patched = DefaultCastableKey::from_castable_parts(
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
        func: impl FnOnce(DefaultCastableKey<D::Target>) -> D,
    ) -> (DefaultCastableKey<D::Target>, &D::Target) {
        let (raw_key, reference) = self.inner.insert_with_key(func);
        let metadata = std::ptr::metadata(reference as *const D::Target);
        let patched = DefaultCastableKey::from_castable_parts(
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
    pub fn get(&self, key: DefaultCastableKey<D::Target>) -> Option<&D::Target> {
        self.inner.get(key)
    }

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
    pub fn get_as<T: ?Sized + Pointee>(
        &self,
        key: DefaultCastableKey<T>,
    ) -> Option<&T>
    where
        <T as Pointee>::Metadata: Copy,
    {
        // Build an inner key (DefaultCastableKey<D::Target>) from the
        // same key_data + map_id. The metadata is irrelevant for lookup —
        // GenMap only checks idx, generation, and Extra (MapId).
        let inner_key = DefaultCastableKey::<D::Target>::from_parts(
            key.data(),
            key.extra(),
        );
        let base_ref: &D::Target = self.inner.get(inner_key)?;

        // Extract the data pointer from the base trait reference.
        let data_ptr: *const () = (base_ref as *const D::Target).cast();

        // Reconstruct &T using the data pointer + the key's metadata.
        let fat_ptr: *const T = std::ptr::from_raw_parts(data_ptr, key.metadata());
        unsafe{ Some(&*fat_ptr) }
    }

    /// Mutable-reference lookup returning `&mut D::Target`.
    #[inline]
    pub fn get_mut(&mut self, key: DefaultCastableKey<D::Target>) -> Option<&mut D::Target>
    where
        D: std::ops::DerefMut,
    {
        self.inner.get_mut(key)
    }

    /// Mutable-reference lookup with a differently-typed key.
    ///
    /// # Safety
    /// Same as [`get_as`](Self::get_as).
    #[inline]
    pub fn get_as_mut<T: ?Sized + Pointee>(
        &mut self,
        key: DefaultCastableKey<T>,
    ) -> Option<&mut T>
    where
        <T as Pointee>::Metadata: Copy,
        D: std::ops::DerefMut,
    {
        let inner_key = DefaultCastableKey::<D::Target>::from_parts(
            key.data(),
            key.extra(),
        );
        let base_ref: &mut D::Target = self.inner.get_mut(inner_key)?;

        let data_ptr: *mut () = (base_ref as *mut D::Target).cast();
        let fat_ptr: *mut T = std::ptr::from_raw_parts_mut(data_ptr, key.metadata());
        unsafe{ Some(&mut *fat_ptr) }
    }

    /// Removes an element by key, returning the owned smart pointer.
    #[inline]
    pub fn remove(&mut self, key: DefaultCastableKey<D::Target>) -> Option<D> {
        self.inner.remove(key)
    }

    /// Removes using a differently-typed key.
    #[inline]
    pub fn remove_by<T: ?Sized + Pointee>(
        &mut self,
        key: DefaultCastableKey<T>,
    ) -> Option<D>
    where
        <T as Pointee>::Metadata: Copy,
    {
        let inner_key = DefaultCastableKey::<D::Target>::from_parts(
            key.data(),
            key.extra(),
        );
        self.inner.remove(inner_key)
    }

    /// Empties the map.
    #[inline]
    pub fn clear(&mut self) {
        self.inner.clear();
    }

    /// Returns a snapshot of all `(key, &target)` pairs.
    #[inline]
    pub fn snapshot(&self) -> Vec<(DefaultCastableKey<D::Target>, &D::Target)> {
        let raw = self.inner.snapshot();
        raw.into_iter()
            .map(|(raw_key, reference)| {
                let metadata = std::ptr::metadata(reference as *const D::Target);
                let patched = DefaultCastableKey::from_castable_parts(
                    raw_key.data(),
                    raw_key.extra(),
                    metadata,
                );
                (patched, reference)
            })
            .collect()
    }
}

/// Convenience alias: `Box<T>` variant.
pub type KeyCastableBoxStableDerefGenMap<T> = KeyCastableStableDerefGenMap<Box<T>>;