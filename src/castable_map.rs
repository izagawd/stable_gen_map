//! Map type that uses [`DefaultCastableKey<T>`] as its user-facing key,
//! storing smart pointers whose deref target is `T`.
//!
//! Only the `StableDerefGenMap` variant makes sense here — the value must
//! be a trait object behind a smart pointer so the key can carry its metadata.
//!
//! # How it works
//!
//! The inner `GenMap` is keyed by `DefaultCastableKey<D::Target>`.  GenMap's
//! `from_parts` produces keys with zeroed metadata; the wrapper patches in
//! the real metadata (from the stored value's fat pointer) before returning
//! keys to the user.
//!
//! `get` combines the data pointer from the slot with the metadata from
//! the key to reconstruct `&D::Target`.

use std::ptr::Pointee;

use crate::key::Key;
use crate::key_castable::{CastableKey, DefaultCastableKey};
use crate::stable_deref_gen_map::{DerefGenMapPromise, StableDerefGenMap};

// ─── KeyCastableStableDerefGenMap ───────────────────────────────────────────

/// A [`StableDerefGenMap`] wrapper whose keys are
/// [`DefaultCastableKey<D::Target>`].
///
/// `D` is the smart pointer type (e.g. `Box<dyn Any>`, `Rc<dyn Foo>`).
/// The key carries the pointer metadata for `D::Target`, so a `&D::Target`
/// can be reconstructed from the key + the stored data pointer.
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
        let metadata = std::ptr::metadata(reference);
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
        let metadata = std::ptr::metadata(reference);
        let patched = DefaultCastableKey::from_castable_parts(
            raw_key.data(),
            raw_key.extra(),
            metadata,
        );
        (patched, reference)
    }

    /// Shared-reference lookup by key.
    ///
    /// The generation and map-id checks happen inside GenMap. The metadata
    /// in the key is not used here — the stored smart pointer already knows
    /// its own type.
    #[inline]
    pub fn get(&self, key: DefaultCastableKey<D::Target>) -> Option<&D::Target> {
        self.inner.get(key)
    }

    /// Mutable-reference lookup by key.
    #[inline]
    pub fn get_mut(&mut self, key: DefaultCastableKey<D::Target>) -> Option<&mut D::Target>
    where
        D: std::ops::DerefMut,
    {
        self.inner.get_mut(key)
    }

    /// Removes an element by key, returning the owned smart pointer.
    #[inline]
    pub fn remove(&mut self, key: DefaultCastableKey<D::Target>) -> Option<D> {
        self.inner.remove(key)
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
                let metadata = std::ptr::metadata(reference);
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
