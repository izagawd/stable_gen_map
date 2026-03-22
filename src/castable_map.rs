//! Map type that uses a castable key family, storing smart pointers
//! whose deref target is some base trait (e.g. `dyn Any`).
//!
//! Generic over the key type `K` so users can plug in
//! `DefaultCastableKey<D::Target>`, `MyCastableKey<D::Target>`, etc.

use std::collections::TryReserveError;
use std::ops::{Index, IndexMut};
use std::ptr::Pointee;

use crate::gen_map;
use crate::key::Key;
use crate::key_castable::{CastableKey, DefaultCastableKey};
use crate::map_id::MapId;
use crate::stable_deref_gen_map::{
    DerefGenMapPromise, SmartPtrCloneable, StableDerefGenMap,
};

// ─── helper: patch a raw key with real metadata ─────────────────────────────

#[inline]
fn patch_key<K, D>(raw_key: K, reference: &D::Target) -> K
where
    K: CastableKey<D::Target>,
    D: DerefGenMapPromise,
    <D::Target as Pointee>::Metadata: Copy,
{
    let metadata = std::ptr::metadata(reference as *const D::Target);
    K::from_castable_parts(raw_key.data(), raw_key.extra(), metadata)
}

// ─── KeyCastableStableGenMap ────────────────────────────────────────────────

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
pub struct KeyCastableStableGenMap<K, D>
where
    K: Key<Extra = MapId>,
    D: DerefGenMapPromise + 'static,
{
    pub(crate) inner: StableDerefGenMap<K, D>,
}

// ─── Basic methods (no metadata patching) ───────────────────────────────────

impl<K, D> KeyCastableStableGenMap<K, D>
where
    K: Key<Extra = MapId>,
    D: DerefGenMapPromise + 'static,
{
    /// Creates a new, empty map.
    #[inline]
    pub const fn new() -> Self {
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

    /// Reserves capacity for at least `additional` more elements.
    #[inline]
    pub fn reserve(&self, additional: usize) {
        self.inner.reserve(additional);
    }

    /// Tries to reserve capacity for at least `additional` more elements.
    #[inline]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.inner.try_reserve(additional)
    }

    /// Returns how many slots the backing `Vec` can hold before reallocating.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
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

// ─── Native operations (K: CastableKey<D::Target>) ─────────────────────────

impl<K, D> KeyCastableStableGenMap<K, D>
where
    K: CastableKey<D::Target>,
    D: DerefGenMapPromise + 'static,
    <D::Target as Pointee>::Metadata: Copy,
{
    // ── insert ──────────────────────────────────────────────────────────

    /// Inserts a smart pointer, returning a key (with real metadata) and a
    /// reference to the deref target.
    #[inline]
    pub fn insert(&self, value: D) -> (K, &D::Target) {
        let (raw_key, reference) = self.inner.insert(value);
        (patch_key::<K, D>(raw_key, reference), reference)
    }

    /// Inserts via a closure that receives the key.
    ///
    /// Note: the key passed to `func` has placeholder metadata since the value
    /// hasn't been stored yet. The returned key will have correct metadata.
    #[inline]
    pub fn insert_with_key(
        &self,
        func: impl FnOnce(K) -> D,
    ) -> (K, &D::Target) {
        let (raw_key, reference) = self.inner.insert_with_key(func);
        (patch_key::<K, D>(raw_key, reference), reference)
    }

    /// Like [`insert_with_key`](Self::insert_with_key) but the closure may
    /// return `Err`, in which case the slot is released.
    #[inline]
    pub fn try_insert_with_key<E>(
        &self,
        func: impl FnOnce(K) -> Result<D, E>,
    ) -> Result<(K, &D::Target), E> {
        let (raw_key, reference) = self.inner.try_insert_with_key(func)?;
        Ok((patch_key::<K, D>(raw_key, reference), reference))
    }

    // ── get ─────────────────────────────────────────────────────────────

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

    /// Shared-reference lookup by index only (ignores generation).
    #[inline]
    pub fn get_by_index_only(&self, idx: K::Idx) -> Option<(K, &D::Target)> {
        let (raw_key, reference) = self.inner.get_by_index_only(idx)?;
        Some((patch_key::<K, D>(raw_key, reference), reference))
    }

    /// Mutable lookup by index only (ignores generation).
    #[inline]
    pub fn get_by_index_only_mut(&mut self, idx: K::Idx) -> Option<(K, &mut D::Target)>
    where
        D: std::ops::DerefMut,
    {
        let (raw_key, reference) = self.inner.get_by_index_only_mut(idx)?;
        let metadata = std::ptr::metadata(reference as *const D::Target);
        let patched = K::from_castable_parts(raw_key.data(), raw_key.extra(), metadata);
        Some((patched, reference))
    }

    // ── remove ──────────────────────────────────────────────────────────

    /// Removes an element by key, returning the owned smart pointer.
    #[inline]
    pub fn remove(&mut self, key: K) -> Option<D> {
        self.inner.remove(key)
    }

    // ── retain ──────────────────────────────────────────────────────────

    /// Retains only elements for which `f(key, &mut stored)` returns `true`.
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(K, &mut D) -> bool,
    {
        self.inner.retain(|raw_key, stored| {
            let reference: &D::Target = &**stored;
            let metadata = std::ptr::metadata(reference as *const D::Target);
            let patched = K::from_castable_parts(raw_key.data(), raw_key.extra(), metadata);
            f(patched, stored)
        })
    }

    // ── snapshot (single heap allocation) ───────────────────────────────

    /// Returns a snapshot of all `(key, &target)` pairs.
    /// One heap allocation.
    #[inline]
    pub fn snapshot(&self) -> Vec<(K, &D::Target)> {
        unsafe {
            let mut vec = Vec::with_capacity(self.inner.len());
            vec.extend(self.inner.iter_unsafe().map(|(raw_key, reference)| {
                (patch_key::<K, D>(raw_key, reference), reference)
            }));
            vec
        }
    }

    /// Returns a snapshot of `&target` references only.
    /// One heap allocation.
    #[inline]
    pub fn snapshot_refs(&self) -> Vec<&D::Target> {
        unsafe {
            let mut vec = Vec::with_capacity(self.inner.len());
            vec.extend(self.inner.iter_unsafe().map(|(_, reference)| reference));
            vec
        }
    }

    /// Returns a snapshot of keys only.
    /// One heap allocation.
    #[inline]
    pub fn snapshot_keys(&self) -> Vec<K> {
        unsafe {
            let mut vec = Vec::with_capacity(self.inner.len());
            vec.extend(self.inner.iter_unsafe().map(|(raw_key, reference)| {
                patch_key::<K, D>(raw_key, reference)
            }));
            vec
        }
    }

    // ── iter_unsafe ─────────────────────────────────────────────────────

    /// # Safety
    /// No mutation (including `insert`) may occur while iterating.
    #[inline]
    pub unsafe fn iter_unsafe(&self) -> impl Iterator<Item = (K, &D::Target)> {
        self.inner.iter_unsafe().map(|(raw_key, reference)| {
            (patch_key::<K, D>(raw_key, reference), reference)
        })
    }

    // ── iter_mut ────────────────────────────────────────────────────────

    /// Mutable iterator over all occupied elements.
    /// Yields `(K, &mut D)` with properly patched keys.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, D> {
        IterMut {
            inner: self.inner.iter_mut(),
        }
    }

    // ── drain ───────────────────────────────────────────────────────────

    /// Removes all elements and returns them as an iterator.
    /// Yields `(K, D)` with properly patched keys.
    #[inline]
    pub fn drain(&mut self) -> Drain<'_, K, D> {
        Drain {
            inner: self.inner.drain(),
        }
    }
}

// ─── Index / IndexMut ───────────────────────────────────────────────────────

impl<K, D> Index<K> for KeyCastableStableGenMap<K, D>
where
    K: CastableKey<D::Target>,
    D: DerefGenMapPromise + 'static,
    <D::Target as Pointee>::Metadata: Copy,
{
    type Output = D::Target;

    fn index(&self, key: K) -> &Self::Output {
        self.get(key).unwrap()
    }
}

impl<K, D> IndexMut<K> for KeyCastableStableGenMap<K, D>
where
    K: CastableKey<D::Target>,
    D: DerefGenMapPromise + 'static + std::ops::DerefMut,
    <D::Target as Pointee>::Metadata: Copy,
{
    fn index_mut(&mut self, key: K) -> &mut Self::Output {
        self.get_mut(key).unwrap()
    }
}

// ─── IterMut ────────────────────────────────────────────────────────────────

pub struct IterMut<'a, K: Key, D: DerefGenMapPromise> {
    inner: gen_map::IterMut<'a, K, crate::stable_deref_gen_map::DerefSlot<D, K>>,
}

impl<'a, K, D> Iterator for IterMut<'a, K, D>
where
    K: CastableKey<D::Target>,
    D: DerefGenMapPromise + 'static,
    <D::Target as Pointee>::Metadata: Copy,
{
    type Item = (K, &'a mut D);

    fn next(&mut self) -> Option<Self::Item> {
        let (raw_key, stored) = self.inner.next()?;
        let reference: &D::Target = &**stored;
        let metadata = std::ptr::metadata(reference as *const D::Target);
        let patched = K::from_castable_parts(raw_key.data(), raw_key.extra(), metadata);
        Some((patched, stored))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

// ─── Drain ──────────────────────────────────────────────────────────────────

pub struct Drain<'a, K: Key, D: DerefGenMapPromise> {
    inner: gen_map::Drain<'a, K, crate::stable_deref_gen_map::DerefSlot<D, K>>,
}

impl<'a, K, D> Iterator for Drain<'a, K, D>
where
    K: CastableKey<D::Target>,
    D: DerefGenMapPromise + 'static,
    <D::Target as Pointee>::Metadata: Copy,
{
    type Item = (K, D);

    fn next(&mut self) -> Option<Self::Item> {
        let (raw_key, value) = self.inner.next()?;
        let reference: &D::Target = &*value;
        let metadata = std::ptr::metadata(reference as *const D::Target);
        let patched = K::from_castable_parts(raw_key.data(), raw_key.extra(), metadata);
        Some((patched, value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

// ─── IntoIter (owning) ─────────────────────────────────────────────────────

pub struct IntoIter<K: Key, D: DerefGenMapPromise> {
    inner: gen_map::IntoIter<K, crate::stable_deref_gen_map::DerefSlot<D, K>>,
}

impl<K, D> Iterator for IntoIter<K, D>
where
    K: CastableKey<D::Target>,
    D: DerefGenMapPromise + 'static,
    <D::Target as Pointee>::Metadata: Copy,
{
    type Item = (K, D);

    fn next(&mut self) -> Option<Self::Item> {
        let (raw_key, value) = self.inner.next()?;
        let reference: &D::Target = &*value;
        let metadata = std::ptr::metadata(reference as *const D::Target);
        let patched = K::from_castable_parts(raw_key.data(), raw_key.extra(), metadata);
        Some((patched, value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K, D> IntoIterator for KeyCastableStableGenMap<K, D>
where
    K: CastableKey<D::Target>,
    D: DerefGenMapPromise + 'static,
    <D::Target as Pointee>::Metadata: Copy,
{
    type Item = (K, D);
    type IntoIter = IntoIter<K, D>;

    /// Consumes the map into an owning iterator.
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.inner.into_iter(),
        }
    }
}

// ─── IntoIterator for &mut ──────────────────────────────────────────────────

impl<'a, K, D> IntoIterator for &'a mut KeyCastableStableGenMap<K, D>
where
    K: CastableKey<D::Target>,
    D: DerefGenMapPromise + 'static,
    <D::Target as Pointee>::Metadata: Copy,
{
    type Item = (K, &'a mut D);
    type IntoIter = IterMut<'a, K, D>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

// ─── Cross-typed lookups ────────────────────────────────────────────────────

impl<K, D> KeyCastableStableGenMap<K, D>
where
    K: Key<Extra = MapId>,
    D: DerefGenMapPromise + 'static,
{
    /// Shared-reference lookup with a key for a *different* type `T`.
    ///
    /// Converts the key to the inner key type (same key_data + map_id),
    /// looks up the slot to get the data pointer, then combines it with
    /// `key.metadata()` to produce `&T`.
    #[inline]
    pub fn get_as<T: ?Sized + Pointee, CK>(
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
        unsafe { Some(&*fat_ptr) }
    }

    /// Mutable-reference lookup with a differently-typed key.
    #[inline]
    pub fn get_as_mut<T: ?Sized + Pointee, CK>(
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
        unsafe { Some(&mut *fat_ptr) }
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

// ─── Type alias ─────────────────────────────────────────────────────────────

/// Convenience alias: [`KeyCastableStableGenMap`] storing `Box<T>` with
/// [`DefaultCastableKey<T>`] keys.
///
/// Usage: `KeyCastableBoxStableGenMap<DefaultCastableKey<dyn Any>, dyn Any>`
pub type KeyCastableBoxStableGenMap<K, T: ?Sized> =
KeyCastableStableGenMap<K, Box<T>>;