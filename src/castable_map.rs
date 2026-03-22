//! Map type that uses a [`CastableKey<T>`] as its user-facing key.
//!
//! Internally, a plain [`CastableInnerKey`] (which implements [`Key`] with
//! `Extra = MapId`) is used by the `GenMap`. The castable map wrapper
//! converts between `CastableInnerKey` and `CastableKey<T>` at every
//! boundary — adding metadata on the way out, stripping it on the way in.
//!
//! This means `GenMap` never sees pointer metadata and no `dangling_metadata`
//! hack is needed.

use std::collections::TryReserveError;
use std::ops::{CoerceUnsized, Index, IndexMut};
use std::ptr::Pointee;

use crate::castable_key::CastableKey;
use crate::{castable_key, gen_map};
use crate::key::{Key, KeyData};
use crate::key_piece::KeyPiece;
use crate::map_id::MapId;
use crate::stable_deref_gen_map::{DerefGenMapPromise, DerefSlot, StableDerefGenMap};

// ─── CastableInnerKey ───────────────────────────────────────────────────────
//
// The key type GenMap actually stores. No metadata, just key_data + map_id.

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct CastableInnerKey<Idx, Gen> {
    key_data: KeyData<Idx, Gen>,
    map_id: MapId,
}

unsafe impl<Idx: Copy + KeyPiece, Gen: Copy + KeyPiece> Key for CastableInnerKey<Idx, Gen> {
    type Idx = Idx;
    type Gen = Gen;
    type Extra = MapId;

    #[inline]
    fn data(&self) -> KeyData<Idx, Gen> {
        self.key_data
    }

    #[inline]
    fn extra(&self) -> MapId {
        self.map_id
    }

    #[inline]
    fn from_parts(data: KeyData<Idx, Gen>, extra: MapId) -> Self {
        Self {
            key_data: data,
            map_id: extra,
        }
    }
}

// ─── Conversion helpers ─────────────────────────────────────────────────────

/// Strip metadata, produce inner key.
#[inline]
fn to_inner<T: ?Sized + Pointee, CK>(key: &CK) -> CastableInnerKey<<CK as CastableKey<T>>::Idx, <CK as CastableKey<T>>::Gen>
where
    CK: CastableKey<T>,
    <T as Pointee>::Metadata: Copy,
{
    CastableInnerKey {
        key_data: key.key_data(),
        map_id: key.map_id(),
    }
}

/// Build a castable key from an inner key + metadata from a reference.
#[inline]
fn to_castable<CK, D>(inner: CastableInnerKey<<CK as CastableKey<D::Target>>::Idx, <CK as CastableKey<D::Target>>::Gen>, reference: &D::Target) -> CK
where
    CK: CastableKey<D::Target>,
    D: DerefGenMapPromise,
    <D::Target as Pointee>::Metadata: Copy,
{
    let metadata = std::ptr::metadata(reference as *const D::Target);
    CK::from_castable_parts(inner.key_data, inner.map_id, metadata)
}

// ─── KeyCastableStableGenMap ────────────────────────────────────────────────

/// A [`StableDerefGenMap`] wrapper that supports typed lookups via
/// [`CastableKey<T>`].
///
/// - `CK`: the castable key family, e.g. `DefaultCastableKey<D::Target>`.
/// - `D`: the smart pointer type, e.g. `Box<dyn Any>`.
pub struct KeyCastableStableGenMap<CK: CastableKey<D::Target>, D>
where
    D: DerefGenMapPromise + 'static,
{
    pub(crate) inner: StableDerefGenMap<CastableInnerKey<<CK as CastableKey<D::Target>>::Idx, <CK as CastableKey<D::Target>>::Gen> , D>,
    _phantom: std::marker::PhantomData<fn() -> CK>,
}

// ─── Basic methods ──────────────────────────────────────────────────────────

impl<CK: CastableKey<D::Target>, D> KeyCastableStableGenMap<CK, D>
where
    D: DerefGenMapPromise + 'static,
{
    /// Creates a new, empty map.
    #[inline]
    pub const fn new() -> Self {
        Self {
            inner: StableDerefGenMap::new(),
            _phantom: std::marker::PhantomData,
        }
    }

    /// Creates a new map with the given pre-allocated capacity.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: StableDerefGenMap::with_capacity(capacity),
            _phantom: std::marker::PhantomData,
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

// ─── Native operations (CK: CastableKey<D::Target>) ────────────────────────

impl<CK, D> KeyCastableStableGenMap<CK, D>
where
    CK: CastableKey<D::Target>,
    D: DerefGenMapPromise + 'static,
    <D::Target as Pointee>::Metadata: Copy,
{
    // ── insert ──────────────────────────────────────────────────────────

    /// Inserts a smart pointer, returning a key (with real metadata) and a
    /// reference to the deref target.
    #[inline]
    pub fn insert(&self, value: D) -> (CK, &D::Target) {
        let (inner_key, reference) = self.inner.insert(value);
        (to_castable::<CK, D>(inner_key, reference), reference)
    }

    /// Inserts via a closure that receives the key.
    ///
    /// Note: the key passed to `func` has placeholder metadata since the value
    /// hasn't been stored yet. The returned key will have correct metadata.
    #[inline]
    pub fn insert_with_key(
        &self,
        func: impl FnOnce(CK) -> D,
    ) -> (CK, &D::Target) {
        // The closure receives a CK, but we only have CastableInnerKey.
        // We can't build a proper CK without metadata (no value yet).
        // So we use try_insert_with_key to get the inner key first,
        // then the user's closure receives it after we patch.
        //
        // Actually — the inner GenMap's insert_with_key gives the closure
        // a CastableInnerKey. We need to wrap it.
        let (inner_key, reference) = self.inner.insert_with_key(|ik| {
            // Build a temporary CK. For sized D::Target, metadata is ().
            // For dyn, we don't have real metadata yet — the user shouldn't
            // rely on the key's metadata inside the closure anyway.
            // We use the map_id from the inner key.
            //
            // This is only sound because insert_with_key's closure receives
            // the key for identity purposes (e.g. self-referential), not for
            // metadata extraction.
            let temp_ck = unsafe {
                CK::from_castable_parts(
                    ik.key_data,
                    ik.map_id,
                    std::mem::zeroed(),
                )
            };
            func(temp_ck)
        });
        (to_castable::<CK, D>(inner_key, reference), reference)
    }

    /// Like [`insert_with_key`](Self::insert_with_key) but the closure may
    /// return `Err`, in which case the slot is released.
    #[inline]
    pub fn try_insert_with_key<E>(
        &self,
        func: impl FnOnce(CK) -> Result<D, E>,
    ) -> Result<(CK, &D::Target), E> {
        let (inner_key, reference) = self.inner.try_insert_with_key(|ik| {
            let temp_ck = unsafe {
                CK::from_castable_parts(
                    ik.key_data,
                    ik.map_id,
                    std::mem::zeroed(),
                )
            };
            func(temp_ck)
        })?;
        Ok((to_castable::<CK, D>(inner_key, reference), reference))
    }

    // ── get ─────────────────────────────────────────────────────────────

    /// Shared-reference lookup returning `&D::Target` (the base trait).
    ///
    /// Use [`get_as`](Self::get_as) to look up with a differently-typed key.
    #[inline]
    pub fn get(&self, key: CK) -> Option<&D::Target> {
        self.inner.get(to_inner(&key))
    }

    /// Mutable-reference lookup returning `&mut D::Target`.
    #[inline]
    pub fn get_mut(&mut self, key: CK) -> Option<&mut D::Target>
    where
        D: std::ops::DerefMut,
    {
        self.inner.get_mut(to_inner(&key))
    }

    /// Shared-reference lookup by index only (ignores generation).
    #[inline]
    pub fn get_by_index_only(&self, idx: CK::Idx) -> Option<(CK, &D::Target)> {
        let (inner_key, reference) = self.inner.get_by_index_only(idx)?;
        Some((to_castable::<CK, D>(inner_key, reference), reference))
    }

    /// Mutable lookup by index only (ignores generation).
    #[inline]
    pub fn get_by_index_only_mut(&mut self, idx: CK::Idx) -> Option<(CK, &mut D::Target)>
    where
        D: std::ops::DerefMut,
    {
        let (inner_key, reference) = self.inner.get_by_index_only_mut(idx)?;
        let patched = to_castable::<CK, D>(inner_key, reference);
        Some((patched, reference))
    }

    // ── remove ──────────────────────────────────────────────────────────

    /// Removes an element by key, returning the owned smart pointer.
    #[inline]
    pub fn remove(&mut self, key: CK) -> Option<D> {
        self.inner.remove(to_inner(&key))
    }

    // ── retain ──────────────────────────────────────────────────────────

    /// Retains only elements for which `f(key, &mut stored)` returns `true`.
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(CK, &mut D) -> bool,
    {
        self.inner.retain(|inner_key, stored| {
            let reference: &D::Target = &**stored;
            let patched = to_castable::<CK, D>(inner_key, reference);
            f(patched, stored)
        })
    }

    // ── snapshot (single heap allocation) ───────────────────────────────

    /// Returns a snapshot of all `(key, &target)` pairs.
    /// One heap allocation.
    #[inline]
    pub fn snapshot(&self) -> Vec<(CK, &D::Target)> {
        unsafe {
            let mut vec = Vec::with_capacity(self.inner.len());
            vec.extend(self.inner.iter_unsafe().map(|(inner_key, reference)| {
                (to_castable::<CK, D>(inner_key, reference), reference)
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
    pub fn snapshot_keys(&self) -> Vec<CK> {
        unsafe {
            let mut vec = Vec::with_capacity(self.inner.len());
            vec.extend(self.inner.iter_unsafe().map(|(inner_key, reference)| {
                to_castable::<CK, D>(inner_key, reference)
            }));
            vec
        }
    }

    // ── iter_unsafe ─────────────────────────────────────────────────────

    /// # Safety
    /// No mutation (including `insert`) may occur while iterating.
    #[inline]
    pub unsafe fn iter_unsafe(&self) -> impl Iterator<Item = (CK, &D::Target)> {
        self.inner.iter_unsafe().map(|(inner_key, reference)| {
            (to_castable::<CK, D>(inner_key, reference), reference)
        })
    }

    // ── iter_mut ────────────────────────────────────────────────────────

    /// Mutable iterator over all occupied elements.
    /// Yields `(K, &mut D)` with properly patched keys.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, CK, D> {
        IterMut {
            inner: self.inner.iter_mut(),
            _phantom: std::marker::PhantomData,
        }
    }

    // ── drain ───────────────────────────────────────────────────────────

    /// Removes all elements and returns them as an iterator.
    /// Yields `(K, D)` with properly patched keys.
    #[inline]
    pub fn drain(&mut self) -> Drain<'_, CK, D> {
        Drain {
            inner: self.inner.drain(),
            _phantom: std::marker::PhantomData,
        }
    }
}

// ─── Cross-typed lookups ────────────────────────────────────────────────────

impl<CK, D> KeyCastableStableGenMap<CK, D>
where
    D: DerefGenMapPromise + 'static,
    CK: CastableKey<<D as std::ops::Deref>::Target>
{
    /// Shared-reference lookup with a key for a *different* type `T`.
    ///
    /// Looks up the slot via key_data + map_id, gets the data pointer,
    /// then combines it with `key.metadata()` to produce `&T`.
    #[inline]
    pub fn get_as<T: ?Sized + Pointee, CKIn>(
        &self,
        key: CKIn,
    ) -> Option<&T>
    where
        CKIn: CastableKey<T, Idx=CK::Idx, Gen=CK::Gen>,
        <T as Pointee>::Metadata: Copy,
    {
        let base_ref: &D::Target = self.inner.get(to_inner(&key))?;
        let data_ptr: *const () = (base_ref as *const D::Target).cast();
        let fat_ptr: *const T = std::ptr::from_raw_parts(data_ptr, key.metadata());
        unsafe { Some(&*fat_ptr) }
    }

    /// Mutable-reference lookup with a differently-typed key.
    #[inline]
    pub fn get_as_mut<T: ?Sized + Pointee, CKIn>(
        &mut self,
        key: CKIn,
    ) -> Option<&mut T>
    where
        CKIn: CastableKey<T, Idx=CK::Idx, Gen=CK::Gen> + CoerceUnsized<CK>,
        <T as Pointee>::Metadata: Copy,
        D: std::ops::DerefMut,
    {
        let base_ref: &mut D::Target = self.inner.get_mut(to_inner(&key))?;
        let data_ptr: *mut () = (base_ref as *mut D::Target).cast();
        let fat_ptr: *mut T = std::ptr::from_raw_parts_mut(data_ptr, key.metadata());
        unsafe { Some(&mut *fat_ptr) }
    }

    /// Removes using a differently-typed key.
    #[inline]
    pub fn remove_by<T: ?Sized + Pointee, CKIn>(
        &mut self,
        key: CKIn,
    ) -> Option<D>
    where
        CKIn: CastableKey<T, Idx=CK::Idx, Gen=CK::Gen>,
        <T as Pointee>::Metadata: Copy,
    {
        self.inner.remove(to_inner(&key))
    }
}

// ─── Index / IndexMut ───────────────────────────────────────────────────────

impl<CK, D> Index<CK> for KeyCastableStableGenMap<CK, D>
where
    CK: CastableKey<D::Target>,
    D: DerefGenMapPromise + 'static,
    <D::Target as Pointee>::Metadata: Copy,
{
    type Output = D::Target;

    fn index(&self, key: CK) -> &Self::Output {
        self.get(key).unwrap()
    }
}

impl<CK, D> IndexMut<CK> for KeyCastableStableGenMap<CK, D>
where
    CK: CastableKey<D::Target>,
    D: DerefGenMapPromise + 'static + std::ops::DerefMut,
    <D::Target as Pointee>::Metadata: Copy,
{
    fn index_mut(&mut self, key: CK) -> &mut Self::Output {
        self.get_mut(key).unwrap()
    }
}

// ─── IterMut ────────────────────────────────────────────────────────────────

pub struct IterMut<'a, CK: CastableKey<D::Target>, D: DerefGenMapPromise> {
    inner: gen_map::IterMut<'a, CastableInnerKey<<CK as CastableKey<D::Target>>::Idx, <CK as CastableKey<D::Target>>::Gen>,
        DerefSlot<D, CastableInnerKey<<CK as CastableKey<D::Target>>::Idx, <CK as CastableKey<D::Target>>::Gen>>>,
    _phantom: std::marker::PhantomData<fn() -> CK>,
}

impl<'a, CK, D> Iterator for IterMut<'a, CK, D>
where
    CK: CastableKey<D::Target>,
    D: DerefGenMapPromise + 'static,
    <D::Target as Pointee>::Metadata: Copy,
{
    type Item = (CK, &'a mut D);

    fn next(&mut self) -> Option<Self::Item> {
        let (inner_key, stored) = self.inner.next()?;
        let patched = to_castable::<CK, D>(inner_key, &**stored);
        Some((patched, stored))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

// ─── Drain ──────────────────────────────────────────────────────────────────

pub struct Drain<'a, CK: CastableKey<D::Target>, D: DerefGenMapPromise> {
    inner: gen_map::Drain<'a, CastableInnerKey<<CK as CastableKey<D::Target>>::Idx, <CK as CastableKey<D::Target>>::Gen>,
        DerefSlot<D, CastableInnerKey<<CK as CastableKey<D::Target>>::Idx, <CK as CastableKey<D::Target>>::Gen>>>,
    _phantom: std::marker::PhantomData<fn() -> CK>,
}

impl<'a, CK, D> Iterator for Drain<'a, CK, D>
where
    CK: CastableKey<D::Target>,
    D: DerefGenMapPromise + 'static,
    <D::Target as Pointee>::Metadata: Copy,
{
    type Item = (CK, D);

    fn next(&mut self) -> Option<Self::Item> {
        let (inner_key, value) = self.inner.next()?;
        let patched = to_castable::<CK, D>(inner_key, &*value);
        Some((patched, value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

// ─── IntoIter (owning) ─────────────────────────────────────────────────────

pub struct IntoIter<CK: CastableKey<D::Target>, D: DerefGenMapPromise> {
    inner: gen_map::IntoIter<CastableInnerKey<<CK as CastableKey<D::Target>>::Idx, <CK as CastableKey<D::Target>>::Gen>,
        DerefSlot<D, CastableInnerKey<<CK as CastableKey<D::Target>>::Idx, <CK as CastableKey<D::Target>>::Gen>>>,
    _phantom: std::marker::PhantomData<fn() -> CK>,
}

impl<CK, D> Iterator for IntoIter<CK, D>
where
    CK: CastableKey<D::Target>,
    D: DerefGenMapPromise + 'static,
    <D::Target as Pointee>::Metadata: Copy,
{
    type Item = (CK, D);

    fn next(&mut self) -> Option<Self::Item> {
        let (inner_key, value) = self.inner.next()?;
        let patched = to_castable::<CK, D>(inner_key, &*value);
        Some((patched, value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<CK, D> IntoIterator for KeyCastableStableGenMap<CK, D>
where
    CK: CastableKey<D::Target>,
    D: DerefGenMapPromise + 'static,
    <D::Target as Pointee>::Metadata: Copy,
{
    type Item = (CK, D);
    type IntoIter = IntoIter<CK, D>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.inner.into_iter(),
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<'a, CK, D> IntoIterator for &'a mut KeyCastableStableGenMap<CK, D>
where
    CK: CastableKey<D::Target>,
    D: DerefGenMapPromise + 'static,
    <D::Target as Pointee>::Metadata: Copy,
{
    type Item = (CK, &'a mut D);
    type IntoIter = IterMut<'a, CK, D>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

// ─── Type alias ─────────────────────────────────────────────────────────────

/// Convenience alias: [`KeyCastableStableGenMap`] storing `Box<T>`.
pub type KeyCastableBoxStableGenMap<CK, T: ?Sized> =
KeyCastableStableGenMap<CK, Box<T>>;