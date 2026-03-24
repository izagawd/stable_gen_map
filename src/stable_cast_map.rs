//! Map type that uses a [`CastKey`] as its user-facing key.
//!
//! Internally, a plain [`CastableInnerKey`] (which implements [`Key`] with
//! `Extra = MapId`) is used by the `GenMap`. The castable map wrapper
//! converts between `CastableInnerKey` and `CastKey` at every
//! boundary — adding metadata on the way out, stripping it on the way in.
//!
//! This means `GenMap` never sees pointer metadata and no `dangling_metadata`
//! hack is needed.

use std::any::Any;
use std::collections::TryReserveError;
use std::ops::{Index, IndexMut};
use std::ptr::Pointee;

use crate::cast_key::CastKey;
use crate::gen_map;
use crate::stable_deref_map::{
    DerefGenMapPromise, DerefSlot, SmartPtrCloneable, StableDerefMap,
};

// ─── Conversion helpers ─────────────────────────────────────────────────────

/// Strip metadata, produce inner key.
#[inline]
fn to_inner<CK: CastKey>(key: &CK) -> CK::InnerKey {
    key.inner_key()
}

/// Build a castable key from an inner key + metadata from a reference.
#[inline]
fn to_castable<CK, D>(inner: CK::InnerKey, reference: &D::Target) -> CK
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise,
{
    let metadata = std::ptr::metadata(reference as *const D::Target);
    unsafe { CK::from_inner_key_and_metadata(inner, metadata) }
}

// ─── KeyCastableStableGenMap ────────────────────────────────────────────────

/// A [`StableDerefMap`] wrapper that supports typed lookups via
/// [`CastKey`].
///
/// - `CK`: the castable key family, e.g. `DefaultCastKey<D::Target>`.
/// - `D`: the smart pointer type, e.g. `Box<dyn Any>`.
pub struct StableCastMap<CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise + 'static,
{
    pub(crate) inner: StableDerefMap<CK::InnerKey, D>,
    _phantom: std::marker::PhantomData<fn() -> CK>,
}

// ─── Clone ──────────────────────────────────────────────────────────────────

impl<CK, D> Clone for StableCastMap<CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise + SmartPtrCloneable + 'static,
{
    /// Clones the map.
    ///
    /// Keys obtained before the clone are valid on **both** the original and
    /// the clone. New inserts into either map produce keys that are only
    /// valid on that map.
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            _phantom: std::marker::PhantomData,
        }
    }
}

// ─── Basic methods ──────────────────────────────────────────────────────────

impl<CK, D> StableCastMap<CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise + 'static,
{
    /// Creates a new, empty map.
    #[inline]
    pub const fn new() -> Self {
        Self {
            inner: StableDerefMap::new(),
            _phantom: std::marker::PhantomData,
        }
    }

    /// Creates a new map with the given pre-allocated capacity.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: StableDerefMap::with_capacity(capacity),
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

// ─── Native operations (CK: CastKey<RefType = D::Target>) ──────────────────

impl<CK, D> StableCastMap<CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise,
{
    /// Attempts to downcast a `CastKey<RefType = dyn Any>` to a `CastKey<RefType = Concrete>`.
    ///
    /// Looks up the actual data to obtain its `TypeId` (no UB). Returns
    /// `None` if the key is stale / wrong map, or the concrete type doesn't match.
    ///
    /// # Example
    /// ```ignore
    /// let dyn_key: DefaultCastKey<dyn Any> = key;
    /// if let Some(concrete) = map.downcast_key::<MyStruct, DefaultCastKey<MyStruct>>(dyn_key) {
    ///     // concrete: DefaultCastKey<MyStruct>
    /// }
    /// ```
    #[inline]
    pub fn downcast_key<Concrete: 'static, KOut>(
        &self,
        key: impl CastKey<RefType = dyn Any, Idx = CK::Idx, Gen = CK::Gen, InnerKey = CK::InnerKey>,
    ) -> Option<KOut>
    where
        KOut: CastKey<RefType = Concrete, Idx = CK::Idx, Gen = CK::Gen>,
    {
        let data: &_ = self.inner.get(to_inner(&key))?;
        let data_as_any_from_key: &dyn Any =
            unsafe { &*std::ptr::from_raw_parts(data as *const _ as *const (), key.metadata()) };
        if data_as_any_from_key.type_id() == std::any::TypeId::of::<Concrete>() {
            Some(unsafe { KOut::from_castable_parts(key.key_data(), key.map_id(), ()) })
        } else {
            None
        }
    }

    // ── insert ──────────────────────────────────────────────────────────

    /// Inserts a smart pointer, returning a key (with real metadata) and a
    /// reference to the deref target.
    #[inline]
    pub fn insert(&self, value: D) -> (CK, &D::Target) {
        let (inner_key, reference) = self.inner.insert(value);
        (to_castable::<CK, D>(inner_key, reference), reference)
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

    // ── inner-key access ────────────────────────────────────────────────

    /// Shared-reference lookup using the inner key (without pointer metadata).
    ///
    /// Returns `&D::Target` directly — no castable key is reconstructed,
    /// so this is slightly cheaper than [`get`](Self::get).
    #[inline]
    pub fn get_by_inner_key(&self, key: CK::InnerKey) -> Option<&D::Target> {
        self.inner.get(key)
    }

    /// Mutable-reference lookup using the inner key.
    #[inline]
    pub fn get_mut_by_inner_key(&mut self, key: CK::InnerKey) -> Option<&mut D::Target>
    where
        D: std::ops::DerefMut,
    {
        self.inner.get_mut(key)
    }

    /// Removes an element by inner key, returning the owned smart pointer.
    #[inline]
    pub fn remove_by_inner_key(&mut self, key: CK::InnerKey) -> Option<D> {
        self.inner.remove(key)
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
            vec.extend(
                self.inner
                    .iter_unsafe()
                    .map(|(inner_key, reference)| to_castable::<CK, D>(inner_key, reference)),
            );
            vec
        }
    }

    // ── iter_unsafe ─────────────────────────────────────────────────────

    /// # Safety
    /// No mutation (including `insert`) may occur while iterating.
    #[inline]
    pub unsafe fn iter_unsafe(&self) -> impl Iterator<Item = (CK, &D::Target)> {
        self.inner
            .iter_unsafe()
            .map(|(inner_key, reference)| (to_castable::<CK, D>(inner_key, reference), reference))
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

// ─── downcast_key (requires D::Target = dyn Any) ───────────────────────────

// ─── Cross-typed lookups ────────────────────────────────────────────────────

impl<CK, D> StableCastMap<CK, D>
where
    D: DerefGenMapPromise + 'static,
    CK: CastKey<RefType = <D as std::ops::Deref>::Target>,
{
    /// Shared-reference lookup with a key for a potentially *different* type `T`.
    ///
    /// Looks up the slot via key_data + map_id, gets the data pointer,
    /// then combines it with `key.metadata()` to produce `&T`.
    #[inline]
    pub fn get<T: ?Sized + Pointee>(
        &self,
        key: impl CastKey<RefType = T, Idx = CK::Idx, Gen = CK::Gen, InnerKey = CK::InnerKey>,
    ) -> Option<&T>
    where
        <T as Pointee>::Metadata: Copy,
    {
        let base_ref: &D::Target = self.inner.get(to_inner(&key))?;
        let data_ptr: *const () = (base_ref as *const D::Target).cast();
        let fat_ptr: *const T = std::ptr::from_raw_parts(data_ptr, key.metadata());
        unsafe { Some(&*fat_ptr) }
    }

    /// Mutable-reference lookup with a potentially differently-typed key.
    #[inline]
    pub fn get_mut<T: ?Sized + Pointee>(
        &mut self,
        key: impl CastKey<RefType = T, Idx = CK::Idx, Gen = CK::Gen, InnerKey = CK::InnerKey>,
    ) -> Option<&mut T>
    where
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
    pub fn remove_by<T: ?Sized + Pointee>(
        &mut self,
        key: impl CastKey<RefType = T, Idx = CK::Idx, Gen = CK::Gen, InnerKey = CK::InnerKey>,
    ) -> Option<D>
    where
        <T as Pointee>::Metadata: Copy,
    {
        self.inner.remove(to_inner(&key))
    }
}

// ─── Index / IndexMut ───────────────────────────────────────────────────────

impl<CK, D> Index<CK> for StableCastMap<CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise + 'static,
{
    type Output = D::Target;

    fn index(&self, key: CK) -> &Self::Output {
        self.get(key).unwrap()
    }
}

impl<CK, D> IndexMut<CK> for StableCastMap<CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise + 'static + std::ops::DerefMut,
{
    fn index_mut(&mut self, key: CK) -> &mut Self::Output {
        self.get_mut(key).unwrap()
    }
}

// ─── IterMut ────────────────────────────────────────────────────────────────

/// Mutable iterator over all occupied elements of a
/// [`StableCastMap`]. Yields `(Key, &mut Item)` pairs with properly
/// patched castable keys.
///
/// Created by [`StableCastMap::iter_mut`].
pub struct IterMut<'a, CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise,
{
    inner: gen_map::IterMut<'a, CK::InnerKey, DerefSlot<D, CK::InnerKey>>,
    _phantom: std::marker::PhantomData<fn() -> CK>,
}

impl<'a, CK, D> Iterator for IterMut<'a, CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise + 'static,
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

/// Draining iterator over a [`StableCastMap`]. Yields all
/// occupied `(Key, Item)` pairs, removing them from the map.
///
/// Created by [`StableCastMap::drain`].
pub struct Drain<'a, CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise,
{
    inner: gen_map::Drain<'a, CK::InnerKey, DerefSlot<D, CK::InnerKey>>,
    _phantom: std::marker::PhantomData<fn() -> CK>,
}

impl<'a, CK, D> Iterator for Drain<'a, CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise + 'static,
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

/// Owning iterator over a [`StableCastMap`]. Consumes the map
/// and yields all occupied `(Key, Item)` pairs.
pub struct IntoIter<CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise,
{
    inner: gen_map::IntoIter<CK::InnerKey, DerefSlot<D, CK::InnerKey>>,
    _phantom: std::marker::PhantomData<fn() -> CK>,
}

impl<CK, D> Iterator for IntoIter<CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise + 'static,
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

impl<CK, D> IntoIterator for StableCastMap<CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise + 'static,
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

impl<'a, CK, D> IntoIterator for &'a mut StableCastMap<CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise + 'static,
{
    type Item = (CK, &'a mut D);
    type IntoIter = IterMut<'a, CK, D>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

// ─── Type alias ─────────────────────────────────────────────────────────────

/// Convenience alias: [`StableCastMap`] storing `Box<T>`.
pub type StableBoxCastMap<CK, T: ?Sized> = StableCastMap<CK, Box<T>>;
