//! Safe wrapper around [`UnsafeCastMap`](crate::unsafe_cast_map::UnsafeCastMap)
//! that binds keys to the map that created them via a [`MapId`].
//!
//! Every [`StableCastKey`](crate::cast_key::StableCastKey) carries the
//! map's identity. Keyed lookups check the id before touching pointer
//! metadata, so a key from map A used on map B returns `None` instead
//! of causing UB.

use std::any::Any;
use std::cell::UnsafeCell;
use std::collections::TryReserveError;
use std::ops::{Deref, DerefMut};
use std::ptr::Pointee;

use crate::cast_key::{CastKey, StableCastKey};
use crate::gen_map::{IdxOfStorage, KeyOfStorage, Slot};
use crate::key::Key;
use crate::map_id::MapId;
use crate::slot_item::{SlotStorage, SlotStorageClone, SlotStorageMutOutput};
use crate::stable_deref_map::{DerefGenMapPromise, DerefSlot};
use crate::unsafe_cast_map;
use crate::unsafe_cast_map::UnsafeCastMap;

// ─── helpers ────────────────────────────────────────────────────────────────

#[inline]
fn stabilize<T: ?Sized + Pointee, K: Key>(key: CastKey<T, K>, map_id: MapId) -> StableCastKey<T, K>
where
    <T as Pointee>::Metadata: Copy,
{
    StableCastKey { inner: key, map_id }
}

// ─── StableCastMap ──────────────────────────────────────────────────────────

/// A safe wrapper around [`UnsafeCastMap`] that checks a per-map
/// [`MapId`] on every keyed access.
///
/// `C` is the per-slot storage strategy (e.g.
/// [`DerefSlot<DefaultKey, Box<dyn Any>>`]).
pub struct StableCastMap<C: SlotStorage>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
{
    inner: UnsafeCastMap<C>,
    map_id: MapId,
}

// ─── Clone ──────────────────────────────────────────────────────────────────

impl<C: SlotStorage> Clone for StableCastMap<C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
    UnsafeCastMap<C>: Clone,
{
    /// Clones the map.
    ///
    /// The clone receives a fresh map identity. Keys from the original are
    /// **not** valid on the clone; use iteration to obtain new keys.
    #[inline]
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            map_id: MapId::next(),
        }
    }
}

// ─── Basic methods ──────────────────────────────────────────────────────────

impl<C: SlotStorage> StableCastMap<C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
{
    /// Creates a new, empty map with a fresh [`MapId`].
    #[inline]
    pub fn new() -> Self {
        Self {
            inner: UnsafeCastMap::new(),
            map_id: MapId::next(),
        }
    }

    /// Returns true if the map is empty
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Creates a new map with the given pre-allocated capacity.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: UnsafeCastMap::with_capacity(capacity),
            map_id: MapId::next(),
        }
    }

    /// Returns this map's unique identity.
    #[inline]
    pub fn map_id(&self) -> MapId {
        self.map_id
    }

    /// Reserves capacity for at least `additional` more elements.
    #[inline]
    pub fn reserve(&self, additional: usize) {
        self.inner.reserve(additional);
    }

    /// Tries to reserve capacity for at least `additional` more elements.
    #[inline]
    pub fn try_reserve(&self, additional: usize) -> Result<(), TryReserveError> {
        self.inner.try_reserve(additional)
    }

    /// Returns how many slots the backing storage can hold before reallocating.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Returns the number of occupied elements.
    #[inline]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Removes all elements from the map.
    #[inline]
    pub fn clear(&mut self) {
        self.inner.clear();
    }
}

// ─── Core operations ────────────────────────────────────────────────────────

impl<C: SlotStorage> StableCastMap<C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
    <C::Output as Pointee>::Metadata: Copy,
{
    /// Attempts to downcast a `StableCastKey<dyn Any>` to a concrete type.
    /// Returns `None` if the key belongs to a different map or the type doesn't match.
    #[inline]
    pub fn downcast_key<Concrete: 'static>(
        &self,
        key: StableCastKey<dyn Any, KeyOfStorage<C>>,
    ) -> Option<StableCastKey<Concrete, KeyOfStorage<C>>> {
        if key.map_id != self.map_id {
            return None;
        }
        let inner = unsafe { self.inner.downcast_key::<Concrete>(key.inner) }?;
        Some(stabilize(inner, self.map_id))
    }

    // ── insert ──────────────────────────────────────────────────────────

    /// Inserts a value and returns its [`StableCastKey`] alongside a reference.
    #[inline]
    pub fn insert(
        &self,
        value: C::Stored,
    ) -> (StableCastKey<C::Output, KeyOfStorage<C>>, &C::Output) {
        let (key, reference) = self.inner.insert(value);
        (stabilize(key, self.map_id), reference)
    }

    /// Inserts a value produced by `func`, which receives the backing key.
    #[inline]
    pub fn insert_with_key(
        &self,
        func: impl FnOnce(KeyOfStorage<C>) -> C::Stored,
    ) -> (StableCastKey<C::Output, KeyOfStorage<C>>, &C::Output) {
        let (key, reference) = self.inner.insert_with_key(func);
        (stabilize(key, self.map_id), reference)
    }

    /// Like [`insert_with_key`](Self::insert_with_key) but the closure may fail.
    #[inline]
    pub fn try_insert_with_key<E>(
        &self,
        func: impl FnOnce(KeyOfStorage<C>) -> Result<C::Stored, E>,
    ) -> Result<(StableCastKey<C::Output, KeyOfStorage<C>>, &C::Output), E> {
        let (key, reference) = self.inner.try_insert_with_key(func)?;
        Ok((stabilize(key, self.map_id), reference))
    }

    // ── insert_sized ────────────────────────────────────────────────────

    /// Inserts a concrete-typed smart pointer, returning a typed [`StableCastKey`].
    #[inline]
    pub fn insert_sized<ConcretePtr>(
        &self,
        value: ConcretePtr,
    ) -> (
        StableCastKey<ConcretePtr::Target, KeyOfStorage<C>>,
        &ConcretePtr::Target,
    )
    where
        ConcretePtr: std::ops::CoerceUnsized<C::Stored> + Deref,
        ConcretePtr::Target: Sized,
    {
        let (key, reference) = self.inner.insert_sized(value);
        (stabilize(key, self.map_id), reference)
    }

    /// Like [`insert_sized`](Self::insert_sized) but the closure receives a typed key.
    #[inline]
    pub fn insert_sized_with_key<ConcretePtr>(
        &self,
        func: impl FnOnce(StableCastKey<ConcretePtr::Target, KeyOfStorage<C>>) -> ConcretePtr,
    ) -> (
        StableCastKey<ConcretePtr::Target, KeyOfStorage<C>>,
        &ConcretePtr::Target,
    )
    where
        ConcretePtr: std::ops::CoerceUnsized<C::Stored> + Deref,
        ConcretePtr::Target: Sized,
    {
        let map_id = self.map_id;
        let (key, reference) = self
            .inner
            .insert_sized_with_key(|ck| func(stabilize(ck, map_id)));
        (stabilize(key, self.map_id), reference)
    }

    /// Fallible version of [`insert_sized_with_key`](Self::insert_sized_with_key).
    #[inline]
    pub fn try_insert_sized_with_key<ConcretePtr, E>(
        &self,
        func: impl FnOnce(StableCastKey<ConcretePtr::Target, KeyOfStorage<C>>) -> Result<ConcretePtr, E>,
    ) -> Result<
        (
            StableCastKey<ConcretePtr::Target, KeyOfStorage<C>>,
            &ConcretePtr::Target,
        ),
        E,
    >
    where
        ConcretePtr: std::ops::CoerceUnsized<C::Stored> + Deref,
        ConcretePtr::Target: Sized,
    {
        let map_id = self.map_id;
        let (key, reference) = self
            .inner
            .try_insert_sized_with_key(|ck| func(stabilize(ck, map_id)))?;
        Ok((stabilize(key, self.map_id), reference))
    }

    // ── insert_as ───────────────────────────────────────────────────────

    /// Inserts a smart pointer, preserving the source pointer's metadata.
    #[inline]
    pub fn insert_as<SourcePtr>(
        &self,
        value: SourcePtr,
    ) -> (
        StableCastKey<SourcePtr::Target, KeyOfStorage<C>>,
        &SourcePtr::Target,
    )
    where
        SourcePtr: std::ops::CoerceUnsized<C::Stored> + Deref,
        SourcePtr::Target: Pointee<Metadata: Copy>,
    {
        let (key, reference) = self.inner.insert_as(value);
        (stabilize(key, self.map_id), reference)
    }

    /// Like [`insert_as`](Self::insert_as) but the closure receives the backing key.
    #[inline]
    pub fn insert_as_with_key<SourcePtr>(
        &self,
        func: impl FnOnce(KeyOfStorage<C>) -> SourcePtr,
    ) -> (
        StableCastKey<SourcePtr::Target, KeyOfStorage<C>>,
        &SourcePtr::Target,
    )
    where
        SourcePtr: std::ops::CoerceUnsized<C::Stored> + Deref,
        SourcePtr::Target: Pointee<Metadata: Copy>,
    {
        let (key, reference) = self.inner.insert_as_with_key(func);
        (stabilize(key, self.map_id), reference)
    }

    /// Fallible version of [`insert_as_with_key`](Self::insert_as_with_key).
    #[inline]
    pub fn try_insert_as_with_key<SourcePtr, E>(
        &self,
        func: impl FnOnce(KeyOfStorage<C>) -> Result<SourcePtr, E>,
    ) -> Result<
        (
            StableCastKey<SourcePtr::Target, KeyOfStorage<C>>,
            &SourcePtr::Target,
        ),
        E,
    >
    where
        SourcePtr: std::ops::CoerceUnsized<C::Stored> + Deref,
        SourcePtr::Target: Pointee<Metadata: Copy>,
    {
        let (key, reference) = self.inner.try_insert_as_with_key(func)?;
        Ok((stabilize(key, self.map_id), reference))
    }

    // ── inner accessors ─────────────────────────────────────────────────

    /// Consumes this map and returns the underlying [`UnsafeCastMap`].
    #[inline]
    pub fn inner(self) -> UnsafeCastMap<C> {
        self.inner
    }

    /// Returns a mutable reference to the underlying [`UnsafeCastMap`].
    #[inline]
    pub fn inner_mut(&mut self) -> &mut UnsafeCastMap<C> {
        &mut self.inner
    }

    /// Returns a shared reference to the underlying [`UnsafeCastMap`].
    #[inline]
    pub fn inner_ref(&self) -> &UnsafeCastMap<C> {
        &self.inner
    }

    // ── get_by_index_only ───────────────────────────────────────────────

    /// Looks up by slot index only (ignores generation).
    #[inline]
    pub fn get_by_index_only(
        &self,
        idx: IdxOfStorage<C>,
    ) -> Option<(StableCastKey<C::Output, KeyOfStorage<C>>, &C::Output)> {
        let (key, reference) = self.inner.get_by_index_only(idx)?;
        Some((stabilize(key, self.map_id), reference))
    }

    /// Mutable version of [`get_by_index_only`](Self::get_by_index_only).
    #[inline]
    pub fn get_by_index_only_mut(
        &mut self,
        idx: IdxOfStorage<C>,
    ) -> Option<(StableCastKey<C::Output, KeyOfStorage<C>>, &mut C::Output)>
    where
        C: SlotStorageMutOutput,
    {
        let (key, reference) = self.inner.get_by_index_only_mut(idx)?;
        Some((stabilize(key, self.map_id), reference))
    }
    // ── get_slot ────────────────────────────────────────────────────────
    /// Returns a reference to the raw [`Slot`] at the given index.
    ///
    /// Performs bounds checking. Returns `None` if out of bounds.
    ///
    /// # Safety
    /// The returned slot exposes internal data structures. The caller
    /// must check occupancy before accessing the slot's value.
    ///
    /// **Holding a `&Slot` reference, performing an `insert`, and then
    /// accessing that old `&Slot` is undefined behaviour.** `insert` only
    /// requires `&self` and may reallocate the backing storage, which
    /// invalidates all previously obtained slot references.
    #[inline]
    pub unsafe fn get_slot(&self, idx: IdxOfStorage<C>) -> Option<&Slot<C>> {
        self.inner.get_slot(idx)
    }
    /// Returns a reference to the raw [`Slot`] without bounds checking.
    ///
    /// # Safety
    /// - The index must be in bounds.
    /// - The caller must check occupancy before accessing the slot's value.
    ///
    /// **Holding a `&Slot` reference, performing an `insert`, and then
    /// accessing that old `&Slot` is undefined behaviour.** `insert` only
    /// requires `&self` and may reallocate the backing storage, which
    /// invalidates all previously obtained slot references.
    #[inline]
    pub unsafe fn get_slot_unchecked(&self, idx: IdxOfStorage<C>) -> &Slot<C> {
        self.inner.get_slot_unchecked(idx)
    }
    /// Returns a reference to the raw [`UnsafeCell`] wrapping the [`Slot`]
    /// at the given index.
    ///
    /// Performs bounds checking. Returns `None` if out of bounds.
    ///
    /// # Safety
    /// The returned cell exposes internal data structures. The caller
    /// must check occupancy before accessing the slot's value.
    ///
    /// **Holding a cell reference, performing an `insert`, and then
    /// accessing that old reference or any of its contents is undefined behaviour.** `insert` only
    /// requires `&self` and may reallocate the backing storage, which
    /// invalidates all previously obtained references.
    #[inline]
    pub unsafe fn get_slot_as_cell(&self, idx: IdxOfStorage<C>) -> Option<&UnsafeCell<Slot<C>>> {
        self.inner.get_slot_as_cell(idx)
    }
    /// Returns a reference to the raw [`UnsafeCell`] wrapping the [`Slot`]
    /// without bounds checking.
    ///
    /// # Safety
    /// - The index must be in bounds.
    /// - The caller must check occupancy before accessing the slot's value.
    ///
    /// **Holding a cell reference, performing an `insert`, and then
    /// accessing that old reference or any of its contents is undefined behaviour.** `insert` only
    /// requires `&self` and may reallocate the backing storage, which
    /// invalidates all previously obtained references.
    #[inline]
    pub unsafe fn get_slot_as_cell_unchecked(&self, idx: IdxOfStorage<C>) -> &UnsafeCell<Slot<C>> {
        self.inner.get_slot_as_cell_unchecked(idx)
    }
    /// Returns a mutable reference to the raw [`Slot`] at the given index.
    ///
    /// Performs bounds checking. Returns `None` if out of bounds.
    ///
    /// # Safety
    /// The returned slot exposes internal data structures. The caller
    /// must not use this to violate map invariants, and must check
    /// occupancy before accessing the slot's value.
    #[inline]
    pub unsafe fn get_slot_mut(&mut self, idx: IdxOfStorage<C>) -> Option<&mut Slot<C>> {
        self.inner.get_slot_mut(idx)
    }
    /// Returns a mutable reference to the raw [`Slot`] without bounds checking.
    ///
    /// # Safety
    /// - The index must be in bounds.
    /// - The caller must not use this to violate map invariants, and must
    ///   check occupancy before accessing the slot's value.
    #[inline]
    pub unsafe fn get_slot_unchecked_mut(&mut self, idx: IdxOfStorage<C>) -> &mut Slot<C> {
        self.inner.get_slot_unchecked_mut(idx)
    }
    /// Safe wrapper around [`clone_efficiently`](Self::clone_efficiently):
    /// the `&mut self` borrow prevents the stored type's `Clone` from
    /// mutating the map.
    #[inline]
    pub fn clone_efficiently_mut(&mut self) -> Self
    where
        C: SlotStorageClone,
    {
        Self {
            inner: self.inner.clone_efficiently_mut(),
            map_id: MapId::next(),
        }
    }

    /// Efficient clone with a fresh [`MapId`]. **UB** if `Clone` mutates the map.
    ///
    /// # Safety
    /// The stored type's `Clone` must not call any method on this map.
    #[inline]
    pub unsafe fn clone_efficiently(&self) -> Self
    where
        C: SlotStorageClone,
    {
        Self {
            inner: self.inner.clone_efficiently(),
            map_id: MapId::next(),
        }
    }

    // ── inner-key access ──────────────────────────────────────────────

    /// Shared-reference lookup using the backing [`Key`] directly (no map-id check).
    #[inline]
    pub fn get_by_inner_key(&self, key: KeyOfStorage<C>) -> Option<&C::Output> {
        self.inner.get_by_inner_key(key)
    }

    /// Mutable-reference lookup using the backing [`Key`] directly.
    #[inline]
    pub fn get_by_inner_key_mut(&mut self, key: KeyOfStorage<C>) -> Option<&mut C::Output>
    where
        C: SlotStorageMutOutput,
    {
        self.inner.get_by_inner_key_mut(key)
    }

    /// Removes an element by its backing [`Key`].
    #[inline]
    pub fn remove_by_inner_key(&mut self, key: KeyOfStorage<C>) -> Option<C::Stored> {
        self.inner.remove_by_inner_key(key)
    }

    /// Converts a backing [`Key`] into a [`StableCastKey`] by reading pointer
    /// metadata from the stored value. Returns `None` if the key is stale.
    #[inline]
    pub fn cast_key_of(
        &self,
        inner: KeyOfStorage<C>,
    ) -> Option<StableCastKey<C::Output, KeyOfStorage<C>>> {
        let key = self.inner.cast_key_of(inner)?;
        Some(stabilize(key, self.map_id))
    }

    // ── retain ──────────────────────────────────────────────────────────

    /// Retains only elements for which `f(key, &mut output)` returns `true`.
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(StableCastKey<C::Output, KeyOfStorage<C>>, &mut C::Output) -> bool,
        C::Stored: DerefMut,
    {
        let map_id = self.map_id;
        self.inner.retain(|ck, val| f(stabilize(ck, map_id), val));
    }

    // ── snapshot ────────────────────────────────────────────────────────

    /// Returns a snapshot of all `(StableCastKey, &output)` pairs.
    #[inline]
    pub fn snapshot(&self) -> Vec<(StableCastKey<C::Output, KeyOfStorage<C>>, &C::Output)> {
        unsafe {
            let map_id = self.map_id;
            let mut vec = Vec::with_capacity(self.inner.len());
            vec.extend(
                self.inner
                    .iter_unsafe()
                    .map(|(ck, r)| (stabilize(ck, map_id), r)),
            );
            vec
        }
    }

    /// Returns a snapshot of `&output` references only.
    #[inline]
    pub fn snapshot_refs(&self) -> Vec<&C::Output> {
        self.inner.snapshot_refs()
    }

    /// Returns a snapshot of all [`StableCastKey`]s.
    #[inline]
    pub fn snapshot_keys(&self) -> Vec<StableCastKey<C::Output, KeyOfStorage<C>>> {
        unsafe {
            let map_id = self.map_id;
            let mut vec = Vec::with_capacity(self.inner.len());
            vec.extend(
                self.inner
                    .iter_unsafe()
                    .map(|(ck, _)| stabilize(ck, map_id)),
            );
            vec
        }
    }

    // ── iter_unsafe ─────────────────────────────────────────────────────

    /// Shared iterator over all occupied elements.
    ///
    /// # Safety
    /// No mutation (including `insert`) may occur while iterating.
    #[inline]
    pub unsafe fn iter_unsafe(
        &self,
    ) -> impl Iterator<Item = (StableCastKey<C::Output, KeyOfStorage<C>>, &C::Output)> {
        let map_id = self.map_id;
        self.inner
            .iter_unsafe()
            .map(move |(ck, r)| (stabilize(ck, map_id), r))
    }

    // ── iter_mut ────────────────────────────────────────────────────────

    /// Mutable iterator over all occupied elements.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, C> {
        IterMut {
            inner: self.inner.iter_mut(),
            map_id: self.map_id,
        }
    }

    // ── drain ───────────────────────────────────────────────────────────

    /// Draining iterator. Removes all elements and yields them.
    #[inline]
    pub fn drain(&mut self) -> Drain<'_, C> {
        Drain {
            inner: self.inner.drain(),
            map_id: self.map_id,
        }
    }
}

// ─── Cross-typed lookups (safe — map-id validated) ──────────────────────────

impl<C: SlotStorage> StableCastMap<C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
    <C::Output as Pointee>::Metadata: Copy,
{
    /// Typed lookup by [`StableCastKey`]. Returns `None` if the key belongs
    /// to a different map or the slot is no longer occupied.
    #[inline]
    pub fn get<T: ?Sized + Pointee>(&self, key: StableCastKey<T, KeyOfStorage<C>>) -> Option<&T>
    where
        <T as Pointee>::Metadata: Copy,
    {
        if key.map_id != self.map_id {
            return None;
        }
        unsafe { self.inner.get(key.inner) }
    }

    /// Mutable typed lookup by [`StableCastKey`].
    #[inline]
    pub fn get_mut<T: ?Sized + Pointee>(
        &mut self,
        key: StableCastKey<T, KeyOfStorage<C>>,
    ) -> Option<&mut T>
    where
        <T as Pointee>::Metadata: Copy,
        C: SlotStorageMutOutput,
    {
        if key.map_id != self.map_id {
            return None;
        }
        unsafe { self.inner.get_mut(key.inner) }
    }

    /// Shared-reference lookup without bounds, generation, or map-id checks.
    ///
    /// # Safety
    /// - The key's index must be in bounds.
    /// - The slot at that index must be occupied with the matching generation.
    /// - The key's pointer metadata must be valid for the data in that slot.
    #[inline]
    pub unsafe fn get_unchecked<T: ?Sized + Pointee>(
        &self,
        key: StableCastKey<T, KeyOfStorage<C>>,
    ) -> &T
    where
        <T as Pointee>::Metadata: Copy,
    {
        self.inner.get_unchecked(key.inner)
    }

    /// Mutable-reference lookup without bounds, generation, or map-id checks.
    ///
    /// # Safety
    /// - The key's index must be in bounds.
    /// - The slot at that index must be occupied with the matching generation.
    /// - The key's pointer metadata must be valid for the data in that slot.
    #[inline]
    pub unsafe fn get_unchecked_mut<T: ?Sized + Pointee>(
        &mut self,
        key: StableCastKey<T, KeyOfStorage<C>>,
    ) -> &mut T
    where
        <T as Pointee>::Metadata: Copy,
        C: SlotStorageMutOutput,
    {
        self.inner.get_unchecked_mut(key.inner)
    }

    /// Removes an element by its [`StableCastKey`]. Returns `None` if the key
    /// belongs to a different map.
    #[inline]
    pub fn remove<T: ?Sized + Pointee>(
        &mut self,
        key: StableCastKey<T, KeyOfStorage<C>>,
    ) -> Option<C::Stored>
    where
        <T as Pointee>::Metadata: Copy,
    {
        if key.map_id != self.map_id {
            return None;
        }
        self.inner.remove(key.inner)
    }
}

// ─── Index / IndexMut ───────────────────────────────────────────────────────

impl<C: SlotStorage> std::ops::Index<StableCastKey<C::Output, KeyOfStorage<C>>> for StableCastMap<C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
    <C::Output as Pointee>::Metadata: Copy,
{
    type Output = C::Output;

    #[inline]
    fn index(&self, key: StableCastKey<C::Output, KeyOfStorage<C>>) -> &Self::Output {
        self.get(key).unwrap()
    }
}

impl<C: SlotStorage + SlotStorageMutOutput>
    std::ops::IndexMut<StableCastKey<C::Output, KeyOfStorage<C>>> for StableCastMap<C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
    <C::Output as Pointee>::Metadata: Copy,
{
    #[inline]
    fn index_mut(&mut self, key: StableCastKey<C::Output, KeyOfStorage<C>>) -> &mut Self::Output {
        self.get_mut(key).unwrap()
    }
}

/// Convenience alias: [`StableCastMap`] using `Box<T>` with a configurable key.
pub type StableBoxCastMap<K, T> = StableCastMap<DerefSlot<K, Box<T>>>;

// ─── IterMut ────────────────────────────────────────────────────────────────

pub struct IterMut<'a, C: SlotStorage>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
{
    inner: unsafe_cast_map::IterMut<'a, C>,
    map_id: MapId,
}

impl<'a, C: SlotStorage> Iterator for IterMut<'a, C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise + DerefMut + 'a,
    <C::Stored as Deref>::Target: 'a,
    <C::Output as Pointee>::Metadata: Copy,
{
    type Item = (StableCastKey<C::Output, KeyOfStorage<C>>, &'a mut C::Output);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let (ck, val) = self.inner.next()?;
        Some((stabilize(ck, self.map_id), val))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

// ─── Drain ──────────────────────────────────────────────────────────────────

pub struct Drain<'a, C: SlotStorage>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
{
    inner: unsafe_cast_map::Drain<'a, C>,
    map_id: MapId,
}

impl<'a, C: SlotStorage> Iterator for Drain<'a, C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
    <C::Output as Pointee>::Metadata: Copy,
{
    type Item = (StableCastKey<C::Output, KeyOfStorage<C>>, C::Stored);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let (ck, val) = self.inner.next()?;
        Some((stabilize(ck, self.map_id), val))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

// ─── IntoIter (owning) ─────────────────────────────────────────────────────

pub struct IntoIter<C: SlotStorage>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
{
    inner: unsafe_cast_map::IntoIter<C>,
    map_id: MapId,
}

impl<C: SlotStorage> Iterator for IntoIter<C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
    <C::Output as Pointee>::Metadata: Copy,
{
    type Item = (StableCastKey<C::Output, KeyOfStorage<C>>, C::Stored);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let (ck, val) = self.inner.next()?;
        Some((stabilize(ck, self.map_id), val))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<C: SlotStorage> IntoIterator for StableCastMap<C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
    <C::Output as Pointee>::Metadata: Copy,
{
    type Item = (StableCastKey<C::Output, KeyOfStorage<C>>, C::Stored);
    type IntoIter = IntoIter<C>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.inner.into_iter(),
            map_id: self.map_id,
        }
    }
}

impl<'a, C: SlotStorage> IntoIterator for &'a mut StableCastMap<C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise + DerefMut + 'a,
    <C::Stored as Deref>::Target: 'a,
    <C::Output as Pointee>::Metadata: Copy,
{
    type Item = (StableCastKey<C::Output, KeyOfStorage<C>>, &'a mut C::Output);
    type IntoIter = IterMut<'a, C>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}
