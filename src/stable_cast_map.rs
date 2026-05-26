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
use std::ops::{DerefMut, Index, IndexMut};
use std::ptr::Pointee;

use crate::cast_key::{CastKey, InnerCastMapKey, StableCastKey};
use crate::gen_map::Slot;
use crate::key_piece::KeyPiece;
use crate::map_id::MapId;
use crate::stable_deref_map::{DerefGenMapPromise, DerefSlot};
use crate::unsafe_cast_map;
use crate::unsafe_cast_map::UnsafeCastMap;

// ─── helpers ────────────────────────────────────────────────────────────────

#[inline]
fn stabilize<T: ?Sized + Pointee, Idx: Copy, Gen: Copy>(
    key: CastKey<T, Idx, Gen>,
    map_id: MapId,
) -> StableCastKey<T, Idx, Gen>
where
    <T as Pointee>::Metadata: Copy,
{
    StableCastKey {
        inner: key,
        map_id,
    }
}

// ─── StableCastMap ──────────────────────────────────────────────────────────

/// A safe wrapper around [`UnsafeCastMap`] that checks a per-map
/// [`MapId`] on every keyed access.
///
/// - `D`: the smart pointer type, e.g. `Box<dyn Any>`.
/// - `Idx`: index type (default `u32`).
/// - `Gen`: generation type (default `u32`).
pub struct StableCastMap<D, Idx = u32, Gen = u32>
where
    D: DerefGenMapPromise,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    inner: UnsafeCastMap<D, Idx, Gen>,
    map_id: MapId,
}

// ─── Clone ──────────────────────────────────────────────────────────────────

impl<D, Idx, Gen> Clone for StableCastMap<D, Idx, Gen>
where
    D: DerefGenMapPromise + crate::stable_deref_map::SmartPtrCloneable,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    /// Clones the map.
    ///
    /// The clone receives a fresh map identity. Keys from the original are
    /// **not** valid on the clone; use iteration to obtain new keys.
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            map_id: MapId::next(),
        }
    }
}

// ─── Basic methods ──────────────────────────────────────────────────────────

impl<D, Idx, Gen> StableCastMap<D, Idx, Gen>
where
    D: DerefGenMapPromise,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    /// Creates a new, empty map with a fresh [`MapId`].
    #[inline]
    pub fn new() -> Self {
        Self {
            inner: UnsafeCastMap::new(),
            map_id: MapId::next(),
        }
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

    #[inline]
    pub fn reserve(&self, additional: usize) {
        self.inner.reserve(additional);
    }

    #[inline]
    pub fn try_reserve(&self, additional: usize) -> Result<(), TryReserveError> {
        self.inner.try_reserve(additional)
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    #[inline]
    pub fn clear(&mut self) {
        self.inner.clear();
    }
}

// ─── Core operations ────────────────────────────────────────────────────────

impl<D, Idx, Gen> StableCastMap<D, Idx, Gen>
where
    D: DerefGenMapPromise,
    <D::Target as Pointee>::Metadata: Copy,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    #[inline]
    pub fn downcast_key<Concrete: 'static>(
        &self,
        key: StableCastKey<dyn Any, Idx, Gen>,
    ) -> Option<StableCastKey<Concrete, Idx, Gen>> {
        if key.map_id != self.map_id {
            return None;
        }
        let inner = unsafe { self.inner.downcast_key::<Concrete>(key.inner) }?;
        Some(stabilize(inner, self.map_id))
    }

    // ── insert ──────────────────────────────────────────────────────────

    #[inline]
    pub fn insert(&self, value: D) -> (StableCastKey<D::Target, Idx, Gen>, &D::Target) {
        let (key, reference) = self.inner.insert(value);
        (stabilize(key, self.map_id), reference)
    }

    #[inline]
    pub fn insert_with_key(
        &self,
        func: impl FnOnce(InnerCastMapKey<Idx, Gen>) -> D,
    ) -> (StableCastKey<D::Target, Idx, Gen>, &D::Target) {
        let (key, reference) = self.inner.insert_with_key(func);
        (stabilize(key, self.map_id), reference)
    }

    #[inline]
    pub fn try_insert_with_key<E>(
        &self,
        func: impl FnOnce(InnerCastMapKey<Idx, Gen>) -> Result<D, E>,
    ) -> Result<(StableCastKey<D::Target, Idx, Gen>, &D::Target), E> {
        let (key, reference) = self.inner.try_insert_with_key(func)?;
        Ok((stabilize(key, self.map_id), reference))
    }

    // ── insert_sized ────────────────────────────────────────────────────

    #[inline]
    pub fn insert_sized<ConcreteD>(
        &self,
        value: ConcreteD,
    ) -> (StableCastKey<ConcreteD::Target, Idx, Gen>, &ConcreteD::Target)
    where
        ConcreteD: std::ops::CoerceUnsized<D> + std::ops::Deref,
        ConcreteD::Target: Sized,
    {
        let (key, reference) = self.inner.insert_sized(value);
        (stabilize(key, self.map_id), reference)
    }

    #[inline]
    pub fn insert_sized_with_key<ConcreteD>(
        &self,
        func: impl FnOnce(StableCastKey<ConcreteD::Target, Idx, Gen>) -> ConcreteD,
    ) -> (StableCastKey<ConcreteD::Target, Idx, Gen>, &ConcreteD::Target)
    where
        ConcreteD: std::ops::CoerceUnsized<D> + std::ops::Deref,
        ConcreteD::Target: Sized,
    {
        let map_id = self.map_id;
        let (key, reference) =
            self.inner
                .insert_sized_with_key(|ck| func(stabilize(ck, map_id)));
        (stabilize(key, self.map_id), reference)
    }

    /// Gets the inner `UnsafeCastMap` as owned
    pub fn inner(self) -> UnsafeCastMap<D, Idx, Gen> {
        self.inner
    }

    /// Gets the inner `UnsafeCastMap` as a mutable reference
    pub fn inner_mut(&mut self) -> &mut UnsafeCastMap<D, Idx, Gen> {
        &mut self.inner
    }

    /// Gets the inner `UnsafeCastMap` as a shared reference
    pub fn inner_ref(&self) -> &UnsafeCastMap<D, Idx, Gen> {
        &self.inner
    }

    #[inline]
    pub fn try_insert_sized_with_key<ConcreteD, E>(
        &self,
        func: impl FnOnce(StableCastKey<ConcreteD::Target, Idx, Gen>) -> Result<ConcreteD, E>,
    ) -> Result<(StableCastKey<ConcreteD::Target, Idx, Gen>, &ConcreteD::Target), E>
    where
        ConcreteD: std::ops::CoerceUnsized<D> + std::ops::Deref,
        ConcreteD::Target: Sized,
    {
        let map_id = self.map_id;
        let (key, reference) =
            self.inner
                .try_insert_sized_with_key(|ck| func(stabilize(ck, map_id)))?;
        Ok((stabilize(key, self.map_id), reference))
    }

    // ── insert_as ───────────────────────────────────────────────────────

    #[inline]
    pub fn insert_as<SourceD>(
        &self,
        value: SourceD,
    ) -> (StableCastKey<SourceD::Target, Idx, Gen>, &SourceD::Target)
    where
        SourceD: std::ops::CoerceUnsized<D> + std::ops::Deref,
        SourceD::Target: Pointee<Metadata: Copy>,
    {
        let (key, reference) = self.inner.insert_as(value);
        (stabilize(key, self.map_id), reference)
    }

    #[inline]
    pub fn insert_as_with_key<SourceD>(
        &self,
        func: impl FnOnce(InnerCastMapKey<Idx, Gen>) -> SourceD,
    ) -> (StableCastKey<SourceD::Target, Idx, Gen>, &SourceD::Target)
    where
        SourceD: std::ops::CoerceUnsized<D> + std::ops::Deref,
        SourceD::Target: Pointee<Metadata: Copy>,
    {
        let (key, reference) = self.inner.insert_as_with_key(func);
        (stabilize(key, self.map_id), reference)
    }

    #[inline]
    pub fn try_insert_as_with_key<SourceD, E>(
        &self,
        func: impl FnOnce(InnerCastMapKey<Idx, Gen>) -> Result<SourceD, E>,
    ) -> Result<(StableCastKey<SourceD::Target, Idx, Gen>, &SourceD::Target), E>
    where
        SourceD: std::ops::CoerceUnsized<D> + std::ops::Deref,
        SourceD::Target: Pointee<Metadata: Copy>,
    {
        let (key, reference) = self.inner.try_insert_as_with_key(func)?;
        Ok((stabilize(key, self.map_id), reference))
    }

    // ── get_by_index_only ───────────────────────────────────────────────

    #[inline]
    pub fn get_by_index_only(
        &self,
        idx: Idx,
    ) -> Option<(StableCastKey<D::Target, Idx, Gen>, &D::Target)> {
        let (key, reference) = self.inner.get_by_index_only(idx)?;
        Some((stabilize(key, self.map_id), reference))
    }

    #[inline]
    pub fn get_by_index_only_mut(
        &mut self,
        idx: Idx,
    ) -> Option<(StableCastKey<D::Target, Idx, Gen>, &mut D::Target)>
    where
        D: DerefMut,
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
    pub unsafe fn get_slot(
        &self,
        idx: Idx,
    ) -> Option<&Slot<DerefSlot<D, InnerCastMapKey<Idx, Gen>>, InnerCastMapKey<Idx, Gen>>> {
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
    pub unsafe fn get_slot_unchecked(
        &self,
        idx: Idx,
    ) -> &Slot<DerefSlot<D, InnerCastMapKey<Idx, Gen>>, InnerCastMapKey<Idx, Gen>> {
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
    pub unsafe fn get_slot_as_cell(
        &self,
        idx: Idx,
    ) -> Option<&UnsafeCell<Slot<DerefSlot<D, InnerCastMapKey<Idx, Gen>>, InnerCastMapKey<Idx, Gen>>>> {
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
    pub unsafe fn get_slot_as_cell_unchecked(
        &self,
        idx: Idx,
    ) -> &UnsafeCell<Slot<DerefSlot<D, InnerCastMapKey<Idx, Gen>>, InnerCastMapKey<Idx, Gen>>> {
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
    pub unsafe fn get_slot_mut(
        &mut self,
        idx: Idx,
    ) -> Option<&mut Slot<DerefSlot<D, InnerCastMapKey<Idx, Gen>>, InnerCastMapKey<Idx, Gen>>> {
        self.inner.get_slot_mut(idx)
    }

    /// Returns a mutable reference to the raw [`Slot`] without bounds checking.
    ///
    /// # Safety
    /// - The index must be in bounds.
    /// - The caller must not use this to violate map invariants, and must
    ///   check occupancy before accessing the slot's value.
    #[inline]
    pub unsafe fn get_slot_mut_unchecked(
        &mut self,
        idx: Idx,
    ) -> &mut Slot<DerefSlot<D, InnerCastMapKey<Idx, Gen>>, InnerCastMapKey<Idx, Gen>> {
        self.inner.get_slot_mut_unchecked(idx)
    }


    /// Safe wrapper around [`clone_efficiently`](Self::clone_efficiently):
    /// the `&mut self` borrow prevents the stored type's `Clone` from
    /// mutating the map.
    #[inline]
    pub fn clone_efficiently_mut(&mut self) -> Self where D: Clone
    {
        Self{
            inner: self.inner.clone_efficiently_mut(),
            map_id: MapId::next()
        }
    }


    /// A more efficient clone than `Clone::clone`, but **UB** if the `Clone`
    /// implementation of the stored type mutates the map.
    #[inline]
    pub unsafe  fn clone_efficiently(&self) -> Self where D: Clone {
        Self{
            inner: self.inner.clone_efficiently(),
            map_id: MapId::next()
        }
    }

    // ── inner-key access ──────────────────────────────────────────────

    #[inline]
    pub fn get_by_inner_key(&self, key: InnerCastMapKey<Idx, Gen>) -> Option<&D::Target> {
        self.inner.get_by_inner_key(key)
    }

    #[inline]
    pub fn get_mut_by_inner_key(&mut self, key: InnerCastMapKey<Idx, Gen>) -> Option<&mut D::Target>
    where
        D: std::ops::DerefMut,
    {
        self.inner.get_mut_by_inner_key(key)
    }

    #[inline]
    pub fn remove_by_inner_key(&mut self, key: InnerCastMapKey<Idx, Gen>) -> Option<D> {
        self.inner.remove_by_inner_key(key)
    }

    #[inline]
    pub fn cast_key_of(
        &self,
        inner: InnerCastMapKey<Idx, Gen>,
    ) -> Option<StableCastKey<D::Target, Idx, Gen>> {
        let key = self.inner.cast_key_of(inner)?;
        Some(stabilize(key, self.map_id))
    }

    // ── retain ──────────────────────────────────────────────────────────

    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(StableCastKey<D::Target, Idx, Gen>, &mut D::Target) -> bool,
        D: DerefMut,
    {
        let map_id = self.map_id;
        self.inner
            .retain(|ck, val| f(stabilize(ck, map_id), val));
    }

    // ── snapshot ────────────────────────────────────────────────────────

    #[inline]
    pub fn snapshot(&self) -> Vec<(StableCastKey<D::Target, Idx, Gen>, &D::Target)> {
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

    #[inline]
    pub fn snapshot_refs(&self) -> Vec<&D::Target> {
        self.inner.snapshot_refs()
    }

    #[inline]
    pub fn snapshot_keys(&self) -> Vec<StableCastKey<D::Target, Idx, Gen>> {
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

    /// # Safety
    /// No mutation (including `insert`) may occur while iterating.
    #[inline]
    pub unsafe fn iter_unsafe(
        &self,
    ) -> impl Iterator<Item = (StableCastKey<D::Target, Idx, Gen>, &D::Target)> {
        let map_id = self.map_id;
        self.inner
            .iter_unsafe()
            .map(move |(ck, r)| (stabilize(ck, map_id), r))
    }

    // ── iter_mut ────────────────────────────────────────────────────────

    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, D, Idx, Gen> {
        IterMut {
            inner: self.inner.iter_mut(),
            map_id: self.map_id,
        }
    }

    // ── drain ───────────────────────────────────────────────────────────

    #[inline]
    pub fn drain(&mut self) -> Drain<'_, D, Idx, Gen> {
        Drain {
            inner: self.inner.drain(),
            map_id: self.map_id,
        }
    }
}

// ─── Cross-typed lookups (safe — map-id validated) ──────────────────────────

impl<D, Idx, Gen> StableCastMap<D, Idx, Gen>
where
    D: DerefGenMapPromise,
    <D::Target as Pointee>::Metadata: Copy,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    #[inline]
    pub fn get<T: ?Sized + Pointee>(&self, key: StableCastKey<T, Idx, Gen>) -> Option<&T>
    where
        <T as Pointee>::Metadata: Copy,
    {
        if key.map_id != self.map_id {
            return None;
        }
        unsafe { self.inner.get(key.inner) }
    }

    #[inline]
    pub fn get_mut<T: ?Sized + Pointee>(
        &mut self,
        key: StableCastKey<T, Idx, Gen>,
    ) -> Option<&mut T>
    where
        <T as Pointee>::Metadata: Copy,
        D: std::ops::DerefMut,
    {
        if key.map_id != self.map_id {
            return None;
        }
        unsafe { self.inner.get_mut(key.inner) }
    }

    /// Shared-reference lookup without bounds, generation, or map-id checks.
    ///
    /// # Safety
    /// - The key must belong to this map.
    /// - The key's index must be in bounds.
    /// - The slot at that index must be occupied with the matching generation.
    /// - The key's metadata must be valid for the data stored at that slot.
    #[inline]
    pub unsafe fn get_unchecked<T: ?Sized + Pointee>(
        &self,
        key: StableCastKey<T, Idx, Gen>,
    ) -> &T
    where
        <T as Pointee>::Metadata: Copy,
    {
        self.inner.get_unchecked(key.inner)
    }

    /// Mutable-reference lookup without bounds, generation, or map-id checks.
    ///
    /// # Safety
    /// - The key must belong to this map.
    /// - The key's index must be in bounds.
    /// - The slot at that index must be occupied with the matching generation.
    /// - The key's metadata must be valid for the data stored at that slot.
    #[inline]
    pub unsafe fn get_unchecked_mut<T: ?Sized + Pointee>(
        &mut self,
        key: StableCastKey<T, Idx, Gen>,
    ) -> &mut T
    where
        <T as Pointee>::Metadata: Copy,
        D: std::ops::DerefMut,
    {
        self.inner.get_unchecked_mut(key.inner)
    }

    #[inline]
    pub fn remove<T: ?Sized + Pointee>(
        &mut self,
        key: StableCastKey<T, Idx, Gen>,
    ) -> Option<D>
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

impl<D, Idx, Gen> Index<StableCastKey<D::Target, Idx, Gen>> for StableCastMap<D, Idx, Gen>
where
    D: DerefGenMapPromise,
    <D::Target as Pointee>::Metadata: Copy,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    type Output = D::Target;

    fn index(&self, key: StableCastKey<D::Target, Idx, Gen>) -> &Self::Output {
        self.get(key).unwrap()
    }
}

impl<D, Idx, Gen> IndexMut<StableCastKey<D::Target, Idx, Gen>> for StableCastMap<D, Idx, Gen>
where
    D: DerefGenMapPromise + std::ops::DerefMut,
    <D::Target as Pointee>::Metadata: Copy,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    fn index_mut(&mut self, key: StableCastKey<D::Target, Idx, Gen>) -> &mut Self::Output {
        self.get_mut(key).unwrap()
    }
}

/// Convenience alias: [`StableCastMap`] storing `Box<T>`.
pub type StableBoxCastMap<T, Idx = u32, Gen = u32> = StableCastMap<Box<T>, Idx, Gen>;

// ─── IterMut ────────────────────────────────────────────────────────────────

pub struct IterMut<'a, D, Idx = u32, Gen = u32>
where
    D: DerefGenMapPromise,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    inner: unsafe_cast_map::IterMut<'a, D, Idx, Gen>,
    map_id: MapId,
}

impl<'a, D, Idx, Gen> Iterator for IterMut<'a, D, Idx, Gen>
where
    D: DerefGenMapPromise + DerefMut,
    <D::Target as Pointee>::Metadata: Copy,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    type Item = (StableCastKey<D::Target, Idx, Gen>, &'a mut D::Target);

    fn next(&mut self) -> Option<Self::Item> {
        let (ck, val) = self.inner.next()?;
        Some((stabilize(ck, self.map_id), val))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

// ─── Drain ──────────────────────────────────────────────────────────────────

pub struct Drain<'a, D, Idx = u32, Gen = u32>
where
    D: DerefGenMapPromise,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    inner: unsafe_cast_map::Drain<'a, D, Idx, Gen>,
    map_id: MapId,
}

impl<'a, D, Idx, Gen> Iterator for Drain<'a, D, Idx, Gen>
where
    D: DerefGenMapPromise,
    <D::Target as Pointee>::Metadata: Copy,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    type Item = (StableCastKey<D::Target, Idx, Gen>, D);

    fn next(&mut self) -> Option<Self::Item> {
        let (ck, val) = self.inner.next()?;
        Some((stabilize(ck, self.map_id), val))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

// ─── IntoIter (owning) ─────────────────────────────────────────────────────

pub struct IntoIter<D, Idx = u32, Gen = u32>
where
    D: DerefGenMapPromise,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    inner: unsafe_cast_map::IntoIter<D, Idx, Gen>,
    map_id: MapId,
}

impl<D, Idx, Gen> Iterator for IntoIter<D, Idx, Gen>
where
    D: DerefGenMapPromise,
    <D::Target as Pointee>::Metadata: Copy,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    type Item = (StableCastKey<D::Target, Idx, Gen>, D);

    fn next(&mut self) -> Option<Self::Item> {
        let (ck, val) = self.inner.next()?;
        Some((stabilize(ck, self.map_id), val))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<D, Idx, Gen> IntoIterator for StableCastMap<D, Idx, Gen>
where
    D: DerefGenMapPromise,
    <D::Target as Pointee>::Metadata: Copy,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    type Item = (StableCastKey<D::Target, Idx, Gen>, D);
    type IntoIter = IntoIter<D, Idx, Gen>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.inner.into_iter(),
            map_id: self.map_id,
        }
    }
}

impl<'a, D, Idx, Gen> IntoIterator for &'a mut StableCastMap<D, Idx, Gen>
where
    D: DerefGenMapPromise + DerefMut,
    <D::Target as Pointee>::Metadata: Copy,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    type Item = (StableCastKey<D::Target, Idx, Gen>, &'a mut D::Target);
    type IntoIter = IterMut<'a, D, Idx, Gen>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}
