//! Safe wrapper around [`UnsafeCastMap`](crate::unsafe_cast_map::UnsafeCastMap)
//! that binds keys to the map that created them via a [`MapId`].
//!
//! Every [`StableCastKey`](crate::cast_key::StableCastKey) carries the
//! map's identity. Keyed lookups check the id before touching pointer
//! metadata, so a key from map A used on map B returns `None` instead
//! of causing UB.

use std::any::Any;
use std::collections::TryReserveError;
use std::ops::{DerefMut, Index, IndexMut};
use std::ptr::Pointee;

use crate::cast_key::{CastKey, DefaultMapKey, StableCastKey};
use crate::key::Key;
use crate::key_piece::KeyPiece;
use crate::map_id::MapId;
use crate::stable_deref_map::DerefGenMapPromise;
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
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
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
        func: impl FnOnce(DefaultMapKey<Idx, Gen>) -> D,
    ) -> (StableCastKey<D::Target, Idx, Gen>, &D::Target) {
        let (key, reference) = self.inner.insert_with_key(func);
        (stabilize(key, self.map_id), reference)
    }

    #[inline]
    pub fn try_insert_with_key<E>(
        &self,
        func: impl FnOnce(DefaultMapKey<Idx, Gen>) -> Result<D, E>,
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
        func: impl FnOnce(DefaultMapKey<Idx, Gen>) -> SourceD,
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
        func: impl FnOnce(DefaultMapKey<Idx, Gen>) -> Result<SourceD, E>,
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

    // ── inner-key access ──────────────────────────────────────────────

    #[inline]
    pub fn get_by_inner_key(&self, key: DefaultMapKey<Idx, Gen>) -> Option<&D::Target> {
        self.inner.get_by_inner_key(key)
    }

    #[inline]
    pub fn get_mut_by_inner_key(&mut self, key: DefaultMapKey<Idx, Gen>) -> Option<&mut D::Target>
    where
        D: std::ops::DerefMut,
    {
        self.inner.get_mut_by_inner_key(key)
    }

    #[inline]
    pub fn remove_by_inner_key(&mut self, key: DefaultMapKey<Idx, Gen>) -> Option<D> {
        self.inner.remove_by_inner_key(key)
    }

    #[inline]
    pub fn cast_key_of(
        &self,
        inner: DefaultMapKey<Idx, Gen>,
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
