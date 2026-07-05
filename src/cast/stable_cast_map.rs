//! Safe wrapper around [`UnsafeCastMap`](crate::cast::unsafe_cast_map::UnsafeCastMap)
//! whose keyed lookups are checked against each slot's stored concrete type id.
//!
//! Where the low-level map's `get` / `get_mut` / `remove` are `unsafe` (the
//! caller must promise the key's metadata fits the slot), `StableCastMap` makes
//! them safe: every value lives in a [`CastBox`] that records its concrete
//! [`TypeId`], and a lookup recovers the type id implied by the key's metadata
//! (via [`type_id_from_meta`]) and compares it to the slot's. A mismatch — wrong
//! type, recycled slot, or a key minted by another map for a different type —
//! returns `None` instead of risking UB.
//!
//! This safety hinges on a stored type id, so `StableCastMap`'s checked lookups
//! require the slot's owning box to implement [`ConcreteTypeId`]. The crate
//! provides that for [`CastBox`] (so `Rc` / `Arc` / `Box` won't work), but the
//! trait is public: implement it for your own box to use that box here.

use std::any::{Any, TypeId};
use std::cell::UnsafeCell;
use std::collections::TryReserveError;
use std::ops::{Deref, DerefMut};
use std::ptr::Pointee;

use crate::cast::any_haver::{type_id_from_meta, AnyHaver};
use crate::cast::cast_box::{CastBox, ConcreteTypeId};
use crate::cast::cast_key::CastKey;
use crate::cast::retype_ptr::RetypePtr;
use crate::cast::unsafe_cast_map;
use crate::cast::unsafe_cast_map::UnsafeCastMap;
use crate::core::gen_map::{IdxOfStorage, KeyOfStorage, Slot};
use crate::core::slot_storage::{SlotStorage, SlotStorageClone, SlotStorageMutOutput};
use crate::keys::key::Key;
use crate::slots::deref_slot::{DerefGenMapPromise, DerefSlot};

// ─── StableCastMap ──────────────────────────────────────────────────────────

/// A safe wrapper around [`UnsafeCastMap`] that validates keyed lookups against
/// each slot's stored concrete [`TypeId`].
///
/// `C` is the per-slot storage strategy. The checked lookups additionally
/// require `C::Stored: ConcreteTypeId` — satisfied by [`CastBox`] (e.g.
/// [`StableBoxCastMap`]) or any custom box that implements [`ConcreteTypeId`].
pub struct StableCastMap<C: SlotStorage>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
{
    inner: UnsafeCastMap<C>,
}

// ─── Basic methods ──────────────────────────────────────────────────────────

impl<C: SlotStorage> Default for StableCastMap<C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<C: SlotStorage> StableCastMap<C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
{
    /// Creates a new, empty map.
    #[inline]
    pub fn new() -> Self {
        Self {
            inner: UnsafeCastMap::new(),
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
        }
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

    /// Total number of slots, occupied and vacant.
    #[inline]
    pub fn slots_len(&self) -> usize {
        self.inner.slots_len()
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
    /// Downcasts a `CastKey<dyn Any>` to a concrete-typed key by comparing the
    /// slot's stored type id with `TypeId::of::<Concrete>()`. Returns `None` if
    /// the key is stale or the stored type differs.
    #[inline]
    pub fn downcast_key<Concrete: 'static>(
        &self,
        key: CastKey<dyn Any, KeyOfStorage<C>>,
    ) -> Option<CastKey<Concrete, KeyOfStorage<C>>>
    where
        C::Stored: ConcreteTypeId,
    {
        let kd = key.key_data();
        let slot: &Slot<C> = unsafe { &*self.inner.get_slot_as_cell(kd.index())?.get() };
        // Generation match ⇒ occupied (keys only carry live, odd generations),
        // and rejects stale keys.
        if slot.generation != kd.generation() {
            return None;
        }
        if unsafe { slot.storage().ref_stored().concrete_type_id() } == TypeId::of::<Concrete>() {
            Some(CastKey {
                key_data: kd,
                metadata: (),
            })
        } else {
            None
        }
    }

    // ── insert ──────────────────────────────────────────────────────────

    /// Inserts a value and returns its [`CastKey`].
    #[inline]
    pub fn insert(&self, value: C::Stored) -> CastKey<C::Output, KeyOfStorage<C>> {
        self.inner.insert(value)
    }

    /// Inserts a value produced by `func`, which receives the backing key.
    #[inline]
    pub fn insert_with_key(
        &self,
        func: impl FnOnce(KeyOfStorage<C>) -> C::Stored,
    ) -> CastKey<C::Output, KeyOfStorage<C>> {
        self.inner.insert_with_key(func)
    }

    /// Like [`insert_with_key`](Self::insert_with_key) but the closure may fail.
    #[inline]
    pub fn try_insert_with_key<E>(
        &self,
        func: impl FnOnce(KeyOfStorage<C>) -> Result<C::Stored, E>,
    ) -> Result<CastKey<C::Output, KeyOfStorage<C>>, E> {
        self.inner.try_insert_with_key(func)
    }

    // ── insert_sized ────────────────────────────────────────────────────

    /// Inserts a concrete-typed smart pointer, returning a typed [`CastKey`].
    #[inline]
    pub fn insert_sized<ConcretePtr>(
        &self,
        value: ConcretePtr,
    ) -> CastKey<ConcretePtr::Target, KeyOfStorage<C>>
    where
        ConcretePtr: std::ops::CoerceUnsized<C::Stored> + Deref,
        ConcretePtr::Target: Sized,
    {
        self.inner.insert_sized(value)
    }

    /// Like [`insert_sized`](Self::insert_sized) but the closure receives a typed key.
    #[inline]
    pub fn insert_sized_with_key<ConcretePtr>(
        &self,
        func: impl FnOnce(CastKey<ConcretePtr::Target, KeyOfStorage<C>>) -> ConcretePtr,
    ) -> CastKey<ConcretePtr::Target, KeyOfStorage<C>>
    where
        ConcretePtr: std::ops::CoerceUnsized<C::Stored> + Deref,
        ConcretePtr::Target: Sized,
    {
        self.inner.insert_sized_with_key(func)
    }

    /// Fallible version of [`insert_sized_with_key`](Self::insert_sized_with_key).
    #[inline]
    pub fn try_insert_sized_with_key<ConcretePtr, E>(
        &self,
        func: impl FnOnce(CastKey<ConcretePtr::Target, KeyOfStorage<C>>) -> Result<ConcretePtr, E>,
    ) -> Result<CastKey<ConcretePtr::Target, KeyOfStorage<C>>, E>
    where
        ConcretePtr: std::ops::CoerceUnsized<C::Stored> + Deref,
        ConcretePtr::Target: Sized,
    {
        self.inner.try_insert_sized_with_key(func)
    }

    // ── insert_as ───────────────────────────────────────────────────────

    /// Inserts a smart pointer, preserving the source pointer's metadata.
    #[inline]
    pub fn insert_as<SourcePtr>(
        &self,
        value: SourcePtr,
    ) -> CastKey<SourcePtr::Target, KeyOfStorage<C>>
    where
        SourcePtr: std::ops::CoerceUnsized<C::Stored> + Deref,
        SourcePtr::Target: Pointee<Metadata: Copy>,
    {
        self.inner.insert_as(value)
    }

    /// Like [`insert_as`](Self::insert_as) but the closure receives the backing key.
    #[inline]
    pub fn insert_as_with_key<SourcePtr>(
        &self,
        func: impl FnOnce(KeyOfStorage<C>) -> SourcePtr,
    ) -> CastKey<SourcePtr::Target, KeyOfStorage<C>>
    where
        SourcePtr: std::ops::CoerceUnsized<C::Stored> + Deref,
        SourcePtr::Target: Pointee<Metadata: Copy>,
    {
        self.inner.insert_as_with_key(func)
    }

    /// Fallible version of [`insert_as_with_key`](Self::insert_as_with_key).
    #[inline]
    pub fn try_insert_as_with_key<SourcePtr, E>(
        &self,
        func: impl FnOnce(KeyOfStorage<C>) -> Result<SourcePtr, E>,
    ) -> Result<CastKey<SourcePtr::Target, KeyOfStorage<C>>, E>
    where
        SourcePtr: std::ops::CoerceUnsized<C::Stored> + Deref,
        SourcePtr::Target: Pointee<Metadata: Copy>,
    {
        self.inner.try_insert_as_with_key(func)
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
    ) -> Option<(CastKey<C::Output, KeyOfStorage<C>>, &C::Output)> {
        self.inner.get_by_index_only(idx)
    }

    /// Mutable version of [`get_by_index_only`](Self::get_by_index_only).
    #[inline]
    pub fn get_by_index_only_mut(
        &mut self,
        idx: IdxOfStorage<C>,
    ) -> Option<(CastKey<C::Output, KeyOfStorage<C>>, &mut C::Output)>
    where
        C: SlotStorageMutOutput,
    {
        self.inner.get_by_index_only_mut(idx)
    }

    // ── slot access (cell + mut) ────────────────────────────────────────

    /// Bounds-checked cell access for the slot at `idx`.
    ///
    /// # Safety
    /// See [`GenMap::get_slot_as_cell`](crate::core::gen_map::GenMap::get_slot_as_cell).
    #[inline]
    pub unsafe fn get_slot_as_cell(&self, idx: IdxOfStorage<C>) -> Option<&UnsafeCell<Slot<C>>> {
        self.inner.get_slot_as_cell(idx)
    }

    /// Unchecked cell access for the slot at `idx`.
    ///
    /// # Safety
    /// See [`GenMap::get_slot_as_cell_unchecked`](crate::core::gen_map::GenMap::get_slot_as_cell_unchecked).
    #[inline]
    pub unsafe fn get_slot_as_cell_unchecked(&self, idx: IdxOfStorage<C>) -> &UnsafeCell<Slot<C>> {
        self.inner.get_slot_as_cell_unchecked(idx)
    }

    /// Returns a mutable reference to the raw [`Slot`] at the given index.
    ///
    /// # Safety
    /// The returned slot exposes internal data structures. The caller must not
    /// use this to violate map invariants, and must check occupancy before
    /// accessing the slot's value.
    #[inline]
    pub unsafe fn get_slot_mut(&mut self, idx: IdxOfStorage<C>) -> Option<&mut Slot<C>> {
        self.inner.get_slot_mut(idx)
    }

    /// Returns a mutable reference to the raw [`Slot`] without bounds checking.
    ///
    /// # Safety
    /// - The index must be in bounds.
    /// - The caller must not use this to violate map invariants, and must check
    ///   occupancy before accessing the slot's value.
    #[inline]
    pub unsafe fn get_slot_unchecked_mut(&mut self, idx: IdxOfStorage<C>) -> &mut Slot<C> {
        self.inner.get_slot_unchecked_mut(idx)
    }

    /// Clone the map in a single pass.
    ///
    /// # Safety
    /// See [`UnsafeCastMap::unsafe_clone`](crate::cast::unsafe_cast_map::UnsafeCastMap::unsafe_clone).
    #[inline]
    pub unsafe fn unsafe_clone(&self) -> Self
    where
        C: SlotStorageClone,
    {
        Self {
            inner: self.inner.unsafe_clone(),
        }
    }

    /// Clone the map through a unique borrow.
    #[inline]
    pub fn clone_mut(&mut self) -> Self
    where
        C: SlotStorageClone,
    {
        Self {
            inner: self.inner.clone_mut(),
        }
    }

    /// `unsafe` counterpart of [`clone_from_mut`](Self::clone_from_mut): reuses
    /// `self`'s inner allocation.
    ///
    /// # Safety
    /// See [`GenMap::unsafe_clone_from`](crate::core::gen_map::GenMap::unsafe_clone_from).
    #[inline]
    pub unsafe fn unsafe_clone_from(&mut self, source: &Self)
    where
        C: SlotStorageClone,
    {
        self.inner.unsafe_clone_from(&source.inner);
    }

    /// Clone `source` into `self` through a unique borrow of `source`, reusing
    /// `self`'s inner allocation.
    #[inline]
    pub fn clone_from_mut(&mut self, source: &mut Self)
    where
        C: SlotStorageClone,
    {
        self.inner.clone_from_mut(&mut source.inner);
    }

    // ── inner-key access ──────────────────────────────────────────────

    /// Shared-reference lookup using the backing [`Key`] directly.
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

    /// Converts a backing [`Key`] into a [`CastKey`] by reading pointer metadata
    /// from the stored value. Returns `None` if the key is stale.
    #[inline]
    pub fn cast_key_of(
        &self,
        inner: KeyOfStorage<C>,
    ) -> Option<CastKey<C::Output, KeyOfStorage<C>>> {
        self.inner.cast_key_of(inner)
    }

    // ── retain ──────────────────────────────────────────────────────────

    /// Retains only elements for which `f(key, &mut output)` returns `true`.
    #[inline]
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(CastKey<C::Output, KeyOfStorage<C>>, &mut C::Output) -> bool,
        C::Stored: DerefMut,
    {
        self.inner.retain(f);
    }

    // ── snapshot ────────────────────────────────────────────────────────

    /// Returns a snapshot of all `(CastKey, &output)` pairs.
    #[inline]
    pub fn snapshot(&self) -> Vec<(CastKey<C::Output, KeyOfStorage<C>>, &C::Output)> {
        self.inner.snapshot()
    }

    /// Returns a snapshot of `&output` references only.
    #[inline]
    pub fn snapshot_refs(&self) -> Vec<&C::Output> {
        self.inner.snapshot_refs()
    }

    /// Returns a snapshot of all [`CastKey`]s.
    #[inline]
    pub fn snapshot_keys(&self) -> Vec<CastKey<C::Output, KeyOfStorage<C>>> {
        self.inner.snapshot_keys()
    }

    // ── unsafe_iter ─────────────────────────────────────────────────────

    /// Shared iterator over all occupied elements.
    ///
    /// # Safety
    /// No mutation (including `insert`) may occur while iterating.
    #[inline]
    pub unsafe fn unsafe_iter(
        &self,
    ) -> impl Iterator<Item = (CastKey<C::Output, KeyOfStorage<C>>, &C::Output)> {
        self.inner.unsafe_iter()
    }

    // ── iter_mut ────────────────────────────────────────────────────────

    /// Mutable iterator over all occupied elements.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, C> {
        IterMut {
            inner: self.inner.iter_mut(),
        }
    }

    // ── drain ───────────────────────────────────────────────────────────

    /// Draining iterator. Removes all elements and yields them.
    #[inline]
    pub fn drain(&mut self) -> Drain<'_, C> {
        Drain {
            inner: self.inner.drain(),
        }
    }
}

// ─── Checked cross-typed lookups (safe — type-id validated) ─────────────────

impl<C: SlotStorage> StableCastMap<C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
    <C::Output as Pointee>::Metadata: Copy,
{
    /// Typed lookup by [`CastKey`]. Returns `None` if the slot is vacant, the
    /// key is stale, or the key's type does not match the value at that slot.
    ///
    /// Resolves the slot once: the stored type id and the output reference are
    /// both read *before* `type_id_from_meta` (whose vtable call is opaque to the
    /// optimizer), and the returned reference is rebuilt from that already-loaded
    /// output pointer — so the slot is not walked a second time across the call.
    #[inline]
    pub fn get<T: ?Sized + AnyHaver + Pointee>(
        &self,
        key: CastKey<T, KeyOfStorage<C>>,
    ) -> Option<&T>
    where
        <T as Pointee>::Metadata: Copy,
        C::Stored: ConcreteTypeId,
    {
        let kd = key.key_data();
        let slot: &Slot<C> = unsafe { &*self.inner.get_slot_as_cell(kd.index())?.get() };
        // Generation match ⇒ the slot is occupied (a key only ever carries a live,
        // odd generation), so the union read and `ref_output` are sound; a stale
        // key is rejected here.
        if slot.generation != kd.generation() {
            return None;
        }
        let stored_tid = unsafe { slot.storage().ref_stored().concrete_type_id() };
        let base: &C::Output = unsafe { slot.ref_output() };
        if stored_tid != type_id_from_meta::<T>(key.metadata()) {
            return None;
        }
        let data: *const () = (base as *const C::Output).cast();
        Some(unsafe { &*std::ptr::from_raw_parts::<T>(data, key.metadata()) })
    }

    /// Mutable typed lookup by [`CastKey`]. Single-walk, like [`get`](Self::get):
    /// the type id is checked before the unique output borrow is taken, and
    /// `mut_output` reuses the slot already in hand.
    #[inline]
    pub fn get_mut<T: ?Sized + AnyHaver + Pointee>(
        &mut self,
        key: CastKey<T, KeyOfStorage<C>>,
    ) -> Option<&mut T>
    where
        <T as Pointee>::Metadata: Copy,
        C: SlotStorageMutOutput,
        C::Stored: ConcreteTypeId,
    {
        let kd = key.key_data();
        let slot: &mut Slot<C> = unsafe { self.inner.get_slot_mut(kd.index())? };
        if slot.generation != kd.generation() {
            return None;
        }
        if unsafe { slot.storage().ref_stored().concrete_type_id() } != type_id_from_meta::<T>(key.metadata()) {
            return None;
        }
        let base: &mut C::Output = unsafe { slot.mut_output() };
        let data: *mut () = (base as *mut C::Output).cast();
        Some(unsafe { &mut *std::ptr::from_raw_parts_mut::<T>(data, key.metadata()) })
    }

    /// Empties the map and resets all slot generations to zero. Capacity is
    /// retained.
    ///
    /// Safe to call: keyed lookups validate the slot's stored type id, so a
    /// stale key that happens to match a recycled slot's generation is still
    /// rejected unless the recycled value has the same concrete type.
    pub fn reset(&mut self) {
        self.inner.reset();
    }

    /// Shared-reference lookup without bounds, generation, or type checks.
    ///
    /// # Safety
    /// - The key's index must be in bounds.
    /// - The slot at that index must be occupied with the matching generation.
    /// - The key's pointer metadata must be valid for the data in that slot.
    #[inline]
    pub unsafe fn get_unchecked<T: ?Sized + Pointee>(
        &self,
        key: CastKey<T, KeyOfStorage<C>>,
    ) -> &T
    where
        <T as Pointee>::Metadata: Copy,
    {
        self.inner.get_unchecked(key)
    }

    /// Mutable-reference lookup without bounds, generation, or type checks.
    ///
    /// # Safety
    /// - The key's index must be in bounds.
    /// - The slot at that index must be occupied with the matching generation.
    /// - The key's pointer metadata must be valid for the data in that slot.
    #[inline]
    pub unsafe fn get_unchecked_mut<T: ?Sized + Pointee>(
        &mut self,
        key: CastKey<T, KeyOfStorage<C>>,
    ) -> &mut T
    where
        <T as Pointee>::Metadata: Copy,
        C: SlotStorageMutOutput,
    {
        self.inner.get_unchecked_mut(key)
    }

    /// Removes an element by its [`CastKey`]. Returns `None` if the slot is
    /// vacant, the key is stale, or the key's type does not match.
    ///
    /// Validation is a single walk; the following `inner.remove` walks the slot
    /// again, but that pass is the removal itself (free-list update + generation
    /// bump), not redundant checking.
    #[inline]
    pub fn remove<'a, T: ?Sized + AnyHaver + Pointee>(
        &mut self,
        key: CastKey<T, KeyOfStorage<C>>,
    ) -> Option<<C::Stored as RetypePtr<'a>>::Retyped<T>>
    where
        <T as Pointee>::Metadata: Copy,
        C::Stored: ConcreteTypeId,
        C::Stored: Deref<Target = C::Output> + DerefGenMapPromise + RetypePtr<'a>,
    {
        let kd = key.key_data();
        {
            let slot: &Slot<C> = unsafe { &*self.inner.get_slot_as_cell(kd.index())?.get() };
            if slot.generation != kd.generation()
                || unsafe { slot.storage().ref_stored().concrete_type_id() }
                != type_id_from_meta::<T>(key.metadata())
            {
                return None;
            }
        }
        unsafe { self.inner.remove(key) }
    }
}

// ─── Index / IndexMut ───────────────────────────────────────────────────────

impl<C: SlotStorage> std::ops::Index<CastKey<C::Output, KeyOfStorage<C>>> for StableCastMap<C>
where
    C::Stored: ConcreteTypeId,
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
    C::Output: AnyHaver,
    <C::Output as Pointee>::Metadata: Copy,
{
    type Output = C::Output;

    #[inline]
    fn index(&self, key: CastKey<C::Output, KeyOfStorage<C>>) -> &Self::Output {
        self.get(key).unwrap()
    }
}

impl<C: SlotStorage + SlotStorageMutOutput>
std::ops::IndexMut<CastKey<C::Output, KeyOfStorage<C>>> for StableCastMap<C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise + ConcreteTypeId,
    C::Output: AnyHaver,
    <C::Output as Pointee>::Metadata: Copy,
{
    #[inline]
    fn index_mut(&mut self, key: CastKey<C::Output, KeyOfStorage<C>>) -> &mut Self::Output {
        self.get_mut(key).unwrap()
    }
}

/// Convenience alias: [`StableCastMap`] backed by the crate's [`CastBox`] with a
/// configurable key. `CastBox` implements [`ConcreteTypeId`], so this is the
/// ready-made form on which the checked lookups are available.
pub type StableBoxCastMap<K, T> = StableCastMap<DerefSlot<K, CastBox<T>>>;

// ─── IterMut ────────────────────────────────────────────────────────────────

pub struct IterMut<'a, C: SlotStorage>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
{
    inner: unsafe_cast_map::IterMut<'a, C>,
}

impl<'a, C: SlotStorage> Iterator for IterMut<'a, C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise + DerefMut + 'a,
    <C::Stored as Deref>::Target: 'a,
    <C::Output as Pointee>::Metadata: Copy,
{
    type Item = (CastKey<C::Output, KeyOfStorage<C>>, &'a mut C::Output);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
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
}

impl<'a, C: SlotStorage> Iterator for Drain<'a, C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
    <C::Output as Pointee>::Metadata: Copy,
{
    type Item = (CastKey<C::Output, KeyOfStorage<C>>, C::Stored);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
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
}

impl<C: SlotStorage> Iterator for IntoIter<C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
    <C::Output as Pointee>::Metadata: Copy,
{
    type Item = (CastKey<C::Output, KeyOfStorage<C>>, C::Stored);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
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
    type Item = (CastKey<C::Output, KeyOfStorage<C>>, C::Stored);
    type IntoIter = IntoIter<C>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.inner.into_iter(),
        }
    }
}

impl<'a, C: SlotStorage> IntoIterator for &'a mut StableCastMap<C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise + DerefMut + 'a,
    <C::Stored as Deref>::Target: 'a,
    <C::Output as Pointee>::Metadata: Copy,
{
    type Item = (CastKey<C::Output, KeyOfStorage<C>>, &'a mut C::Output);
    type IntoIter = IterMut<'a, C>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}