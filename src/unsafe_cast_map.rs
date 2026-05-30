//! Low-level cast map without per-map identity checks.
//!
//! [`UnsafeCastMap`] supports typed lookups via [`CastKey`], but the
//! `get`, `get_mut`, and `downcast_key` methods are **`unsafe`** because
//! the caller must ensure the key's pointer metadata is valid for the
//! data stored at that slot.
//!
//! For a safe wrapper that checks a per-map [`MapId`](crate::map_id::MapId),
//! see [`StableCastMap`](crate::stable_cast_map::StableCastMap).

use std::any::Any;
use std::cell::UnsafeCell;
use std::collections::TryReserveError;
use std::ops::{Deref, DerefMut};
use std::ptr::Pointee;

use crate::cast_key::CastKey;
use crate::deref_slot::{DerefGenMapPromise, DerefSlot};
use crate::gen_map::{self, GenMap, IdxOfStorage, KeyOfStorage, Slot};
use crate::key::Key;
use crate::retype_ptr::RetypePtr;
use crate::slot_storage::{SlotStorage, SlotStorageMutOutput};
// ─── Conversion helper ─────────────────────────────────────────────────────

/// Build a cast key from an inner key and a reference (for pointer metadata).
#[inline]
fn to_castable<C: SlotStorage>(
    inner: KeyOfStorage<C>,
    reference: &C::Output,
) -> CastKey<C::Output, KeyOfStorage<C>>
where
    <C::Output as Pointee>::Metadata: Copy,
{
    let metadata = std::ptr::metadata(reference as *const C::Output);
    CastKey {
        key_data: inner.data(),
        metadata,
    }
}

// ─── UnsafeCastMap ───────────────────────────────────────────────────────────

/// A [`GenMap`] wrapper that supports typed lookups via [`CastKey`].
///
/// `C` is the per-slot storage strategy (e.g.
/// [`DerefSlot<DefaultKey, Box<dyn Any>>`]).
///
/// The slot's [`Stored`](SlotStorage::Stored) type must implement
/// [`DerefGenMapPromise`] so that pointer-metadata casts are sound.
pub struct UnsafeCastMap<C: SlotStorage>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
{
    pub(crate) inner: GenMap<C>,
}

// ─── Clone ──────────────────────────────────────────────────────────────────

impl<C: SlotStorage> Clone for UnsafeCastMap<C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
    GenMap<C>: Clone,
{
    #[inline]
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

// ─── Basic methods ──────────────────────────────────────────────────────────

impl<C: SlotStorage> Default for UnsafeCastMap<C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<C: SlotStorage> UnsafeCastMap<C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
{
    /// Creates a new, empty map.
    #[inline]
    pub const fn new() -> Self {
        Self {
            inner: GenMap::new(),
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
            inner: GenMap::with_capacity(capacity),
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

    /// Removes all elements from the map.
    #[inline]
    pub fn clear(&mut self) {
        self.inner.clear();
    }
}

// ─── Core operations ────────────────────────────────────────────────────────

impl<C: SlotStorage> UnsafeCastMap<C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
    <C::Output as Pointee>::Metadata: Copy,
{
    /// Attempts to downcast a `CastKey<dyn Any, ..>` to a concrete-typed key.
    /// Returns `None` if the actual type doesn't match `Concrete`.
    ///
    /// # Safety
    /// The key's metadata must be a valid vtable for `dyn Any` pointing at
    /// the data stored in that slot.
    #[inline]
    pub unsafe fn downcast_key<Concrete: 'static>(
        &self,
        key: CastKey<dyn Any, KeyOfStorage<C>>,
    ) -> Option<CastKey<Concrete, KeyOfStorage<C>>> {
        let data = self.inner.get(key.inner_key())?;
        let data_as_any: &dyn Any =
            unsafe { &*std::ptr::from_raw_parts(data as *const _ as *const (), key.metadata()) };
        if data_as_any.type_id() == std::any::TypeId::of::<Concrete>() {
            Some(CastKey {
                key_data: key.key_data,
                metadata: (),
            })
        } else {
            None
        }
    }
    // ── insert ──────────────────────────────────────────────────────────
    /// Inserts a smart pointer, returning a key with metadata.
    #[inline]
    pub fn insert(&self, value: C::Stored) -> CastKey<C::Output, KeyOfStorage<C>> {
        self.insert_with_key(|_| value)
    }
    /// Inserts a smart pointer produced by `func`, which receives the
    /// inner key that will identify the inserted element.
    #[inline]
    pub fn insert_with_key(
        &self,
        func: impl FnOnce(KeyOfStorage<C>) -> C::Stored,
    ) -> CastKey<C::Output, KeyOfStorage<C>> {
        self.try_insert_with_key(|key| Ok::<_, ()>(func(key)))
            .unwrap()
    }
    /// Like [`insert_with_key`](Self::insert_with_key) but the closure may
    /// return `Err`, in which case the slot is released.
    #[inline]
    pub fn try_insert_with_key<E>(
        &self,
        func: impl FnOnce(KeyOfStorage<C>) -> Result<C::Stored, E>,
    ) -> Result<CastKey<C::Output, KeyOfStorage<C>>, E> {
        let inner_key = self.inner.try_insert_with_key(func)?;
        let reference = self.inner.get(inner_key).unwrap();
        Ok(to_castable::<C>(inner_key, reference))
    }

    // ── insert_sized ────────────────────────────────────────────────────

    /// Inserts a concrete-typed smart pointer, returning a [`CastKey`] whose
    /// metadata is for `ConcretePtr::Target` (not the erased `C::Output`).
    #[inline]
    pub fn insert_sized<ConcretePtr>(
        &self,
        value: ConcretePtr,
    ) -> CastKey<ConcretePtr::Target, KeyOfStorage<C>>
    where
        ConcretePtr: std::ops::CoerceUnsized<C::Stored> + Deref,
        ConcretePtr::Target: Sized,
    {
        self.insert_sized_with_key(|_| value)
    }
    /// Inserts a concrete smart pointer produced by `func`, which receives
    /// the fully-typed [`CastKey`].
    #[inline]
    pub fn insert_sized_with_key<ConcretePtr>(
        &self,
        func: impl FnOnce(CastKey<ConcretePtr::Target, KeyOfStorage<C>>) -> ConcretePtr,
    ) -> CastKey<ConcretePtr::Target, KeyOfStorage<C>>
    where
        ConcretePtr: std::ops::CoerceUnsized<C::Stored> + Deref,
        ConcretePtr::Target: Sized,
    {
        self.try_insert_sized_with_key(|key| Ok::<_, ()>(func(key)))
            .unwrap()
    }
    /// Like [`insert_sized_with_key`](Self::insert_sized_with_key) but the
    /// closure may return `Err`.
    #[inline]
    pub fn try_insert_sized_with_key<ConcretePtr, E>(
        &self,
        func: impl FnOnce(CastKey<ConcretePtr::Target, KeyOfStorage<C>>) -> Result<ConcretePtr, E>,
    ) -> Result<CastKey<ConcretePtr::Target, KeyOfStorage<C>>, E>
    where
        ConcretePtr: std::ops::CoerceUnsized<C::Stored> + Deref,
        ConcretePtr::Target: Sized,
    {
        let mut saved_key: Option<CastKey<ConcretePtr::Target, KeyOfStorage<C>>> = None;

        self.inner
            .try_insert_with_key(|inner_key| -> Result<C::Stored, E> {
                let typed_key = CastKey {
                    key_data: inner_key.data(),
                    metadata: (),
                };
                saved_key = Some(typed_key);
                let concrete: ConcretePtr = func(typed_key)?;
                Ok(concrete)
            })?;

        Ok(saved_key.unwrap())
    }
    // ── insert_as ───────────────────────────────────────────────────────
    /// Inserts a smart pointer whose target type differs from the map's
    /// `D::Target`, returning a key typed with the *source* type.
    #[inline]
    pub fn insert_as<SourcePtr>(
        &self,
        value: SourcePtr,
    ) -> CastKey<SourcePtr::Target, KeyOfStorage<C>>
    where
        SourcePtr: std::ops::CoerceUnsized<C::Stored> + Deref,
        SourcePtr::Target: Pointee<Metadata: Copy>,
    {
        self.insert_as_with_key(|_| value)
    }
    /// Inserts a smart pointer produced by `func`, returning a key
    /// typed with the source `SourceD::Target`.
    #[inline]
    pub fn insert_as_with_key<SourcePtr>(
        &self,
        func: impl FnOnce(KeyOfStorage<C>) -> SourcePtr,
    ) -> CastKey<SourcePtr::Target, KeyOfStorage<C>>
    where
        SourcePtr: std::ops::CoerceUnsized<C::Stored> + Deref,
        SourcePtr::Target: Pointee<Metadata: Copy>,
    {
        self.try_insert_as_with_key(|key| Ok::<_, ()>(func(key)))
            .unwrap()
    }
    /// Like [`insert_as_with_key`](Self::insert_as_with_key) but the closure
    /// may return `Err`.
    #[inline]
    pub fn try_insert_as_with_key<SourcePtr, E>(
        &self,
        func: impl FnOnce(KeyOfStorage<C>) -> Result<SourcePtr, E>,
    ) -> Result<CastKey<SourcePtr::Target, KeyOfStorage<C>>, E>
    where
        SourcePtr: std::ops::CoerceUnsized<C::Stored> + Deref,
        SourcePtr::Target: Pointee<Metadata: Copy>,
    {
        let mut saved_metadata: Option<<SourcePtr::Target as Pointee>::Metadata> = None;

        let inner_key = self
            .inner
            .try_insert_with_key(|inner_key| -> Result<C::Stored, E> {
                let concrete: SourcePtr = func(inner_key)?;
                saved_metadata = Some(std::ptr::metadata(&*concrete as *const SourcePtr::Target));
                Ok(concrete)
            })?;

        let metadata = saved_metadata.unwrap();
        let key = CastKey {
            key_data: inner_key.data(),
            metadata,
        };
        Ok(key)
    }

    // ── get_by_index_only ───────────────────────────────────────────────

    /// Looks up by slot index only (ignores generation). Returns the cast key
    /// and a reference if the slot is occupied.
    #[inline]
    pub fn get_by_index_only(
        &self,
        idx: IdxOfStorage<C>,
    ) -> Option<(CastKey<C::Output, KeyOfStorage<C>>, &C::Output)> {
        let (inner_key, reference) = self.inner.get_by_index_only(idx)?;
        Some((to_castable::<C>(inner_key, reference), reference))
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
        let (inner_key, reference) = self.inner.get_by_index_only_mut(idx)?;
        let patched = to_castable::<C>(inner_key, reference);
        Some((patched, reference))
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
    /// accessing that old `&Slot` or any of its contents is undefined behaviour.** `insert` only
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
    /// accessing that old `&Slot` or any of its contents is undefined behaviour.** `insert` only
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

    // ── inner-key access ──────────────────────────────────────────────

    /// Shared-reference lookup using the backing [`Key`] directly (no pointer metadata).
    #[inline]
    pub fn get_by_inner_key(&self, key: KeyOfStorage<C>) -> Option<&C::Output> {
        self.inner.get(key)
    }

    /// Mutable-reference lookup using the backing [`Key`] directly.
    #[inline]
    pub fn get_by_inner_key_mut(&mut self, key: KeyOfStorage<C>) -> Option<&mut C::Output>
    where
        C: SlotStorageMutOutput,
    {
        self.inner.get_mut(key)
    }

    /// Removes an element by its backing [`Key`], returning the owned smart pointer.
    #[inline]
    pub fn remove_by_inner_key(&mut self, key: KeyOfStorage<C>) -> Option<C::Stored> {
        self.inner.remove(key)
    }
    /// Converts an inner key to a full [`CastKey`] by looking up the stored
    /// value to obtain its pointer metadata.
    ///
    /// Returns `None` if the inner key is stale.
    #[inline]
    pub fn cast_key_of(
        &self,
        inner: KeyOfStorage<C>,
    ) -> Option<CastKey<C::Output, KeyOfStorage<C>>> {
        let reference: &C::Output = self.inner.get(inner)?;
        Some(to_castable::<C>(inner, reference))
    }

    // ── retain ──────────────────────────────────────────────────────────

    /// Retains only elements for which `f(key, &mut output)` returns `true`.
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(CastKey<C::Output, KeyOfStorage<C>>, &mut C::Output) -> bool,
        C::Stored: DerefMut,
    {
        self.inner.retain(|inner_key, stored| {
            let reference: &C::Output = stored;
            let patched = to_castable::<C>(inner_key, reference);
            f(patched, stored.deref_mut())
        })
    }

    // ── snapshot ────────────────────────────────────────────────────────

    /// Returns a snapshot of all `(CastKey, &output)` pairs. Heap-allocates one `Vec`.
    #[inline]
    pub fn snapshot(&self) -> Vec<(CastKey<C::Output, KeyOfStorage<C>>, &C::Output)> {
        unsafe {
            let mut vec = Vec::with_capacity(self.inner.len());
            vec.extend(
                self.inner.iter_unsafe().map(|(inner_key, reference)| {
                    (to_castable::<C>(inner_key, reference), reference)
                }),
            );
            vec
        }
    }

    /// Returns a snapshot of `&output` references only.
    #[inline]
    pub fn snapshot_refs(&self) -> Vec<&C::Output> {
        unsafe {
            let mut vec = Vec::with_capacity(self.inner.len());
            vec.extend(self.inner.iter_unsafe().map(|(_, reference)| reference));
            vec
        }
    }

    /// Returns a snapshot of all [`CastKey`]s.
    #[inline]
    pub fn snapshot_keys(&self) -> Vec<CastKey<C::Output, KeyOfStorage<C>>> {
        unsafe {
            let mut vec = Vec::with_capacity(self.inner.len());
            vec.extend(
                self.inner
                    .iter_unsafe()
                    .map(|(inner_key, reference)| to_castable::<C>(inner_key, reference)),
            );
            vec
        }
    }

    /// Empties the map and resets all slot generations to zero. Capacity is
    /// retained. Unlike [`clear`](Self::clear), does **not** invalidate
    /// outstanding keys — a pre-`reset` [`CastKey`] may match a live slot again.
    ///
    /// Safe to call: the `get` methods are already `unsafe` and
    /// require valid metadata for the slot the key refers to, so `reset` adds no new unsafe surface.
    /// It just makes UB mistakes more likely, since a stale key can match a reused slot
    /// again, so passing one to those lookups may read the wrong slot.
    pub fn reset(&mut self) {
        self.inner.reset()
    }

    // ── iter_unsafe ─────────────────────────────────────────────────────

    /// Shared iterator over all occupied elements.
    ///
    /// # Safety
    /// No mutation (including `insert`) may occur while iterating.
    #[inline]
    pub unsafe fn iter_unsafe(
        &self,
    ) -> impl Iterator<Item = (CastKey<C::Output, KeyOfStorage<C>>, &C::Output)> {
        self.inner
            .iter_unsafe()
            .map(move |(inner_key, reference)| (to_castable::<C>(inner_key, reference), reference))
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

/// Convenience alias: [`UnsafeCastMap`] using `Box<T>` with a configurable key.
pub type UnsafeBoxCastMap<K, T> = UnsafeCastMap<DerefSlot<K, Box<T>>>;

// ─── Cross-typed lookups ────────────────────────────────────────────────────

impl<C: SlotStorage> UnsafeCastMap<C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
    <C::Output as Pointee>::Metadata: Copy,
{
    /// Cross-typed shared-reference lookup. Reconstructs a fat pointer to `T`
    /// from the stored output's data pointer and the key's metadata.
    ///
    /// # Safety
    /// The key's pointer metadata must be valid for the data stored at that
    /// slot. For example, when `T` is a trait object, the metadata must be
    /// the correct vtable for the concrete type that was originally inserted.
    #[inline]
    pub unsafe fn get<T: ?Sized + Pointee>(&self, key: CastKey<T, KeyOfStorage<C>>) -> Option<&T>
    where
        <T as Pointee>::Metadata: Copy,
    {
        let base_ref: &C::Output = self.inner.get(key.inner_key())?;
        let data_ptr: *const () = (base_ref as *const C::Output).cast();
        let fat_ptr: *const T = std::ptr::from_raw_parts(data_ptr, key.metadata());
        unsafe { Some(&*fat_ptr) }
    }

    /// Cross-typed mutable-reference lookup. Reconstructs a fat pointer to `T`
    /// from the stored output's data pointer and the key's metadata.
    ///
    /// # Safety
    /// The key's pointer metadata must be valid for the data stored at that
    /// slot. For example, when `T` is a trait object, the metadata must be
    /// the correct vtable for the concrete type that was originally inserted.
    #[inline]
    pub unsafe fn get_mut<T: ?Sized + Pointee>(
        &mut self,
        key: CastKey<T, KeyOfStorage<C>>,
    ) -> Option<&mut T>
    where
        <T as Pointee>::Metadata: Copy,
        C: SlotStorageMutOutput,
    {
        let base_ref: &mut C::Output = self.inner.get_mut(key.inner_key())?;
        let data_ptr: *mut () = (base_ref as *mut C::Output).cast();
        let fat_ptr: *mut T = std::ptr::from_raw_parts_mut(data_ptr, key.metadata());
        unsafe { Some(&mut *fat_ptr) }
    }

    /// Shared-reference lookup without bounds or generation checks.
    ///
    /// # Safety
    /// - The key's index must be in bounds.
    /// - The slot at that index must be occupied with the matching generation.
    /// - The key's pointer metadata must be valid for the data in that slot.
    #[inline]
    pub unsafe fn get_unchecked<T: ?Sized + Pointee>(&self, key: CastKey<T, KeyOfStorage<C>>) -> &T
    where
        <T as Pointee>::Metadata: Copy,
    {
        let base_ref: &C::Output = self.inner.get_unchecked(key.inner_key());
        let data_ptr: *const () = (base_ref as *const C::Output).cast();
        let fat_ptr: *const T = std::ptr::from_raw_parts(data_ptr, key.metadata());
        &*fat_ptr
    }

    /// Mutable-reference lookup without bounds or generation checks.
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
        let base_ref: &mut C::Output = self.inner.get_unchecked_mut(key.inner_key());
        let data_ptr: *mut () = (base_ref as *mut C::Output).cast();
        let fat_ptr: *mut T = std::ptr::from_raw_parts_mut(data_ptr, key.metadata());
        &mut *fat_ptr
    }

    /// Removes an element by its [`CastKey`], returning the owned smart pointer.
    /// # Safety
    /// The key's pointer metadata must be valid for the data stored at that
    /// slot. For example, when `T` is a trait object, the metadata must be
    /// the correct vtable for the concrete type that was originally inserted.
    #[inline]
    pub unsafe fn remove<'a, T: ?Sized + Pointee>(
        &mut self,
        key: CastKey<T, KeyOfStorage<C>>,
    ) -> Option<<C::Stored as RetypePtr<'a>>::Retyped<T>>
    where
        <T as Pointee>::Metadata: Copy,
        C::Stored: Deref<Target = C::Output> + DerefGenMapPromise + RetypePtr<'a>,
    {
        let stored = self.inner.remove(key.inner_key())?;
        Some(stored.retype::<T>(key.metadata()))
    }
}

// ─── IterMut ────────────────────────────────────────────────────────────────

pub struct IterMut<'a, C: SlotStorage>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
{
    inner: gen_map::IterMut<'a, C>,
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
        let (inner_key, stored) = self.inner.next()?;
        let patched = to_castable::<C>(inner_key, &**stored);
        Some((patched, stored.deref_mut()))
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
    inner: gen_map::Drain<'a, C>,
}

impl<'a, C: SlotStorage> Iterator for Drain<'a, C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
    <C::Output as Pointee>::Metadata: Copy,
{
    type Item = (CastKey<C::Output, KeyOfStorage<C>>, C::Stored);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let (inner_key, value) = self.inner.next()?;
        let patched = to_castable::<C>(inner_key, &*value);
        Some((patched, value))
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
    inner: gen_map::IntoIter<C>,
}

impl<C: SlotStorage> Iterator for IntoIter<C>
where
    C::Stored: Deref<Target = C::Output> + DerefGenMapPromise,
    <C::Output as Pointee>::Metadata: Copy,
{
    type Item = (CastKey<C::Output, KeyOfStorage<C>>, C::Stored);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let (inner_key, value) = self.inner.next()?;
        let patched = to_castable::<C>(inner_key, &*value);
        Some((patched, value))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<C: SlotStorage> IntoIterator for UnsafeCastMap<C>
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

impl<'a, C: SlotStorage> IntoIterator for &'a mut UnsafeCastMap<C>
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
