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
use std::ops::DerefMut;
use std::ptr::Pointee;

use crate::cast_key::{CastKey, InnerCastMapKey};
use crate::gen_map;
use crate::gen_map::Slot;
use crate::key_piece::KeyPiece;
use crate::stable_deref_map::{
    DerefGenMapPromise, DerefSlot, SmartPtrCloneable, StableDerefMap,
};

// ─── Conversion helper ─────────────────────────────────────────────────────

/// Build a cast key from an inner key and a reference (for pointer metadata).
#[inline]
fn to_castable<D, Idx, Gen>(
    inner: InnerCastMapKey<Idx, Gen>,
    reference: &D::Target,
) -> CastKey<D::Target, Idx, Gen>
where
    D: DerefGenMapPromise,
    <D::Target as Pointee>::Metadata: Copy,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    let metadata = std::ptr::metadata(reference as *const D::Target);
    CastKey {
        key_data: inner.key_data,
        metadata,
    }
}

// ─── UnsafeCastMap ───────────────────────────────────────────────────────────

/// A [`StableDerefMap`] wrapper that supports typed lookups via
/// [`CastKey`].
///
/// - `D`: the smart pointer type, e.g. `Box<dyn Any>`.
/// - `Idx`: index type (default `u32`).
/// - `Gen`: generation type (default `u32`).
pub struct UnsafeCastMap<D, Idx = u32, Gen = u32>
where
    D: DerefGenMapPromise,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    pub(crate) inner: StableDerefMap<InnerCastMapKey<Idx, Gen>, D>,
}

// ─── Clone ──────────────────────────────────────────────────────────────────

impl<D, Idx, Gen> Clone for UnsafeCastMap<D, Idx, Gen>
where
    D: DerefGenMapPromise + SmartPtrCloneable,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    /// Clones the map.
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

// ─── Basic methods ──────────────────────────────────────────────────────────

impl<D, Idx, Gen> UnsafeCastMap<D, Idx, Gen>
where
    D: DerefGenMapPromise,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    /// Creates a new, empty map.
    #[inline]
    pub const fn new() -> Self {
        Self {
            inner: StableDerefMap::new(),
        }
    }

    /// Creates a new map with the given pre-allocated capacity.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: StableDerefMap::with_capacity(capacity),
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

// ─── Core operations ────────────────────────────────────────────────────────

impl<D, Idx, Gen> UnsafeCastMap<D, Idx, Gen>
where
    D: DerefGenMapPromise,
    <D::Target as Pointee>::Metadata: Copy,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    /// Attempts to downcast a `CastKey<dyn Any, ..>` to a concrete-typed key.
    ///
    /// Returns `None` if the key is stale or the concrete type doesn't match.
    ///
    /// # Safety
    /// The key's metadata must be valid for the data stored at that slot.
    #[inline]
    pub unsafe fn downcast_key<Concrete: 'static>(
        &self,
        key: CastKey<dyn Any, Idx, Gen>,
    ) -> Option<CastKey<Concrete, Idx, Gen>> {
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

    /// Inserts a smart pointer, returning a key (with metadata)
    /// and a reference to the deref target.
    #[inline]
    pub fn insert(&self, value: D) -> (CastKey<D::Target, Idx, Gen>, &D::Target) {
        self.insert_with_key(|_| value)
    }

    /// Inserts a smart pointer produced by `func`, which receives the
    /// inner key that will identify the inserted element.
    #[inline]
    pub fn insert_with_key(
        &self,
        func: impl FnOnce(InnerCastMapKey<Idx, Gen>) -> D,
    ) -> (CastKey<D::Target, Idx, Gen>, &D::Target) {
        self.try_insert_with_key(|key| Ok::<_, ()>(func(key)))
            .unwrap()
    }

    /// Like [`insert_with_key`](Self::insert_with_key) but the closure may
    /// return `Err`, in which case the slot is released.
    #[inline]
    pub fn try_insert_with_key<E>(
        &self,
        func: impl FnOnce(InnerCastMapKey<Idx, Gen>) -> Result<D, E>,
    ) -> Result<(CastKey<D::Target, Idx, Gen>, &D::Target), E> {
        let (inner_key, reference) = self.inner.try_insert_with_key(func)?;
        Ok((to_castable::<D, Idx, Gen>(inner_key, reference), reference))
    }

    // ── insert_sized ────────────────────────────────────────────────────

    /// Inserts a *concrete* smart pointer, returning a key and reference
    /// typed with the concrete `ConcreteD::Target`.
    #[inline]
    pub fn insert_sized<ConcreteD>(
        &self,
        value: ConcreteD,
    ) -> (CastKey<ConcreteD::Target, Idx, Gen>, &ConcreteD::Target)
    where
        ConcreteD: std::ops::CoerceUnsized<D> + std::ops::Deref,
        ConcreteD::Target: Sized,
    {
        self.insert_sized_with_key(|_| value)
    }

    /// Inserts a concrete smart pointer produced by `func`, which receives
    /// the fully-typed [`CastKey`].
    #[inline]
    pub fn insert_sized_with_key<ConcreteD>(
        &self,
        func: impl FnOnce(CastKey<ConcreteD::Target, Idx, Gen>) -> ConcreteD,
    ) -> (CastKey<ConcreteD::Target, Idx, Gen>, &ConcreteD::Target)
    where
        ConcreteD: std::ops::CoerceUnsized<D> + std::ops::Deref,
        ConcreteD::Target: Sized,
    {
        self.try_insert_sized_with_key(|key| Ok::<_, ()>(func(key)))
            .unwrap()
    }

    /// Like [`insert_sized_with_key`](Self::insert_sized_with_key) but the
    /// closure may return `Err`.
    #[inline]
    pub fn try_insert_sized_with_key<ConcreteD, E>(
        &self,
        func: impl FnOnce(CastKey<ConcreteD::Target, Idx, Gen>) -> Result<ConcreteD, E>,
    ) -> Result<(CastKey<ConcreteD::Target, Idx, Gen>, &ConcreteD::Target), E>
    where
        ConcreteD: std::ops::CoerceUnsized<D> + std::ops::Deref,
        ConcreteD::Target: Sized,
    {
        let mut saved_key: Option<CastKey<ConcreteD::Target, Idx, Gen>> = None;

        let (_, erased_ref) =
            self.inner
                .try_insert_with_key(|inner_key| -> Result<D, E> {
                    let typed_key = CastKey {
                        key_data: inner_key.key_data,
                        metadata: (),
                    };
                    saved_key = Some(typed_key);
                    let concrete: ConcreteD = func(typed_key)?;
                    Ok(concrete)
                })?;

        let key = saved_key.unwrap();
        let concrete_ref: &ConcreteD::Target = unsafe {
            &*(erased_ref as *const D::Target as *const () as *const ConcreteD::Target)
        };
        Ok((key, concrete_ref))
    }

    // ── insert_as ───────────────────────────────────────────────────────

    /// Inserts a smart pointer whose target type differs from the map's
    /// `D::Target`, returning a key and reference typed with the *source*
    /// type.
    #[inline]
    pub fn insert_as<SourceD>(
        &self,
        value: SourceD,
    ) -> (CastKey<SourceD::Target, Idx, Gen>, &SourceD::Target)
    where
        SourceD: std::ops::CoerceUnsized<D> + std::ops::Deref,
        SourceD::Target: Pointee<Metadata: Copy>,
    {
        self.insert_as_with_key(|_| value)
    }

    /// Inserts a smart pointer produced by `func`, returning a key and
    /// reference typed with the source `SourceD::Target`.
    #[inline]
    pub fn insert_as_with_key<SourceD>(
        &self,
        func: impl FnOnce(InnerCastMapKey<Idx, Gen>) -> SourceD,
    ) -> (CastKey<SourceD::Target, Idx, Gen>, &SourceD::Target)
    where
        SourceD: std::ops::CoerceUnsized<D> + std::ops::Deref,
        SourceD::Target: Pointee<Metadata: Copy>,
    {
        self.try_insert_as_with_key(|key| Ok::<_, ()>(func(key)))
            .unwrap()
    }

    /// Like [`insert_as_with_key`](Self::insert_as_with_key) but the closure
    /// may return `Err`.
    #[inline]
    pub fn try_insert_as_with_key<SourceD, E>(
        &self,
        func: impl FnOnce(InnerCastMapKey<Idx, Gen>) -> Result<SourceD, E>,
    ) -> Result<(CastKey<SourceD::Target, Idx, Gen>, &SourceD::Target), E>
    where
        SourceD: std::ops::CoerceUnsized<D> + std::ops::Deref,
        SourceD::Target: Pointee<Metadata: Copy>,
    {
        let mut saved_metadata: Option<<SourceD::Target as Pointee>::Metadata> = None;

        let (inner_key, erased_ref) =
            self.inner
                .try_insert_with_key(|inner_key| -> Result<D, E> {
                    let concrete: SourceD = func(inner_key)?;
                    saved_metadata =
                        Some(std::ptr::metadata(&*concrete as *const SourceD::Target));
                    Ok(concrete)
                })?;

        let metadata = saved_metadata.unwrap();
        let data_ptr: *const () = (erased_ref as *const D::Target).cast();
        let concrete_ref: &SourceD::Target =
            unsafe { &*std::ptr::from_raw_parts(data_ptr, metadata) };
        let key = CastKey {
            key_data: inner_key.key_data,
            metadata,
        };
        Ok((key, concrete_ref))
    }

    // ── get_by_index_only ───────────────────────────────────────────────

    /// Shared-reference lookup by index only (ignores generation).
    #[inline]
    pub fn get_by_index_only(&self, idx: Idx) -> Option<(CastKey<D::Target, Idx, Gen>, &D::Target)> {
        let (inner_key, reference) = self.inner.get_by_index_only(idx)?;
        Some((to_castable::<D, Idx, Gen>(inner_key, reference), reference))
    }

    /// Mutable lookup by index only (ignores generation).
    #[inline]
    pub fn get_by_index_only_mut(
        &mut self,
        idx: Idx,
    ) -> Option<(CastKey<D::Target, Idx, Gen>, &mut D::Target)>
    where
        D: DerefMut,
    {
        let (inner_key, reference) = self.inner.get_by_index_only_mut(idx)?;
        let patched = to_castable::<D, Idx, Gen>(inner_key, reference);
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
    /// accessing that old `&Slot` or any of its contents is undefined behaviour.** `insert` only
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
    pub unsafe fn get_slot_unchecked_mut(
        &mut self,
        idx: Idx,
    ) -> &mut Slot<DerefSlot<D, InnerCastMapKey<Idx, Gen>>, InnerCastMapKey<Idx, Gen>> {
        self.inner.get_slot_unchecked_mut(idx)
    }

    /// Safe wrapper around [`clone_efficiently`](Self::clone_efficiently):
    /// the `&mut self` borrow prevents the stored type's `Clone` from
    /// mutating the map.
    #[inline]
    pub fn clone_efficiently_mut(&mut self) -> Self where D: Clone
    {
        Self{
            inner: self.inner.clone_efficiently_mut()
        }
    }

    /// A more efficient clone than `Clone::clone`, but **UB** if the `Clone`
    /// implementation of the stored type mutates the map.
    pub unsafe  fn clone_efficiently(&self) -> Self  where D: Clone {
        Self{
            inner: self.inner.clone_efficiently(),
        }
    }

    // ── inner-key access ──────────────────────────────────────────────

    /// Shared-reference lookup using the inner key directly.
    #[inline]
    pub fn get_by_inner_key(&self, key: InnerCastMapKey<Idx, Gen>) -> Option<&D::Target> {
        self.inner.get(key)
    }

    /// Mutable-reference lookup using the inner key directly.
    #[inline]
    pub fn get_by_inner_key_mut(&mut self, key: InnerCastMapKey<Idx, Gen>) -> Option<&mut D::Target>
    where
        D: std::ops::DerefMut,
    {
        self.inner.get_mut(key)
    }

    /// Removes an element by inner key.
    #[inline]
    pub fn remove_by_inner_key(&mut self, key: InnerCastMapKey<Idx, Gen>) -> Option<D> {
        self.inner.remove(key)
    }

    /// Converts an inner key to a full [`CastKey`] by looking up the stored
    /// value to obtain its pointer metadata.
    ///
    /// Returns `None` if the inner key is stale.
    #[inline]
    pub fn cast_key_of(&self, inner: InnerCastMapKey<Idx, Gen>) -> Option<CastKey<D::Target, Idx, Gen>> {
        let reference: &D::Target = self.inner.get(inner)?;
        Some(to_castable::<D, Idx, Gen>(inner, reference))
    }

    // ── retain ──────────────────────────────────────────────────────────

    /// Retains only elements for which `f(key, &mut target)` returns `true`.
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(CastKey<D::Target, Idx, Gen>, &mut D::Target) -> bool,
        D: DerefMut,
    {
        self.inner.retain(|inner_key, stored| {
            let reference: &D::Target = &**stored;
            let patched = to_castable::<D, Idx, Gen>(inner_key, reference);
            f(patched, stored.deref_mut())
        })
    }

    // ── snapshot ────────────────────────────────────────────────────────

    /// Returns a snapshot of all `(key, &target)` pairs.
    #[inline]
    pub fn snapshot(&self) -> Vec<(CastKey<D::Target, Idx, Gen>, &D::Target)> {
        unsafe {
            let mut vec = Vec::with_capacity(self.inner.len());
            vec.extend(self.inner.iter_unsafe().map(|(inner_key, reference)| {
                (to_castable::<D, Idx, Gen>(inner_key, reference), reference)
            }));
            vec
        }
    }

    /// Returns a snapshot of `&target` references only.
    #[inline]
    pub fn snapshot_refs(&self) -> Vec<&D::Target> {
        unsafe {
            let mut vec = Vec::with_capacity(self.inner.len());
            vec.extend(self.inner.iter_unsafe().map(|(_, reference)| reference));
            vec
        }
    }

    /// Returns a snapshot of keys only.
    #[inline]
    pub fn snapshot_keys(&self) -> Vec<CastKey<D::Target, Idx, Gen>> {
        unsafe {
            let mut vec = Vec::with_capacity(self.inner.len());
            vec.extend(
                self.inner
                    .iter_unsafe()
                    .map(|(inner_key, reference)| to_castable::<D, Idx, Gen>(inner_key, reference)),
            );
            vec
        }
    }

    // ── iter_unsafe ─────────────────────────────────────────────────────

    /// # Safety
    /// No mutation (including `insert`) may occur while iterating.
    #[inline]
    pub unsafe fn iter_unsafe(&self) -> impl Iterator<Item = (CastKey<D::Target, Idx, Gen>, &D::Target)> {
        self.inner
            .iter_unsafe()
            .map(move |(inner_key, reference)| {
                (to_castable::<D, Idx, Gen>(inner_key, reference), reference)
            })
    }

    // ── iter_mut ────────────────────────────────────────────────────────

    /// Mutable iterator over all occupied elements.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, D, Idx, Gen> {
        IterMut {
            inner: self.inner.iter_mut(),
        }
    }

    // ── drain ───────────────────────────────────────────────────────────

    /// Removes all elements and returns them as an iterator.
    #[inline]
    pub fn drain(&mut self) -> Drain<'_, D, Idx, Gen> {
        Drain {
            inner: self.inner.drain(),
        }
    }
}

/// Convenience alias: [`UnsafeCastMap`] storing `Box<T>`.
pub type UnsafeBoxCastMap<T, Idx = u32, Gen = u32> = UnsafeCastMap<Box<T>, Idx, Gen>;

// ─── Cross-typed lookups ────────────────────────────────────────────────────

impl<D, Idx, Gen> UnsafeCastMap<D, Idx, Gen>
where
    D: DerefGenMapPromise,
    <D::Target as Pointee>::Metadata: Copy,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    /// Shared-reference lookup with a key for a potentially *different* type `T`.
    ///
    /// # Safety
    /// The key's metadata must be valid for the data stored at that slot.
    #[inline]
    pub unsafe fn get<T: ?Sized + Pointee>(&self, key: CastKey<T, Idx, Gen>) -> Option<&T>
    where
        <T as Pointee>::Metadata: Copy,
    {
        let base_ref: &D::Target = self.inner.get(key.inner_key())?;
        let data_ptr: *const () = (base_ref as *const D::Target).cast();
        let fat_ptr: *const T = std::ptr::from_raw_parts(data_ptr, key.metadata());
        unsafe { Some(&*fat_ptr) }
    }

    /// Mutable-reference lookup with a potentially differently-typed key.
    ///
    /// # Safety
    /// The key's metadata must be valid for the data stored at that slot.
    #[inline]
    pub unsafe fn get_mut<T: ?Sized + Pointee>(&mut self, key: CastKey<T, Idx, Gen>) -> Option<&mut T>
    where
        <T as Pointee>::Metadata: Copy,
        D: std::ops::DerefMut,
    {
        let base_ref: &mut D::Target = self.inner.get_mut(key.inner_key())?;
        let data_ptr: *mut () = (base_ref as *mut D::Target).cast();
        let fat_ptr: *mut T = std::ptr::from_raw_parts_mut(data_ptr, key.metadata());
        unsafe { Some(&mut *fat_ptr) }
    }

    /// Shared-reference lookup without bounds or generation checks.
    ///
    /// # Safety
    /// - The key's index must be in bounds.
    /// - The slot at that index must be occupied with the matching generation.
    /// - The key's metadata must be valid for the data stored at that slot.
    #[inline]
    pub unsafe fn get_unchecked<T: ?Sized + Pointee>(&self, key: CastKey<T, Idx, Gen>) -> &T
    where
        <T as Pointee>::Metadata: Copy,
    {
        let base_ref: &D::Target = self.inner.get_unchecked(key.inner_key());
        let data_ptr: *const () = (base_ref as *const D::Target).cast();
        let fat_ptr: *const T = std::ptr::from_raw_parts(data_ptr, key.metadata());
        &*fat_ptr
    }

    /// Mutable-reference lookup without bounds or generation checks.
    ///
    /// # Safety
    /// - The key's index must be in bounds.
    /// - The slot at that index must be occupied with the matching generation.
    /// - The key's metadata must be valid for the data stored at that slot.
    #[inline]
    pub unsafe fn get_unchecked_mut<T: ?Sized + Pointee>(&mut self, key: CastKey<T, Idx, Gen>) -> &mut T
    where
        <T as Pointee>::Metadata: Copy,
        D: std::ops::DerefMut,
    {
        let base_ref: &mut D::Target = self.inner.get_unchecked_mut(key.inner_key());
        let data_ptr: *mut () = (base_ref as *mut D::Target).cast();
        let fat_ptr: *mut T = std::ptr::from_raw_parts_mut(data_ptr, key.metadata());
        &mut *fat_ptr
    }

    /// Removes an element by cast key.
    #[inline]
    pub fn remove<T: ?Sized + Pointee>(&mut self, key: CastKey<T, Idx, Gen>) -> Option<D>
    where
        <T as Pointee>::Metadata: Copy,
    {
        self.inner.remove(key.inner_key())
    }
}




// ─── IterMut ────────────────────────────────────────────────────────────────

pub struct IterMut<'a, D, Idx = u32, Gen = u32>
where
    D: DerefGenMapPromise,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    inner: gen_map::IterMut<'a, InnerCastMapKey<Idx, Gen>, DerefSlot<D, InnerCastMapKey<Idx, Gen>>>,
}

impl<'a, D, Idx, Gen> Iterator for IterMut<'a, D, Idx, Gen>
where
    D: DerefGenMapPromise + DerefMut,
    <D::Target as Pointee>::Metadata: Copy,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    type Item = (CastKey<D::Target, Idx, Gen>, &'a mut D::Target);

    fn next(&mut self) -> Option<Self::Item> {
        let (inner_key, stored) = self.inner.next()?;
        let patched = to_castable::<D, Idx, Gen>(inner_key, &**stored);
        Some((patched, stored.deref_mut()))
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
    inner: gen_map::Drain<'a, InnerCastMapKey<Idx, Gen>, DerefSlot<D, InnerCastMapKey<Idx, Gen>>>,
}

impl<'a, D, Idx, Gen> Iterator for Drain<'a, D, Idx, Gen>
where
    D: DerefGenMapPromise,
    <D::Target as Pointee>::Metadata: Copy,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    type Item = (CastKey<D::Target, Idx, Gen>, D);

    fn next(&mut self) -> Option<Self::Item> {
        let (inner_key, value) = self.inner.next()?;
        let patched = to_castable::<D, Idx, Gen>(inner_key, &*value);
        Some((patched, value))
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
    inner: gen_map::IntoIter<InnerCastMapKey<Idx, Gen>, DerefSlot<D, InnerCastMapKey<Idx, Gen>>>,
}

impl<D, Idx, Gen> Iterator for IntoIter<D, Idx, Gen>
where
    D: DerefGenMapPromise,
    <D::Target as Pointee>::Metadata: Copy,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    type Item = (CastKey<D::Target, Idx, Gen>, D);

    fn next(&mut self) -> Option<Self::Item> {
        let (inner_key, value) = self.inner.next()?;
        let patched = to_castable::<D, Idx, Gen>(inner_key, &*value);
        Some((patched, value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<D, Idx, Gen> IntoIterator for UnsafeCastMap<D, Idx, Gen>
where
    D: DerefGenMapPromise,
    <D::Target as Pointee>::Metadata: Copy,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    type Item = (CastKey<D::Target, Idx, Gen>, D);
    type IntoIter = IntoIter<D, Idx, Gen>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.inner.into_iter(),
        }
    }
}

impl<'a, D, Idx, Gen> IntoIterator for &'a mut UnsafeCastMap<D, Idx, Gen>
where
    D: DerefGenMapPromise + DerefMut,
    <D::Target as Pointee>::Metadata: Copy,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    type Item = (CastKey<D::Target, Idx, Gen>, &'a mut D::Target);
    type IntoIter = IterMut<'a, D, Idx, Gen>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}
