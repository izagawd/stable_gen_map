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
use std::collections::TryReserveError;
use std::ops::{DerefMut, Index, IndexMut};
use std::ptr::Pointee;

use crate::cast_key::{CastKey, DefaultMapKey};
use crate::gen_map;
use crate::key::Key;
use crate::key_piece::KeyPiece;
use crate::stable_deref_map::{
    DerefGenMapPromise, DerefSlot, SmartPtrCloneable, StableDerefMap,
};

// ─── Conversion helper ─────────────────────────────────────────────────────

/// Build a cast key from an inner key and a reference (for pointer metadata).
#[inline]
fn to_castable<D, Idx, Gen>(
    inner: DefaultMapKey<Idx, Gen>,
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
    pub(crate) inner: StableDerefMap<DefaultMapKey<Idx, Gen>, D>,
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
        func: impl FnOnce(DefaultMapKey<Idx, Gen>) -> D,
    ) -> (CastKey<D::Target, Idx, Gen>, &D::Target) {
        self.try_insert_with_key(|key| Ok::<_, ()>(func(key)))
            .unwrap()
    }

    /// Like [`insert_with_key`](Self::insert_with_key) but the closure may
    /// return `Err`, in which case the slot is released.
    #[inline]
    pub fn try_insert_with_key<E>(
        &self,
        func: impl FnOnce(DefaultMapKey<Idx, Gen>) -> Result<D, E>,
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
        func: impl FnOnce(DefaultMapKey<Idx, Gen>) -> SourceD,
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
        func: impl FnOnce(DefaultMapKey<Idx, Gen>) -> Result<SourceD, E>,
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

    // ── inner-key access ──────────────────────────────────────────────

    /// Shared-reference lookup using the inner key directly.
    #[inline]
    pub fn get_by_inner_key(&self, key: DefaultMapKey<Idx, Gen>) -> Option<&D::Target> {
        self.inner.get(key)
    }

    /// Mutable-reference lookup using the inner key directly.
    #[inline]
    pub fn get_mut_by_inner_key(&mut self, key: DefaultMapKey<Idx, Gen>) -> Option<&mut D::Target>
    where
        D: std::ops::DerefMut,
    {
        self.inner.get_mut(key)
    }

    /// Removes an element by inner key.
    #[inline]
    pub fn remove_by_inner_key(&mut self, key: DefaultMapKey<Idx, Gen>) -> Option<D> {
        self.inner.remove(key)
    }

    /// Converts an inner key to a full [`CastKey`] by looking up the stored
    /// value to obtain its pointer metadata.
    ///
    /// Returns `None` if the inner key is stale.
    #[inline]
    pub fn cast_key_of(&self, inner: DefaultMapKey<Idx, Gen>) -> Option<CastKey<D::Target, Idx, Gen>> {
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

    /// Removes an element by cast key.
    #[inline]
    pub fn remove<T: ?Sized + Pointee>(&mut self, key: CastKey<T, Idx, Gen>) -> Option<D>
    where
        <T as Pointee>::Metadata: Copy,
    {
        self.inner.remove(key.inner_key())
    }
}

// ─── Index / IndexMut ───────────────────────────────────────────────────────

impl<D, Idx, Gen> Index<CastKey<D::Target, Idx, Gen>> for UnsafeCastMap<D, Idx, Gen>
where
    D: DerefGenMapPromise,
    <D::Target as Pointee>::Metadata: Copy,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    type Output = D::Target;

    fn index(&self, key: CastKey<D::Target, Idx, Gen>) -> &Self::Output {
        unsafe { self.get(key).unwrap() }
    }
}

impl<D, Idx, Gen> IndexMut<CastKey<D::Target, Idx, Gen>> for UnsafeCastMap<D, Idx, Gen>
where
    D: DerefGenMapPromise + std::ops::DerefMut,
    <D::Target as Pointee>::Metadata: Copy,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    fn index_mut(&mut self, key: CastKey<D::Target, Idx, Gen>) -> &mut Self::Output {
        unsafe { self.get_mut(key).unwrap() }
    }
}

// ─── IterMut ────────────────────────────────────────────────────────────────

pub struct IterMut<'a, D, Idx = u32, Gen = u32>
where
    D: DerefGenMapPromise,
    Idx: Copy + KeyPiece,
    Gen: Copy + KeyPiece,
{
    inner: gen_map::IterMut<'a, DefaultMapKey<Idx, Gen>, DerefSlot<D, DefaultMapKey<Idx, Gen>>>,
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
    inner: gen_map::Drain<'a, DefaultMapKey<Idx, Gen>, DerefSlot<D, DefaultMapKey<Idx, Gen>>>,
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
    inner: gen_map::IntoIter<DefaultMapKey<Idx, Gen>, DerefSlot<D, DefaultMapKey<Idx, Gen>>>,
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
