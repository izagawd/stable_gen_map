//! Map type that uses a [`CastKey`] as its user-facing key.
//!
//! Internally, a plain key (e.g. [`DefaultMapKey`](crate::cast_key::DefaultMapKey))
//! is used by the `GenMap`. The cast map wrapper converts between the inner
//! key and `CastKey` at every boundary — adding metadata and map id on the
//! way out, stripping them on the way in.
//!
//! The map id is stored once in the container and checked on every keyed
//! access, so keys from one map cannot be used on another.

use std::any::Any;
use std::collections::TryReserveError;
use std::ops::{DerefMut, Index, IndexMut};
use std::ptr::Pointee;

use crate::cast_key::CastKey;
use crate::gen_map;
use crate::key::Key;
use crate::map_id::{MapId, MapIdState};
use crate::stable_deref_map::{
    DerefGenMapPromise, DerefSlot, SmartPtrCloneable, StableDerefMap,
};

// ─── Conversion helper ─────────────────────────────────────────────────────

/// Build a castable key from an inner key, a map id, and a reference (for
/// pointer metadata).
#[inline]
fn to_castable<CK, D>(inner: CK::InnerKey, map_id: MapId, reference: &D::Target) -> CK
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise,
{
    let metadata = std::ptr::metadata(reference as *const D::Target);
    unsafe { CK::from_inner_key_and_metadata(inner, map_id, metadata) }
}

// ─── StableCastMap ───────────────────────────────────────────────────────────

/// A [`StableDerefMap`] wrapper that supports typed lookups via
/// [`CastKey`] and cross-map key safety via a per-map
/// [`MapId`](crate::map_id::MapId).
///
/// - `CK`: the castable key family, e.g. `DefaultCastKey<D::Target>`.
/// - `D`: the smart pointer type, e.g. `Box<dyn Any>`.
pub struct StableCastMap<CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise,
{
    pub(crate) inner: StableDerefMap<CK::InnerKey, D>,
    pub(crate) map_id: MapIdState,
    _phantom: std::marker::PhantomData<fn() -> CK>,
}

// ─── Clone ──────────────────────────────────────────────────────────────────

impl<CK, D> Clone for StableCastMap<CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise + SmartPtrCloneable,
{
    /// Clones the map.
    ///
    /// The clone receives a fresh map identity. Keys from the original are
    /// **not** valid on the clone; use iteration to obtain new keys.
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            map_id: MapIdState::new(),
            _phantom: std::marker::PhantomData,
        }
    }
}

// ─── Helpers ────────────────────────────────────────────────────────────────

impl<CK, D> StableCastMap<CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise,
{
    /// Returns `true` if `key_map_id` matches this map's identity.
    #[inline]
    fn validate_map_id(&self, key_map_id: MapId) -> bool {
        self.map_id
            .current_id()
            .map_or(false, |id| id == key_map_id)
    }

    /// Returns this map's id, assigning one if needed.
    #[inline]
    fn map_id_for_key(&self) -> MapId {
        self.map_id.ensure_id()
    }
}

// ─── Basic methods ──────────────────────────────────────────────────────────

impl<CK, D> StableCastMap<CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise,
{
    /// Creates a new, empty map.
    #[inline]
    pub const fn new() -> Self {
        Self {
            inner: StableDerefMap::new(),
            map_id: MapIdState::new(),
            _phantom: std::marker::PhantomData,
        }
    }

    /// Creates a new map with the given pre-allocated capacity.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: StableDerefMap::with_capacity(capacity),
            map_id: MapIdState::new(),
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

// ─── Core operations ────────────────────────────────────────────────────────

impl<CK, D> StableCastMap<CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise,
{
    /// Attempts to downcast a `CK` (e.g. `DefaultCastKey<dyn Any>`) to a
    /// concrete-typed key from the same family (e.g. `DefaultCastKey<Dog>`).
    ///
    /// Returns `None` if the key is stale, from a different map, or the
    /// concrete type doesn't match.
    #[inline]
    pub fn downcast_key<Concrete: 'static>(
        &self,
        key: CK::WithRef<dyn Any>,
    ) -> Option<CK::WithRef<Concrete>> {
        if !self.validate_map_id(key.map_id()) {
            return None;
        }
        let data = self.inner.get(key.inner_key())?;
        let data_as_any: &dyn Any =
            unsafe { &*std::ptr::from_raw_parts(data as *const _ as *const (), key.metadata()) };
        if data_as_any.type_id() == std::any::TypeId::of::<Concrete>() {
            let map_id = self.map_id_for_key();
            Some(unsafe {
                <CK::WithRef<Concrete> as CastKey>::from_inner_key_and_metadata(
                    key.inner_key(),
                    map_id,
                    (),
                )
            })
        } else {
            None
        }
    }

    // ── insert ──────────────────────────────────────────────────────────

    /// Inserts a smart pointer, returning a key (with metadata and map id)
    /// and a reference to the deref target.
    #[inline]
    pub fn insert(&self, value: D) -> (CK, &D::Target) {
        self.insert_with_key(|_| value)
    }

    /// Inserts a smart pointer produced by `func`, which receives the
    /// inner key that will identify the inserted element.
    #[inline]
    pub fn insert_with_key(&self, func: impl FnOnce(CK::InnerKey) -> D) -> (CK, &D::Target) {
        self.try_insert_with_key(|key| Ok::<_, ()>(func(key)))
            .unwrap()
    }

    /// Like [`insert_with_key`](Self::insert_with_key) but the closure may
    /// return `Err`.
    #[inline]
    pub fn try_insert_with_key<E>(
        &self,
        func: impl FnOnce(CK::InnerKey) -> Result<D, E>,
    ) -> Result<(CK, &D::Target), E> {
        let map_id = self.map_id_for_key();
        let (inner_key, reference) = self.inner.try_insert_with_key(func)?;
        Ok((to_castable::<CK, D>(inner_key, map_id, reference), reference))
    }

    // ── insert_sized ────────────────────────────────────────────────────

    /// Inserts a *concrete* smart pointer, returning a key and reference
    /// typed with the concrete `ConcreteD::Target`.
    #[inline]
    pub fn insert_sized<ConcreteD>(
        &self,
        value: ConcreteD,
    ) -> (CK::WithRef<ConcreteD::Target>, &ConcreteD::Target)
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
        func: impl FnOnce(CK::WithRef<ConcreteD::Target>) -> ConcreteD,
    ) -> (CK::WithRef<ConcreteD::Target>, &ConcreteD::Target)
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
        func: impl FnOnce(CK::WithRef<ConcreteD::Target>) -> Result<ConcreteD, E>,
    ) -> Result<(CK::WithRef<ConcreteD::Target>, &ConcreteD::Target), E>
    where
        ConcreteD: std::ops::CoerceUnsized<D> + std::ops::Deref,
        ConcreteD::Target: Sized,
    {
        let map_id = self.map_id_for_key();
        let mut saved_key: Option<CK::WithRef<ConcreteD::Target>> = None;

        let (_, erased_ref) =
            self.inner
                .try_insert_with_key(|inner_key| -> Result<D, E> {
                    let typed_key = unsafe {
                        <CK::WithRef<ConcreteD::Target> as CastKey>::from_inner_key_and_metadata(
                            inner_key, map_id, (),
                        )
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
    ) -> (CK::WithRef<SourceD::Target>, &SourceD::Target)
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
        func: impl FnOnce(CK::InnerKey) -> SourceD,
    ) -> (CK::WithRef<SourceD::Target>, &SourceD::Target)
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
        func: impl FnOnce(CK::InnerKey) -> Result<SourceD, E>,
    ) -> Result<(CK::WithRef<SourceD::Target>, &SourceD::Target), E>
    where
        SourceD: std::ops::CoerceUnsized<D> + std::ops::Deref,
        SourceD::Target: Pointee<Metadata: Copy>,
    {
        let map_id = self.map_id_for_key();
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
        let key = unsafe {
            <CK::WithRef<SourceD::Target> as CastKey>::from_inner_key_and_metadata(
                inner_key, map_id, metadata,
            )
        };
        Ok((key, concrete_ref))
    }

    // ── get_by_index_only ───────────────────────────────────────────────

    /// Shared-reference lookup by index only (ignores generation and map id).
    #[inline]
    pub fn get_by_index_only(&self, idx: CK::Idx) -> Option<(CK, &D::Target)> {
        let map_id = self.map_id_for_key();
        let (inner_key, reference) = self.inner.get_by_index_only(idx)?;
        Some((to_castable::<CK, D>(inner_key, map_id, reference), reference))
    }

    /// Mutable lookup by index only (ignores generation and map id).
    #[inline]
    pub fn get_by_index_only_mut(&mut self, idx: CK::Idx) -> Option<(CK, &mut D::Target)>
    where
        D: std::ops::DerefMut,
    {
        let map_id = self.map_id_for_key();
        let (inner_key, reference) = self.inner.get_by_index_only_mut(idx)?;
        let patched = to_castable::<CK, D>(inner_key, map_id, reference);
        Some((patched, reference))
    }

    // ── inner-key access (bypasses map-id check) ────────────────────────

    /// Shared-reference lookup using the inner key directly.
    ///
    /// This bypasses the map-id check — the caller is responsible for
    /// ensuring the key belongs to this map if they desire that
    #[inline]
    pub fn get_by_inner_key(&self, key: CK::InnerKey) -> Option<&D::Target> {
        self.inner.get(key)
    }

    /// Mutable-reference lookup using the inner key directly. It does not do a MapId check
    #[inline]
    pub fn get_mut_by_inner_key(&mut self, key: CK::InnerKey) -> Option<&mut D::Target>
    where
        D: std::ops::DerefMut,
    {
        self.inner.get_mut(key)
    }

    /// Removes an element by inner key. It does not do a MapId check
    #[inline]
    pub fn remove_by_inner_key(&mut self, key: CK::InnerKey) -> Option<D> {
        self.inner.remove(key)
    }

    /// Converts an inner key to a full [`CastKey`] by looking up the stored
    /// value to obtain its pointer metadata.
    ///
    /// Returns `None` if the inner key is stale.
    #[inline]
    pub fn cast_key_of(&self, inner: CK::InnerKey) -> Option<CK> {
        let map_id = self.map_id_for_key();
        let reference: &D::Target = self.inner.get(inner)?;
        Some(to_castable::<CK, D>(inner, map_id, reference))
    }

    // ── retain ──────────────────────────────────────────────────────────

    /// Retains only elements for which `f(key, &mut target)` returns `true`.
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(CK, &mut D::Target) -> bool,
        D: DerefMut,
    {
        let map_id = self.map_id_for_key();
        self.inner.retain(|inner_key, stored| {
            let reference: &D::Target = &**stored;
            let patched = to_castable::<CK, D>(inner_key, map_id, reference);
            f(patched, stored.deref_mut())
        })
    }

    // ── snapshot ────────────────────────────────────────────────────────

    /// Returns a snapshot of all `(key, &target)` pairs.
    #[inline]
    pub fn snapshot(&self) -> Vec<(CK, &D::Target)> {
        let map_id = self.map_id_for_key();
        unsafe {
            let mut vec = Vec::with_capacity(self.inner.len());
            vec.extend(self.inner.iter_unsafe().map(|(inner_key, reference)| {
                (to_castable::<CK, D>(inner_key, map_id, reference), reference)
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
    pub fn snapshot_keys(&self) -> Vec<CK> {
        let map_id = self.map_id_for_key();
        unsafe {
            let mut vec = Vec::with_capacity(self.inner.len());
            vec.extend(
                self.inner
                    .iter_unsafe()
                    .map(|(inner_key, reference)| to_castable::<CK, D>(inner_key, map_id, reference)),
            );
            vec
        }
    }

    // ── iter_unsafe ─────────────────────────────────────────────────────

    /// # Safety
    /// No mutation (including `insert`) may occur while iterating.
    #[inline]
    pub unsafe fn iter_unsafe(&self) -> impl Iterator<Item = (CK, &D::Target)> {
        let map_id = self.map_id_for_key();
        self.inner
            .iter_unsafe()
            .map(move |(inner_key, reference)| {
                (to_castable::<CK, D>(inner_key, map_id, reference), reference)
            })
    }

    // ── iter_mut ────────────────────────────────────────────────────────

    /// Mutable iterator over all occupied elements.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, CK, D> {
        let map_id = self.map_id_for_key();
        IterMut {
            inner: self.inner.iter_mut(),
            map_id,
            _phantom: std::marker::PhantomData,
        }
    }

    // ── drain ───────────────────────────────────────────────────────────

    /// Removes all elements and returns them as an iterator.
    #[inline]
    pub fn drain(&mut self) -> Drain<'_, CK, D> {
        let map_id = self.map_id_for_key();
        Drain {
            inner: self.inner.drain(),
            map_id,
            _phantom: std::marker::PhantomData,
        }
    }
}

// ─── Cross-typed lookups (with map-id validation) ───────────────────────────

impl<CK, D> StableCastMap<CK, D>
where
    D: DerefGenMapPromise,
    CK: CastKey<RefType = <D as std::ops::Deref>::Target>,
{
    /// Shared-reference lookup with a key for a potentially *different* type `T`.
    #[inline]
    pub fn get<T: ?Sized + Pointee>(&self, key: CK::WithRef<T>) -> Option<&T>
    where
        <T as Pointee>::Metadata: Copy,
    {
        if !self.validate_map_id(key.map_id()) {
            return None;
        }
        let base_ref: &D::Target = self.inner.get(key.inner_key())?;
        let data_ptr: *const () = (base_ref as *const D::Target).cast();
        let fat_ptr: *const T = std::ptr::from_raw_parts(data_ptr, key.metadata());
        unsafe { Some(&*fat_ptr) }
    }

    /// Mutable-reference lookup with a potentially differently-typed key.
    #[inline]
    pub fn get_mut<T: ?Sized + Pointee>(&mut self, key: CK::WithRef<T>) -> Option<&mut T>
    where
        <T as Pointee>::Metadata: Copy,
        D: std::ops::DerefMut,
    {
        if !self.validate_map_id(key.map_id()) {
            return None;
        }
        let base_ref: &mut D::Target = self.inner.get_mut(key.inner_key())?;
        let data_ptr: *mut () = (base_ref as *mut D::Target).cast();
        let fat_ptr: *mut T = std::ptr::from_raw_parts_mut(data_ptr, key.metadata());
        unsafe { Some(&mut *fat_ptr) }
    }

    /// Removes an element by cast key.
    #[inline]
    pub fn remove<T: ?Sized + Pointee>(&mut self, key: CK::WithRef<T>) -> Option<D>
    where
        <T as Pointee>::Metadata: Copy,
    {
        if !self.validate_map_id(key.map_id()) {
            return None;
        }
        self.inner.remove(key.inner_key())
    }
}

// ─── Index / IndexMut ───────────────────────────────────────────────────────

impl<CK, D> Index<CK::WithRef<CK::RefType>> for StableCastMap<CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise,
{
    type Output = D::Target;

    fn index(&self, key: CK::WithRef<CK::RefType>) -> &Self::Output {
        self.get(key).unwrap()
    }
}

impl<CK, D> IndexMut<CK::WithRef<CK::RefType>> for StableCastMap<CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise + std::ops::DerefMut,
{
    fn index_mut(&mut self, key: CK::WithRef<CK::RefType>) -> &mut Self::Output {
        self.get_mut(key).unwrap()
    }
}

// ─── IterMut ────────────────────────────────────────────────────────────────

pub struct IterMut<'a, CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise,
{
    inner: gen_map::IterMut<'a, CK::InnerKey, DerefSlot<D, CK::InnerKey>>,
    map_id: MapId,
    _phantom: std::marker::PhantomData<fn() -> CK>,
}

impl<'a, CK, D> Iterator for IterMut<'a, CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise + DerefMut,
{
    type Item = (CK, &'a mut D::Target);

    fn next(&mut self) -> Option<Self::Item> {
        let (inner_key, stored) = self.inner.next()?;
        let patched = to_castable::<CK, D>(inner_key, self.map_id, &**stored);
        Some((patched, stored.deref_mut()))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

// ─── Drain ──────────────────────────────────────────────────────────────────

pub struct Drain<'a, CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise,
{
    inner: gen_map::Drain<'a, CK::InnerKey, DerefSlot<D, CK::InnerKey>>,
    map_id: MapId,
    _phantom: std::marker::PhantomData<fn() -> CK>,
}

impl<'a, CK, D> Iterator for Drain<'a, CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise,
{
    type Item = (CK, D);

    fn next(&mut self) -> Option<Self::Item> {
        let (inner_key, value) = self.inner.next()?;
        let patched = to_castable::<CK, D>(inner_key, self.map_id, &*value);
        Some((patched, value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

// ─── IntoIter (owning) ─────────────────────────────────────────────────────

pub struct IntoIter<CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise,
{
    inner: gen_map::IntoIter<CK::InnerKey, DerefSlot<D, CK::InnerKey>>,
    map_id: MapId,
    _phantom: std::marker::PhantomData<fn() -> CK>,
}

impl<CK, D> Iterator for IntoIter<CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise,
{
    type Item = (CK, D);

    fn next(&mut self) -> Option<Self::Item> {
        let (inner_key, value) = self.inner.next()?;
        let patched = to_castable::<CK, D>(inner_key, self.map_id, &*value);
        Some((patched, value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<CK, D> IntoIterator for StableCastMap<CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise,
{
    type Item = (CK, D);
    type IntoIter = IntoIter<CK, D>;

    fn into_iter(self) -> Self::IntoIter {
        let map_id = self.map_id.ensure_id();
        IntoIter {
            inner: self.inner.into_iter(),
            map_id,
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<'a, CK, D> IntoIterator for &'a mut StableCastMap<CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise + DerefMut,
{
    type Item = (CK, &'a mut D::Target);
    type IntoIter = IterMut<'a, CK, D>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

// ─── Type alias ─────────────────────────────────────────────────────────────

/// Convenience alias: [`StableCastMap`] storing `Box<T>`.
pub type StableBoxCastMap<CK> = StableCastMap<CK, Box<<CK as CastKey>::RefType>>;
