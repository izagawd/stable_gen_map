//! Map type that uses a [`CastKey`] as its user-facing key.
//!
//! Internally, a plain [`DefaultMapKey`](crate::cast_key::DefaultMapKey)
//! (which implements [`Key`] with `Extra = MapId`) is used by the `GenMap`.
//! The cast map wrapper converts between the inner key and `CastKey` at
//! every boundary — adding metadata on the way out, stripping it on the
//! way in.
//!
//! This means `GenMap` never sees pointer metadata and no `dangling_metadata`
//! hack is needed.

use std::any::Any;
use std::collections::TryReserveError;
use std::ops::{DerefMut, Index, IndexMut};
use std::ptr::Pointee;

use crate::cast_key::CastKey;
use crate::gen_map;
use crate::stable_deref_map::{DerefGenMapPromise, DerefSlot, SmartPtrCloneable, StableDerefMap};

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

// ─── StableCastMap ───────────────────────────────────────────────────────────

/// A [`StableDerefMap`] wrapper that supports typed lookups via
/// [`CastKey`].
///
/// - `CK`: the castable key family, e.g. `DefaultCastKey<D::Target>`.
/// - `D`: the smart pointer type, e.g. `Box<dyn Any>`.
pub struct StableCastMap<CK, D>
where
    CK: CastKey<RefType = D::Target>,
    D: DerefGenMapPromise,
{
    pub(crate) inner: StableDerefMap<CK::InnerKey, D>,
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
    D: DerefGenMapPromise,
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
    /// Attempts to downcast a `CK` (e.g. `DefaultCastKey<dyn Any>`) to a
    /// concrete-typed key from the same family (e.g. `DefaultCastKey<Dog>`).
    ///
    /// Only one generic parameter is needed — the concrete type. The output
    /// key type is derived automatically via [`CastKey::WithRef`].
    ///
    /// The input `key` must be the map's own key type `CK`, so a
    /// `CustomCastKey<dyn Any>` cannot be passed to a map that uses
    /// `DefaultCastKey<dyn Any>`.
    ///
    /// Returns `None` if the key is stale / wrong map, or the concrete type
    /// doesn't match.
    ///
    /// # Example
    /// ```ignore
    /// let dyn_key: DefaultCastKey<dyn Any> = map.insert(Box::new(dog) as _).0;
    /// if let Some(dog_key) = map.downcast_key::<Dog>(dyn_key) {
    ///     // dog_key: DefaultCastKey<Dog>
    ///     let dog: &Dog = map.get(dog_key).unwrap();
    /// }
    /// ```
    #[inline]
    pub fn downcast_key<Concrete: 'static>(
        &self,
        key: CK::WithRef<dyn Any>,
    ) -> Option<CK::WithRef<Concrete>> {
        let data = self.inner.get(key.inner_key())?;
        let data_as_any: &dyn Any =
            unsafe { &*std::ptr::from_raw_parts(data as *const _ as *const (), key.metadata()) };
        if data_as_any.type_id() == std::any::TypeId::of::<Concrete>() {
            Some(unsafe {
                <CK::WithRef<Concrete> as CastKey>::from_inner_key_and_metadata(key.inner_key(), ())
            })
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

    /// Inserts a smart pointer produced by `func`, which receives the
    /// [`InnerKey`](CastKey::InnerKey) that will identify the inserted
    /// element.
    ///
    /// The closure receives the inner key (without pointer metadata) rather
    /// than a full `CastKey` because the metadata is only available after
    /// the value has been created and its deref target can be inspected.
    /// The full `CastKey` is returned alongside the reference once the
    /// insertion is complete.
    #[inline]
    pub fn insert_with_key(&self, func: impl FnOnce(CK::InnerKey) -> D) -> (CK, &D::Target) {
        let (inner_key, reference) = self.inner.insert_with_key(func);
        (to_castable::<CK, D>(inner_key, reference), reference)
    }

    /// Like [`insert_with_key`](Self::insert_with_key) but the closure may
    /// return `Err`, in which case the slot is released and the error is
    /// propagated.
    #[inline]
    pub fn try_insert_with_key<E>(
        &self,
        func: impl FnOnce(CK::InnerKey) -> Result<D, E>,
    ) -> Result<(CK, &D::Target), E> {
        let (inner_key, reference) = self.inner.try_insert_with_key(func)?;
        Ok((to_castable::<CK, D>(inner_key, reference), reference))
    }

    // ── insert_sized ─────────────────────────────────────────────────────

    /// Inserts a *concrete* smart pointer, returning a key and reference
    /// typed with the concrete `ConcreteD::Target` rather than the map's
    /// erased `D::Target`.
    ///
    /// `ConcreteD` is the un-erased smart pointer (e.g. `Box<Dog>`). It is
    /// coerced to `D` (e.g. `Box<dyn Any>`) internally via `CoerceUnsized`.
    ///
    /// Because `ConcreteD::Target` is `Sized`, the pointer metadata is `()`
    /// and the returned key carries the concrete type information.
    ///
    /// # Example
    /// ```ignore
    /// // map: StableCastMap<DefaultCastKey<dyn Any>, Box<dyn Any>>
    /// let (dog_key, dog_ref) = map.insert_sized(Box::new(dog));
    /// // dog_key: DefaultCastKey<Dog>
    /// // dog_ref: &Dog
    ///
    /// // upcast the key when you need the erased form:
    /// let dyn_key: DefaultCastKey<dyn Any> = dog_key;
    /// ```
    #[inline]
    pub fn insert_sized<ConcreteD>(
        &self,
        value: ConcreteD,
    ) -> (CK::WithRef<ConcreteD::Target>, &ConcreteD::Target)
    where
        ConcreteD: std::ops::CoerceUnsized<D> + std::ops::Deref,
        ConcreteD::Target: Sized,
    {
        let erased: D = value;
        let (inner_key, erased_ref) = self.inner.insert(erased);
        let concrete_ref: &ConcreteD::Target = unsafe {
            &*(erased_ref as *const D::Target as *const () as *const ConcreteD::Target)
        };
        let key = unsafe {
            <CK::WithRef<ConcreteD::Target> as CastKey>::from_inner_key_and_metadata(
                inner_key, (),
            )
        };
        (key, concrete_ref)
    }

    /// Inserts a concrete smart pointer produced by `func`, which receives
    /// the fully-typed [`CastKey`] that will identify the inserted element.
    ///
    /// Unlike [`insert_with_key`](Self::insert_with_key) (which passes the
    /// inner key because the erased metadata is unavailable until after
    /// insertion), this method can pass the complete
    /// `CK::WithRef<ConcreteD::Target>` because sized types have `()`
    /// metadata.
    ///
    /// # Example
    /// ```ignore
    /// let (dog_key, dog_ref) = map.insert_sized_with_key(|key| {
    ///     // key: DefaultCastKey<Dog>
    ///     Box::new(Dog { id: key })
    /// });
    /// ```
    #[inline]
    pub fn insert_sized_with_key<ConcreteD>(
        &self,
        func: impl FnOnce(CK::WithRef<ConcreteD::Target>) -> ConcreteD,
    ) -> (CK::WithRef<ConcreteD::Target>, &ConcreteD::Target)
    where
        ConcreteD: std::ops::CoerceUnsized<D> + std::ops::Deref,
        ConcreteD::Target: Sized,
    {
        let (inner_key, erased_ref) = self.inner.insert_with_key(|inner_key| -> D {
            let typed_key = unsafe {
                <CK::WithRef<ConcreteD::Target> as CastKey>::from_inner_key_and_metadata(
                    inner_key, (),
                )
            };
            let concrete: ConcreteD = func(typed_key);
            concrete
        });
        let concrete_ref: &ConcreteD::Target = unsafe {
            &*(erased_ref as *const D::Target as *const () as *const ConcreteD::Target)
        };
        let key = unsafe {
            <CK::WithRef<ConcreteD::Target> as CastKey>::from_inner_key_and_metadata(
                inner_key, (),
            )
        };
        (key, concrete_ref)
    }

    /// Like [`insert_sized_with_key`](Self::insert_sized_with_key) but the closure
    /// may return `Err`, in which case the slot is released and the error is
    /// propagated.
    #[inline]
    pub fn try_insert_sized_with_key<ConcreteD, E>(
        &self,
        func: impl FnOnce(CK::WithRef<ConcreteD::Target>) -> Result<ConcreteD, E>,
    ) -> Result<(CK::WithRef<ConcreteD::Target>, &ConcreteD::Target), E>
    where
        ConcreteD: std::ops::CoerceUnsized<D> + std::ops::Deref,
        ConcreteD::Target: Sized,
    {
        let (inner_key, erased_ref) =
            self.inner
                .try_insert_with_key(|inner_key| -> Result<D, E> {
                    let typed_key = unsafe {
                        <CK::WithRef<ConcreteD::Target> as CastKey>::from_inner_key_and_metadata(
                            inner_key, (),
                        )
                    };
                    let concrete: ConcreteD = func(typed_key)?;
                    Ok(concrete)
                })?;
        let concrete_ref: &ConcreteD::Target = unsafe {
            &*(erased_ref as *const D::Target as *const () as *const ConcreteD::Target)
        };
        let key = unsafe {
            <CK::WithRef<ConcreteD::Target> as CastKey>::from_inner_key_and_metadata(
                inner_key, (),
            )
        };
        Ok((key, concrete_ref))
    }

    // ── insert_as ─────────────────────────────────────────────────────────

    /// Inserts a smart pointer whose target type differs from the map's
    /// `D::Target`, returning a key and reference typed with the *source*
    /// type.
    ///
    /// Unlike [`insert_sized`](Self::insert_sized), `SourceD::Target` may
    /// be `?Sized` — this is the entry-point for trait-upcasting scenarios
    /// such as inserting `Box<dyn Child>` into a map of `Box<dyn Parent>`.
    ///
    /// The metadata (e.g. the `dyn Child` vtable) is captured *before* the
    /// smart pointer is coerced to `D`, so the returned key and reference
    /// carry the original type information.
    ///
    /// # Example
    /// ```ignore
    /// // map: StableCastMap<DefaultCastKey<dyn Parent>, Box<dyn Parent>>
    /// let child: Box<dyn Child> = Box::new(dog);
    /// let (child_key, child_ref) = map.insert_as(child);
    /// // child_key: DefaultCastKey<dyn Child>
    /// // child_ref: &dyn Child
    ///
    /// // upcast the key when you need the parent form:
    /// let parent_key: DefaultCastKey<dyn Parent> = child_key;
    /// ```
    #[inline]
    pub fn insert_as<SourceD>(
        &self,
        value: SourceD,
    ) -> (CK::WithRef<SourceD::Target>, &SourceD::Target)
    where
        SourceD: std::ops::CoerceUnsized<D> + std::ops::Deref,
        SourceD::Target: Pointee<Metadata: Copy>,
    {
        let metadata = std::ptr::metadata(&*value as *const SourceD::Target);
        let erased: D = value;
        let (inner_key, erased_ref) = self.inner.insert(erased);
        let data_ptr: *const () = (erased_ref as *const D::Target).cast();
        let concrete_ref: &SourceD::Target = unsafe {
            &*std::ptr::from_raw_parts(data_ptr, metadata)
        };
        let key = unsafe {
            <CK::WithRef<SourceD::Target> as CastKey>::from_inner_key_and_metadata(
                inner_key, metadata,
            )
        };
        (key, concrete_ref)
    }

    /// Inserts a smart pointer produced by `func`, returning a key and
    /// reference typed with the source `SourceD::Target`.
    ///
    /// The closure receives the [`InnerKey`](CastKey::InnerKey) rather than
    /// a full `CastKey` because the pointer metadata (e.g. vtable) is only
    /// available after the value is created.
    ///
    /// # Example
    /// ```ignore
    /// let (child_key, child_ref) = map.insert_as_with_key(|inner_key| {
    ///     // inner_key: DefaultMapKey<u32, u32>
    ///     Box::new(Dog { id: inner_key }) as Box<dyn Child>
    /// });
    /// // child_key: DefaultCastKey<dyn Child>
    /// ```
    #[inline]
    pub fn insert_as_with_key<SourceD>(
        &self,
        func: impl FnOnce(CK::InnerKey) -> SourceD,
    ) -> (CK::WithRef<SourceD::Target>, &SourceD::Target)
    where
        SourceD: std::ops::CoerceUnsized<D> + std::ops::Deref,
        SourceD::Target: Pointee<Metadata: Copy>,
    {
        let saved_metadata: std::cell::Cell<
            Option<<SourceD::Target as Pointee>::Metadata>,
        > = std::cell::Cell::new(None);

        let (inner_key, erased_ref) = self.inner.insert_with_key(|inner_key| -> D {
            let concrete: SourceD = func(inner_key);
            saved_metadata.set(Some(std::ptr::metadata(
                &*concrete as *const SourceD::Target,
            )));
            concrete
        });

        let metadata = saved_metadata.get().unwrap();
        let data_ptr: *const () = (erased_ref as *const D::Target).cast();
        let concrete_ref: &SourceD::Target = unsafe {
            &*std::ptr::from_raw_parts(data_ptr, metadata)
        };
        let key = unsafe {
            <CK::WithRef<SourceD::Target> as CastKey>::from_inner_key_and_metadata(
                inner_key, metadata,
            )
        };
        (key, concrete_ref)
    }

    /// Like [`insert_as_with_key`](Self::insert_as_with_key) but the closure
    /// may return `Err`, in which case the slot is released and the error is
    /// propagated.
    #[inline]
    pub fn try_insert_as_with_key<SourceD, E>(
        &self,
        func: impl FnOnce(CK::InnerKey) -> Result<SourceD, E>,
    ) -> Result<(CK::WithRef<SourceD::Target>, &SourceD::Target), E>
    where
        SourceD: std::ops::CoerceUnsized<D> + std::ops::Deref,
        SourceD::Target: Pointee<Metadata: Copy>,
    {
        let saved_metadata: std::cell::Cell<
            Option<<SourceD::Target as Pointee>::Metadata>,
        > = std::cell::Cell::new(None);

        let (inner_key, erased_ref) =
            self.inner
                .try_insert_with_key(|inner_key| -> Result<D, E> {
                    let concrete: SourceD = func(inner_key)?;
                    saved_metadata.set(Some(std::ptr::metadata(
                        &*concrete as *const SourceD::Target,
                    )));
                    Ok(concrete)
                })?;

        let metadata = saved_metadata.get().unwrap();
        let data_ptr: *const () = (erased_ref as *const D::Target).cast();
        let concrete_ref: &SourceD::Target = unsafe {
            &*std::ptr::from_raw_parts(data_ptr, metadata)
        };
        let key = unsafe {
            <CK::WithRef<SourceD::Target> as CastKey>::from_inner_key_and_metadata(
                inner_key, metadata,
            )
        };
        Ok((key, concrete_ref))
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

    /// Converts an inner key to a full [`CastKey`] by looking up the stored
    /// value to obtain its pointer metadata.
    ///
    /// Returns `None` if the inner key is stale or from a different map.
    ///
    /// # Example
    /// ```ignore
    /// let (cast_key, _) = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);
    /// let inner = cast_key.inner_key();
    ///
    /// // Later, reconstruct the full cast key from the inner key:
    /// let recovered: DefaultCastKey<dyn Any> = map.cast_key_of(inner).unwrap();
    /// assert_eq!(recovered, cast_key);
    /// ```
    #[inline]
    pub fn cast_key_of(&self, inner: CK::InnerKey) -> Option<CK> {
        let reference: &D::Target = self.inner.get(inner)?;
        Some(to_castable::<CK, D>(inner, reference))
    }

    // ── retain ──────────────────────────────────────────────────────────

    /// Retains only elements for which `f(key, &mut stored)` returns `true`.
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(CK, &mut D::Target) -> bool,
        D: DerefMut,
    {
        self.inner.retain(|inner_key, mut stored| {
            let reference: &D::Target = &**stored;
            let patched = to_castable::<CK, D>(inner_key, reference);
            f(patched, stored.deref_mut())
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
    D: DerefGenMapPromise,
    CK: CastKey<RefType = <D as std::ops::Deref>::Target>,
{
    /// Shared-reference lookup with a key for a potentially *different* type `T`.
    ///
    /// Looks up the slot via key_data + map_id, gets the data pointer,
    /// then combines it with `key.metadata()` to produce `&T`.
    #[inline]
    pub fn get<T: ?Sized + Pointee>(&self, key: CK::WithRef<T>) -> Option<&T>
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
    pub fn get_mut<T: ?Sized + Pointee>(&mut self, key: CK::WithRef<T>) -> Option<&mut T>
    where
        <T as Pointee>::Metadata: Copy,
        D: std::ops::DerefMut,
    {
        let base_ref: &mut D::Target = self.inner.get_mut(to_inner(&key))?;
        let data_ptr: *mut () = (base_ref as *mut D::Target).cast();
        let fat_ptr: *mut T = std::ptr::from_raw_parts_mut(data_ptr, key.metadata());
        unsafe { Some(&mut *fat_ptr) }
    }

    /// Removes an element
    #[inline]
    pub fn remove<T: ?Sized + Pointee>(&mut self, key: CK::WithRef<T>) -> Option<D>
    where
        <T as Pointee>::Metadata: Copy,
    {
        self.inner.remove(to_inner(&key))
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
    D: DerefGenMapPromise,
    D: DerefMut,
{
    type Item = (CK, &'a mut D::Target);

    fn next(&mut self) -> Option<Self::Item> {
        let (inner_key, mut stored) = self.inner.next()?;
        let patched = to_castable::<CK, D>(inner_key, &**stored);
        Some((patched, stored.deref_mut()))
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
    D: DerefGenMapPromise,
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
    D: DerefGenMapPromise,
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
    D: DerefGenMapPromise,
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
    D: DerefGenMapPromise,
    D: DerefMut,
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
pub type StableBoxCastMap<CK: CastKey> = StableCastMap<CK, Box<CK::RefType>>;
