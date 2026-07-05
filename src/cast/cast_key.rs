//! The castable key type for [`UnsafeCastMap`](crate::cast::unsafe_cast_map::UnsafeCastMap)
//! and [`StableCastMap`](crate::cast::stable_cast_map::StableCastMap).
//!
//! [`CastKey<T, K>`] stores `T`'s pointer metadata alongside a generational
//! index. It is the only key type used by both maps: `UnsafeCastMap` exposes it
//! through `unsafe` lookups, while `StableCastMap` makes the same key safe by
//! checking each slot's stored [`TypeId`](std::any::TypeId) before trusting the
//! metadata. There is no separate "stable" key — the safety lives in the map.
//!
//! `CastKey` is not a [`Key`](crate::keys::key::Key); the cast maps convert at
//! the boundary via [`CastKey::inner_key`].
//!
//! # Sizes (64-bit)
//! - `CastKey<SizedType>`: 8 bytes (KeyData only, metadata is `()`)
//! - `CastKey<dyn Trait>`: 16 bytes (KeyData + vtable pointer)

use std::marker::{PhantomData, Unsize};
use std::mem::{transmute_copy};
use std::num::NonZeroUsize;
use std::ops::{CoerceUnsized, DispatchFromDyn, Receiver};
use std::ptr::{NonNull, Pointee};

use crate::keys::key::{DefaultKey, Key, KeyData};
use crate::keys::key_piece::KeyPiece;
// ─── CastKey<T, K> ──────────────────────────────────────────────────────

/// A key parameterized over `T: ?Sized` that stores `T`'s pointer
/// metadata alongside a generational index.
///
/// The index and generation types default to `u32`.
///
/// `K` is the backing key type (defaults to [`DefaultKey`]).
#[repr(C)]
pub struct CastKey<T: ?Sized + Pointee, K: Key = DefaultKey>
where
    <T as Pointee>::Metadata: Copy,
{
    pub(crate) key_data: KeyData<K::Idx, K::Gen>,
    pub(crate) metadata: <T as Pointee>::Metadata,
}





pub struct DispatchableKey<'a, T: ?Sized, K: Key = DefaultKey> {
    ptr: NonNull<T>,            // addr = packed KeyData, metadata = vtable / len / ()
    _borrow: PhantomData<&'a KeyData<K::Idx, K::Gen>>
}

impl<'a, T: ?Sized + Unsize<U>, U: ?Sized, K: Key> CoerceUnsized<DispatchableKey<'a, U, K>> for DispatchableKey<'a, T, K> {}
impl<'a, T: ?Sized + Unsize<U>, U: ?Sized, K: Key> DispatchFromDyn<DispatchableKey<'a, U, K>> for DispatchableKey<'a, T, K> {}
impl<'a, T: ?Sized, K: Key> Receiver for DispatchableKey<'a, T, K> { type Target = T; }

impl<'a, T: ?Sized + Pointee, K: Key> DispatchableKey<'a, T, K>
where T::Metadata: Copy,
{

    #[inline]
    pub fn new(key: &'a CastKey<T, K>) -> Self {
        let thin: NonNull<()> = if const{ can_transmute::<K>()} {
            // no padding + gen is NonZero => all bytes init, value nonzero
            NonNull::without_provenance(unsafe { transmute_copy(&key.key_data) })
        } else  if  const{ fits_inline::<K>() } {
            // gen is NonZero and fully in range => packed != 0
            NonNull::without_provenance(NonZeroUsize::new(pack_inline::<K>(key.key_data)).unwrap())
        } else {
            NonNull::from(&key.key_data).cast()
        };
        Self { ptr: NonNull::from_raw_parts(thin, key.metadata), _borrow: PhantomData }
    }

    #[inline]
    pub fn key(self) -> CastKey<T, K> {
        let (thin, metadata) = self.ptr.to_raw_parts();
        let key_data = if const { can_transmute::<K>() } {
            let addr = thin.addr().get();
            unsafe { transmute_copy::<usize, KeyData<K::Idx, K::Gen>>(&addr) }
        } else if const {fits_inline::<K>()}{
            unpack_inline::<K>(thin.addr().get())
        } else {
            unsafe { thin.cast::<KeyData<K::Idx, K::Gen>>().read() }
        };
        CastKey { key_data, metadata }
    }
}

impl<'a, T: ?Sized + Pointee, K: Key> From<&'a CastKey<T, K>> for DispatchableKey<'a, T, K>
where
    T::Metadata: Copy,
{
    #[inline]
    fn from(key: &'a CastKey<T, K>) -> Self {
        Self::new(key)
    }
}



#[inline]
const fn can_transmute<K: Key>() -> bool {
    size_of::<KeyData<K::Idx, K::Gen>>() == size_of::<usize>()
        && size_of::<K::Idx>() + size_of::<K::Gen>() == size_of::<KeyData<K::Idx, K::Gen>>()
}
#[inline]
const fn fits_inline<K: Key>() -> bool {
    (size_of::<K::Idx>() + size_of::<K::Gen>()) <= size_of::<usize>()
}
#[inline]
fn pack_inline<K: Key>(kd: KeyData<K::Idx, K::Gen>) -> usize {
    let idx_bits = size_of::<K::Idx>() * 8; // <= 56 in the inline case, shift is safe
    kd.index().into_usize() | (kd.generation().into_usize() << idx_bits)
}

#[inline]
fn unpack_inline<K: Key>(v: usize) -> KeyData<K::Idx, K::Gen> {
    let idx_bits = size_of::<K::Idx>() * 8;
    let idx = K::Idx::from_usize(v & ((1usize << idx_bits) - 1));
    let gen = K::Gen::from_usize(v >> idx_bits);
    KeyData {
        idx,
        generation: match gen.try_into() {
            Ok(nz) => nz,
            Err(_) => unreachable!(), // came from a NonZero
        },
    }
}




// ── Manual trait impls ──────────────────────────────────────────────────

impl<T: ?Sized + Pointee, K: Key> Clone for CastKey<T, K>
where
    <T as Pointee>::Metadata: Copy,
{
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized + Pointee, K: Key> Copy for CastKey<T, K> where <T as Pointee>::Metadata: Copy {}

impl<T: ?Sized + Pointee, K: Key> std::fmt::Debug for CastKey<T, K>
where
    <T as Pointee>::Metadata: Copy,
    KeyData<K::Idx, K::Gen>: std::fmt::Debug,
{
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CastKey")
            .field("key_data", &self.key_data)
            .finish()
    }
}

impl<T: ?Sized + Pointee, K: Key> PartialEq for CastKey<T, K>
where
    <T as Pointee>::Metadata: Copy,
    KeyData<K::Idx, K::Gen>: PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.key_data == other.key_data
    }
}

impl<T: ?Sized + Pointee, K: Key> Eq for CastKey<T, K>
where
    <T as Pointee>::Metadata: Copy,
    KeyData<K::Idx, K::Gen>: Eq,
{
}

impl<T: ?Sized + Pointee, K: Key> std::hash::Hash for CastKey<T, K>
where
    <T as Pointee>::Metadata: Copy,
    KeyData<K::Idx, K::Gen>: std::hash::Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.key_data.hash(state);
    }
}

// ── Methods ────────────────────────────────────────────────────────────

impl<T: ?Sized + Pointee, K: Key> CastKey<T, K>
where
    <T as Pointee>::Metadata: Copy,
{
    /// Returns the generational key data.
    #[inline]
    pub fn key_data(&self) -> KeyData<K::Idx, K::Gen> {
        self.key_data
    }

    /// Returns the pointer metadata for `T`.
    #[inline]
    pub fn metadata(&self) -> <T as Pointee>::Metadata {
        self.metadata
    }

    /// Strips pointer metadata, producing the backing [`Key`] used by
    /// the `GenMap`.
    #[inline]
    pub fn inner_key(&self) -> K {
        K::from(self.key_data)
    }

    /// Upcasts the key's metadata from `T` to `U` where `T: Unsize<U>`.
    ///
    /// This enables converting e.g. `CastKey<Dog>` to `CastKey<dyn Any>`
    /// without needing a data pointer.
    #[inline]
    pub fn upcast<U: ?Sized + Pointee>(self) -> CastKey<U, K>
    where
        T: std::marker::Unsize<U>,
        <U as Pointee>::Metadata: Copy,
    {
        let dummy: *const T = std::ptr::from_raw_parts(std::ptr::null::<()>(), self.metadata);
        let upcast: *const U = dummy;
        CastKey {
            key_data: self.key_data,
            metadata: std::ptr::metadata(upcast),
        }
    }

    /// Build a cast key from raw parts.
    ///
    /// # Safety
    /// - `metadata` must be valid for the allocation identified by the key.
    /// - `data`'s generation must be one that a map actually issued for an
    ///   occupied slot (i.e. odd/"live"). `StableCastMap` relies on a generation
    ///   match implying occupancy before it reads a slot's stored type id; a
    ///   forged even generation that collides with a vacant slot would make that
    ///   read unsound.
    #[inline]
    pub unsafe fn from_parts(
        data: KeyData<K::Idx, K::Gen>,
        metadata: <T as Pointee>::Metadata,
    ) -> Self {
        Self {
            key_data: data,
            metadata,
        }
    }
}