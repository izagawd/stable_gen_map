//! Castable key types whose key is generic over `T: ?Sized`, storing
//! pointer metadata alongside a map identifier in a single `NonNull<T>`.
//!
//! The data-pointer half of `NonNull<T>` is the map identifier (a non-zero
//! `usize` assigned on first insert). The metadata half is `T`'s pointer
//! metadata (vtable for `dyn Trait`, `()` for sized types).
//!
//! `CastKey` is **not** a [`Key`](crate::key::Key). The inner
//! `GenMap` uses a plain identified key; the castable map wrapper converts
//! at the boundary.
//!
//! Because `NonNull<T>` implements `CoerceUnsized`, upcasting is implicit:
//!
//! ```ignore
//! let key: DefaultCastKey<MyStruct> = map.insert(Box::new(val)).0;
//! let key: DefaultCastKey<dyn Foo>  = key; // implicit coercion
//! ```
//!
//! # Sizes (64-bit)
//! - `DefaultCastKey<SizedType>`: 16 bytes (KeyData + thin NonNull)
//! - `DefaultCastKey<dyn Trait>`:  24 bytes (KeyData + fat NonNull)

use std::ptr::Pointee;

use crate::key::{Key, KeyData};
use crate::key_piece::KeyPiece;
use crate::map_id::MapId;

// ─── CastKey trait ──────────────────────────────────────────────────────

/// A key parameterised over `RefType: ?Sized` that stores `RefType`'s pointer metadata
/// alongside a map identifier and generational index.
///
/// This trait is **not** a supertrait of [`Key`](crate::key::Key). The
/// castable map wrapper handles conversion between `CastKey` and
/// the inner `Key` used by `GenMap`.
///
/// # Safety
/// `from_castable_parts` must produce a key whose accessors round-trip
/// correctly.
pub unsafe trait CastKey: Copy {
    type RefType: ?Sized + Pointee<Metadata: Copy>;
    type Idx: KeyPiece;
    type Gen: KeyPiece;

    /// The key type used by the inner `GenMap`, without pointer metadata.
    /// This is "the castable key minus the `RefType` metadata".
    type InnerKey: Key<Idx = Self::Idx, Gen = Self::Gen>;

    /// The same key family re-parameterized over a different (sized) `RefType`.
    ///
    /// For `DefaultCastKey<T>`, `WithRef<U> = DefaultCastKey<U>`.
    /// This is used by [`StableCastMap::downcast_key`] so that only one
    /// generic parameter (the concrete type) is needed, and the output key
    /// type is derived automatically from the map's own key family.
    type WithRef<U: ?Sized>: CastKey<
        RefType = U,
        Idx = Self::Idx,
        Gen = Self::Gen,
        InnerKey = Self::InnerKey,
    >;

    fn key_data(&self) -> KeyData<Self::Idx, Self::Gen>;
    fn map_id(&self) -> MapId;
    fn metadata(&self) -> <Self::RefType as Pointee>::Metadata;

    /// Strip pointer metadata, producing the inner key used by the backing
    /// `GenMap`.
    fn inner_key(&self) -> Self::InnerKey;

    /// # Safety
    /// The provided `MapId`'s inner `usize` value must NOT be zero, or else UB may occur, since most CastKeys internally use NonNull ptrs (which can never be zero) to store the `MapId`s.<br><br>
    /// `NonNull` ptrs are used because that is what enables the keys to upcast their metadata implicitly
    unsafe fn from_castable_parts(
        data: KeyData<Self::Idx, Self::Gen>,
        map_id: MapId,
        metadata: <Self::RefType as Pointee>::Metadata,
    ) -> Self;

    /// Build a castable key from an inner key and pointer metadata.
    unsafe fn from_inner_key_and_metadata(
        inner: Self::InnerKey,
        metadata: <Self::RefType as Pointee>::Metadata,
    ) -> Self;
}

// ─── DefaultMapKey ───────────────────────────────────────────────────────────
//
// The key type GenMap actually stores. No metadata, just key_data + map_id.
// This is the default `InnerKey` for cast key types.

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct DefaultMapKey<Idx, Gen> {
    pub(crate) key_data: KeyData<Idx, Gen>,
    pub(crate) map_id: MapId,
}

unsafe impl<Idx: Copy + KeyPiece, Gen: Copy + KeyPiece> Key for DefaultMapKey<Idx, Gen> {
    type Idx = Idx;
    type Gen = Gen;
    type Extra = MapId;

    #[inline]
    fn data(&self) -> KeyData<Idx, Gen> {
        self.key_data
    }

    #[inline]
    fn extra(&self) -> MapId {
        self.map_id
    }

    #[inline]
    fn from_parts(data: KeyData<Idx, Gen>, extra: MapId) -> Self {
        Self {
            key_data: data,
            map_id: extra,
        }
    }
}

// ─── DefaultCastKey<T> ──────────────────────────────────────────────────

/// The default castable key type, using `u32` index and `u32` generation.
///
/// The `map_id_and_metadata` field packs:
/// - The map identifier into the data-pointer half of `NonNull<T>`
/// - The pointer metadata (vtable / `()`) into the metadata half
///
/// Supports implicit upcasting via `CoerceUnsized`.
pub struct DefaultCastKey<T: ?Sized + Pointee>
where
    <T as Pointee>::Metadata: Copy,
{
    pub(crate) key_data: KeyData<u32, u32>,
    pub(crate) map_id_and_metadata: std::ptr::NonNull<T>,
}

// ── CoerceUnsized ──────────────────────────────────────────────────────────

impl<T, U> std::ops::CoerceUnsized<DefaultCastKey<U>> for DefaultCastKey<T>
where
    T: ?Sized + Pointee + std::marker::Unsize<U>,
    U: ?Sized + Pointee,
    <T as Pointee>::Metadata: Copy,
    <U as Pointee>::Metadata: Copy,
{
}

// ── Manual trait impls ──────────────────────────────────────────────────────

impl<T: ?Sized + Pointee> Clone for DefaultCastKey<T>
where
    <T as Pointee>::Metadata: Copy,
{
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized + Pointee> Copy for DefaultCastKey<T> where <T as Pointee>::Metadata: Copy {}

impl<T: ?Sized + Pointee> std::fmt::Debug for DefaultCastKey<T>
where
    <T as Pointee>::Metadata: Copy,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DefaultCastKey")
            .field("key_data", &self.key_data)
            .field("map_id", &self.map_id())
            .finish()
    }
}

impl<T: ?Sized + Pointee> PartialEq for DefaultCastKey<T>
where
    <T as Pointee>::Metadata: Copy,
{
    fn eq(&self, other: &Self) -> bool {
        self.key_data == other.key_data
            && self.map_id_and_metadata.as_ptr() as *const () as usize
                == other.map_id_and_metadata.as_ptr() as *const () as usize
    }
}

impl<T: ?Sized + Pointee> Eq for DefaultCastKey<T> where <T as Pointee>::Metadata: Copy {}

impl<T: ?Sized + Pointee> std::hash::Hash for DefaultCastKey<T>
where
    <T as Pointee>::Metadata: Copy,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.key_data.hash(state);
        (self.map_id_and_metadata.as_ptr() as *const () as usize).hash(state);
    }
}

// ── CastKey impl ───────────────────────────────────────────────────────

unsafe impl<T: ?Sized + Pointee> CastKey for DefaultCastKey<T>
where
    <T as Pointee>::Metadata: Copy,
{
    type RefType = T;
    type Idx = u32;
    type Gen = u32;
    type InnerKey = DefaultMapKey<u32, u32>;
    type WithRef<U: ?Sized> = DefaultCastKey<U>;

    #[inline]
    fn key_data(&self) -> KeyData<u32, u32> {
        self.key_data
    }

    #[inline]
    fn map_id(&self) -> MapId {
        MapId(self.map_id_and_metadata.as_ptr() as *const () as usize)
    }

    #[inline]
    fn metadata(&self) -> <T as Pointee>::Metadata {
        std::ptr::metadata(self.map_id_and_metadata.as_ptr() as *const T)
    }

    #[inline]
    fn inner_key(&self) -> DefaultMapKey<u32, u32> {
        DefaultMapKey {
            key_data: self.key_data,
            map_id: self.map_id(),
        }
    }

    #[inline]
    unsafe fn from_castable_parts(
        data: KeyData<u32, u32>,
        map_id: MapId,
        metadata: <T as Pointee>::Metadata,
    ) -> Self {
        unsafe {
            debug_assert!(
                map_id.0 != 0,
                "cannot construct castable key with null map id"
            );
            let raw: *mut T = std::ptr::from_raw_parts_mut(map_id.0 as *mut (), metadata);
            Self {
                key_data: data,
                map_id_and_metadata: std::ptr::NonNull::new_unchecked(raw),
            }
        }
    }

    #[inline]
    unsafe fn from_inner_key_and_metadata(
        inner: DefaultMapKey<u32, u32>,
        metadata: <T as Pointee>::Metadata,
    ) -> Self {
        unsafe { Self::from_castable_parts(inner.data(), inner.extra(), metadata) }
    }
}

// ─── Macro for custom castable key types ────────────────────────────────────

/// Create a custom castable-key family with the chosen index/generation types.
///
/// # Examples
/// ```ignore
/// use stable_gen_map::new_castable_key_type;
///
/// // Default (u32/u32, DefaultMapKey inner key):
/// new_castable_key_type! {
///     pub struct EntityKey;
/// }
///
/// // Custom index/generation sizes:
/// new_castable_key_type! {
///     pub struct SmallEntityKey(u16, u16);
/// }
///
/// // Custom inner key type (must impl Key<Idx=u32, Gen=u32, Extra=MapId>):
/// new_castable_key_type! {
///     pub struct EntityKey inner_key MyInnerKey;
/// }
///
/// // Custom index/generation + custom inner key:
/// new_castable_key_type! {
///     pub struct SmallEntityKey(u16, u16) inner_key MySmallInnerKey;
/// }
/// ```
#[macro_export]
macro_rules! new_castable_key_type {
    // ── default idx/gen, default inner key ──────────────────────────────
    ( $(#[$attr:meta])* $vis:vis struct $name:ident ; $($rest:tt)* ) => {
        $(#[$attr])*
        $vis struct $name<T: ?Sized + ::std::ptr::Pointee>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy,
        {
            key_data: $crate::key::KeyData<u32, u32>,
            map_id_and_metadata: ::std::ptr::NonNull<T>,
        }

        $crate::__impl_castable_key!($name, u32, u32, $crate::cast_key::DefaultMapKey<u32, u32>);
        $crate::new_castable_key_type!($($rest)*);
    };

    // ── custom idx/gen, default inner key ───────────────────────────────
    ( $(#[$attr:meta])* $vis:vis struct $name:ident ( $idx:ty , $gen:ty ) ; $($rest:tt)* ) => {
        $(#[$attr])*
        $vis struct $name<T: ?Sized + ::std::ptr::Pointee>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy,
        {
            key_data: $crate::key::KeyData<$idx, $gen>,
            map_id_and_metadata: ::std::ptr::NonNull<T>,
        }

        $crate::__impl_castable_key!($name, $idx, $gen, $crate::cast_key::DefaultMapKey<$idx, $gen>);
        $crate::new_castable_key_type!($($rest)*);
    };

    // ── default idx/gen, custom inner key ───────────────────────────────
    ( $(#[$attr:meta])* $vis:vis struct $name:ident inner_key $inner:ty ; $($rest:tt)* ) => {
        $(#[$attr])*
        $vis struct $name<T: ?Sized + ::std::ptr::Pointee>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy,
        {
            key_data: $crate::key::KeyData<u32, u32>,
            map_id_and_metadata: ::std::ptr::NonNull<T>,
        }

        $crate::__impl_castable_key!($name, u32, u32, $inner);
        $crate::new_castable_key_type!($($rest)*);
    };

    // ── custom idx/gen, custom inner key ────────────────────────────────
    ( $(#[$attr:meta])* $vis:vis struct $name:ident ( $idx:ty , $gen:ty ) inner_key $inner:ty ; $($rest:tt)* ) => {
        $(#[$attr])*
        $vis struct $name<T: ?Sized + ::std::ptr::Pointee>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy,
        {
            key_data: $crate::key::KeyData<$idx, $gen>,
            map_id_and_metadata: ::std::ptr::NonNull<T>,
        }

        $crate::__impl_castable_key!($name, $idx, $gen, $inner);
        $crate::new_castable_key_type!($($rest)*);
    };

    () => {};
}

#[macro_export]
#[doc(hidden)]
macro_rules! __impl_castable_key {
    ($name:ident, $idx:ty, $gen:ty, $inner_key:ty) => {
        impl<T, U> ::std::ops::CoerceUnsized<$name<U>> for $name<T>
        where
            T: ?Sized + ::std::ptr::Pointee + ::std::marker::Unsize<U>,
            U: ?Sized + ::std::ptr::Pointee,
            <T as ::std::ptr::Pointee>::Metadata: Copy,
            <U as ::std::ptr::Pointee>::Metadata: Copy,
        {
        }

        impl<T: ?Sized + ::std::ptr::Pointee> Clone for $name<T>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy,
        {
            #[inline]
            fn clone(&self) -> Self {
                *self
            }
        }

        impl<T: ?Sized + ::std::ptr::Pointee> Copy for $name<T> where
            <T as ::std::ptr::Pointee>::Metadata: Copy
        {
        }

        impl<T: ?Sized + ::std::ptr::Pointee> ::std::fmt::Debug for $name<T>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy,
        {
            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                use $crate::cast_key::CastKey;
                f.debug_struct(stringify!($name))
                    .field("key_data", &self.key_data)
                    .field("map_id", &self.map_id())
                    .finish()
            }
        }

        impl<T: ?Sized + ::std::ptr::Pointee> PartialEq for $name<T>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy,
        {
            fn eq(&self, other: &Self) -> bool {
                self.key_data == other.key_data
                    && self.map_id_and_metadata.as_ptr() as *const () as usize
                        == other.map_id_and_metadata.as_ptr() as *const () as usize
            }
        }

        impl<T: ?Sized + ::std::ptr::Pointee> Eq for $name<T> where
            <T as ::std::ptr::Pointee>::Metadata: Copy
        {
        }

        impl<T: ?Sized + ::std::ptr::Pointee> ::std::hash::Hash for $name<T>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy,
        {
            fn hash<H: ::std::hash::Hasher>(&self, state: &mut H) {
                self.key_data.hash(state);
                (self.map_id_and_metadata.as_ptr() as *const () as usize).hash(state);
            }
        }

        unsafe impl<T: ?Sized + ::std::ptr::Pointee> $crate::cast_key::CastKey for $name<T>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy,
        {
            type RefType = T;
            type Idx = $idx;
            type Gen = $gen;
            type InnerKey = $inner_key;
            type WithRef<U: ?Sized> = $name<U>;

            #[inline]
            fn key_data(&self) -> $crate::key::KeyData<$idx, $gen> {
                self.key_data
            }

            #[inline]
            fn map_id(&self) -> $crate::map_id::MapId {
                unsafe {
                    $crate::map_id::MapId::from_usize(
                        self.map_id_and_metadata.as_ptr() as *const () as usize,
                    )
                }
            }

            #[inline]
            fn metadata(&self) -> <T as ::std::ptr::Pointee>::Metadata {
                ::std::ptr::metadata(self.map_id_and_metadata.as_ptr() as *const T)
            }

            #[inline]
            fn inner_key(&self) -> $inner_key {
                use $crate::cast_key::CastKey;
                use $crate::key::Key;
                <$inner_key as Key>::from_parts(self.key_data(), self.map_id())
            }

            #[inline]
            unsafe fn from_castable_parts(
                data: $crate::key::KeyData<$idx, $gen>,
                map_id: $crate::map_id::MapId,
                metadata: <T as ::std::ptr::Pointee>::Metadata,
            ) -> Self {
                unsafe {
                    debug_assert!(
                        map_id.get_underlying_usize() != 0,
                        "cannot construct castable key with null map id"
                    );
                    let raw: *mut T = ::std::ptr::from_raw_parts_mut(
                        map_id.get_underlying_usize() as *mut (),
                        metadata,
                    );
                    Self {
                        key_data: data,
                        map_id_and_metadata: ::std::ptr::NonNull::new_unchecked(raw),
                    }
                }
            }

            #[inline]
            unsafe fn from_inner_key_and_metadata(
                inner: $inner_key,
                metadata: <T as ::std::ptr::Pointee>::Metadata,
            ) -> Self {
                use $crate::key::Key;
                unsafe { Self::from_castable_parts(inner.data(), inner.extra(), metadata) }
            }
        }
    };
}
