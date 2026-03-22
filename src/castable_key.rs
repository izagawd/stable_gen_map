//! Castable key types whose key is generic over `T: ?Sized`, storing
//! pointer metadata alongside a map identifier in a single `NonNull<T>`.
//!
//! The data-pointer half of `NonNull<T>` is the map identifier (a non-zero
//! `usize` assigned on first insert). The metadata half is `T`'s pointer
//! metadata (vtable for `dyn Trait`, `()` for sized types).
//!
//! `CastableKey<T>` is **not** a [`Key`](crate::key::Key). The inner
//! `GenMap` uses a plain identified key; the castable map wrapper converts
//! at the boundary.
//!
//! Because `NonNull<T>` implements `CoerceUnsized`, upcasting is implicit:
//!
//! ```ignore
//! let key: DefaultCastableKey<MyStruct> = map.insert(Box::new(val)).0;
//! let key: DefaultCastableKey<dyn Foo>  = key; // implicit coercion
//! ```
//!
//! # Sizes (64-bit)
//! - `DefaultCastableKey<SizedType>`: 16 bytes (KeyData + thin NonNull)
//! - `DefaultCastableKey<dyn Trait>`:  24 bytes (KeyData + fat NonNull)

use std::any::Any;
use std::ptr::Pointee;

use crate::key::KeyData;
use crate::key_piece::KeyPiece;
use crate::map_id::MapId;

// ─── CastableKey trait ──────────────────────────────────────────────────────

/// A key parameterised over `T: ?Sized` that stores `T`'s pointer metadata
/// alongside a map identifier and generational index.
///
/// This trait is **not** a supertrait of [`Key`](crate::key::Key). The
/// castable map wrapper handles conversion between `CastableKey<T>` and
/// the inner `Key` used by `GenMap`.
///
/// # Safety
/// `from_castable_parts` must produce a key whose accessors round-trip
/// correctly.
pub unsafe trait CastableKey<T: ?Sized + Pointee>: Copy
where
    <T as Pointee>::Metadata: Copy,
{
    type Idx: KeyPiece;
    type Gen: KeyPiece;

    fn key_data(&self) -> KeyData<Self::Idx, Self::Gen>;
    fn map_id(&self) -> MapId;
    fn metadata(&self) -> <T as Pointee>::Metadata;

    fn from_castable_parts(
        data: KeyData<Self::Idx, Self::Gen>,
        map_id: MapId,
        metadata: <T as Pointee>::Metadata,
    ) -> Self;
}

// ─── DefaultCastableKey<T> ──────────────────────────────────────────────────

/// The default castable key type, using `u32` index and `u32` generation.
///
/// The `map_id_and_metadata` field packs:
/// - The map identifier into the data-pointer half of `NonNull<T>`
/// - The pointer metadata (vtable / `()`) into the metadata half
///
/// Supports implicit upcasting via `CoerceUnsized`.
pub struct DefaultCastableKey<T: ?Sized + Pointee>
where
    <T as Pointee>::Metadata: Copy,
{
    pub(crate) key_data: KeyData<u32, u32>,
    pub(crate) map_id_and_metadata: std::ptr::NonNull<T>,
}

// ── CoerceUnsized ──────────────────────────────────────────────────────────

impl<T, U> std::ops::CoerceUnsized<DefaultCastableKey<U>> for DefaultCastableKey<T>
where
    T: ?Sized + Pointee + std::marker::Unsize<U>,
    U: ?Sized + Pointee,
    <T as Pointee>::Metadata: Copy,
    <U as Pointee>::Metadata: Copy,
{
}

// ── Manual trait impls ──────────────────────────────────────────────────────

impl<T: ?Sized + Pointee> Clone for DefaultCastableKey<T>
where
    <T as Pointee>::Metadata: Copy,
{
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized + Pointee> Copy for DefaultCastableKey<T> where <T as Pointee>::Metadata: Copy {}

impl<T: ?Sized + Pointee> std::fmt::Debug for DefaultCastableKey<T>
where
    <T as Pointee>::Metadata: Copy,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DefaultCastableKey")
            .field("key_data", &self.key_data)
            .field("map_id", &self.map_id().0)
            .finish()
    }
}

impl<T: ?Sized + Pointee> PartialEq for DefaultCastableKey<T>
where
    <T as Pointee>::Metadata: Copy,
{
    fn eq(&self, other: &Self) -> bool {
        self.key_data == other.key_data
            && self.map_id_and_metadata.as_ptr() as *const () as usize
            == other.map_id_and_metadata.as_ptr() as *const () as usize
    }
}

impl<T: ?Sized + Pointee> Eq for DefaultCastableKey<T> where <T as Pointee>::Metadata: Copy {}

impl<T: ?Sized + Pointee> std::hash::Hash for DefaultCastableKey<T>
where
    <T as Pointee>::Metadata: Copy,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.key_data.hash(state);
        (self.map_id_and_metadata.as_ptr() as *const () as usize).hash(state);
    }
}

// ── CastableKey impl ───────────────────────────────────────────────────────

unsafe impl<T: ?Sized + Pointee> CastableKey<T> for DefaultCastableKey<T>
where
    <T as Pointee>::Metadata: Copy,
{
    type Idx = u32;
    type Gen = u32;

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
    fn from_castable_parts(
        data: KeyData<u32, u32>,
        map_id: MapId,
        metadata: <T as Pointee>::Metadata,
    ) -> Self {
        unsafe {
            debug_assert!(map_id.0 != 0, "cannot construct castable key with null map id");
            let raw: *mut T =
                std::ptr::from_raw_parts_mut(map_id.0 as *mut (), metadata);
            Self {
                key_data: data,
                map_id_and_metadata: std::ptr::NonNull::new_unchecked(raw),
            }
        }
    }
}

// ─── downcast_key ───────────────────────────────────────────────────────────

/// Attempts to downcast a `CastableKey<dyn Any>` to a `CastableKey<Concrete>`.
///
/// Checks the `TypeId` stored in the `dyn Any` vtable at runtime. Returns
/// `None` if the concrete type doesn't match.
///
/// # Example
/// ```ignore
/// let dyn_key: DefaultCastableKey<dyn Any> = key;
/// if let Some(concrete) = downcast_key::<MyStruct, _, DefaultCastableKey<MyStruct>>(dyn_key) {
///     // concrete: DefaultCastableKey<MyStruct>
/// }
/// ```
#[inline]
pub fn downcast_key<Concrete: 'static, KIn, KOut>(key: KIn) -> Option<KOut>
where
    KIn: CastableKey<dyn Any>,
    KOut: CastableKey<Concrete, Idx = KIn::Idx, Gen = KIn::Gen>,
{
    let metadata = key.metadata();
    unsafe {
        let gotten: &dyn Any = &*std::ptr::from_raw_parts(&(), metadata);
        if gotten.type_id() == std::any::TypeId::of::<Concrete>() {
            Some(KOut::from_castable_parts(key.key_data(), key.map_id(), ()))
        } else {
            None
        }
    }
}

// ─── Macro for custom castable key types ────────────────────────────────────

/// Create a custom castable-key family with the chosen index/generation types.
///
/// # Examples
/// ```ignore
/// use stable_gen_map::new_castable_key_type;
///
/// new_castable_key_type! {
///     pub struct EntityKey;
/// }
///
/// new_castable_key_type! {
///     pub struct SmallEntityKey(u16, u16);
/// }
/// ```
#[macro_export]
macro_rules! new_castable_key_type {
    ( $(#[$attr:meta])* $vis:vis struct $name:ident ; $($rest:tt)* ) => {
        $(#[$attr])*
        $vis struct $name<T: ?Sized + ::std::ptr::Pointee>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy,
        {
            key_data: $crate::key::KeyData<u32, u32>,
            map_id_and_metadata: ::std::ptr::NonNull<T>,
        }

        $crate::__impl_castable_key!($name, u32, u32);
        $crate::new_castable_key_type!($($rest)*);
    };

    ( $(#[$attr:meta])* $vis:vis struct $name:ident ( $idx:ty , $gen:ty ) ; $($rest:tt)* ) => {
        $(#[$attr])*
        $vis struct $name<T: ?Sized + ::std::ptr::Pointee>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy,
        {
            key_data: $crate::key::KeyData<$idx, $gen>,
            map_id_and_metadata: ::std::ptr::NonNull<T>,
        }

        $crate::__impl_castable_key!($name, $idx, $gen);
        $crate::new_castable_key_type!($($rest)*);
    };

    () => {};
}

#[macro_export]
#[doc(hidden)]
macro_rules! __impl_castable_key {
    ($name:ident, $idx:ty, $gen:ty) => {
        impl<T, U> ::std::ops::CoerceUnsized<$name<U>> for $name<T>
        where
            T: ?Sized + ::std::ptr::Pointee + ::std::marker::Unsize<U>,
            U: ?Sized + ::std::ptr::Pointee,
            <T as ::std::ptr::Pointee>::Metadata: Copy,
            <U as ::std::ptr::Pointee>::Metadata: Copy,
        {}

        impl<T: ?Sized + ::std::ptr::Pointee> Clone for $name<T>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy,
        {
            #[inline]
            fn clone(&self) -> Self { *self }
        }

        impl<T: ?Sized + ::std::ptr::Pointee> Copy for $name<T>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy,
        {}

        impl<T: ?Sized + ::std::ptr::Pointee> ::std::fmt::Debug for $name<T>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy,
        {
            fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                use $crate::castable_key::CastableKey;
                f.debug_struct(stringify!($name))
                    .field("key_data", &self.key_data)
                    .field("map_id", &self.map_id().0)
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

        impl<T: ?Sized + ::std::ptr::Pointee> Eq for $name<T>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy,
        {}

        impl<T: ?Sized + ::std::ptr::Pointee> ::std::hash::Hash for $name<T>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy,
        {
            fn hash<H: ::std::hash::Hasher>(&self, state: &mut H) {
                self.key_data.hash(state);
                (self.map_id_and_metadata.as_ptr() as *const () as usize).hash(state);
            }
        }

        unsafe impl<T: ?Sized + ::std::ptr::Pointee> $crate::castable_key::CastableKey<T>
            for $name<T>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy,
        {
            type Idx = $idx;
            type Gen = $gen;

            #[inline]
            fn key_data(&self) -> $crate::key::KeyData<$idx, $gen> {
                self.key_data
            }

            #[inline]
            fn map_id(&self) -> $crate::map_id::MapId {
                $crate::map_id::MapId(self.map_id_and_metadata.as_ptr() as *const () as usize)
            }

            #[inline]
            fn metadata(&self) -> <T as ::std::ptr::Pointee>::Metadata {
                ::std::ptr::metadata(self.map_id_and_metadata.as_ptr() as *const T)
            }

            #[inline]
            fn from_castable_parts(
                data: $crate::key::KeyData<$idx, $gen>,
                map_id: $crate::map_id::MapId,
                metadata: <T as ::std::ptr::Pointee>::Metadata,
            ) -> Self {
                unsafe {
                    debug_assert!(map_id.0 != 0, "cannot construct castable key with null map id");
                    let raw: *mut T = ::std::ptr::from_raw_parts_mut(
                        map_id.0 as *mut (),
                        metadata,
                    );
                    Self {
                        key_data: data,
                        map_id_and_metadata: ::std::ptr::NonNull::new_unchecked(raw),
                    }
                }
            }
        }
    };
}