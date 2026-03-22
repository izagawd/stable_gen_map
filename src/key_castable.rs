//! Castable key types whose key is generic over `T: ?Sized`, storing
//! `T`'s pointer metadata directly so a `&T` can be reconstructed from
//! just the key + a data pointer.
//!
//! - `DefaultCastableKey<SizedType>`: 16 bytes on 64-bit (key_data + map_id)
//! - `DefaultCastableKey<dyn Trait>`:  24 bytes on 64-bit (+ vtable pointer)
//!
//! Users can define their own castable key families via
//! [`new_castable_key_type!`].

use std::ptr::Pointee;

use crate::key::{Key, KeyData};
use crate::key_piece::KeyPiece;
use crate::map_id::MapId;

// ─── CastableKey trait ──────────────────────────────────────────────────────

/// A key parameterised over `T: ?Sized` that stores `T`'s pointer metadata.
///
/// Extends [`Key`] (with `Extra = MapId`). The metadata is used alongside
/// a data pointer to reconstruct `&T`.
///
/// # Safety
/// `from_castable_parts` must produce a key whose accessors round-trip
/// correctly. The metadata must correspond to a valid `T` vtable / length.
pub unsafe trait CastableKey<T: ?Sized + Pointee>: Key<Extra = MapId>
where
    <T as Pointee>::Metadata: Copy,
{
    fn metadata(&self) -> <T as Pointee>::Metadata;

    fn from_castable_parts(
        data: KeyData<Self::Idx, Self::Gen>,
        map_id: MapId,
        metadata: <T as Pointee>::Metadata,
    ) -> Self;
}

// ─── DefaultCastableKey<T> ──────────────────────────────────────────────────

/// The default castable key type, using `u32` index and `u32` generation.
#[derive(Debug)]
pub struct DefaultCastableKey<T: ?Sized + Pointee>
where
    <T as Pointee>::Metadata: Copy,
{
    pub(crate) key_data: KeyData<u32, u32>,
    pub(crate) map_id: MapId,
    pub(crate) metadata: <T as Pointee>::Metadata,
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

impl<T: ?Sized + Pointee> PartialEq for DefaultCastableKey<T>
where
    <T as Pointee>::Metadata: Copy + PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.key_data == other.key_data && self.map_id == other.map_id
    }
}

impl<T: ?Sized + Pointee> Eq for DefaultCastableKey<T> where
    <T as Pointee>::Metadata: Copy + Eq
{
}

impl<T: ?Sized + Pointee> std::hash::Hash for DefaultCastableKey<T>
where
    <T as Pointee>::Metadata: Copy + std::hash::Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.key_data.hash(state);
        self.map_id.hash(state);
    }
}

// ── Key impl ────────────────────────────────────────────────────────────────

unsafe impl<T: ?Sized + Pointee> Key for DefaultCastableKey<T>
where
    <T as Pointee>::Metadata: Copy,
{
    type Idx = u32;
    type Gen = u32;
    type Extra = MapId;

    #[inline]
    fn data(&self) -> KeyData<u32, u32> {
        self.key_data
    }

    #[inline]
    fn extra(&self) -> MapId {
        self.map_id
    }

    /// Constructs a key with default metadata.
    ///
    /// GenMap calls this internally for insert/iteration. For dyn trait keys
    /// the metadata will be uninitialized garbage — the map wrapper must
    /// overwrite it with the real vtable before handing the key to the user.
    #[inline]
    fn from_parts(data: KeyData<u32, u32>, extra: MapId) -> Self {
        // SAFETY: this produces a key whose metadata is only valid for sized T
        // (where Metadata = () and Default gives ()). For dyn T the castable
        // map wrapper is responsible for patching the metadata before the key
        // escapes to user code.
        unsafe {
            Self {
                key_data: data,
                map_id: extra,
                metadata: std::mem::zeroed(),
            }
        }
    }
}

// ── CastableKey impl ───────────────────────────────────────────────────────

unsafe impl<T: ?Sized + Pointee> CastableKey<T> for DefaultCastableKey<T>
where
    <T as Pointee>::Metadata: Copy,
{
    #[inline]
    fn metadata(&self) -> <T as Pointee>::Metadata {
        self.metadata
    }

    #[inline]
    fn from_castable_parts(
        data: KeyData<u32, u32>,
        map_id: MapId,
        metadata: <T as Pointee>::Metadata,
    ) -> Self {
        Self {
            key_data: data,
            map_id,
            metadata,
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
        #[derive(Debug)]
        $vis struct $name<T: ?Sized + ::std::ptr::Pointee>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy,
        {
            key_data: $crate::key::KeyData<u32, u32>,
            map_id: $crate::map_id::MapId,
            metadata: <T as ::std::ptr::Pointee>::Metadata,
        }

        $crate::__impl_castable_key!($name, u32, u32);
        $crate::new_castable_key_type!($($rest)*);
    };

    ( $(#[$attr:meta])* $vis:vis struct $name:ident ( $idx:ty , $gen:ty ) ; $($rest:tt)* ) => {
        $(#[$attr])*
        #[derive(Debug)]
        $vis struct $name<T: ?Sized + ::std::ptr::Pointee>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy,
        {
            key_data: $crate::key::KeyData<$idx, $gen>,
            map_id: $crate::map_id::MapId,
            metadata: <T as ::std::ptr::Pointee>::Metadata,
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

        impl<T: ?Sized + ::std::ptr::Pointee> PartialEq for $name<T>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy + PartialEq,
        {
            fn eq(&self, other: &Self) -> bool {
                self.key_data == other.key_data && self.map_id == other.map_id
            }
        }

        impl<T: ?Sized + ::std::ptr::Pointee> Eq for $name<T>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy + Eq,
        {}

        impl<T: ?Sized + ::std::ptr::Pointee> ::std::hash::Hash for $name<T>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy + ::std::hash::Hash,
        {
            fn hash<H: ::std::hash::Hasher>(&self, state: &mut H) {
                self.key_data.hash(state);
                self.map_id.hash(state);
            }
        }

        unsafe impl<T: ?Sized + ::std::ptr::Pointee> $crate::key::Key for $name<T>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy,
        {
            type Idx = $idx;
            type Gen = $gen;
            type Extra = $crate::map_id::MapId;

            #[inline]
            fn data(&self) -> $crate::key::KeyData<$idx, $gen> {
                self.key_data
            }
            #[inline]
            fn extra(&self) -> $crate::map_id::MapId {
                self.map_id
            }
            #[inline]
            fn from_parts(data: $crate::key::KeyData<$idx, $gen>, extra: $crate::map_id::MapId) -> Self {
                unsafe {
                    Self {
                        key_data: data,
                        map_id: extra,
                        metadata: ::std::mem::zeroed(),
                    }
                }
            }
        }

        unsafe impl<T: ?Sized + ::std::ptr::Pointee> $crate::key_castable::CastableKey<T> for $name<T>
        where
            <T as ::std::ptr::Pointee>::Metadata: Copy,
        {
            #[inline]
            fn metadata(&self) -> <T as ::std::ptr::Pointee>::Metadata {
                self.metadata
            }
            #[inline]
            fn from_castable_parts(
                data: $crate::key::KeyData<$idx, $gen>,
                map_id: $crate::map_id::MapId,
                metadata: <T as ::std::ptr::Pointee>::Metadata,
            ) -> Self {
                Self { key_data: data, map_id, metadata }
            }
        }
    };
}
