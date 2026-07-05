//! The custom owning box used by [`StableCastMap`](crate::cast::stable_cast_map::StableCastMap).
//!
//! Unlike `Box` / `Rc` / `Arc`, a [`CastBox`] records the **concrete** type id
//! of the value it was built from. That stored id is what makes `StableCastMap`'s
//! keyed lookups safe without a per-map identity: every slot can report the
//! concrete type it actually holds, and a lookup compares that against the type
//! id recovered from the key's metadata.
//!
//! The id is kept in the box handle itself (next to a plain `Box<T>`), not in
//! the heap allocation, so the value's allocation layout is identical to a bare
//! `Box<T>` and re-typing is a straight `Box<O> -> Box<U>`.
//!
//! This is why `StableCastMap` is fixed to type-id-carrying boxes and cannot use
//! `Rc` / `Arc` / `Box`: those carry no type id, so they don't implement
//! [`ConcreteTypeId`]. `CastBox` does; any custom box can too.

use std::any::TypeId;
use std::marker::Unsize;
use std::ops::{CoerceUnsized, Deref, DerefMut};
use std::ptr::Pointee;

use crate::cast::retype_ptr::RetypePtr;
use crate::slots::deref_slot::DerefGenMapPromise;

// ─── CastBox ─────────────────────────────────────────────────────────────────

/// An owning, pointer-stable box that remembers the concrete [`TypeId`] of the
/// value it was constructed from, even after the value is coerced to a trait
/// object.
///
/// The type id is captured by [`CastBox::new`] and stored in the handle; it is
/// preserved across unsizing coercions (`CastBox<Dog> -> CastBox<dyn Animal>`),
/// since unsizing only touches the inner `Box`.
pub struct CastBox<T: ?Sized> {
    type_id: TypeId,
    inner: Box<T>,
}

impl<T: 'static> CastBox<T> {
    /// Boxes `value`, capturing `TypeId::of::<T>()`.
    #[inline]
    pub fn new(value: T) -> Self {
        CastBox {
            type_id: TypeId::of::<T>(),
            inner: Box::new(value),
        }
    }
}

impl<T: ?Sized> Deref for CastBox<T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        &self.inner
    }
}

impl<T: ?Sized> DerefMut for CastBox<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        &mut self.inner
    }
}

// `CastBox<U> -> CastBox<dyn Trait>`: only the `inner: Box<_>` field changes
// type (the `TypeId` field is identical in both), so the single-field
// `CoerceUnsized` rule applies.
impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<CastBox<U>> for CastBox<T> {}

// Box-backed: deref never touches a shared map and the target address is stable.
unsafe impl<T: ?Sized> DerefGenMapPromise for CastBox<T> {}

// Re-type the inner box's tail (used by `remove`) and carry the id across
// unchanged — same operation as the bare `Box<O>` impl.
unsafe impl<'a, O: ?Sized> RetypePtr<'a> for CastBox<O> {
    type Retyped<U: ?Sized + 'a> = CastBox<U>;
    #[inline]
    unsafe fn retype<U: ?Sized>(self, meta: <U as Pointee>::Metadata) -> CastBox<U> {
        let data: *mut () = Box::into_raw(self.inner).cast();
        CastBox {
            type_id: self.type_id,
            inner: Box::from_raw(std::ptr::from_raw_parts_mut(data, meta)),
        }
    }
}

// ─── ConcreteTypeId ──────────────────────────────────────────────────────────

/// A stored value that knows the concrete [`TypeId`] of what it owns.
///
/// This is the extension point for [`StableCastMap`](crate::cast::stable_cast_map::StableCastMap):
/// its checked lookups read it to validate a key's type. The crate implements
/// it for [`CastBox`], but it is deliberately a public, box-level trait — to use
/// your own owning box with `StableCastMap`, implement `ConcreteTypeId` for it
/// (alongside `Deref` + [`DerefGenMapPromise`], which any deref-slot payload
/// needs). Nothing here assumes `CastBox` specifically.
pub trait ConcreteTypeId {
    /// The concrete type id of the value this box owns.
    fn concrete_type_id(&self) -> TypeId;
}

impl<T: ?Sized> ConcreteTypeId for CastBox<T> {
    #[inline]
    fn concrete_type_id(&self) -> TypeId {
        self.type_id
    }
}