use crate::key::Key;
use std::mem::ManuallyDrop;
use std::ops::{Deref, DerefMut};

// ─── trait: DerefGenMapPromise ───────────────────────────────────────────────

/// A promise that the `Deref` (and `DerefMut`, if implemented) implementation
/// does **not** mutate any shared `GenMap` (e.g. via `insert`), and that the
/// deref target pointer is stable (does not move).
///
/// # Safety
/// Violating either promise may cause undefined behaviour.
pub unsafe trait DerefGenMapPromise: Deref {}

unsafe impl<T: ?Sized> DerefGenMapPromise for Box<T> {}
unsafe impl<T: ?Sized> DerefGenMapPromise for std::rc::Rc<T> {}
unsafe impl<T: ?Sized> DerefGenMapPromise for std::sync::Arc<T> {}
unsafe impl<'a, T: ?Sized> DerefGenMapPromise for &'a T {}

// ─── trait: SlotItem ─────────────────────────────────────────────────────────

/// Abstracts the per-slot storage strategy.
///
/// * [`BoxedSlot`] – wraps the payload in a `Box` for pointer stability;
///   the `Box` allocation is **reused** across remove / re-insert cycles.
/// * [`DerefSlot`] – stores the user-supplied smart pointer directly; the
///   smart pointer itself provides pointer stability.
///
/// # Safety
/// Implementations must guarantee that references returned by [`ref_output`]
/// survive reallocation of the `Vec` that owns the `Slot`.
pub unsafe trait SlotItem<K: Key>: Sized {
    /// The type inside `ManuallyDrop`.
    /// Also what `insert` accepts and `remove` / `drain` return.
    type Stored;

    /// The type that shared references point to
    /// (`get` / `Index` return `&Self::Output`).
    type Output: ?Sized;

    fn new_vacant(next: Option<K::Idx>) -> Self;

    /// # Safety: slot must be vacant.
    unsafe fn get_vacant(&self) -> Option<K::Idx>;

    /// # Safety: slot must be vacant.
    unsafe fn set_vacant(&mut self, next: Option<K::Idx>);

    /// # Safety: slot must be vacant / reserved (not occupied).
    unsafe fn write_occupied(&mut self, value: Self::Stored);

    /// Takes the value out, leaving the item in a vacant-like state.
    /// # Safety: slot must be occupied.
    unsafe fn take_occupied(&mut self) -> Self::Stored;

    /// # Safety: slot must be occupied.
    unsafe fn ref_output(&self) -> &Self::Output;

    /// Mutable reference to the *stored* value (the `ManuallyDrop` payload).
    /// For `BoxedSlot` this is `&mut T`; for `DerefSlot` this is `&mut D`.
    /// # Safety: slot must be occupied.
    unsafe fn stored_mut(&mut self) -> &mut Self::Stored;

    /// Drop the occupied value in place.
    /// # Safety: slot must be occupied.
    unsafe fn drop_occupied(&mut self);
}

/// Slot items that can provide `&mut Self::Output`.
///
/// [`BoxedSlot`] always implements this (`Output == Stored == T`).
/// [`DerefSlot`] implements it when `D: DerefMut`.
///
/// # Safety
/// Same pointer-stability guarantees as [`SlotItem`].
pub unsafe trait SlotItemMutOutput<K: Key>: SlotItem<K> {
    /// # Safety: slot must be occupied.
    unsafe fn mut_output(&mut self) -> &mut Self::Output;
}

/// Slot items that can be cloned without going through a two-phase snapshot.
///
/// # Safety
/// `clone_item` must correctly reproduce the slot's payload.
pub unsafe trait SlotItemClone<K: Key>: SlotItem<K> {
    /// Clone the slot item.
    /// # Safety: `is_occupied` must truthfully reflect the slot state.
    unsafe fn clone_item(&self, is_occupied: bool) -> Self;
}

// ─── BoxedSlot ───────────────────────────────────────────────────────────────

/// Per-slot storage used by [`StableGenMap`](crate::stable_gen_map::StableGenMap).
///
/// The payload union lives behind a `Box`, which provides pointer stability.
/// On `remove` the `Box` allocation is kept and reused for the next insert
/// into the same slot.
pub struct BoxedSlot<T, K: Key>(pub(crate) Box<SlotData<T, K>>);

/// The underlying union. `S` is the stored payload type.
pub(crate) union SlotData<S, K: Key> {
    pub(crate) occupied: ManuallyDrop<S>,
    pub(crate) vacant: Option<K::Idx>,
}

unsafe impl<T, K: Key> SlotItem<K> for BoxedSlot<T, K> {
    type Stored = T;
    type Output = T;

    #[inline]
    fn new_vacant(next: Option<K::Idx>) -> Self {
        BoxedSlot(Box::new(SlotData { vacant: next }))
    }

    #[inline]
    unsafe fn get_vacant(&self) -> Option<K::Idx> {
        self.0.vacant
    }

    #[inline]
    unsafe fn set_vacant(&mut self, next: Option<K::Idx>) {
        self.0.vacant = next;
    }

    #[inline]
    unsafe fn write_occupied(&mut self, value: T) {
        self.0.occupied = ManuallyDrop::new(value);
    }

    #[inline]
    unsafe fn take_occupied(&mut self) -> T {
        let old = std::mem::replace(&mut *self.0, SlotData { vacant: None });
        ManuallyDrop::into_inner(old.occupied)
    }

    #[inline]
    unsafe fn ref_output(&self) -> &T {
        &*self.0.occupied
    }

    #[inline]
    unsafe fn stored_mut(&mut self) -> &mut T {
        &mut *self.0.occupied
    }

    #[inline]
    unsafe fn drop_occupied(&mut self) {
        ManuallyDrop::drop(&mut self.0.occupied);
    }
}

unsafe impl<T, K: Key> SlotItemMutOutput<K> for BoxedSlot<T, K> {
    #[inline]
    unsafe fn mut_output(&mut self) -> &mut T {
        &mut *self.0.occupied
    }
}

unsafe impl<T: Clone, K: Key> SlotItemClone<K> for BoxedSlot<T, K> {
    #[inline]
    unsafe fn clone_item(&self, is_occupied: bool) -> Self {
        if is_occupied {
            BoxedSlot(Box::new(SlotData {
                occupied: ManuallyDrop::new((*self.0.occupied).clone()),
            }))
        } else {
            BoxedSlot(Box::new(SlotData {
                vacant: self.0.vacant,
            }))
        }
    }
}

// ─── DerefSlot ───────────────────────────────────────────────────────────────

/// Per-slot storage used by
/// [`StableDerefGenMap`](crate::stable_deref_gen_map::StableDerefGenMap).
///
/// The user-supplied smart pointer (`Box<T>`, `Rc<T>`, `Arc<T>`, …) is stored
/// inline.  The smart pointer itself provides pointer stability; there is no
/// outer `Box`.
pub struct DerefSlot<D: DerefGenMapPromise, K: Key>(pub(crate) SlotData<D, K>);

unsafe impl<D: DerefGenMapPromise, K: Key> SlotItem<K> for DerefSlot<D, K> {
    type Stored = D;
    type Output = D::Target;

    #[inline]
    fn new_vacant(next: Option<K::Idx>) -> Self {
        DerefSlot(SlotData { vacant: next })
    }

    #[inline]
    unsafe fn get_vacant(&self) -> Option<K::Idx> {
        self.0.vacant
    }

    #[inline]
    unsafe fn set_vacant(&mut self, next: Option<K::Idx>) {
        self.0.vacant = next;
    }

    #[inline]
    unsafe fn write_occupied(&mut self, value: D) {
        self.0.occupied = ManuallyDrop::new(value);
    }

    #[inline]
    unsafe fn take_occupied(&mut self) -> D {
        let old = std::mem::replace(&mut self.0, SlotData { vacant: None });
        ManuallyDrop::into_inner(old.occupied)
    }

    #[inline]
    unsafe fn ref_output(&self) -> &D::Target {
        self.0.occupied.deref().deref()
    }

    #[inline]
    unsafe fn stored_mut(&mut self) -> &mut D {
        &mut *self.0.occupied
    }

    #[inline]
    unsafe fn drop_occupied(&mut self) {
        ManuallyDrop::drop(&mut self.0.occupied);
    }
}

unsafe impl<D: DerefGenMapPromise + DerefMut, K: Key> SlotItemMutOutput<K>
    for DerefSlot<D, K>
{
    #[inline]
    unsafe fn mut_output(&mut self) -> &mut D::Target {
        self.0.occupied.deref_mut().deref_mut()
    }
}

unsafe impl<D: DerefGenMapPromise + Clone, K: Key> SlotItemClone<K>
    for DerefSlot<D, K>
{
    #[inline]
    unsafe fn clone_item(&self, is_occupied: bool) -> Self {
        if is_occupied {
            DerefSlot(SlotData {
                occupied: self.0.occupied.clone(),
            })
        } else {
            DerefSlot(SlotData {
                vacant: self.0.vacant,
            })
        }
    }
}
