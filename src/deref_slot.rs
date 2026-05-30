use crate::gen_map::GenMap;
use crate::key::Key;
use crate::clone_gen_map_promise::CloneGenMapPromise;
use crate::slot_storage::{SlotData, SlotStorage, SlotStorageClone, SlotStorageMutOutput};
use std::mem::ManuallyDrop;
use std::ops::{Deref, DerefMut};
use std::rc::Rc;
use std::sync::Arc;

// ─── DerefGenMapPromise ──────────────────────────────────────────────────────

/// A promise that the `Deref` (and `DerefMut`, if implemented) implementation
/// does **not** mutate any shared `GenMap` (e.g. via `insert`), and that the
/// deref target pointer is stable (does not move).
///
/// # Safety
/// Violating either promise may cause undefined behaviour.
pub unsafe trait DerefGenMapPromise: Deref {}

unsafe impl<T: ?Sized> DerefGenMapPromise for Box<T> {}
unsafe impl<T: ?Sized> DerefGenMapPromise for Rc<T> {}
unsafe impl<T: ?Sized> DerefGenMapPromise for Arc<T> {}
unsafe impl<T: ?Sized> DerefGenMapPromise for &T {}
unsafe impl<T: ?Sized> DerefGenMapPromise for &mut T {}

// ─── DerefSlot ───────────────────────────────────────────────────────────────

/// Per-slot storage that stores the user-supplied smart pointer (`Box<T>`,
/// `Rc<T>`, `Arc<T>`, …) directly.  The smart pointer itself provides pointer
/// stability; there is no outer `Box`.
pub struct DerefSlot<K: Key, Ptr: DerefGenMapPromise>(pub(crate) SlotData<Ptr, K>);

unsafe impl<K: Key, Ptr: DerefGenMapPromise> SlotStorage for DerefSlot<K, Ptr> {
    type Key = K;
    type Stored = Ptr;
    type Output = Ptr::Target;

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
    unsafe fn write_occupied(&mut self, value: Ptr) {
        self.0.occupied = ManuallyDrop::new(value);
    }

    #[inline]
    unsafe fn take_occupied(&mut self) -> Ptr {
        let old = std::mem::replace(&mut self.0, SlotData { vacant: None });
        ManuallyDrop::into_inner(old.occupied)
    }

    #[inline]
    unsafe fn ref_output(&self) -> &Ptr::Target {
        self.0.occupied.deref().deref()
    }

    #[inline]
    unsafe fn stored_mut(&mut self) -> &mut Ptr {
        &mut self.0.occupied
    }

    #[inline]
    unsafe fn drop_contents(&mut self, is_occupied: bool) {
        if is_occupied {
            ManuallyDrop::drop(&mut self.0.occupied);
        }
        // Vacant variant is `Option<K::Idx>` (Copy); nothing to drop.
    }
}

unsafe impl<K: Key, Ptr: DerefGenMapPromise + DerefMut> SlotStorageMutOutput for DerefSlot<K, Ptr> {
    #[inline]
    unsafe fn mut_output(&mut self) -> &mut Ptr::Target {
        self.0.occupied.deref_mut().deref_mut()
    }
}

unsafe impl<K: Key, Ptr: DerefGenMapPromise + CloneGenMapPromise> SlotStorageClone
    for DerefSlot<K, Ptr>
{
    // # SAFETY: cloning an occupied slot clones the stored pointer. The
    // `CloneGenMapPromise` bound guarantees that clone cannot mutate / re-enter
    // a `GenMap` — unconditionally true for shared pointers (`Rc`/`Arc`/`&T`),
    // a refcount bump / copy; and for an owned `Box<T>` it holds exactly when
    // `T: CloneGenMapPromise`. So the `&self` borrow into the slot buffer stays
    // valid for the call.
    #[inline]
    unsafe fn clone_storage(&self, is_occupied: bool) -> Self {
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

// ─── Type aliases ────────────────────────────────────────────────────────────

/// Generational map that stores user-supplied smart pointers (`Box`, `Rc`,
/// `Arc`, `&T`, …) directly.  The smart pointer provides pointer stability.
pub type StableDerefMap<K, Ptr> = GenMap<DerefSlot<K, Ptr>>;

pub type BoxStableDerefMap<K, T> = StableDerefMap<K, Box<T>>;
