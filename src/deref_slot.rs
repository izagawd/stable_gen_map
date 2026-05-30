use crate::gen_map::GenMap;
use crate::key::Key;
use crate::slot_item::{SlotData, SlotStorage, SlotStorageClone, SlotStorageMutOutput};
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

unsafe impl<K: Key, Ptr: DerefGenMapPromise + SmartPtrCloneable> SlotStorageClone
    for DerefSlot<K, Ptr>
{
    // Owned smart pointers (e.g. `Box<T>`) clone by calling `T::clone`, which
    // may re-enter the map; shared ones (`Rc`/`Arc`/`&T`) only bump a refcount
    // and cannot. The kind comes from `SmartPtrCloneable::KIND`.
    const CLONE_MAY_REENTER: bool = matches!(Ptr::KIND, SmartPtrKind::Owned);

    type CloneSnapshot = ();

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

    #[inline]
    unsafe fn snapshot_slot(&self) {}

    #[inline]
    unsafe fn clone_occupied_from_output(_snapshot: (), output: &Ptr::Target) -> Self {
        // Only reached for `Owned` pointers (`CLONE_MAY_REENTER == true`),
        // where `clone_from_reference` returns `Some`.
        DerefSlot(SlotData {
            occupied: ManuallyDrop::new(Ptr::clone_from_reference(output).unwrap()),
        })
    }
}

// ─── SmartPtrKind / SmartPtrCloneable ────────────────────────────────────────

/// NOTE: SELECTING THE WRONG SMART POINTER KIND FOR A SMART POINTER MAY LEAD TO UNDEFINED BEHAVIOUR.<br><br>
/// EACH SMART POINTER KIND IS DOCUMENTED WITH GUIDELINES TO FOLLOW.<br><br> NOT FOLLOWING THEM MEANS YOU HAVE SELECTED THE WRONG SMART POINTER KIND,
/// WHICH, AS I SAID, MAY LEAD TO UNDEFINED BEHAVIOUR
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum SmartPtrKind {
    /// Meaning the smart pointer owns the type. When the smart pointer is destroyed, so as the type its pointing to. eg `Box`
    Owned,

    /// Meaning the smart pointer is borrowing a reference to the type, or has shared ownership to the type its pointing to.<br>
    /// eg `Rc` `Arc` `Ref`.<br><br>
    /// if the smart pointers is of kind `Shared` and its `Clone` implementation calls the type it is pointing to's `Clone` implementation, you should not be implementing
    /// `SmartPtrCloneable` for the smart pointer at all.<br> If not, there would be a possibility of Undefined Behavior.
    /// <br><br>
    /// If your smart pointer is of kind `Shared` and implements `Clone`, the `Clone` implementation must NOT mutate any shared `Stable Gen Map` (eg with `insert`)
    /// If not, there would be a possibility of Undefined Behavior
    Shared,
}

pub unsafe trait SmartPtrCloneable: DerefGenMapPromise + Clone {
    /// BE VERY CAREFUL WHEN SELECTING THE SMART POINTER KIND TO AVOID POSSIBLE UNDEFINED BEHAVIOR
    const KIND: SmartPtrKind;

    /// NOTE: THIS METHOD MUST BE IMPLEMENTED BY SMART POINTERS WITH KIND `Owned`. IF THE SMART POINTER KIND IS `Shared`, SIMPLY RETURN `None`.
    unsafe fn clone_from_reference(reference: &Self::Target) -> Option<Self>;
}

unsafe impl<T: Clone> SmartPtrCloneable for Box<T> {
    const KIND: SmartPtrKind = SmartPtrKind::Owned;
    unsafe fn clone_from_reference(reference: &T) -> Option<Self> {
        Some(Box::new(reference.clone()))
    }
}
unsafe impl<T: ?Sized> SmartPtrCloneable for &T {
    const KIND: SmartPtrKind = SmartPtrKind::Shared;
    unsafe fn clone_from_reference(_: &T) -> Option<Self> {
        None
    }
}
unsafe impl<T: ?Sized> SmartPtrCloneable for Rc<T> {
    const KIND: SmartPtrKind = SmartPtrKind::Shared;
    unsafe fn clone_from_reference(_: &T) -> Option<Self> {
        None
    }
}
unsafe impl<T: ?Sized> SmartPtrCloneable for Arc<T> {
    const KIND: SmartPtrKind = SmartPtrKind::Shared;
    unsafe fn clone_from_reference(_: &T) -> Option<Self> {
        None
    }
}

// ─── Type aliases ────────────────────────────────────────────────────────────

/// Generational map that stores user-supplied smart pointers (`Box`, `Rc`,
/// `Arc`, `&T`, …) directly.  The smart pointer provides pointer stability.
pub type StableDerefMap<K, Ptr> = GenMap<DerefSlot<K, Ptr>>;

pub type BoxStableDerefMap<K, T> = StableDerefMap<K, Box<T>>;
