use crate::gen_map::GenMap;
use crate::key::Key;
use crate::slot_storage::{SlotData, SlotStorage, SlotStorageClone, SlotStorageMutOutput};
use std::mem::ManuallyDrop;

// ─── BoxedSlot ───────────────────────────────────────────────────────────────

/// Per-slot storage that wraps the payload in a `Box` for pointer stability.
/// The `Box` allocation is **reused** across remove / re-insert cycles.
pub struct BoxedSlot<K: Key, T>(pub(crate) Box<SlotData<T, K>>);

unsafe impl<K: Key, T> SlotStorage for BoxedSlot<K, T> {
    type Key = K;
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
        &self.0.occupied
    }

    #[inline]
    unsafe fn stored_mut(&mut self) -> &mut T {
        &mut self.0.occupied
    }

    #[inline]
    unsafe fn drop_contents(&mut self, is_occupied: bool) {
        if is_occupied {
            ManuallyDrop::drop(&mut self.0.occupied);
        }
        // Vacant variant is `Option<K::Idx>` (Copy); nothing to drop. The `Box`
        // holding the union is freed by `BoxedSlot`'s own drop afterwards.
    }
}

unsafe impl<K: Key, T> SlotStorageMutOutput for BoxedSlot<K, T> {
    #[inline]
    unsafe fn mut_output(&mut self) -> &mut T {
        &mut self.0.occupied
    }
}

unsafe impl<K: Key, T: Clone> SlotStorageClone for BoxedSlot<K, T> {
    // `BoxedSlot` owns its `T`, so cloning an occupied slot runs `T::clone`,
    // which may re-enter the map through `&self` `insert`; the two-phase path
    // is required for soundness.
    const CLONE_MAY_REENTER: bool = true;

    type CloneSnapshot = ();

    #[inline]
    unsafe fn clone_storage(&self, is_occupied: bool) -> Self {
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

    #[inline]
    unsafe fn snapshot_slot(&self) {}

    #[inline]
    unsafe fn clone_occupied_from_output(_snapshot: (), output: &T) -> Self {
        // `Output == Stored == T` for `BoxedSlot`, so cloning the stable `&T`
        // output reproduces the payload without touching the live slot.
        BoxedSlot(Box::new(SlotData {
            occupied: ManuallyDrop::new(output.clone()),
        }))
    }
}

// ─── StableGenMap (type alias) ───────────────────────────────────────────────

/// Generational map where each value is stored behind a `Box` for pointer
/// stability.  The `Box` allocation is **reused** across remove / re-insert
/// cycles, so a `remove` followed by an `insert` into the same slot incurs
/// no heap traffic.
pub type StableGenMap<K, T> = GenMap<BoxedSlot<K, T>>;
