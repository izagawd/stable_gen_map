use crate::gen_map::{GenMap, Slot};
use crate::key::{is_occupied_by_generation, Key};
use crate::slot_item::{SlotData, SlotStorage, SlotStorageClone, SlotStorageMutOutput};
use std::cell::UnsafeCell;
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
    unsafe fn drop_occupied(&mut self) {
        ManuallyDrop::drop(&mut self.0.occupied);
    }
}

unsafe impl<K: Key, T> SlotStorageMutOutput for BoxedSlot<K, T> {
    #[inline]
    unsafe fn mut_output(&mut self) -> &mut T {
        &mut self.0.occupied
    }
}

unsafe impl<K: Key, T: Clone> SlotStorageClone for BoxedSlot<K, T> {
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
}

// ─── StableGenMap (type alias) ───────────────────────────────────────────────

/// Generational map where each value is stored behind a `Box` for pointer
/// stability.  The `Box` allocation is **reused** across remove / re-insert
/// cycles, so a `remove` followed by an `insert` into the same slot incurs
/// no heap traffic.
pub type StableGenMap<K, T> = GenMap<BoxedSlot<K, T>>;

// ─── Clone (two-phase snapshot) ──────────────────────────────────────────────
//
// Phase 1: snapshot all &T refs (stable behind Box) without cloning.
// Phase 2: clone each T – this may re-enter the original map via &self,
//          which is safe because we no longer touch self.slots.

impl<K: Key, T: Clone> Clone for StableGenMap<K, T> {
    #[inline]
    fn clone(&self) -> Self {
        unsafe {
            enum Snap<'a, K: Key, T> {
                Occupied(&'a T),
                Vacant(Option<K::Idx>),
            }

            let num_elements = self.len();
            let next_free = self.next_free.get();
            let slots_ref: &Vec<UnsafeCell<Slot<BoxedSlot<K, T>>>> = &*self.slots.get();

            // ── phase 1: snapshot ────────────────────────────────────────
            let mut snapshot: Vec<(K::Gen, Snap<'_, K, T>)> = Vec::with_capacity(slots_ref.len());

            for cell in slots_ref.iter() {
                let slot: &Slot<BoxedSlot<K, T>> = &*cell.get();
                let gen = slot.generation;

                let snap = if is_occupied_by_generation(gen) {
                    Snap::Occupied(slot.storage.ref_output())
                } else {
                    Snap::Vacant(slot.storage.get_vacant())
                };
                snapshot.push((gen, snap));
            }

            // ── phase 2: rebuild ─────────────────────────────────────────
            let mut new_slots: Vec<UnsafeCell<Slot<BoxedSlot<K, T>>>> =
                Vec::with_capacity(snapshot.len());

            for (generation, snap) in snapshot {
                let data = match snap {
                    Snap::Occupied(vref) => SlotData {
                        occupied: ManuallyDrop::new(vref.clone()),
                    },
                    Snap::Vacant(next) => SlotData { vacant: next },
                };

                new_slots.push(UnsafeCell::new(Slot {
                    generation,
                    storage: BoxedSlot(Box::new(data)),
                }));
            }

            GenMap::from_raw_parts(new_slots, next_free, num_elements)
        }
    }
}
