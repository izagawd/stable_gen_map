use crate::gen_map::{GenMap, Slot};
use crate::key::{is_occupied_by_generation, Key};
use crate::slot_item::{SlotData, SlotItem, SlotItemClone, SlotItemMutOutput};
use std::cell::UnsafeCell;
use std::mem::ManuallyDrop;

// ─── BoxedSlot ───────────────────────────────────────────────────────────────

/// Per-slot storage that wraps the payload in a `Box` for pointer stability.
/// The `Box` allocation is **reused** across remove / re-insert cycles.
pub struct BoxedSlot<T, K: Key>(pub(crate) Box<SlotData<T, K>>);

unsafe impl<T, K: Key> SlotItem<K> for BoxedSlot<T, K> {
    type Stored = T;
    type Output = T;

    #[inline]
    fn new_vacant(next: Option<K::Idx>) -> Self {
        BoxedSlot(Box::new(SlotData::new_vacant(next)))
    }

    #[inline]
    unsafe fn get_vacant(&self) -> Option<K::Idx> {
        self.0.get_vacant()
    }

    #[inline]
    unsafe fn set_vacant(&mut self, next: Option<K::Idx>) {
        self.0.set_vacant(next);
    }

    #[inline]
    unsafe fn write_occupied(&mut self, value: T) {
        self.0.write_occupied(value);
    }

    #[inline]
    unsafe fn take_occupied(&mut self) -> T {
        self.0.take_occupied()
    }

    #[inline]
    unsafe fn ref_output(&self) -> &T {
        self.0.ref_occupied()
    }

    #[inline]
    unsafe fn stored_mut(&mut self) -> &mut T {
        self.0.stored_mut()
    }

    #[inline]
    unsafe fn drop_occupied(&mut self) {
        self.0.drop_occupied();
    }
}

unsafe impl<T, K: Key> SlotItemMutOutput<K> for BoxedSlot<T, K> {
    #[inline]
    unsafe fn mut_output(&mut self) -> &mut T {
        self.0.stored_mut()
    }
}

unsafe impl<T: Clone, K: Key> SlotItemClone<K> for BoxedSlot<T, K> {
    #[inline]
    unsafe fn clone_item(&self, is_occupied: bool) -> Self {
        if is_occupied {
            BoxedSlot(Box::new(SlotData {
                occupied: ManuallyDrop::new(self.0.ref_occupied().clone()),
            }))
        } else {
            BoxedSlot(Box::new(SlotData {
                vacant: self.0.get_vacant(),
            }))
        }
    }
}

// ─── StableGenMap (type alias) ───────────────────────────────────────────────

/// Generational map where each value is stored behind a `Box` for pointer
/// stability.  The `Box` allocation is **reused** across remove / re-insert
/// cycles, so a `remove` followed by an `insert` into the same slot incurs
/// no heap traffic.
pub type StableGenMap<K, T> = GenMap<K, BoxedSlot<T, K>>;

// ─── Clone (two-phase snapshot) ──────────────────────────────────────────────
//
// Phase 1: snapshot all &T refs (stable behind Box) without cloning.
// Phase 2: clone each T – this may re-enter the original map via &self,
//          which is safe because we no longer touch self.slots.

impl<K: Key, T: Clone> Clone for StableGenMap<K, T> {
    fn clone(&self) -> Self {
        unsafe {
            enum Snap<'a, K: Key, T> {
                Occupied(&'a T),
                Vacant(Option<K::Idx>),
            }

            let num_elements = self.len();
            let next_free = self.next_free.get();
            let slots_ref: &Vec<UnsafeCell<Slot<BoxedSlot<T, K>, K>>> = &*self.slots.get();

            // ── phase 1: snapshot ────────────────────────────────────────
            let mut snapshot: Vec<(K::Gen, K::Extra, Snap<'_, K, T>)> =
                Vec::with_capacity(slots_ref.len());

            for cell in slots_ref.iter() {
                let slot: &Slot<BoxedSlot<T, K>, K> = &*cell.get();
                let gen = slot.generation;
                let other = slot.other;

                let snap = if is_occupied_by_generation(gen) {
                    Snap::Occupied(slot.item.ref_output())
                } else {
                    Snap::Vacant(slot.item.get_vacant())
                };
                snapshot.push((gen, other, snap));
            }

            // ── phase 2: rebuild ─────────────────────────────────────────
            let mut new_slots: Vec<UnsafeCell<Slot<BoxedSlot<T, K>, K>>> =
                Vec::with_capacity(snapshot.len());

            for (generation, other, snap) in snapshot {
                let data = match snap {
                    Snap::Occupied(vref) => SlotData {
                        occupied: ManuallyDrop::new(vref.clone()),
                    },
                    Snap::Vacant(next) => SlotData { vacant: next },
                };

                new_slots.push(UnsafeCell::new(Slot {
                    generation,
                    other,
                    item: BoxedSlot(Box::new(data)),
                }));
            }

            GenMap::from_raw_parts(new_slots, next_free, num_elements)
        }
    }
}
