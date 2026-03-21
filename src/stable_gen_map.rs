use crate::gen_map::{GenMap, Slot};
use crate::key::{is_occupied_by_generation, Key, KeyData};
use crate::slot_item::{BoxedSlot, SlotData, SlotItem};
use num_traits::{CheckedAdd, One, Zero};
use std::cell::{Cell, UnsafeCell};
use std::marker::PhantomData;
use std::mem::ManuallyDrop;

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
            let slots_ref: &Vec<UnsafeCell<Slot<BoxedSlot<T, K>, K>>> =
                &*self.slots.get();

            // ── phase 1: snapshot ────────────────────────────────────────
            let mut snapshot: Vec<(K::Gen, Snap<'_, K, T>)> =
                Vec::with_capacity(slots_ref.len());

            for cell in slots_ref.iter() {
                let slot: &Slot<BoxedSlot<T, K>, K> = &*cell.get();
                let gen = slot.generation;

                let snap = if is_occupied_by_generation(gen) {
                    Snap::Occupied(slot.item.ref_output())
                } else {
                    Snap::Vacant(slot.item.get_vacant())
                };
                snapshot.push((gen, snap));
            }

            // ── phase 2: rebuild ─────────────────────────────────────────
            let mut new_slots: Vec<UnsafeCell<Slot<BoxedSlot<T, K>, K>>> =
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
                    item: BoxedSlot(Box::new(data)),
                }));
            }

            GenMap::from_raw_parts(new_slots, next_free, num_elements)
        }
    }
}