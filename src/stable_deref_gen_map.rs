use crate::gen_map::{GenMap, Slot};
use crate::key::{is_occupied_by_generation, Key, KeyData};
use crate::slot_item::{DerefGenMapPromise, DerefSlot, SlotData, SlotItem};
use num_traits::{CheckedAdd, One, Zero};
use std::cell::{Cell, UnsafeCell};
use std::marker::PhantomData;
use std::mem::ManuallyDrop;
use std::ops::Deref;
use std::rc::Rc;
use std::sync::Arc;

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
    /// IF THESE GUIDELINES ARE NOT FOLLOWED, THERE COULD BE BUGS, UNEXPECTED BEHAVIOUR, AND MAYBE UNDEFINED BEHAVIOUR
    ///<br><br>
    /// The implementation of this method should have very similar logic to the smart pointer's `Clone::clone` implementation to ensure consistency.
    /// If still in doubt, you can look at how we implemented `SmartPtrCloneable` for `Box`
    unsafe fn clone_from_reference(reference: &Self::Target) -> Option<Self>;
}

unsafe impl<T: Clone> SmartPtrCloneable for Box<T> {
    const KIND: SmartPtrKind = SmartPtrKind::Owned;
    unsafe fn clone_from_reference(reference: &T) -> Option<Self> {
        Some(Box::new(reference.clone()))
    }
}
unsafe impl<'a, T: ?Sized> SmartPtrCloneable for &'a T {
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

// ─── type aliases ────────────────────────────────────────────────────────────

/// Generational map that stores user-supplied smart pointers (`Box`, `Rc`,
/// `Arc`, `&T`, …) directly.  The smart pointer provides pointer stability.
pub type StableDerefGenMap<K, Derefable> = GenMap<K, DerefSlot<Derefable, K>>;

pub type BoxStableDerefGenMap<K, T> = StableDerefGenMap<K, Box<T>>;

// ─── Clone (two strategies) ──────────────────────────────────────────────────

impl<K: Key, Derefable: DerefGenMapPromise + SmartPtrCloneable> Clone
for StableDerefGenMap<K, Derefable>
{
    fn clone(&self) -> Self {
        unsafe {
            // Fast path for Shared smart pointers (Rc, Arc, &T):
            // Clone can't mutate the map, so clone_efficiently is safe.
            if <Derefable as SmartPtrCloneable>::KIND == SmartPtrKind::Shared {
                return self.clone_efficiently();
            }

            // Slow path for Owned smart pointers (Box<T>):
            // Two-phase snapshot to tolerate T::clone re-entering the map.
            enum RefOrNext<'a, K: Key, T: ?Sized> {
                Ref(&'a T),
                Next(Option<K::Idx>),
            }

            let num_elements = self.len();
            let next_free = self.next_free.clone();
            let slots_ref: &Vec<UnsafeCell<Slot<DerefSlot<Derefable, K>, K>>> =
                &*self.slots.get();

            // ── phase 1: snapshot refs ───────────────────────────────────
            let mut snapshot: Vec<(K::Gen, RefOrNext<'_, K, Derefable::Target>)> =
                Vec::with_capacity(slots_ref.len());

            for cell in slots_ref.iter() {
                let slot = &*cell.get();
                let gen = slot.generation;

                let snap = if is_occupied_by_generation(gen) {
                    RefOrNext::Ref(slot.item.ref_output())
                } else {
                    RefOrNext::Next(slot.item.get_vacant())
                };
                snapshot.push((gen, snap));
            }

            // ── phase 2: rebuild via clone_from_reference ────────────────
            let new_slots: Vec<UnsafeCell<Slot<DerefSlot<Derefable, K>, K>>> =
                snapshot
                    .into_iter()
                    .map(|(generation, snap)| {
                        let data = match snap {
                            RefOrNext::Ref(the_ref) => SlotData {
                                occupied: ManuallyDrop::new(
                                    Derefable::clone_from_reference(the_ref).unwrap(),
                                ),
                            },
                            RefOrNext::Next(next_free) => SlotData { vacant: next_free },
                        };
                        UnsafeCell::new(Slot {
                            generation,
                            item: DerefSlot(data),
                        })
                    })
                    .collect();

            GenMap::from_raw_parts(new_slots, next_free.get(), num_elements)
        }
    }
}