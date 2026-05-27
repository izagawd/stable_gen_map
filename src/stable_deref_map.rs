use crate::gen_map::{GenMap, Slot};
use crate::key::{is_occupied_by_generation, Key, KeyData};
use crate::slot_item::{SlotData, SlotStorage, SlotStorageClone, SlotStorageMutOutput};
use num_traits::{CheckedAdd, One, Zero};
use std::cell::{Cell, UnsafeCell};
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
unsafe impl<'a, T: ?Sized> DerefGenMapPromise for &'a T {}

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
        &mut *self.0.occupied
    }

    #[inline]
    unsafe fn drop_occupied(&mut self) {
        ManuallyDrop::drop(&mut self.0.occupied);
    }
}

unsafe impl<K: Key, Ptr: DerefGenMapPromise + DerefMut> SlotStorageMutOutput for DerefSlot<K, Ptr> {
    #[inline]
    unsafe fn mut_output(&mut self) -> &mut Ptr::Target {
        self.0.occupied.deref_mut().deref_mut()
    }
}

unsafe impl<K: Key, Ptr: DerefGenMapPromise + Clone> SlotStorageClone for DerefSlot<K, Ptr> {
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

// ─── Type aliases ────────────────────────────────────────────────────────────

/// Generational map that stores user-supplied smart pointers (`Box`, `Rc`,
/// `Arc`, `&T`, …) directly.  The smart pointer provides pointer stability.
pub type StableDerefMap<K, Ptr> = GenMap<DerefSlot<K, Ptr>>;

pub type BoxStableDerefMap<K, T> = StableDerefMap<K, Box<T>>;

// ─── Clone (two strategies) ──────────────────────────────────────────────────

impl<K: Key, Ptr: DerefGenMapPromise + SmartPtrCloneable> Clone
    for StableDerefMap<K, Ptr>
{
    #[inline]
    fn clone(&self) -> Self {
        unsafe {
            // Fast path for Shared smart pointers (Rc, Arc, &T):
            // Clone can't mutate the map, so clone_efficiently is safe.
            if <Ptr as SmartPtrCloneable>::KIND == SmartPtrKind::Shared {
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
            let slots_ref: &Vec<UnsafeCell<Slot<DerefSlot<K, Ptr>>>> = &*self.slots.get();

            // ── phase 1: snapshot refs ───────────────────────────────────
            let mut snapshot: Vec<(K::Gen, RefOrNext<'_, K, Ptr::Target>)> =
                Vec::with_capacity(slots_ref.len());

            for cell in slots_ref.iter() {
                let slot = &*cell.get();
                let gen = slot.generation;

                let snap = if is_occupied_by_generation(gen) {
                    RefOrNext::Ref(slot.storage.ref_output())
                } else {
                    RefOrNext::Next(slot.storage.get_vacant())
                };
                snapshot.push((gen, snap));
            }

            // ── phase 2: rebuild via clone_from_reference ────────────────
            let new_slots: Vec<UnsafeCell<Slot<DerefSlot<K, Ptr>>>> = snapshot
                .into_iter()
                .map(|(generation, snap)| {
                    let data = match snap {
                        RefOrNext::Ref(the_ref) => SlotData {
                            occupied: ManuallyDrop::new(
                                Ptr::clone_from_reference(the_ref).unwrap(),
                            ),
                        },
                        RefOrNext::Next(next_free) => SlotData { vacant: next_free },
                    };
                    UnsafeCell::new(Slot {
                        generation,
                        storage: DerefSlot(data),
                    })
                })
                .collect();

            GenMap::from_raw_parts(new_slots, next_free.get(), num_elements)
        }
    }
}
