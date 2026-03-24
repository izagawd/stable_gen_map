use crate::gen_map::{GenMap, Slot};
use crate::key::{is_occupied_by_generation, Key};
use crate::slot_item::{SlotData, SlotItem, SlotItemClone, SlotItemMutOutput};
use std::cell::UnsafeCell;
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
pub struct DerefSlot<D: DerefGenMapPromise, K: Key>(pub(crate) SlotData<D, K>);

unsafe impl<D: DerefGenMapPromise, K: Key> SlotItem<K> for DerefSlot<D, K> {
    type Stored = D;
    type Output = D::Target;

    #[inline]
    fn new_vacant(next: Option<K::Idx>) -> Self {
        DerefSlot(SlotData::new_vacant(next))
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
    unsafe fn write_occupied(&mut self, value: D) {
        self.0.write_occupied(value);
    }

    #[inline]
    unsafe fn take_occupied(&mut self) -> D {
        self.0.take_occupied()
    }

    #[inline]
    unsafe fn ref_output(&self) -> &D::Target {
        self.0.ref_occupied().deref()
    }

    #[inline]
    unsafe fn stored_mut(&mut self) -> &mut D {
        self.0.stored_mut()
    }

    #[inline]
    unsafe fn drop_occupied(&mut self) {
        self.0.drop_occupied();
    }
}

unsafe impl<D: DerefGenMapPromise + DerefMut, K: Key> SlotItemMutOutput<K> for DerefSlot<D, K> {
    #[inline]
    unsafe fn mut_output(&mut self) -> &mut D::Target {
        self.0.stored_mut().deref_mut()
    }
}

unsafe impl<D: DerefGenMapPromise + Clone, K: Key> SlotItemClone<K> for DerefSlot<D, K> {
    #[inline]
    unsafe fn clone_item(&self, is_occupied: bool) -> Self {
        if is_occupied {
            DerefSlot(SlotData {
                occupied: self.0.occupied.clone(),
            })
        } else {
            DerefSlot(SlotData {
                vacant: self.0.get_vacant(),
            })
        }
    }
}

// ─── SmartPtrKind / SmartPtrCloneable ────────────────────────────────────────

/// Describes the ownership semantics of a smart pointer stored in a
/// [`StableDerefMap`].
///
/// Selecting the wrong kind for a smart pointer may lead to **undefined
/// behaviour** — read the per-variant docs carefully.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum SmartPtrKind {
    /// The smart pointer owns its pointee exclusively. When the smart pointer
    /// is dropped, the pointee is dropped too (e.g. `Box`).
    Owned,

    /// The smart pointer borrows or shares ownership of its pointee
    /// (e.g. `Rc`, `Arc`, `&T`).
    ///
    /// If the smart pointer's `Clone` implementation clones the *pointee*
    /// (calls `T::clone`), you must **not** implement [`SmartPtrCloneable`]
    /// for it — doing so may cause undefined behaviour.
    ///
    /// If the smart pointer does implement `Clone`, its `Clone` must **not**
    /// mutate any shared `StableDerefMap` (e.g. via `insert`).
    Shared,
}

/// Marker trait for smart pointers that can be safely cloned inside a
/// [`StableDerefMap`].
///
/// # Safety
///
/// Implementors must:
/// - Choose the correct [`SmartPtrKind`].
/// - For `Owned` pointers: implement `clone_from_reference` to produce a
///   new smart pointer from a `&Self::Target` (similar logic to `Clone::clone`).
/// - For `Shared` pointers: return `None` from `clone_from_reference`.
pub unsafe trait SmartPtrCloneable: DerefGenMapPromise + Clone {
    /// The ownership kind of this smart pointer.
    const KIND: SmartPtrKind;

    /// For `Owned` pointers, clone the pointee into a new smart pointer.
    /// For `Shared` pointers, return `None`.
    ///
    /// # Safety
    /// Must only be called when the slot is known to be occupied.
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
pub type StableDerefMap<K, Derefable> = GenMap<K, DerefSlot<Derefable, K>>;

/// Convenience alias for `StableDerefMap<K, Box<T>>`.
///
/// Equivalent to [`StableMap`](crate::stable_map::StableMap) in
/// behaviour, but stores the `Box` directly rather than wrapping `T` in a
/// second `Box`. Prefer this when your values are already boxed.
pub type BoxStableDerefMap<K, T> = StableDerefMap<K, Box<T>>;

// ─── Clone (two strategies) ──────────────────────────────────────────────────

impl<K: Key, Derefable: DerefGenMapPromise + SmartPtrCloneable> Clone
for StableDerefMap<K, Derefable>
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
            let slots_ref: &Vec<UnsafeCell<Slot<DerefSlot<Derefable, K>, K>>> = &*self.slots.get();

            // ── phase 1: snapshot refs ───────────────────────────────────
            let mut snapshot: Vec<(K::Gen, K::Extra, RefOrNext<'_, K, Derefable::Target>)> =
                Vec::with_capacity(slots_ref.len());

            for cell in slots_ref.iter() {
                let slot = &*cell.get();
                let gen = slot.generation;
                let other = slot.other;

                let snap = if is_occupied_by_generation(gen) {
                    RefOrNext::Ref(slot.item.ref_output())
                } else {
                    RefOrNext::Next(slot.item.get_vacant())
                };
                snapshot.push((gen, other, snap));
            }

            // ── phase 2: rebuild via clone_from_reference ────────────────
            let new_slots: Vec<UnsafeCell<Slot<DerefSlot<Derefable, K>, K>>> = snapshot
                .into_iter()
                .map(|(generation, other, snap)| {
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
                        other,
                        item: DerefSlot(data),
                    })
                })
                .collect();

            GenMap::from_raw_parts(new_slots, next_free.get(), num_elements)
        }
    }
}