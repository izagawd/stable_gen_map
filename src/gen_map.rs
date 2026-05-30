use crate::key::{is_occupied_by_generation, Key, KeyData};
use crate::key_piece::KeyPiece;
use crate::slot_storage::{
    NonMutatingSlotStorageClone, SlotStorage, SlotStorageClone, SlotStorageMutOutput,
};
use num_traits::{CheckedAdd, One, Zero};
use std::cell::{Cell, UnsafeCell};
use std::collections::TryReserveError;
use std::ops::{Index, IndexMut};
// ─── Private type-level shortcuts ────────────────────────────────────────────
// These reduce the verbosity of double-associated-type projections.

pub(crate) type KeyOfStorage<C> = <C as SlotStorage>::Key;
pub(crate) type IdxOfStorage<C> = <<C as SlotStorage>::Key as Key>::Idx;
pub(crate) type GenOfStorage<C> = <<C as SlotStorage>::Key as Key>::Gen;

// ─── Slot ────────────────────────────────────────────────────────────────────

pub struct Slot<C: SlotStorage> {
    pub(crate) storage: C,
    pub(crate) generation: GenOfStorage<C>,
}

impl<C: SlotStorage> Slot<C> {
    /// Returns `true` if this slot currently holds a value.
    #[inline]
    pub fn is_occupied(&self) -> bool {
        is_occupied_by_generation(self.generation)
    }
    /// Returns a shared reference to the generation stored in this slot.
    #[inline]
    pub fn generation(&self) -> &GenOfStorage<C> {
        &self.generation
    }

    /// Returns a mutable reference to the generation stored in this slot.
    ///
    /// # Safety
    /// The caller must not violate map invariants
    #[inline]
    pub unsafe fn generation_mut(&mut self) -> &mut GenOfStorage<C> {
        &mut self.generation
    }

    /// Returns a shared reference to the slot's [`SlotStorage`].
    ///
    /// # Safety
    /// The caller must not violate map invariants.
    #[inline]
    pub unsafe fn storage(&self) -> &C {
        &self.storage
    }

    /// Returns a mutable reference to the slot's [`SlotStorage`].
    ///
    /// # Safety
    /// The caller must not violate map invariants.
    #[inline]
    pub unsafe fn storage_mut(&mut self) -> &mut C {
        &mut self.storage
    }

    /// Returns a shared reference to the slot's output.
    ///
    /// # Safety
    /// The slot must be occupied.
    #[inline]
    pub unsafe fn ref_output(&self) -> &C::Output {
        self.storage.ref_output()
    }
}

impl<C: SlotStorageMutOutput> Slot<C> {
    /// Returns a mutable reference to the slot's output.
    ///
    /// # Safety
    /// The slot must be occupied.
    #[inline]
    pub unsafe fn mut_output(&mut self) -> &mut C::Output {
        self.storage.mut_output()
    }
}

impl<C: SlotStorage> Drop for Slot<C> {
    #[inline]
    fn drop(&mut self) {
        unsafe { self.storage.drop_contents(self.is_occupied()) }
    }
}

impl<C: SlotStorage> Slot<C> {
    /// Take the occupied value if the slot is actually occupied, else `None`.
    #[inline]
    fn take_occupied(&mut self) -> Option<C::Stored> {
        if is_occupied_by_generation(self.generation) {
            Some(unsafe { self.storage.take_occupied() })
        } else {
            None
        }
    }
}

// ─── GenMap ──────────────────────────────────────────────────────────────────

/// Generational arena with interior-mutable insertion and pointer-stable
/// references.
///
/// The storage strategy is determined by `C`:
/// - [`BoxedSlot`](crate::boxed_slot::BoxedSlot) – wraps each value in a `Box`;
///   the allocation is reused across remove/insert cycles.
/// - [`DerefSlot`](crate::deref_slot::DerefSlot) – stores a user-supplied smart
///   pointer directly.
///
/// You will normally use the type aliases
/// [`StableGenMap`](crate::boxed_slot::StableGenMap) and
/// [`StableDerefMap`](crate::deref_slot::StableDerefMap).
pub struct GenMap<C: SlotStorage> {
    pub(crate) slots: UnsafeCell<Vec<UnsafeCell<Slot<C>>>>,
    pub(crate) next_free: Cell<Option<IdxOfStorage<C>>>,
    pub(crate) num_elements: Cell<usize>,
}

// ─── Index / IndexMut ────────────────────────────────────────────────────────

impl<C: SlotStorage> Index<KeyOfStorage<C>> for GenMap<C> {
    type Output = C::Output;

    #[inline]
    fn index(&self, key: KeyOfStorage<C>) -> &Self::Output {
        self.get(key).unwrap()
    }
}

impl<C: SlotStorageMutOutput> IndexMut<KeyOfStorage<C>> for GenMap<C> {
    #[inline]
    fn index_mut(&mut self, key: KeyOfStorage<C>) -> &mut Self::Output {
        self.get_mut(key).unwrap()
    }
}

// ─── RemoveArguments (borrow-checker helper) ─────────────────────────────────

struct RemoveArguments<'a, C: SlotStorage> {
    slot: &'a mut Slot<C>,
    key: KeyOfStorage<C>,
    num_elements: &'a Cell<usize>,
    next_free: &'a Cell<Option<IdxOfStorage<C>>>,
}

// ─── FreeGuard (RAII reservation for a single index) ─────────────────────────

struct FreeGuard<'a, C: SlotStorage> {
    map: &'a GenMap<C>,
    idx: IdxOfStorage<C>,
}

impl<'a, C: SlotStorage> FreeGuard<'a, C> {
    #[inline]
    fn commit(self) {
        std::mem::forget(self);
    }
}

impl<'a, C: SlotStorage> Drop for FreeGuard<'a, C> {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            let slots = &mut *self.map.slots.get();
            let slot = slots.get_unchecked_mut(self.idx.into_usize()).get_mut();

            // add by two to maintain evenness (even == vacant)
            if let Some(checked_add) = slot
                .generation
                .checked_add(&(GenOfStorage::<C>::one() + GenOfStorage::<C>::one()))
            {
                slot.generation = checked_add;
                let old_head = self.map.next_free.get();
                slot.storage.set_vacant(old_head);
                self.map.next_free.set(Some(self.idx));
            }
        }
    }
}

// ─── shared methods ──────────────────────────────────────────────────────────

impl<C: SlotStorage> Default for GenMap<C> {
    fn default() -> Self {
        Self::new()
    }
}

impl<C: SlotStorage> GenMap<C> {
    // ── construction ────────────────────────────────────────────────────

    /// Creates a new, empty map.
    #[inline]
    pub const fn new() -> Self {
        Self {
            slots: UnsafeCell::new(Vec::new()),
            next_free: Cell::new(None),
            num_elements: Cell::new(0),
        }
    }

    /// Returns true if the map is empty
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Creates a new map with the given pre-allocated capacity.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            slots: UnsafeCell::new(Vec::with_capacity(capacity)),
            next_free: Cell::new(None),
            num_elements: Cell::new(0),
        }
    }

    /// Reserves capacity for at least `additional` more elements.
    #[inline]
    pub fn reserve(&self, additional: usize) {
        unsafe { &mut *self.slots.get() }.reserve(additional);
    }

    /// Tries to reserve capacity for at least `additional` more elements.
    #[inline]
    pub fn try_reserve(&self, additional: usize) -> Result<(), TryReserveError> {
        unsafe { &mut *self.slots.get() }.try_reserve(additional)
    }

    /// Returns how many slots the backing `Vec` can hold before reallocating.
    #[inline]
    pub fn capacity(&self) -> usize {
        unsafe { &*self.slots.get() }.capacity()
    }

    // ── length ──────────────────────────────────────────────────────────

    /// Returns the number of occupied elements.
    #[inline]
    pub fn len(&self) -> usize {
        self.num_elements.get()
    }

    /// Total number of slots, occupied and vacant.
    #[inline]
    pub fn slots_len(&self) -> usize {
        // SAFETY: shared read of the slot vector's length.
        unsafe { (*self.slots.get()).len() }
    }

    // ── get (shared) ────────────────────────────────────────────────────

    /// Shared-reference lookup by key.
    #[inline]
    pub fn get(&self, k: KeyOfStorage<C>) -> Option<&C::Output> {
        unsafe {
            let key_data = k.data();
            let slots = &*self.slots.get();
            let slot = &*slots.get(key_data.idx.into_usize())?.get();
            if slot.generation != key_data.generation.into() {
                return None;
            }
            Some(slot.storage.ref_output())
        }
    }

    /// Shared-reference lookup by index only (ignores generation).
    /// Returns `None` if the slot is unoccupied
    #[inline]
    pub fn get_by_index_only(&self, idx: IdxOfStorage<C>) -> Option<(KeyOfStorage<C>, &C::Output)> {
        unsafe {
            let slots = &*self.slots.get();
            let slot = &*slots.get(idx.into_usize())?.get();
            if is_occupied_by_generation(slot.generation) {
                Some((
                    KeyOfStorage::<C>::from(KeyData {
                        idx,
                        generation: slot.generation.try_into().unwrap_unchecked(),
                    }),
                    slot.storage.ref_output(),
                ))
            } else {
                None
            }
        }
    }

    /// Returns a reference to the raw [`Slot`] at the given index.
    ///
    /// Performs bounds checking. Returns `None` if out of bounds.
    ///
    /// # Safety
    /// The returned slot exposes internal data structures. The caller
    /// must not use this to violate map invariants, and must check
    /// occupancy before accessing the slot's value.
    ///
    /// **Holding a `&Slot` reference, performing an `insert`, and then
    /// accessing that old `&Slot` or any of its contents is undefined behaviour.** `insert` only
    /// requires `&self` and may reallocate the backing storage, which
    /// invalidates all previously obtained slot references.
    #[inline]
    pub unsafe fn get_slot(&self, idx: IdxOfStorage<C>) -> Option<&Slot<C>> {
        let slots = &*self.slots.get();
        let slot = &*slots.get(idx.into_usize())?.get();
        Some(slot)
    }

    /// Returns a reference to the raw [`Slot`] without bounds checking.
    ///
    /// # Safety
    /// - The index must be in bounds.
    /// - The caller must check occupancy before accessing the slot's value.
    ///
    /// **Holding a `&Slot` reference, performing an `insert`, and then
    /// accessing that old `&Slot` or any of its contents is undefined behaviour.** `insert` only
    /// requires `&self` and may reallocate the backing storage, which
    /// invalidates all previously obtained slot references.
    #[inline]
    pub unsafe fn get_slot_unchecked(&self, idx: IdxOfStorage<C>) -> &Slot<C> {
        let slots = &*self.slots.get();
        &*slots.get_unchecked(idx.into_usize()).get()
    }

    /// Returns a reference to the raw [`UnsafeCell`] wrapping the [`Slot`]
    /// at the given index.
    ///
    /// Performs bounds checking. Returns `None` if out of bounds.
    ///
    /// # Safety
    /// The returned cell exposes internal data structures. The caller
    /// must check occupancy before accessing the slot's value.
    ///
    /// **Holding a cell reference, performing an `insert`, and then
    /// accessing that old reference or any of its contents is undefined behaviour.** `insert` only
    /// requires `&self` and may reallocate the backing storage, which
    /// invalidates all previously obtained references.
    #[inline]
    pub unsafe fn get_slot_as_cell(&self, idx: IdxOfStorage<C>) -> Option<&UnsafeCell<Slot<C>>> {
        let slots = &*self.slots.get();
        slots.get(idx.into_usize())
    }

    /// Returns a reference to the raw [`UnsafeCell`] wrapping the [`Slot`]
    /// without bounds checking.
    ///
    /// # Safety
    /// - The index must be in bounds.
    /// - The caller must check occupancy before accessing the slot's value.
    ///
    /// **Holding a cell reference, performing an `insert`, and then
    /// accessing that old reference or any of its contents is undefined behaviour.** `insert` only
    /// requires `&self` and may reallocate the backing storage, which
    /// invalidates all previously obtained references.
    #[inline]
    pub unsafe fn get_slot_as_cell_unchecked(&self, idx: IdxOfStorage<C>) -> &UnsafeCell<Slot<C>> {
        let slots = &*self.slots.get();
        slots.get_unchecked(idx.into_usize())
    }

    /// Returns a mutable reference to the raw [`Slot`] at the given index.
    ///
    /// Performs bounds checking. Returns `None` if out of bounds.
    ///
    /// # Safety
    /// The returned slot exposes internal data structures. The caller
    /// must not use this to violate map invariants, and must check
    /// occupancy before accessing the slot's value.
    #[inline]
    pub unsafe fn get_slot_mut(&mut self, idx: IdxOfStorage<C>) -> Option<&mut Slot<C>> {
        let slots = self.slots.get_mut();
        Some(slots.get_mut(idx.into_usize())?.get_mut())
    }

    /// Returns a mutable reference to the raw [`Slot`] without bounds checking.
    ///
    /// # Safety
    /// - The index must be in bounds.
    /// - The caller must not use this to violate map invariants, and must
    ///   check occupancy before accessing the slot's value.
    #[inline]
    pub unsafe fn get_slot_unchecked_mut(&mut self, idx: IdxOfStorage<C>) -> &mut Slot<C> {
        let slots = self.slots.get_mut();
        slots.get_unchecked_mut(idx.into_usize()).get_mut()
    }

    /// Shared-reference lookup without bounds or generation checks.
    ///
    /// # Safety
    /// - The key's index must be in bounds.
    /// - The slot at that index must be occupied with the matching generation.
    #[inline]
    pub unsafe fn get_unchecked(&self, k: KeyOfStorage<C>) -> &C::Output {
        let key_data = k.data();
        let slots = &*self.slots.get();
        let slot = &*slots.get_unchecked(key_data.idx.into_usize()).get();
        slot.storage.ref_output()
    }

    // ── get_mut (requires SlotStorageMutOutput) ────────────────────────
    // (placed inside a separate impl block below)

    // ── insert ──────────────────────────────────────────────────────────

    /// Simple insert. Returns the key for the stored output.
    #[inline]
    pub fn insert(&self, value: C::Stored) -> KeyOfStorage<C> {
        self.insert_with_key(|_| value)
    }

    /// Inserts a value produced by `func`, which receives the key that will
    /// identify the inserted element.
    #[inline]
    pub fn insert_with_key(
        &self,
        func: impl FnOnce(KeyOfStorage<C>) -> C::Stored,
    ) -> KeyOfStorage<C> {
        self.try_insert_with_key::<()>(|key| Ok(func(key))).unwrap()
    }

    /// Like [`insert_with_key`](Self::insert_with_key) but the closure may
    /// return `Err`, in which case the slot is released.
    #[inline]
    pub fn try_insert_with_key<E>(
        &self,
        func: impl FnOnce(KeyOfStorage<C>) -> Result<C::Stored, E>,
    ) -> Result<KeyOfStorage<C>, E> {
        unsafe {
            let slots = &mut *self.slots.get();

            let (idx, generation) = if let Some(idx) = self.next_free.get() {
                // reuse a free slot
                let slot = slots.get_unchecked_mut(idx.into_usize()).get_mut();

                let next = slot.storage.get_vacant();
                self.next_free.set(next);
                slot.storage.set_vacant(None); // mark reserved

                let generation = slot.generation;
                (idx, generation)
            } else {
                // append a new slot
                let generation = GenOfStorage::<C>::zero();
                let idx = IdxOfStorage::<C>::from_usize(slots.len());
                slots.push(UnsafeCell::new(Slot {
                    generation,
                    storage: C::new_vacant(None),
                }));
                (idx, generation)
            };

            let generation_zeroable: GenOfStorage<C> = generation.into();
            // key gen is one ahead; only valid after we commit
            let key = KeyOfStorage::<C>::from(KeyData {
                idx,
                generation: generation_zeroable
                    .checked_add(&GenOfStorage::<C>::one())
                    .unwrap()
                    .try_into()
                    .unwrap_unchecked(),
            });

            let guard = FreeGuard { map: self, idx };

            let value = func(key)?; // may panic / Err

            guard.commit();

            // re-borrow – func() may have caused the vec to grow
            let slots = &*self.slots.get();
            let slot = &mut *slots.get_unchecked(idx.into_usize()).get();

            slot.storage.write_occupied(value);
            slot.generation += GenOfStorage::<C>::one();
            self.num_elements.set(self.num_elements.get() + 1);

            Ok(key)
        }
    }

    // ── remove ──────────────────────────────────────────────────────────

    /// Shared removal helper (avoids borrow-checker issues).
    #[inline]
    unsafe fn remove_split_data<const DO_GENERATION_CHECK: bool>(
        args: RemoveArguments<C>,
    ) -> Option<C::Stored> {
        let slot = args.slot;
        let num_elements = args.num_elements;
        let next_free = args.next_free;
        let key_data = args.key.data();

        if DO_GENERATION_CHECK && slot.generation != key_data.generation.into() {
            return None;
        }

        let value = slot.take_occupied()?;

        num_elements.set(num_elements.get() - 1);

        match slot.generation.checked_add(&GenOfStorage::<C>::one()) {
            Some(new_gen) => {
                slot.generation = new_gen;
                let old_head = next_free.get();
                slot.storage.set_vacant(old_head);
                next_free.set(Some(key_data.idx));
            }
            None => {
                slot.generation = GenOfStorage::<C>::zero();
            }
        }

        Some(value)
    }

    /// Removes an element by key, returning its owned value.
    #[inline]
    pub fn remove(&mut self, k: KeyOfStorage<C>) -> Option<C::Stored> {
        let key_data = k.data();
        let slots = self.slots.get_mut();
        let slot = slots.get_mut(key_data.idx.into_usize())?.get_mut();
        unsafe {
            Self::remove_split_data::<true>(RemoveArguments {
                slot,
                key: k,
                num_elements: &self.num_elements,
                next_free: &self.next_free,
            })
        }
    }

    /// Empties the map and resets every slot's generation to zero, reclaiming
    /// generation headroom. Capacity is retained.
    ///
    /// Unlike [`clear`](Self::clear), this does **not** invalidate already existing
    /// keys: `clear` bumps generations of the slots so old keys can never match again, whereas
    /// `reset` winds them back to zero, so later inserts reproduce key values
    /// already handed out. A pre-`reset` key may then resolve to a *different*
    /// value. Memory-safe, but a silent logic hazard
    /// use [`clear`](Self::clear) if you need old keys to be invalid.
    #[inline]
    pub fn reset(&mut self) {
        self.slots.get_mut().clear();
        *self.next_free.get_mut() = None;
        *self.num_elements.get_mut() = 0;
    }

    // ── clear / retain ──────────────────────────────────────────────────

    /// Empties the map, removing all elements.
    #[inline]
    pub fn clear(&mut self) {
        let slots_len = self.slots.get_mut().len();
        for idx in 0..slots_len {
            let slot = unsafe { self.slots.get_mut().get_unchecked_mut(idx).get_mut() };
            if !slot.is_occupied() {
                continue;
            }
            let key = KeyOfStorage::<C>::from(KeyData {
                idx: IdxOfStorage::<C>::from_usize(idx),
                generation: unsafe { slot.generation.try_into().unwrap_unchecked() },
            });
            let _ = self.remove(key);
        }
        debug_assert_eq!(self.len(), 0);
    }

    /// Retains only elements for which `f(key, &mut stored)` returns `true`.
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(KeyOfStorage<C>, &mut C::Stored) -> bool,
    {
        unsafe {
            let slots: &mut Vec<_> = self.slots.get_mut();

            for (idx, slot_cell) in slots.iter_mut().enumerate() {
                let slot = slot_cell.get_mut();
                if is_occupied_by_generation(slot.generation) {
                    let value = slot.storage.stored_mut();
                    let key_data = KeyData {
                        idx: IdxOfStorage::<C>::from_usize(idx),
                        generation: slot.generation.try_into().unwrap_unchecked(),
                    };
                    let key = KeyOfStorage::<C>::from(key_data);

                    if !f(key, value) {
                        Self::remove_split_data::<false>(RemoveArguments {
                            slot,
                            key,
                            num_elements: &self.num_elements,
                            next_free: &self.next_free,
                        });
                    }
                }
            }
        }
    }

    // ── snapshot / unsafe_iter ───────────────────────────────────────────

    /// Returns a snapshot of all `(key, &output)` pairs at the current moment.
    /// Ignores future inserts. Heap-allocates one `Vec`.
    #[inline]
    pub fn snapshot(&self) -> Vec<(KeyOfStorage<C>, &C::Output)> {
        unsafe {
            let mut vec = Vec::with_capacity(self.len());
            vec.extend(self.unsafe_iter());
            vec
        }
    }

    /// Returns a snapshot of `&output` references only.
    #[inline]
    pub fn snapshot_refs(&self) -> Vec<&C::Output> {
        unsafe {
            let mut vec = Vec::with_capacity(self.len());
            vec.extend(self.unsafe_iter().map(|x| x.1));
            vec
        }
    }

    /// Returns a snapshot of keys only.
    #[inline]
    pub fn snapshot_keys(&self) -> Vec<KeyOfStorage<C>> {
        unsafe {
            let mut vec = Vec::with_capacity(self.len());
            vec.extend(self.unsafe_iter().map(|x| x.0));
            vec
        }
    }

    /// # Safety
    /// No mutation (including `insert`) may occur while iterating.
    #[inline]
    pub unsafe fn unsafe_iter(&self) -> impl Iterator<Item = (KeyOfStorage<C>, &C::Output)> {
        (&*self.slots.get())
            .iter()
            .enumerate()
            .filter_map(|(idx, slot_cell)| {
                let slot = &*slot_cell.get();
                if is_occupied_by_generation(slot.generation) {
                    Some((
                        KeyOfStorage::<C>::from(KeyData {
                            idx: IdxOfStorage::<C>::from_usize(idx),
                            generation: unsafe { slot.generation.try_into().unwrap_unchecked() },
                        }),
                        slot.storage.ref_output(),
                    ))
                } else {
                    None
                }
            })
    }
}

// ─── clone helpers ───────────────────────────────────────────────────────────

impl<C: SlotStorageClone> GenMap<C> {
    /// Clone the map in a single pass, duplicating each slot in place.
    ///
    /// # Safety
    /// Cloning a slot may run user code, and
    /// the pass holds `&self` into the slot buffer throughout. The caller must
    /// guarantee none of that code **mutates this map** (for example, via
    /// `insert`) before the pass finishes; a mutation that grows / reallocates
    /// the slot buffer would free the memory this borrow points into, which is
    /// undefined behaviour. Read-only re-entry (`get`, `len`, iteration, …) is
    /// fine.
    #[inline]
    pub unsafe fn unsafe_clone(&self) -> Self {
        Self {
            num_elements: self.num_elements.clone(),
            next_free: self.next_free.clone(),
            slots: UnsafeCell::new(
                (&*self.slots.get())
                    .iter()
                    .map(|slot_cell| {
                        let slot = &*slot_cell.get();
                        UnsafeCell::new(Slot {
                            generation: slot.generation,
                            storage: slot.storage.clone_storage(slot.is_occupied()),
                        })
                    })
                    .collect(),
            ),
        }
    }

    /// Clone the map through a unique borrow.
    #[inline]
    pub fn clone_mut(&mut self) -> Self {
        // SAFETY: `&mut self` rules out a concurrent `&self` mutation (e.g.
        // `insert`), so no `clone_storage` on this pass can grow / reallocate
        // `self.slots`. Read-only re-entry would be harmless anyway.
        unsafe { self.unsafe_clone() }
    }

    /// Clone `source` into `self`, reusing `self`'s slot-vector allocation.
    ///
    /// # Safety
    /// Similar to [`unsafe_clone`](Self::unsafe_clone), the caller must guarantee that the source's
    /// clone does not mutate
    #[inline]
    pub unsafe fn unsafe_clone_from(&mut self, source: &Self) {
        let src_slots = &*source.slots.get();
        // Reuse the buffer: drop old slots, grow only if `source` is larger.
        let dst_slots = self.slots.get_mut();
        dst_slots.clear();
        dst_slots.reserve(src_slots.len());
        for src_cell in src_slots.iter() {
            let src = &*src_cell.get();
            let storage = src.storage.clone_storage(src.is_occupied());
            dst_slots.push(UnsafeCell::new(Slot {
                generation: src.generation,
                storage,
            }));
        }
        self.next_free.set(source.next_free.get());
        self.num_elements.set(source.len());
    }
}

// ─── Clone (for storages whose clone cannot mutate the map) ──────────────────
//
// One blanket impl serves every storage that implements
// `NonMutatingSlotStorageClone`, including custom user storages: the free-list
// / generation bookkeeping is duplicated once, and each slot's payload is cloned
// in a single in-place pass (`unsafe_clone`).
//
// The `&self` pass is sound only because the marker promises `clone_storage`
// will not mutate `self` (its `&self` borrows into the slot buffer for the whole
// pass, which a mutation such as `insert` could grow / reallocate and free;
// read-only re-entry is harmless). The crate's storages obtain that promise by
// requiring their stored value to be `CloneGenMapPromise`, so a `GenMap` of an
// owned payload whose `Clone` might mutate the map is simply not `Clone` —
// though it is still `clone_mut`-able.
impl<C: NonMutatingSlotStorageClone> Clone for GenMap<C> {
    #[inline]
    fn clone(&self) -> Self {
        // SAFETY: `NonMutatingSlotStorageClone` guarantees `clone_storage` does
        // not mutate this map, so the single in-place pass cannot invalidate the
        // `&self` borrow it holds into the slot buffer.
        unsafe { self.unsafe_clone() }
    }

    /// Clones `source` into `self`, reusing `self`'s existing slot-vector
    /// allocation (see [`unsafe_clone_from`](Self::unsafe_clone_from)).
    fn clone_from(&mut self, source: &Self) {
        // SAFETY: the `NonMutatingSlotStorageClone` bound guarantees
        // `clone_storage` cannot mutate either map mid-pass.
        unsafe { self.unsafe_clone_from(source) }
    }
}

// ─── get_mut / get_by_index_only_mut (requires SlotStorageMutOutput) ────────────

impl<C: SlotStorageMutOutput> GenMap<C> {
    /// Unique-reference lookup by key.
    #[inline]
    pub fn get_mut(&mut self, k: KeyOfStorage<C>) -> Option<&mut C::Output> {
        let key_data = k.data();
        let slots = self.slots.get_mut();
        let slot = slots.get_mut(key_data.idx.into_usize())?.get_mut();
        if slot.generation != key_data.generation.into() {
            return None;
        }
        Some(unsafe { slot.storage.mut_output() })
    }

    /// Mutable lookup by index only (ignores generation).
    #[inline]
    pub fn get_by_index_only_mut(
        &mut self,
        idx: IdxOfStorage<C>,
    ) -> Option<(KeyOfStorage<C>, &mut C::Output)> {
        let slot = self.slots.get_mut().get_mut(idx.into_usize())?.get_mut();
        if is_occupied_by_generation(slot.generation) {
            Some((
                KeyOfStorage::<C>::from(KeyData {
                    idx,
                    generation: unsafe { slot.generation.try_into().unwrap_unchecked() },
                }),
                unsafe { slot.storage.mut_output() },
            ))
        } else {
            None
        }
    }

    /// Mutable-reference lookup without bounds or generation checks.
    ///
    /// # Safety
    /// - The key's index must be in bounds.
    /// - The slot at that index must be occupied with the matching generation.
    #[inline]
    pub unsafe fn get_unchecked_mut(&mut self, k: KeyOfStorage<C>) -> &mut C::Output {
        let key_data = k.data();
        let slots = self.slots.get_mut();
        let slot = slots.get_unchecked_mut(key_data.idx.into_usize()).get_mut();
        slot.storage.mut_output()
    }
}

// ─── IterMut ─────────────────────────────────────────────────────────────────

pub struct IterMut<'a, C: SlotStorage> {
    inner: std::slice::IterMut<'a, UnsafeCell<Slot<C>>>,
    idx: usize,
}

impl<'a, C: SlotStorage> Iterator for IterMut<'a, C> {
    type Item = (KeyOfStorage<C>, &'a mut C::Stored);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        for slot_cell in self.inner.by_ref() {
            let idx = self.idx;
            self.idx += 1;

            let slot = slot_cell.get_mut();
            if !is_occupied_by_generation(slot.generation) {
                continue;
            }

            let value: &mut C::Stored = unsafe { slot.storage.stored_mut() };
            let key = KeyOfStorage::<C>::from(KeyData {
                idx: IdxOfStorage::<C>::from_usize(idx),
                generation: unsafe { slot.generation.try_into().unwrap_unchecked() },
            });
            return Some((key, value));
        }
        None
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.inner.len()))
    }
}

impl<C: SlotStorage> GenMap<C> {
    /// Mutable iterator over all occupied elements.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, C> {
        IterMut {
            inner: self.slots.get_mut().iter_mut(),
            idx: 0,
        }
    }
}

impl<'a, C: SlotStorage> IntoIterator for &'a mut GenMap<C> {
    type Item = (KeyOfStorage<C>, &'a mut C::Stored);
    type IntoIter = IterMut<'a, C>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

// ─── Drain ───────────────────────────────────────────────────────────────────

/// Draining iterator. Created by [`GenMap::drain`].
///
/// Yields all occupied `(K, C::Stored)` pairs, removing them.
/// Remaining elements are dropped if the iterator is dropped early.
pub struct Drain<'a, C: SlotStorage> {
    map: &'a mut GenMap<C>,
    idx: usize,
}

impl<'a, C: SlotStorage> Iterator for Drain<'a, C> {
    type Item = (KeyOfStorage<C>, C::Stored);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let idx = self.idx;

            let generation = {
                let slots = self.map.slots.get_mut();
                if idx >= slots.len() {
                    return None;
                }
                self.idx += 1;
                let slot = slots[idx].get_mut();
                if !is_occupied_by_generation(slot.generation) {
                    continue;
                }
                slot.generation
            };

            let key = KeyOfStorage::<C>::from(KeyData {
                idx: IdxOfStorage::<C>::from_usize(idx),
                generation: unsafe { generation.try_into().unwrap_unchecked() },
            });
            let value = unsafe { self.map.remove(key).unwrap_unchecked() };
            return Some((key, value));
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.map.len()))
    }
}

impl<'a, C: SlotStorage> Drop for Drain<'a, C> {
    #[inline]
    fn drop(&mut self) {
        while self.next().is_some() {}
    }
}

impl<C: SlotStorage> GenMap<C> {
    /// Removes all elements and returns them as an iterator.
    /// The map is left empty but retains its allocated capacity.
    #[inline]
    pub fn drain(&mut self) -> Drain<'_, C> {
        Drain { map: self, idx: 0 }
    }
}

// ─── IntoIter (owning) ──────────────────────────────────────────────────────

pub struct IntoIter<C: SlotStorage> {
    inner: std::vec::IntoIter<UnsafeCell<Slot<C>>>,
    idx: usize,
}

impl<C: SlotStorage> Iterator for IntoIter<C> {
    type Item = (KeyOfStorage<C>, C::Stored);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        for mut slot_cell in self.inner.by_ref() {
            let idx = self.idx;
            self.idx += 1;

            let slot = slot_cell.get_mut();
            if !is_occupied_by_generation(slot.generation) {
                continue;
            }

            let value = unsafe { slot.storage.take_occupied() };

            let key_data = KeyData {
                generation: unsafe { slot.generation.try_into().unwrap_unchecked() },
                idx: IdxOfStorage::<C>::from_usize(idx),
            };

            // prevent Slot::drop from double-dropping
            slot.generation = GenOfStorage::<C>::zero();

            let key = KeyOfStorage::<C>::from(key_data);
            return Some((key, value));
        }
        None
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.inner.len()))
    }
}

impl<C: SlotStorage> IntoIterator for GenMap<C> {
    type Item = (KeyOfStorage<C>, C::Stored);
    type IntoIter = IntoIter<C>;

    /// Consumes the map into an owning iterator.
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.slots.into_inner().into_iter(),
            idx: 0,
        }
    }
}
