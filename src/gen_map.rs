use crate::key::{is_occupied_by_generation, Key, KeyData, KeyExtra};
use crate::key_piece::KeyPiece;
use crate::slot_item::{SlotItem, SlotItemClone, SlotItemMutOutput};
use num_traits::{CheckedAdd, One, Zero};
use std::cell::{Cell, UnsafeCell};
use std::collections::TryReserveError;
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

// ─── Slot ────────────────────────────────────────────────────────────────────

pub(crate) struct Slot<C: SlotItem<K>, K: Key> {
    pub(crate) item: C,
    pub(crate) generation: K::Gen,
    pub(crate) other: K::Extra,
}

impl<C: SlotItem<K>, K: Key> Drop for Slot<C, K> {
    fn drop(&mut self) {
        if is_occupied_by_generation(self.generation) {
            unsafe { self.item.drop_occupied() }
        }
    }
}

impl<C: SlotItem<K>, K: Key> Slot<C, K> {
    /// Take the occupied value if the slot is actually occupied, else `None`.
    #[inline]
    fn take_occupied(&mut self) -> Option<C::Stored> {
        if is_occupied_by_generation(self.generation) {
            Some(unsafe { self.item.take_occupied() })
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
/// - [`BoxedSlot`](crate::slot_item::BoxedSlot) – wraps each value in a `Box`;
///   the allocation is reused across remove/insert cycles.
/// - [`DerefSlot`](crate::slot_item::DerefSlot) – stores a user-supplied smart
///   pointer directly.
///
/// You will normally use the type aliases
/// [`StableGenMap`](crate::stable_map::StableMap) and
/// [`StableDerefGenMap`](crate::stable_deref_map::StableDerefMap).
pub struct GenMap<K: Key, C: SlotItem<K>> {
    pub(crate) slots: UnsafeCell<Vec<UnsafeCell<Slot<C, K>>>>,
    pub(crate) next_free: Cell<Option<K::Idx>>,
    pub(crate) phantom: PhantomData<fn(K)>,
    pub(crate) num_elements: Cell<usize>,
    pub(crate) extra_state: <K::Extra as KeyExtra>::State,
}

// ─── Index / IndexMut ────────────────────────────────────────────────────────

impl<K: Key, C: SlotItem<K>> Index<K> for GenMap<K, C> {
    type Output = C::Output;

    fn index(&self, key: K) -> &Self::Output {
        self.get(key).unwrap()
    }
}

impl<K: Key, C: SlotItemMutOutput<K>> IndexMut<K> for GenMap<K, C> {
    fn index_mut(&mut self, key: K) -> &mut Self::Output {
        self.get_mut(key).unwrap()
    }
}

// ─── RemoveArguments (borrow-checker helper) ─────────────────────────────────

struct RemoveArguments<'a, K: Key, C: SlotItem<K>> {
    slot: &'a mut Slot<C, K>,
    key: K,
    num_elements: &'a Cell<usize>,
    next_free: &'a Cell<Option<K::Idx>>,
}

// ─── FreeGuard (RAII reservation for a single index) ─────────────────────────

struct FreeGuard<'a, K: Key, C: SlotItem<K>> {
    map: &'a GenMap<K, C>,
    idx: K::Idx,
}

impl<'a, K: Key, C: SlotItem<K>> FreeGuard<'a, K, C> {
    fn commit(self) {
        std::mem::forget(self);
    }
}

impl<'a, K: Key, C: SlotItem<K>> Drop for FreeGuard<'a, K, C> {
    fn drop(&mut self) {
        unsafe {
            let slots = &mut *self.map.slots.get();
            let slot = slots.get_unchecked_mut(self.idx.into_usize()).get_mut();

            // add by two to maintain evenness (even == vacant)
            if let Some(checked_add) = slot
                .generation
                .checked_add(&(K::Gen::one() + K::Gen::one()))
            {
                slot.generation = checked_add;
                let old_head = self.map.next_free.get();
                unsafe { slot.item.set_vacant(old_head) };
                self.map.next_free.set(Some(self.idx));
            }
        }
    }
}

// ─── shared methods ──────────────────────────────────────────────────────────

impl<K: Key, C: SlotItem<K>> GenMap<K, C> {
    // ── construction ────────────────────────────────────────────────────

    /// Creates a new, empty map.
    #[inline]
    pub const fn new() -> Self {
        Self {
            slots: UnsafeCell::new(Vec::new()),
            next_free: Cell::new(None),
            phantom: PhantomData,
            num_elements: Cell::new(0),
            extra_state: K::Extra::EMPTY_STATE,
        }
    }

    /// Creates a new map with the given pre-allocated capacity.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            slots: UnsafeCell::new(Vec::with_capacity(capacity)),
            next_free: Cell::new(None),
            phantom: PhantomData,
            num_elements: Cell::new(0),
            extra_state: K::Extra::EMPTY_STATE,
        }
    }

    /// Reserves capacity for at least `additional` more elements.
    #[inline]
    pub fn reserve(&self, additional: usize) {
        unsafe { &mut *self.slots.get() }.reserve(additional);
    }

    /// Tries to reserve capacity for at least `additional` more elements.
    #[inline]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.slots.get_mut().try_reserve(additional)
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

    // ── get (shared) ────────────────────────────────────────────────────

    /// Shared-reference lookup by key.
    #[inline]
    pub fn get(&self, k: K) -> Option<&C::Output> {
        unsafe {
            let key_data = k.data();
            let slots = &*self.slots.get();
            let slot = &*slots.get(key_data.idx.into_usize())?.get();
            if slot.generation != key_data.generation {
                return None;
            }
            if !K::Extra::validate(k.extra(), slot.other) {
                return None;
            }
            Some(slot.item.ref_output())
        }
    }

    /// Shared-reference lookup by index only (ignores generation).
    /// Returns `None` if the slot is unoccupied
    #[inline]
    pub fn get_by_index_only(&self, idx: K::Idx) -> Option<(K, &C::Output)> {
        unsafe {
            let slots = &*self.slots.get();
            let slot = &*slots.get(idx.into_usize())?.get();
            if is_occupied_by_generation(slot.generation) {
                Some((
                    K::from_parts(
                        KeyData {
                            idx,
                            generation: slot.generation,
                        },
                        slot.other,
                    ),
                    slot.item.ref_output(),
                ))
            } else {
                None
            }
        }
    }

    // ── insert ──────────────────────────────────────────────────────────

    /// Simple insert. Returns the key and a reference to the stored output.
    #[inline]
    pub fn insert(&self, value: C::Stored) -> (K, &C::Output) {
        self.insert_with_key(|_| value)
    }

    /// Inserts a value produced by `func`, which receives the key that will
    /// identify the inserted element.
    #[inline]
    pub fn insert_with_key(&self, func: impl FnOnce(K) -> C::Stored) -> (K, &C::Output) {
        self.try_insert_with_key::<()>(|key| Ok(func(key))).unwrap()
    }

    /// Like [`insert_with_key`](Self::insert_with_key) but the closure may
    /// return `Err`, in which case the slot is released.
    #[inline]
    pub fn try_insert_with_key<E>(
        &self,
        func: impl FnOnce(K) -> Result<C::Stored, E>,
    ) -> Result<(K, &C::Output), E> {
        unsafe {
            let slots = &mut *self.slots.get();

            let extra = K::Extra::produce(&self.extra_state);

            let (idx, generation) = if let Some(idx) = self.next_free.get() {
                // reuse a free slot
                let slot = slots.get_unchecked_mut(idx.into_usize()).get_mut();

                let next = slot.item.get_vacant();
                self.next_free.set(next);
                slot.item.set_vacant(None); // mark reserved

                let generation = slot.generation;
                (idx, generation)
            } else {
                // append a new slot
                let generation = K::Gen::zero();
                let idx = K::Idx::from_usize(slots.len());
                slots.push(UnsafeCell::new(Slot {
                    generation,
                    item: C::new_vacant(None),
                    other: K::Extra::vacant_placeholder(),
                }));
                (idx, generation)
            };

            // key gen is one ahead; only valid after we commit
            let key = K::from_parts(
                KeyData {
                    idx,
                    generation: generation.checked_add(&K::Gen::one()).unwrap(),
                },
                extra,
            );

            let guard = FreeGuard { map: self, idx };

            let value = func(key)?; // may panic / Err

            guard.commit();

            // re-borrow – func() may have caused the vec to grow
            let slots = &*self.slots.get();
            let slot = &mut *slots.get_unchecked(idx.into_usize()).get();

            slot.item.write_occupied(value);
            slot.generation += K::Gen::one();
            slot.other = extra;
            self.num_elements.set(self.num_elements.get() + 1);

            let value_ref: &C::Output = slot.item.ref_output();
            Ok((key, value_ref))
        }
    }

    // ── remove ──────────────────────────────────────────────────────────

    /// Shared removal helper (avoids borrow-checker issues).
    #[inline]
    unsafe fn remove_split_data<const DO_GENERATION_CHECK: bool>(
        args: RemoveArguments<K, C>,
    ) -> Option<C::Stored> {
        let slot = args.slot;
        let num_elements = args.num_elements;
        let next_free = args.next_free;
        let key_data = args.key.data();

        if DO_GENERATION_CHECK {
            if slot.generation != key_data.generation {
                return None;
            }
            if !K::Extra::validate(args.key.extra(), slot.other) {
                return None;
            }
        }

        let value = match slot.take_occupied() {
            Some(v) => v,
            None => return None,
        };

        num_elements.set(num_elements.get() - 1);

        match slot.generation.checked_add(&K::Gen::one()) {
            Some(new_gen) => {
                slot.generation = new_gen;
                let old_head = next_free.get();
                slot.item.set_vacant(old_head);
                next_free.set(Some(key_data.idx));
            }
            None => {
                slot.generation = K::Gen::zero();
            }
        }

        Some(value)
    }

    /// Removes an element by key, returning its owned value.
    #[inline]
    pub fn remove(&mut self, k: K) -> Option<C::Stored> {
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

    // ── clear / retain ──────────────────────────────────────────────────

    /// Empties the map, removing all elements.
    #[inline]
    pub fn clear(&mut self) {
        let slots_len = self.slots.get_mut().len();
        for idx in 0..slots_len {
            let slot = unsafe { self.slots.get_mut().get_unchecked_mut(idx).get_mut() };
            let generation = slot.generation;
            let other = slot.other;
            let key = K::from_parts(
                KeyData {
                    idx: K::Idx::from_usize(idx),
                    generation,
                },
                other,
            );
            let _ = self.remove(key);
        }
        debug_assert_eq!(self.len(), 0);
    }

    /// Retains only elements for which `f(key, &mut stored)` returns `true`.
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(K, &mut C::Stored) -> bool,
    {
        unsafe {
            let slots: &mut Vec<_> = self.slots.get_mut();

            for (idx, slot_cell) in slots.iter_mut().enumerate() {
                let slot = slot_cell.get_mut();
                if is_occupied_by_generation(slot.generation) {
                    let value = slot.item.stored_mut();
                    let key = K::from_parts(
                        KeyData {
                            idx: K::Idx::from_usize(idx),
                            generation: slot.generation,
                        },
                        slot.other,
                    );

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

    // ── snapshot / iter_unsafe ───────────────────────────────────────────

    /// Returns a snapshot of all `(key, &output)` pairs at the current moment.
    /// Ignores future inserts. Heap-allocates one `Vec`.
    #[inline]
    pub fn snapshot(&self) -> Vec<(K, &C::Output)> {
        unsafe {
            let mut vec = Vec::with_capacity(self.len());
            vec.extend(self.iter_unsafe());
            vec
        }
    }

    /// Returns a snapshot of `&output` references only.
    #[inline]
    pub fn snapshot_refs(&self) -> Vec<&C::Output> {
        unsafe {
            let mut vec = Vec::with_capacity(self.len());
            vec.extend(self.iter_unsafe().map(|x| x.1));
            vec
        }
    }

    /// Returns a snapshot of keys only.
    #[inline]
    pub fn snapshot_keys(&self) -> Vec<K> {
        unsafe {
            let mut vec = Vec::with_capacity(self.len());
            vec.extend(self.iter_unsafe().map(|x| x.0));
            vec
        }
    }

    /// # Safety
    /// No mutation (including `insert`) may occur while iterating.
    #[inline]
    pub unsafe fn iter_unsafe(&self) -> impl Iterator<Item = (K, &C::Output)> {
        (&*self.slots.get())
            .iter()
            .enumerate()
            .filter_map(|(idx, slot_cell)| {
                let slot = &*slot_cell.get();
                if is_occupied_by_generation(slot.generation) {
                    Some((
                        K::from_parts(
                            KeyData {
                                idx: K::Idx::from_usize(idx),
                                generation: slot.generation,
                            },
                            slot.other,
                        ),
                        slot.item.ref_output(),
                    ))
                } else {
                    None
                }
            })
    }

    // ── clone helpers ───────────────────────────────────────────────────

    /// A more efficient clone than `Clone::clone`, but **UB** if the `Clone`
    /// implementation of the stored type mutates the map.
    #[inline]
    pub unsafe fn clone_efficiently(&self) -> Self
    where
        C: SlotItemClone<K>,
    {
        Self {
            num_elements: self.num_elements.clone(),
            phantom: PhantomData,
            next_free: self.next_free.clone(),
            extra_state: K::Extra::EMPTY_STATE,
            slots: UnsafeCell::new(
                (&*self.slots.get())
                    .iter()
                    .map(|slot_cell| {
                        let slot = &*slot_cell.get();
                        UnsafeCell::new(Slot {
                            generation: slot.generation,
                            other: slot.other,
                            item: slot
                                .item
                                .clone_item(is_occupied_by_generation(slot.generation)),
                        })
                    })
                    .collect(),
            ),
        }
    }

    /// Safe wrapper around [`clone_efficiently`](Self::clone_efficiently):
    /// the `&mut self` borrow prevents the stored type's `Clone` from
    /// mutating the map.
    #[inline]
    pub fn clone_efficiently_mut(&mut self) -> Self
    where
        C: SlotItemClone<K>,
    {
        unsafe { self.clone_efficiently() }
    }

    // ── helpers used by Clone impls in stable_gen_map / stable_deref_gen_map

    /// Build a `GenMap` from pre-built parts. Used by custom `Clone` impls.
    ///
    /// # Safety
    /// Caller must ensure the parts are self-consistent (matching free-list,
    /// generation parity, element count).
    #[inline]
    pub(crate) unsafe fn from_raw_parts(
        slots: Vec<UnsafeCell<Slot<C, K>>>,
        next_free: Option<K::Idx>,
        num_elements: usize,
    ) -> Self {
        Self {
            slots: UnsafeCell::new(slots),
            next_free: Cell::new(next_free),
            phantom: PhantomData,
            num_elements: Cell::new(num_elements),
            // Clone targets always get a fresh extra state so new inserts
            // into the clone produce their own map id.
            extra_state: K::Extra::EMPTY_STATE,
        }
    }
}

// ─── get_mut / get_by_index_only_mut (requires SlotItemMutOutput) ────────────

impl<K: Key, C: SlotItemMutOutput<K>> GenMap<K, C> {
    /// Unique-reference lookup by key.
    #[inline]
    pub fn get_mut(&mut self, k: K) -> Option<&mut C::Output> {
        let key_data = k.data();
        let slots = self.slots.get_mut();
        let slot = slots.get_mut(key_data.idx.into_usize())?.get_mut();
        if slot.generation != key_data.generation {
            return None;
        }
        if !K::Extra::validate(k.extra(), slot.other) {
            return None;
        }
        Some(unsafe { slot.item.mut_output() })
    }

    /// Mutable lookup by index only (ignores generation).
    #[inline]
    pub fn get_by_index_only_mut(&mut self, idx: K::Idx) -> Option<(K, &mut C::Output)> {
        let slot = self.slots.get_mut().get_mut(idx.into_usize())?.get_mut();
        if is_occupied_by_generation(slot.generation) {
            Some((
                K::from_parts(
                    KeyData {
                        idx,
                        generation: slot.generation,
                    },
                    slot.other,
                ),
                unsafe { slot.item.mut_output() },
            ))
        } else {
            None
        }
    }
}

// ─── IterMut ─────────────────────────────────────────────────────────────────

/// Mutable iterator over all occupied elements of a [`GenMap`].
///
/// Created by [`GenMap::iter_mut`].
pub struct IterMut<'a, K: Key, C: SlotItem<K>> {
    inner: std::slice::IterMut<'a, UnsafeCell<Slot<C, K>>>,
    idx: usize,
}

impl<'a, K: Key, C: SlotItem<K>> Iterator for IterMut<'a, K, C> {
    type Item = (K, &'a mut C::Stored);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(slot_cell) = self.inner.next() {
            let idx = self.idx;
            self.idx += 1;

            let slot = slot_cell.get_mut();
            if !is_occupied_by_generation(slot.generation) {
                continue;
            }

            let value: &mut C::Stored = unsafe { slot.item.stored_mut() };
            let key = K::from_parts(
                KeyData {
                    idx: K::Idx::from_usize(idx),
                    generation: slot.generation,
                },
                slot.other,
            );
            return Some((key, value));
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.inner.len()))
    }
}

impl<K: Key, C: SlotItem<K>> GenMap<K, C> {
    /// Mutable iterator over all occupied elements.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, C> {
        IterMut {
            inner: self.slots.get_mut().iter_mut(),
            idx: 0,
        }
    }
}

impl<'a, K: Key, C: SlotItem<K>> IntoIterator for &'a mut GenMap<K, C> {
    type Item = (K, &'a mut C::Stored);
    type IntoIter = IterMut<'a, K, C>;

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
pub struct Drain<'a, K: Key, C: SlotItem<K>> {
    map: &'a mut GenMap<K, C>,
    idx: usize,
}

impl<'a, K: Key, C: SlotItem<K>> Iterator for Drain<'a, K, C> {
    type Item = (K, C::Stored);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let idx = self.idx;

            let (generation, other) = {
                let slots = self.map.slots.get_mut();
                if idx >= slots.len() {
                    return None;
                }
                self.idx += 1;
                let slot = slots[idx].get_mut();
                if !is_occupied_by_generation(slot.generation) {
                    continue;
                }
                (slot.generation, slot.other)
            };

            let key = K::from_parts(
                KeyData {
                    idx: K::Idx::from_usize(idx),
                    generation,
                },
                other,
            );
            let value = unsafe { self.map.remove(key).unwrap_unchecked() };
            return Some((key, value));
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.map.len()))
    }
}

impl<'a, K: Key, C: SlotItem<K>> Drop for Drain<'a, K, C> {
    fn drop(&mut self) {
        while self.next().is_some() {}
    }
}

impl<K: Key, C: SlotItem<K>> GenMap<K, C> {
    /// Removes all elements and returns them as an iterator.
    /// The map is left empty but retains its allocated capacity.
    #[inline]
    pub fn drain(&mut self) -> Drain<'_, K, C> {
        Drain { map: self, idx: 0 }
    }
}

// ─── IntoIter (owning) ──────────────────────────────────────────────────────

/// Owning iterator over all occupied elements of a [`GenMap`].
///
/// Created by calling `.into_iter()` on a `GenMap`. Consumes the map.
pub struct IntoIter<K: Key, C: SlotItem<K>> {
    inner: std::vec::IntoIter<UnsafeCell<Slot<C, K>>>,
    idx: usize,
    _marker: PhantomData<K>,
}

impl<K: Key, C: SlotItem<K>> Iterator for IntoIter<K, C> {
    type Item = (K, C::Stored);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(mut slot_cell) = self.inner.next() {
            let idx = self.idx;
            self.idx += 1;

            let slot = slot_cell.get_mut();
            if !is_occupied_by_generation(slot.generation) {
                continue;
            }

            let value = unsafe { slot.item.take_occupied() };

            let key_data = KeyData {
                generation: slot.generation,
                idx: K::Idx::from_usize(idx),
            };
            let other = slot.other;

            // prevent Slot::drop from double-dropping
            slot.generation = K::Gen::zero();

            let key = K::from_parts(key_data, other);
            return Some((key, value));
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.inner.len()))
    }
}

impl<K: Key, C: SlotItem<K>> IntoIterator for GenMap<K, C> {
    type Item = (K, C::Stored);
    type IntoIter = IntoIter<K, C>;

    /// Consumes the map into an owning iterator.
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.slots.into_inner().into_iter(),
            idx: 0,
            _marker: PhantomData,
        }
    }
}
