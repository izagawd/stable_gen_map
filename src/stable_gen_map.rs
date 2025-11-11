use crate::key::{is_occupied_by_generation, Key, KeyData};
use crate::numeric::Numeric;
use num_traits::{CheckedAdd, One, Zero};
use std::array::from_fn;
use std::cell::{Cell, UnsafeCell};
use std::marker::PhantomData;
use std::mem::{ManuallyDrop, MaybeUninit};
use std::ops::{Deref, DerefMut, Index, IndexMut};







/// Occupancy + intrusive free list
union SlotVariant<T, K: Key> {
    occupied: ManuallyDrop<T>,
    vacant: Option<K::Idx>,
}

impl<T, K: Key> SlotVariant<T, K> {


}

pub(crate) struct Slot<T, K: Key> {
    item: Box<SlotVariant<T, K>>,
    generation: K::Gen,
}
impl<T, K: Key> Drop for Slot<T, K>{
    fn drop(&mut self) {
        if is_occupied_by_generation(self.generation){
          unsafe{  ManuallyDrop::drop(&mut self.item.occupied) }
        }
    }
}
impl<T, K: Key> Slot<T, K> {
    /// If occupied, take the value and make this slot Vacant(None).
    /// If already vacant, leave as-is and return None.
    #[inline]
    fn take_occupied(&mut self) -> Option<T> {
        use std::mem;

        let mut matched = mem::replace(&mut self.item,  Box::new( SlotVariant{vacant: None}));
        if is_occupied_by_generation(self.generation){
           unsafe{ Some(ManuallyDrop::take(&mut matched.occupied)) }
        } else{
            None
        }
    }

    #[inline]
    unsafe fn clone(&self) -> Self where T: Clone {
        let item =if is_occupied_by_generation(self.generation){
            SlotVariant{occupied: ManuallyDrop::new( self.item.occupied.deref().clone())}
        } else{
            SlotVariant{vacant:self.item.vacant.clone() }
        };
        Self { item: Box::new(item), generation: self.generation }
    }

}





/// Stable Gen Map with intrusive free list.
pub struct StableGenMap<K: Key, T> {
    pub(crate) slots: UnsafeCell<Vec<UnsafeCell<Slot<T, K>>>>,
    next_free: Cell<Option<K::Idx>>, // head of free-list
    phantom: PhantomData<fn(K)>,
    num_elements: Cell<usize>,
}



impl<K: Key, T> Index<K>
for StableGenMap<K, T>
{
    type Output = T;
    fn index(&self, key: K) -> &Self::Output {
        self.get(key).unwrap()
    }
}

impl<K: Key, T> IndexMut<K>
for StableGenMap<K, T>
{
    fn index_mut(&mut self, key: K) -> &mut Self::Output {
        self.get_mut(key).unwrap()
    }
}


struct RemoveArguments<'a, K: Key, T> {
    slot: &'a mut Slot<T, K>,
    key: K,
    num_elements: &'a Cell<usize>,
    next_free: &'a Cell<Option<K::Idx>>,
}

impl<K: Key, T> StableGenMap<K, T>
{

    /// Returns a snapshot of the map at the current moment. it ignores future inserts
    /// NOTE: this does a heap allocation, and a heap deallocation when the snapshot drops
    #[inline]
    pub fn snapshot(&self) -> Vec<(K, &T)> {
        unsafe{
            let mut vec = Vec::with_capacity(self.len());
            vec.extend(self.iter_unsafe());
            vec
        }
    }

    #[inline]
    /// Iteration with this method is only safe if no mutation of the map occurs while iterating, which can happen even with safe code. For example, inserting while iterating with this is UB
    pub unsafe fn iter_unsafe(&self) -> impl Iterator<Item=(K, &T)> {
        (&*self.slots.get())
            .iter()
            .enumerate()
            .map(|(idx, slot)| {
                let slot_pure = (&*slot.get());
                if is_occupied_by_generation(slot_pure.generation) {
                    Some(
                        (K::from(KeyData{idx: K::Idx::from_usize(idx),generation: slot_pure.generation}),
                         slot_pure.item.occupied.deref()))
                } else{
                    None
                }
            })
            .flatten()
    }
    /// Returns a snapshot of the map at the current moment. it ignores future inserts
    /// NOTE: this does a heap allocation, and a heap deallocation when the snapshot drops
    #[inline]
    pub fn snapshot_iter(&self) -> <Vec<(K, &T)> as IntoIterator>::IntoIter {
        self.snapshot().into_iter()
    }

    /// Returns a snapshot of the current value references only (no keys).
    /// Future inserts are ignored. Allocates a single `Vec<&T>`.
    #[inline]
    pub fn snapshot_ref_only(&self) -> Vec<&T> {

        unsafe{
            let mut vec = Vec::with_capacity(self.len());
            vec.extend(
                self
                    .iter_unsafe()
                    .map(|x| x.1)
            );
            vec
        }
    }

    /// Returns a snapshot of the current keys only (no references).
    /// Future inserts are ignored. Allocates a single `Vec<K>`.
    #[inline]
    pub fn snapshot_key_only(&self) -> Vec<K> {
        unsafe{
            let mut vec = Vec::with_capacity(self.len());
            vec.extend(
                self
                    .iter_unsafe()
                    .map(|x| x.0)
            );
            vec
        }

    }


    /// Creates a new, empty StableGenMap
    #[inline]
    pub const fn new() -> Self {
        Self {
            slots: UnsafeCell::new(Vec::new()),
            next_free: Cell::new(None),
            phantom: PhantomData,
            num_elements: Cell::new(0),
        }
    }



    /// A more efficient Clone operation than the Clone::clone implementation, but if the `Clone` implementation of `T` mutates the map, UB occurs
    #[inline]
    pub unsafe fn clone_efficiently(&self) -> Self where T: Clone {
        Self{
            num_elements: self.num_elements.clone(),
            phantom: PhantomData,
            next_free: self.next_free.clone(),
            slots: UnsafeCell::new((&*self.slots.get()).iter().map(|x| UnsafeCell::new((&*x.get()).clone())).collect()),
        }
    }
    /// a more efficient Clone operation than the Clone::clone implementation. since done with a mutable reference, the `Clone` implementation of `T` cannot mutate the map without unsafe code
    /// so `clone_efficiently_mut` is safe
    #[inline]
    pub fn clone_efficiently_mut(&mut self) -> Self where T: Clone {
        unsafe {
            self.clone_efficiently()
        }

    }
    /// Gets a unique reference to an element
    #[inline]
    pub fn get_mut(&mut self, k: K) -> Option<&mut T> {
        let key_data = k.data();

        let slots = self.slots.get_mut();
        let mut slot = slots .get_mut(key_data.idx.into_usize())?.get_mut();
        if slot.generation != key_data.generation {
            return None;
        }
        let variant: &mut SlotVariant<T, K> = &mut slot.item;
        unsafe { Some(variant.occupied.deref_mut()) }
    }

    /// gets by index, ignores generational count
    #[inline]
    pub fn get_by_index_only(&self, idx: K::Idx) -> Option<(K, &T)> {

        let slots = unsafe { &*self.slots.get() };

        unsafe{
            let slot = &*slots.get(idx.into_usize())?.get();
            if is_occupied_by_generation(slot.generation) {
                Some((K::from(KeyData{idx,generation: slot.generation}) ,slot.item.occupied.deref()))
            } else {
                None
            }
        }
    }

    /// gets by index, ignores generational count
    #[inline]
    pub fn get_by_index_only_mut(&mut self, idx: K::Idx) -> Option<(K, &mut T)> {

        let slots = self.slots.get_mut();
        let slot = slots.get_mut(idx.into_usize())?.get_mut();
        unsafe{
            if is_occupied_by_generation(slot.generation) {
                Some((K::from(KeyData{idx,generation: slot.generation}) ,slot.item.occupied.deref_mut()))
            } else {
                None
            }
        }
    }

    /// Gets a shared reference to an element
    #[inline]
    pub fn get(&self, k: K) -> Option<&T> {
        unsafe{
            let key_data = k.data();

            let slots = &*self.slots.get();
            let mut slot = &*slots.get(key_data.idx.into_usize())?.get();
            if slot.generation != key_data.generation {
                return None;
            }
            let variant = &slot.item;
            Some(variant.occupied.deref())
        }

    }

    /// Empties the map, removing all elements
    #[inline]
    pub fn clear(&mut self) {

        let slots_len = self.slots.get_mut().len();

        for idx in 0..slots_len {
            let generation = unsafe {

                self.slots.get_mut().get_unchecked_mut(idx)
                    .get_mut()
                    .generation
            };
            let key = K::from(KeyData { idx: K::Idx::from_usize(idx), generation });
            let _ = self.remove(key);
        }

        debug_assert_eq!(self.len(), 0);
    }
    /// Retains only elements for which `f(key, &mut value)` returns true.
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(K, &mut T) -> bool,
    {
        unsafe {
            let slots: &mut Vec<_> =self.slots.get_mut();

            for (idx, slot) in slots.iter_mut().enumerate() {
                    let slot = slot.get_mut();
                    if is_occupied_by_generation(slot.generation) {
                        let value = slot.item.occupied.deref_mut();

                        let key_data = KeyData {
                            idx: K::Idx::from_usize(idx),
                            generation: slot.generation,
                        };
                        let key = K::from(key_data);

                        if !f(key, value) {
                            // Use shared removal logic (no generation check, we know this is current).
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
    /// Gets the number of elements in the map
    #[inline]
    pub fn len(&self) -> usize {
        self.num_elements.get()
    }


    /// This to allow code repetition without the borrow checker getting in the way
    #[inline]
    unsafe fn remove_split_data<const DO_GENERATION_CHECK: bool>(args: RemoveArguments<K, T>,
    ) -> Option<T> {


        let slot = args.slot;
        let num_elements = args.num_elements;
        let next_free = args.next_free;
        let key_data = args.key.data();

        if DO_GENERATION_CHECK {
            if  slot.generation != key_data.generation{
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
                slot.item.vacant = old_head;
                next_free.set(Some(key_data.idx));
            }
            None => {

                slot.item.vacant = None;
            }
        }

        Some(value)
    }
    /// Removes an element by key, returning its owned value.
    /// Removes only with &mut self. This is safe because the borrow checker
    /// prevents calling this while any &'_ T derived from &self is alive.
    /// A use case will be in, for example, freeing memory after the end of a frame in a video game
    #[inline]
    pub fn remove(&mut self, k: K) -> Option<T> {
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

    /// Inserts a value given by the inputted function into the map. The key where the
    /// value will be stored is passed into the inputted function
    /// # Examples
    /// ```
    /// # use stable_gen_map::key::DefaultKey;
    /// use stable_gen_map::stable_gen_map::{ StableGenMap};
    /// let mut sm = StableGenMap::new();
    /// #[derive(Eq,PartialEq, Debug)]
    /// struct KeyHolder{
    ///     key: DefaultKey
    /// }
    /// let (key, reference) = sm.insert_with_key(|k| KeyHolder{
    ///     key: k
    /// });
    /// assert_eq!(sm[key], KeyHolder{key});
    /// ```
    #[inline]
    pub fn insert_with_key(&self, func: impl FnOnce(K) -> T) -> (K, &T) {
        self.try_insert_with_key::<()>(|key| Ok(func(key))).unwrap()
    }

    /// Same as insert_with_key but allowing the closure to return a Result.
    /// Inserts a value given by the inputted function into the map. The key where the
    /// value will be stored is passed into the inputted function.
    /// This is useful to store values that contain their own key.
    /// This version allows the closure to return a `Result`, so you can propagate errors.
    /// # Examples
    /// ```rust
    /// use stable_gen_map::key::DefaultKey;
    /// use stable_gen_map::stable_gen_map::StableGenMap;
    ///
    /// #[derive(Eq, PartialEq, Debug)]
    /// struct KeyHolder {
    ///     key: DefaultKey,
    /// }
    ///
    /// let sm = StableGenMap::new();
    ///
    /// let (key, reference) = sm
    ///     .try_insert_with_key::<()>(|k| Ok(KeyHolder { key: k }))
    ///     .unwrap();
    ///
    /// assert_eq!(sm[key], KeyHolder { key });
    /// // optional: also prove `reference` really points to the same element:
    /// assert!(std::ptr::eq(reference, &sm[key]));
    /// ```
    #[inline]
    pub fn try_insert_with_key<E>(
        &self,
        func: impl FnOnce(K) -> Result<T, E>,
    ) -> Result<(K, &T), E> {
        unsafe {
            let slots = &mut *self.slots.get();

            // Case 1: reuse a free slot from the intrusive free list.
            let (idx, generation) =  if let Some(idx) = self.next_free.get() {
                let slot = slots.get_unchecked_mut(idx.into_usize()).get_mut();

                let next = slot.item.vacant;
                self.next_free.set(next);

                // Mark as reserved: not linked in the free list anymore.
                slot.item.vacant = None;

                let generation = slot.generation;
                (idx, generation)
            } else {
                let generation = K::Gen::zero();
                let idx = K::Idx::from_usize(slots.len());
                slots.push(UnsafeCell::new(
                    Slot {
                        generation ,
                        item: Box::new(SlotVariant{
                            vacant: None,
                        }),
                    }
                ));
                (idx, generation)
            };

            let key = K::from(KeyData {
                idx,
                generation: generation.checked_add(&K::Gen::one()).unwrap() // increment only the keys gen by 1, so the key of the inserter isn't valid until after the slot
                // has incremented their key, which would be after it confirms the func call didn't have any errors/panics
            });

            // RAII guard: if func panics/returns Err, put this index
            // back into the free list using the *current* head.
            let guard = FreeGuard {
                map: self,
                idx,
            };

            let value = func(key)?; // may panic / Err

            // Success: don't put it back into free list.
            guard.commit();

            // Re-borrow pages because func(key) may have re-entered and
            // caused pages to grow, etc.
            let slots = &*self.slots.get();
            let slot = &mut *slots.get_unchecked(idx.into_usize()).get();

            slot.item.occupied = ManuallyDrop::new(value);

            // no need for overflow check here, as that was done when incrementing generation for key
            slot.generation += K::Gen::one(); // add one to match up with keys idx, since the function has succeeded from this point
            self.num_elements.set(self.num_elements.get() + 1);

            // Build &T from ManuallyDrop.
            let value_ref: &T = slot.item.occupied.deref();

            Ok((key, value_ref))
        }
    }

    /// Simple insert. When it inserts, it returns the key and reference.
    /// # Examples
    /// ```rust
    /// use stable_gen_map::key::DefaultKey;
    /// use stable_gen_map::stable_gen_map::StableGenMap;
    /// let sm = StableGenMap::<DefaultKey,_>::new();
    /// let (key, reference) = sm.insert(4);
    /// assert_eq!(*reference, 4);
    /// assert_eq!(*sm.get(key).unwrap(), 4);
    ///```
    #[inline]
    pub fn insert(&self, value: T) -> (K, &T) {
        self.insert_with_key(|_| value)
    }
}

// Mutable iterator over flat slots
impl<'a, K: Key, T> Iterator for IterMut<'a, K, T> {
    type Item = (K, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            while self.ptr != self.end {
                let current = self.ptr;
                self.ptr = self.ptr.add(1);

                let idx = self.idx;
                self.idx += 1;

                // current: *mut UnsafeCell<Slot<T, K>>
                let slot_cell: &mut UnsafeCell<Slot<T, K>> = &mut *current;
                let slot= &mut *slot_cell.get();

                if !is_occupied_by_generation(slot.generation) {
                    continue;
                }

                let value: &mut T = slot.item.occupied.deref_mut();

                let key_idx = K::Idx::from_usize(idx);
                let key_data = KeyData {
                    idx: key_idx,
                    generation: slot.generation,
                };
                let key = K::from(key_data);

                return Some((key, value));
            }

            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, None)
    }
}
impl<K: Key, T: Clone> Clone for StableGenMap<K, T> {
    fn clone(&self) -> Self {
        unsafe {
            // Snapshot payload for each slot:
            // either a &T (for occupied) or the next_free index (for vacant).
            enum Snap<'a, K: Key, T> {
                Occupied(&'a T),
                Vacant(Option<K::Idx>),
            }

            let num_elements = self.len();
            let next_free = self.next_free.get();
            let slots_ref: &Vec<UnsafeCell<Slot<T, K>>> = &*self.slots.get();

            // 1) SNAPSHOT PHASE: read slots once, no T::clone yet.
            //
            //    We gather a Vec of (generation, Snap) for every slot in the Vec.
            //    After this, we never touch self.slots / self.next_free again.
            let mut snapshot: Vec<(K::Gen, Snap<'_, K, T>)> =
                Vec::with_capacity(slots_ref.len());

            for cell in slots_ref.iter() {
                let slot: &Slot<T, K> = &*cell.get();
                let generation = slot.generation;
                let variant: &SlotVariant<T, K> = &slot.item;

                let snap = if is_occupied_by_generation(generation) {
                    // SAFETY: in the "occupied" branch we read the occupied field.
                    Snap::Occupied(variant.occupied.deref())
                } else {
                    // Vacant: we read the vacant field.
                    Snap::Vacant(variant.vacant)
                };

                snapshot.push((generation, snap));
            }

            // 2) REBUILD PHASE: build a fresh Vec<UnsafeCell<Slot<..>>> from the snapshot.
            //
            //    Now we *do* call T::clone, so user code can re-enter and mutate
            //    the ORIGINAL map via &self.insert(...). That’s fine:
            //    we never touch self.slots again, and our &T references remain valid
            //    because T is stored inside Box<SlotVariant<..>> (stable heap allocation).
            let mut new_slots: Vec<UnsafeCell<Slot<T, K>>> =
                Vec::with_capacity(snapshot.len());

            for (generation, snap) in snapshot {
                let item = match snap {
                    Snap::Occupied(vref) => {
                        SlotVariant {
                            occupied: ManuallyDrop::new(vref.clone()),
                        }
                    }
                    Snap::Vacant(next) => SlotVariant { vacant: next },
                };

                let slot = Slot {
                    generation,
                    item: Box::new(item),
                };

                new_slots.push(UnsafeCell::new(slot));
            }

            Self {
                slots: UnsafeCell::new(new_slots),
                next_free: Cell::new(next_free),
                phantom: PhantomData,
                num_elements: Cell::new(num_elements),
            }
        }
    }
}

pub struct IterMut<'a, K: Key, T> {
    // Pointer into the slots Vec (current position)
    ptr: *mut UnsafeCell<Slot<T, K>>,
    // One-past-the-end pointer
    end: *mut UnsafeCell<Slot<T, K>>,
    // Current index in the Vec (for building keys)
    idx: usize,
    // Tie lifetime to "&mut T" so we can yield &'a mut T
    _marker: PhantomData<&'a mut T>,
}

impl<K: Key, T> StableGenMap<K, T> {
    /// Gets a mutable iterator of the map, allowing mutable iteration between all elements
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, T> {
        unsafe {
            let slots: &mut Vec<UnsafeCell<Slot<T, K>>> = &mut *self.slots.get();
            let ptr = slots.as_mut_ptr();
            let len = slots.len();
            let end = ptr.add(len);

            IterMut {
                ptr,
                end,
                idx: 0,
                _marker: PhantomData,
            }
        }
    }
}
// Owning iterator (consumes map)
pub struct IntoIter<K: Key, T> {
    // We keep the Vec so the underlying allocation stays alive.
    slots: Vec<UnsafeCell<Slot<T, K>>>,
    // Pointer into slots (current)
    ptr: *mut UnsafeCell<Slot<T, K>>,
    // One-past-the-end
    end: *mut UnsafeCell<Slot<T, K>>,
    // Current index for key.idx
    idx: usize,
    _marker: PhantomData<K>,
}

impl<K: Key, T> Iterator for IntoIter<K, T> {
    type Item = (K, T);

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            while self.ptr != self.end {
                let current = self.ptr;
                self.ptr = self.ptr.add(1);

                let idx = self.idx;
                self.idx += 1;

                let slot_cell: &mut UnsafeCell<Slot<T, K>> = &mut *current;
                let slot: &mut Slot<T, K> = &mut *slot_cell.get();

                if !is_occupied_by_generation(slot.generation) {
                    continue;
                }

                // Take the value out of the occupied variant
                let value = ManuallyDrop::take(&mut slot.item.occupied);

                let key_idx = K::Idx::from_usize(idx);
                let key_data = KeyData {
                    generation: slot.generation,
                    idx: key_idx,
                };

                // Bump generation so drop of the map (if any) won't drop T again.
                slot.generation += K::Gen::one();

                let key = K::from(key_data);
                return Some((key, value));
            }

            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, None)
    }
}

impl<K: Key, T> IntoIterator for StableGenMap<K, T> {
    type Item = (K, T);
    type IntoIter = IntoIter<K, T>;

    /// Converts the map into an iterator that owns all elements. This operation consumes the map
    fn into_iter(self) -> Self::IntoIter {
        // Take ownership of the underlying Vec<UnsafeCell<Slot<...>>>
        let mut slots_vec = self.slots.into_inner();
        let ptr = slots_vec.as_mut_ptr();
        let len = slots_vec.len();
        let end = unsafe { ptr.add(len) };

        IntoIter {
            slots: slots_vec,
            ptr,
            end,
            idx: 0,
            _marker: PhantomData,
        }
    }
}
// into_iter for &mut map uses IterMut
impl<'a, K: Key, T> IntoIterator
for &'a mut StableGenMap<K, T>
{
    type Item = (K, &'a mut T);
    type IntoIter = IterMut<'a, K, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}




// RAII "reservation" for a single index in the intrusive free list.
struct FreeGuard<'a, K: Key, T> {
    map: &'a StableGenMap<K, T>,
    idx: K::Idx,
}

impl<'a, K: Key, T> FreeGuard<'a, K, T> {
    fn commit(self) {
        std::mem::forget(self);
    }
}

impl<'a, K: Key, T> Drop
for FreeGuard<'a, K, T>
{
    fn drop(&mut self) {
        unsafe {

            let slots = &mut *self.map.slots.get();
            let slot = slots.get_unchecked_mut(self.idx.into_usize()).get_mut();




            // increment generation to invalidate previous indexes
            if let Some(checked_add) =
                slot.generation.checked_add(&(K::Gen::one() + K::Gen::one())) // add by two to maintain evenness, cuz even means vacant, and thats what it is
            {
                slot.generation = checked_add;

                let old_head = self.map.next_free.get();
                slot.item.vacant = old_head;
                self.map.next_free.set(Some(self.idx));
            }
        }
    }
}
