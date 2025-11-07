use crate::key::{Key, KeyData};
use crate::numeric::Numeric;
use crate::stable_gen_map::SlotVariant::{Occupied, Vacant};
use aliasable::boxed::AliasableBox;
use num_traits::{CheckedAdd, One, Zero};
use std::cell::{Cell, UnsafeCell};
use std::collections::TryReserveError;
use std::hint;
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

struct Slot<T: ?Sized, K: Key> {
    generation: K::Gen,
    item: SlotVariant<T, K>,
}
impl<T: Clone, K: Key> Clone for SlotVariant<T, K> {
    fn clone(&self) -> Self {
        match self {
            SlotVariant::Occupied(za_box) => {
                SlotVariant::Occupied(AliasableBox::from_unique(Box::new( (*za_box).clone())))
            }
            Vacant(free) => {
                SlotVariant::Vacant(*free)
            }
        }
    }
}
impl<T: ?Sized, K: Key> Slot<T, K> {}
impl<T: Clone, K: Key> Clone for Slot<T, K> {
    fn clone(&self) -> Self {
        Self{
            generation: self.generation,
            item:   self.item.clone(),
        }
    }
}


pub struct IterMut<'a, K: Key, T: ?Sized> {
    ptr: *mut Slot<T,K>,
    len: usize,
    idx: usize,
    _marker: PhantomData<&'a mut T>,
    _key_marker: PhantomData<K>,
}

impl<K: Key, T: ?Sized> StableGenMap<K, T> where K::Idx : Zero {
    /// Gets a mutable iterator of the map, allowing mutable iteration between all elements
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, T> {
        let slots = self.slots.get_mut(); // &mut Vec<Slot<T>>
        IterMut {
            ptr: slots.as_mut_ptr(),
            len: slots.len(),
            idx: 0,
            _marker: PhantomData,
            _key_marker: PhantomData,
        }
    }
}

impl<'a, K: Key + 'a , T: ?Sized> Iterator for IterMut<'a, K, T> where K::Idx : Numeric, K::Gen: Numeric {
    type Item = (K, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.len {
            let idx = self.idx;
            self.idx += 1;

            let slot: &mut Slot<T, K> = unsafe { &mut *self.ptr.add(idx) };

            let boxed = match &mut slot.item {
                SlotVariant::Occupied(b) => b,
                _ => continue,
            };

            let key_data = KeyData {
                idx: K::Idx::from_usize(idx),
                generation: slot.generation,
            };
            let key = K::from(key_data);

            let value: &mut T = boxed.as_mut();

            return Some((key, value));
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining_slots = self.len.saturating_sub(self.idx);
        (0, Some(remaining_slots))
    }
}

impl<'a, K: Key, T: ?Sized> IntoIterator for &'a mut StableGenMap<K, T> where K::Idx : Numeric, <K as Key>::Gen: Numeric {
    type Item = (K, &'a mut T);
    type IntoIter = IterMut<'a, K, T>;
    

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}





pub struct StableGenMap<K: Key, T: ?Sized> {
    slots: UnsafeCell<Vec<Slot<T, K>>>,
    phantom: PhantomData<fn(K)>,
    next_free: Cell<Option<K::Idx>>,
    num_elements: Cell<usize>,
}

impl<K: Key,T: ?Sized> Index<K> for StableGenMap<K,T> {
    type Output = T;
    fn index(&self, key: K) -> &Self::Output{
        self.get(key).unwrap()
    }
}
impl<K: Key,T: ?Sized> IndexMut<K> for StableGenMap<K,T> {

    fn index_mut(&mut self, key: K) -> &mut Self::Output{
        self.get_mut(key).unwrap()
    }
}

enum SlotVariant<T: ?Sized, K: Key>{
    Occupied(AliasableBox<T>),
    Vacant(Option<K::Idx>),
}

pub struct IntoIter<K: Key, T: ?Sized> {
    slots: std::vec::IntoIter<Slot<T, K>>,
    idx: usize,
    _marker: PhantomData<K>,
}

impl<K: Key, T: ?Sized> Iterator for IntoIter<K, T> where <K as Key>::Idx : Numeric{
    type Item = (K, Box<T>);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(slot) = self.slots.next() {
            let idx = self.idx;
            self.idx += 1;

            let alias = match slot.item {
                Occupied(a) => a,
                _ => continue,
            };

            let key_data = KeyData {
                idx: K::Idx::from_usize(idx),
                generation: slot.generation,
            };
            let key = K::from(key_data);

            let boxed = AliasableBox::into_unique(alias);
            return Some((key, boxed));
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining_slots = self.slots.len().saturating_sub(self.idx);
        (0, Some(remaining_slots))
    }
}

impl<K: Key, T: ?Sized> IntoIterator for StableGenMap<K, T> where <K as Key>::Idx: Numeric{
    type Item = (K, Box<T>);
    type IntoIter = IntoIter<K, T>;

    /// Converts the map into an iterator that owns all elements. This operation consumes the map
    fn into_iter(self) -> Self::IntoIter {
        let slots_vec = self.slots.into_inner();
        IntoIter {
            slots: slots_vec.into_iter(),
            idx: 0,
            _marker: PhantomData,
        }
    }
}

// RAII "reservation" for a single index in `free`.
struct FreeGuard<'a, K: Key, T: ?Sized> {
    map: &'a StableGenMap<K, T>,
    idx: K::Idx,
}

impl<'a, K: Key, T: ?Sized> FreeGuard<'a, K, T> {
    fn commit(self) {
        std::mem::forget(self);
    }
}

impl<'a, K: Key, T: ?Sized> Drop for FreeGuard<'a, K, T> {
    fn drop(&mut self) {

        unsafe {

            let slots_mut = &mut *self.map.slots.get();
            // increment generation to invalidate previous indexes
            let generation = &mut slots_mut.get_unchecked_mut(self.idx.into_usize()).generation;
            let checked_add_maybe = generation.checked_add(&K::Gen::one());
            if let Some(checked_add) = checked_add_maybe {
                *generation  = checked_add;
                let old_head = self.map.next_free.get();
                 slots_mut.get_unchecked_mut(self.idx.into_usize()).item = Vacant(old_head);
                self.map.next_free.set(Some(self.idx));


            }

        }
    }
}


impl<K: Key, T: Clone> Clone for StableGenMap<K,T> {
    fn clone(&self) -> Self {
        unsafe {
            unimplemented!()
        }
    }
}
impl<T: ?Sized, K: Key> SlotVariant<T, K> where K::Idx : Zero {
    fn is_occupied(&self) -> bool {
        matches!(self, Occupied(_))
    }
    /// If occupied, take the value and make this slot Vacant(None).
    /// If already vacant, leave as-is and return None.
    #[inline]
    fn take_occupied(&mut self) -> Option<AliasableBox<T>> {
        use std::mem;

        match mem::replace(self, SlotVariant::Vacant(None)) {
            Occupied(boxed) => Some(boxed),
            vacant @ Vacant(_) => {
                // Already vacant; restore the previous vacant state.
                *self = vacant;
                None
            }
        }
    }

    #[inline]
    unsafe fn next_free_unchecked(&self) -> Option<K::Idx> {
        match self{
            Vacant(next_free) => *next_free,
            Occupied(_) => {
                hint::unreachable_unchecked()
            }
        }
    }
}
impl<K: Key,T: ?Sized> StableGenMap<K,T> {





    /// Returns a snapshot of the map at the current moment. it ignores future inserts
    /// NOTE: this does a heap allocation, and a heap deallocation when the snapshot drops
    #[inline]
    pub fn snapshot(&self) -> Vec<(K, &T)> {
        unsafe{
            let mut vec = Vec::with_capacity(self.len());
            vec.extend(
                self.unsafe_iter()
            );
            return vec;
        }

    }




    /// Returns a snapshot of the current keys only (no references).
    /// Future inserts are ignored. Allocates a single `Vec<K>`.
    pub fn snapshot_key_only(&self) -> Vec<K> {
        unsafe{
            let mut vec = Vec::with_capacity(self.len());
            vec.extend(
                self.unsafe_iter()
                    .map(|(k, _)| k)
            );
             vec
        }
    }

    /// Iterator over `&T` for a snapshot of the map. Ignores future inserts.
    /// Allocates internally via `snapshot_ref_only`.
    pub fn snapshot_ref_only(&self) -> Vec<&T> {
        unsafe{
            let mut vec = Vec::with_capacity(self.len());
            vec.extend(
                self.unsafe_iter()
                    .map(|(_, r)| r)
            );
            vec
        }
    }
    /// Iteration is only safe if no mutation in the map occurs while iterating, which can happen even with safe code. For example, inserting while iterating with this is UB
    pub unsafe fn unsafe_iter(&self) -> impl Iterator<Item = (K, &T)> {
        unsafe{(&*self.slots.get())}
            .iter()
            .enumerate()
            .filter_map(|(idx, x)| {
                match x.item {
                    Occupied(ref a) => Some(
                        (K::from(KeyData{idx: K::Idx::from_usize(idx),generation: x.generation}),
                         a.as_ref())),
                    _ => None
                }
            })
        
    }

    /// Removes all elements from the map
    #[inline]
    pub fn clear(&mut self){
        self.slots.get_mut().clear();
        self.next_free.set(None);
        self.num_elements.set(0);
    }

    /// Creates a new StableGenMap, with an initial capacity. 
    /// The map will be able to hold at least `capacity` elements before a need to resize
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self{
            slots: UnsafeCell::new(Vec::with_capacity(capacity)),
            next_free: Cell::new(None),
            phantom: PhantomData,
            num_elements: Cell::new(0),
        }
    }

    /// Creates a new StableGenMap, with no elements
    #[inline]
    pub const fn new() -> Self {
        Self {
            slots: UnsafeCell::new(Vec::new()),
            next_free: Cell::new(None),
            phantom: PhantomData,
            num_elements: Cell::new(0),
        }
    }
    /// Tries to reserve capacity for at least `additional` more elements to be inserted before a resize occurs
    #[inline]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
       unsafe { &mut *self.slots.get() }.try_reserve(additional)
    }

    /// Reserves capacity for at least `additional` more elements to be inserted before a resize occurs
    #[inline]
    pub fn reserve(&self, additional: usize){
        unsafe { &mut *self.slots.get() }.reserve(additional);
    }
    /// Shared access to a value by key (no guard, plain &T).
    #[inline]
    pub fn get(&self, k: K) -> Option<&T> {

        let key_data = k.data();
        let slot = unsafe { &*self.slots.get() }.get(key_data.idx.into_usize())?;
        if  slot.generation == key_data.generation {
            match &slot.item {
                Occupied(item) => {
                    unsafe { Some(&*(item.as_ref() as *const T)) }
                },
                SlotVariant::Vacant(_) => {
                    None
                }
            }
        }
        else {
            None
        }
    }

    /// Gets a unique reference to a value when supplied a key
    #[inline]
    pub fn get_mut(&mut self, k: K) -> Option<&mut T> {

        let key_data = k.data();
        let slot = self.slots.get_mut().get_mut(key_data.idx.into_usize())?;
        if  slot.generation == key_data.generation {
            match &mut slot.item {
                Occupied(ref mut item) => {
                    // SAFETY: value is live; we never move the Box's allocation.
                    Some(item.as_mut())
                }
                _ => None
            }
        }
        else {
            None
        }
    }

    /// Removes an element of the supplied key from the map, and returns its owned value.
    /// Removes only with &mut self. This is safe because the borrow checker
    /// prevents calling this while any &'_ T derived from &self is alive.
    /// A use case will be in, for example, freeing memory after the end of a frame in a video game 
    #[inline]
    pub fn remove(&mut self, k: K) -> Option<Box<T>> {
        let key_data = k.data();
        let slot = self.slots.get_mut().get_mut(key_data.idx.into_usize())?;
        if slot.generation != key_data.generation { return None; }

        let boxed = slot.item.take_occupied()?;
        self.num_elements.set(self.num_elements.get() - 1);
        match slot.generation.checked_add(&K::Gen::one()) {
            Some(generation) => {
                slot.generation = generation;

                // 3. Link this vacant slot into the intrusive free list.
                //    head = Some(idx); slot.next_free = old_head.
                let old_head = self.next_free.get();
                slot.item = SlotVariant::Vacant(old_head);
                self.next_free.set(Some(key_data.idx));
            }
            None => {

            }
        }
        Some(AliasableBox::into_unique(boxed))

    }
    
    
    /// Returns the total amount of elements in the map
    #[inline]
    pub fn len(&self) -> usize {
        self.num_elements.get()
    }
    
    
    /// How much elements (Occupied or Vacant, doesn't matter), the stable_gen_map can hold before reallocating
    #[inline]
    pub fn capacity(&self) -> usize {
        unsafe { &*self.slots.get() }.capacity()
    }

    /// Inserts a value given by the inputted function into the map. The key where the
    /// value will be stored is passed into the inputted function.
    /// This is useful to store values that contain their own key.
    /// # Examples
    /// ```
    /// # use stable_gen_map::key::DefaultKey;
    /// use stable_gen_map::stable_gen_map::StableGenMap;
    /// let mut sm = StableGenMap::new();
    /// #[derive(Eq,PartialEq, Debug)]
    /// struct KeyHolder{
    ///     key: DefaultKey
    /// }
    /// let (key, reference) = sm.insert_with_key(|k| Box::new(KeyHolder{
    ///     key: k
    /// }));
    /// assert_eq!(sm[key], KeyHolder{key});
    /// ```
    #[inline]
    pub fn insert_with_key(&self, func: impl FnOnce(K) -> Box<T>) -> (K, &T){
        self.try_insert_with_key::<()>(|key| Ok(func(key))).unwrap()
    }


    /// Inserts a value given by the inputted function into the map. The key where the
    /// value will be stored is passed into the inputted function.
    /// This is useful to store values that contain their own key.
    /// This version allows the closure to return a `Result`, so you can propagate errors.
    ///
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
    ///     .try_insert_with_key::<()>(|k| Ok(Box::new(KeyHolder { key: k })))
    ///     .unwrap();
    ///
    /// assert_eq!(sm[key], KeyHolder { key });
    /// // optional: also prove `reference` really points to the same element:
    /// assert!(std::ptr::eq(reference, &sm[key]));
    /// ```
    #[inline]
    pub fn try_insert_with_key<E>(
        &self,
        func: impl FnOnce(K) -> Result<Box<T>, E>,
    ) -> Result<(K, &T), E> {
        unsafe {
            let slots = &mut *self.slots.get();

            // Case 1: reuse a free slot from the intrusive free list.
            if let Some(idx) = self.next_free.get() {
                let i = idx.into_usize();
                let slot = slots.get_unchecked_mut(i);

                // Pop this slot from the free list.
                let next = slot.item.next_free_unchecked();
                self.next_free.set(next);

                // Mark as reserved: not linked in the free list anymore.
                slot.item = SlotVariant::Vacant(None);

                let generation = slot.generation;
                let key = K::from(KeyData { idx, generation });

                // RAII guard: if func panics/returns Err, put this index
                // back into the free list using the *current* head.
                let guard = FreeGuard { map: self, idx };

                let value_box = func(key)?;  // may panic / return Err

                // Success: don't put it back into free list.
                guard.commit();

                // Re-borrow slots because func(key) may have re-entered and
                // caused reallocations / new slots etc.
                let slots = &mut *self.slots.get();
                let slot = slots.get_unchecked_mut(i);

                // Store value as occupied.
                slot.item = SlotVariant::Occupied(AliasableBox::from_unique(value_box));
                self.num_elements.set(self.num_elements.get() + 1);

                // Build &T from the AliasableBox.
                let value_ref: &T = match &slot.item {
                    Occupied(b) => &**b,
                    Vacant(_) => hint::unreachable_unchecked(),
                };

                Ok((key, value_ref))
            } else {
                // Case 2: no free slot; append a new slot at the end.
                let idx = K::Idx::from_usize(slots.len());
                let generation = K::Gen::zero();
                let key = K::from(KeyData { idx, generation });

                // Push an initially vacant/reserved slot.
                slots.push(Slot {
                    generation,
                    item: Vacant(None),
                });

                // Guard: if func fails, this brand-new slot becomes a free slot.
                let guard = FreeGuard { map: self, idx };

                let value_box = func(key)?; // may panic / Err
                guard.commit();

                let slots = &mut *self.slots.get();
                let i = idx.into_usize();
                let slot = slots.get_unchecked_mut(i);

                slot.item = Occupied(AliasableBox::from_unique(value_box));
                self.num_elements.set(self.num_elements.get() + 1);

                let value_ref: &T = match &slot.item {
                    Occupied(b) => &**b,
                    Vacant(_) => hint::unreachable_unchecked(),
                };

                Ok((key, value_ref))
            }
        }
    }

    /// Simple insert. When it inserts, it returns the key and reference
    /// # Examples
    /// ```rust
    /// use stable_gen_map::key::DefaultKey;
    /// use stable_gen_map::stable_gen_map::StableGenMap;
    /// let sm = StableGenMap::<DefaultKey,_>::new();
    /// let (key, reference) = sm.insert(Box::new(4));
    /// assert_eq!(*reference, 4);
    /// assert_eq!(*sm.get(key).unwrap(), 4);
    ///```
    #[inline]
    pub fn insert(&self, value: Box<T>) -> (K, &T) {
        self.insert_with_key(|_| value)
    }

}

