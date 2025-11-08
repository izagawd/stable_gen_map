use crate::stable_deref_gen_map::SlotVariant::{Occupied, Vacant};
use crate::key::{Key, KeyData};
use crate::numeric::Numeric;
use num_traits::{CheckedAdd, One, Zero};
use stable_deref_trait::StableDeref;
use std::cell::{Cell, UnsafeCell};
use std::cmp::PartialEq;
use std::collections::TryReserveError;
use std::hint;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::rc::Rc;
use std::sync::Arc;

/// NOTE: SELECTING THE WRONG SMART POINTER KIND FOR A SMART POINTER MAY LEAD TO UNDEFINED BEHAVIOUR.<br><br>
/// EACH SMART POINTER KIND IS DOCUMENTED WITH GUIDELINES TO FOLLOW.<br><br> NOT FOLLOWING THEM MEANS YOU HAVE SELECTED THE WRONG SMART POINTER KIND,
/// WHICH, AS I SAID, MAY LEAD TO UNDEFINED BEHAVIOUR
#[derive(Clone,Copy,PartialEq,Eq)]
pub enum SmartPtrKind{

    /// Meaning the smart pointer owns the type. When the smart pointer is destroyed, so as the type its pointing to. eg `Box`
    Owned,

    /// Meaning the smart pointer is borrowing a reference to the type, or has shared ownership to the type its pointing to.<br>
    /// eg `Rc` `Arc` `Ref`.<br><br>
    /// if the smart pointers is of kind `Shared` and its `Clone` implementation calls the type it is pointing to's `Clone` implementation, you should not be implementing
    /// `SmartPtrCloneable` for the smart pointer at all.<br> If not, there would be a possibility of Undefined Behavior.
    /// <br><br>
    /// If your smart pointer is of kind `Shared` and implements `Clone`, the `Clone` implementation must NOT mutate any shared `Stable Gen Map` (eg with `insert`)
    /// If not, there would be a possibility of Undefined Behavior
    Shared
}

pub unsafe trait SmartPtrCloneable: StableDeref + Clone{

    /// BE VERY CAREFUL WHEN SELECTING THE SMART POINTER KIND TO AVOID POSSIBLE UNDEFINED BEHAVIOR
    const KIND : SmartPtrKind;


    /// NOTE: THIS METHOD MUST BE IMPLEMENTED BY SMART POINTERS WITH KIND `Owned`. IF THE SMART POINTER KIND IS `Shared`, SIMPLY RETURN `None`.
    /// IF THESE GUIDELINES ARE NOT FOLLOWED, THERE COULD BE BUGS, UNEXPECTED BEHAVIOUR, AND MAYBE UNDEFINED BEHAVIOUR
    ///<br><br>
    /// The implementation of this method should have very similar logic to the smart pointer's `Clone::clone` implementation to ensure consistency.
    /// If still in doubt, you can look at how we implemented `SmartPtrCloneable` for `Box`
    unsafe fn clone_from_reference(reference: &Self::Target) -> Option<Self>;
}

unsafe impl<T: Clone> SmartPtrCloneable for Box<T>{
    const KIND : SmartPtrKind = SmartPtrKind::Owned;
    unsafe fn clone_from_reference(reference: &T) -> Option<Self>{
        Some(Box::new(reference.clone())) // this is essentially what Box::clone does, assuming `reference` is what it `Derefs` to
    }
}
unsafe impl<'a,T: Clone> SmartPtrCloneable for &'a T{
    const KIND : SmartPtrKind = SmartPtrKind::Shared;
    unsafe fn clone_from_reference(_: &T) -> Option<Self>{
        None
    }
}
unsafe impl<T: Clone> SmartPtrCloneable for Rc<T>{
    const KIND : SmartPtrKind = SmartPtrKind::Shared;
    unsafe fn clone_from_reference(_: &T) -> Option<Self>{
        None
    }
}
unsafe impl<T: Clone> SmartPtrCloneable for Arc<T>{
    const KIND : SmartPtrKind = SmartPtrKind::Shared;
    unsafe fn clone_from_reference(_: &T) -> Option<Self>{
        None
    }
}

struct Slot<Derefable, K: Key> {
    generation: K::Gen,
    item: SlotVariant<Derefable, K>,
}
impl<Derefable: StableDeref + Clone, K: Key> SlotVariant<Derefable, K> {
    #[inline]
    unsafe fn clone(&self) -> Self {

            match self{
                Occupied(v) => {
                    Occupied(v.clone())
                } Vacant(vacant) => {
                    Vacant(vacant.clone())
                }
            }
        
    }
}
impl<Derefable: StableDeref + Clone, K: Key>  Slot<Derefable, K> {
    #[inline]
    unsafe fn clone(&self) -> Self {
        Self{
            generation: self.generation,
            item: self.item.clone(),
        }
    }
}
pub struct IterMut<'a, K: Key, Derefable: StableDeref + 'a> {
    ptr: *mut Slot<Derefable,K>,
    len: usize,
    idx: usize,
    _marker: PhantomData<&'a mut Derefable::Target>,
    _key_marker: PhantomData<K>,
}
pub type BoxStableDerefGenMap<K: Key, T: ?Sized> = StableDerefGenMap<K, Box<T>>;
impl<K: Key, Derefable: StableDeref> StableDerefGenMap<K, Derefable> where K::Idx : Zero {
    /// Gets a mutable iterator of the map, allowing mutable iteration between all elements
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, Derefable> {
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


/// I am aware that types like `Rc<T>` can still clone even if T does not `Clone`, but `Specialization` is not stabilized yet, so this is the only safe way I can think of.
/// This implementation still has a lot of room to grow, and I do not mind crit
impl<K: Key, Derefable: StableDeref + SmartPtrCloneable> Clone for StableDerefGenMap< K, Derefable>  {
    fn clone(&self) -> Self {

        unsafe {
            if <Derefable as SmartPtrCloneable>::KIND == SmartPtrKind::Shared{
                // if the smart pointer kind was correctly selected as `Shared`, as per the documentation of `Shared`, This should not cause
                // any undefined behavior and is a faster path
                return self.clone_efficiently()
            }
            enum RefOrNextFree<'a, K: Key, T: ?Sized> {
                Ref(&'a T),
                Next(Option<K::Idx>),
            }
            let num_elements = self.len();
            let next_free = self.next_free.clone();
            let mut slots_ref = Vec::with_capacity(num_elements);

            slots_ref.extend((&*self.slots.get())
                .iter()
                .enumerate()
                .map(|(slot_idx, slot)| ( slot.generation, match &slot.item {
                    Occupied(v) => RefOrNextFree::<K, _>::Ref(v.deref()),
                    Vacant(nxt_free) => RefOrNextFree::<K, _>::Next(*nxt_free),
                }))
            );
            Self{
                num_elements: Cell::new(num_elements),
                next_free,
                slots: UnsafeCell::new(slots_ref
                    .into_iter()
                    .map(|x| {

                        Slot{

                            generation: x.0,
                            item: match x.1 {
                                RefOrNextFree::Ref(the_ref) => Occupied(Derefable::clone_from_reference(the_ref).unwrap()) ,
                                RefOrNextFree::Next(next_free) => Vacant(next_free)
                            }
                        }
                    })
                    .collect()),
                phantom: PhantomData,
            }
        }

    }
}

impl<'a, K: Key + 'a , Derefable: StableDeref + DerefMut> Iterator for IterMut<'a, K, Derefable> where K::Idx : Numeric, K::Gen: Numeric {
    type Item = (K, &'a mut Derefable::Target);

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.len {
            let idx = self.idx;
            self.idx += 1;

            let slot: &mut Slot<Derefable, K> = unsafe { &mut *self.ptr.add(idx) };

            let smart_ptr = match &mut slot.item {
                SlotVariant::Occupied(b) => b,
                _ => continue,
            };

            let key_data = KeyData {
                idx: K::Idx::from_usize(idx),
                generation: slot.generation,
            };
            let key = K::from(key_data);

            let value: &mut Derefable::Target = smart_ptr.deref_mut();

            return Some((key, value));
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining_slots = self.len.saturating_sub(self.idx);
        (0, Some(remaining_slots))
    }
}

impl<'a, K: Key, Derefable: StableDeref + DerefMut> IntoIterator for &'a mut StableDerefGenMap<K, Derefable> where K::Idx : Numeric, <K as Key>::Gen: Numeric {
    type Item = (K, &'a mut Derefable::Target);
    type IntoIter = IterMut<'a, K, Derefable>;


    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}





pub struct StableDerefGenMap<K: Key, Derefable: StableDeref> {
    slots: UnsafeCell<Vec<Slot<Derefable, K>>>,
    phantom: PhantomData<fn(K)>,
    next_free: Cell<Option<K::Idx>>,
    num_elements: Cell<usize>,
}

impl<K: Key, Derefable: StableDeref> Index<K> for StableDerefGenMap<K,Derefable> {
    type Output = Derefable::Target;
    fn index(&self, key: K) -> &Self::Output{
        self.get(key).unwrap()
    }
}
impl<K: Key,Derefable: StableDeref + DerefMut> IndexMut<K> for StableDerefGenMap<K,Derefable> {

    fn index_mut(&mut self, key: K) -> &mut Self::Output{
        self.get_mut(key).unwrap()
    }
}

enum SlotVariant<Derefable, K: Key>{
    Occupied(Derefable),
    Vacant(Option<K::Idx>),
}

pub struct IntoIter<K: Key, Derefable> {
    slots: std::vec::IntoIter<Slot<Derefable, K>>,
    idx: usize,
    _marker: PhantomData<K>,
}

impl<K: Key, Derefable: StableDeref> Iterator for IntoIter<K, Derefable> where <K as Key>::Idx : Numeric{
    type Item = (K, Derefable);

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

       
            return Some((key, alias));
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining_slots = self.slots.len().saturating_sub(self.idx);
        (0, Some(remaining_slots))
    }
}

impl<K: Key, Derefable: StableDeref> IntoIterator for StableDerefGenMap<K, Derefable> where <K as Key>::Idx: Numeric{
    type Item = (K, Derefable);
    type IntoIter = IntoIter<K, Derefable>;

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
struct FreeGuard<'a, K: Key, Derefable: StableDeref> {
    map: &'a StableDerefGenMap<K, Derefable>,
    idx: K::Idx,
}

impl<'a, K: Key, Derefable: StableDeref> FreeGuard<'a, K, Derefable> {
    fn commit(self) {
        std::mem::forget(self);
    }
}

impl<'a, K: Key, Derefable: StableDeref> Drop for FreeGuard<'a, K, Derefable> {
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



impl<Derefable, K: Key> SlotVariant<Derefable, K> where K::Idx : Zero {
    fn is_occupied(&self) -> bool {
        matches!(self, Occupied(_))
    }
    /// If occupied, take the value and make this slot Vacant(None).
    /// If already vacant, leave as-is and return None.
    #[inline]
    fn take_occupied(&mut self) -> Option<Derefable> {
        use std::mem;

        match mem::replace(self, SlotVariant::Vacant(None)) {
            Occupied(smart_ptr) => Some(smart_ptr),
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
impl<K: Key,Derefable: StableDeref> StableDerefGenMap<K,Derefable> {





    /// Returns a snapshot of the map at the current moment. it ignores future inserts
    /// NOTE: this does a heap allocation, and a heap deallocation when the snapshot drops
    #[inline]
    pub fn snapshot(&self) -> Vec<(K, &Derefable::Target)> {
        unsafe{
            let mut vec = Vec::with_capacity(self.len());
            vec.extend(
                self.iter_unsafe()
            );
            return vec;
        }

    }




    /// Returns a snapshot of the current keys only (no references).
    /// Future inserts are ignored. Allocates a single `Vec<K>`.
    #[inline]
    pub fn snapshot_key_only(&self) -> Vec<K> {
        unsafe{
            let mut vec = Vec::with_capacity(self.len());
            vec.extend(
                self.iter_unsafe()
                    .map(|(k, _)| k)
            );
            vec
        }
    }

    /// Iterator over `&T` for a snapshot of the map. Ignores future inserts.
    /// Allocates internally via `snapshot_ref_only`.
    #[inline]
    pub fn snapshot_ref_only(&self) -> Vec<&Derefable::Target> {
        unsafe{
            let mut vec = Vec::with_capacity(self.len());
            vec.extend(
                self.iter_unsafe()
                    .map(|(_, r)| r)
            );
            vec
        }
    }
    /// Iteration with this method is only safe if no mutation of the map occurs while iterating, which can happen even with safe code. For example, inserting while iterating with this is UB
    #[inline]
    pub unsafe fn iter_unsafe(&self) -> impl Iterator<Item = (K, &Derefable::Target)> {
        (&*self.slots.get())
            .iter()
            .enumerate()
            .filter_map(|(idx, x)| {
                match x.item {
                    Occupied(ref a) => Some(
                        (K::from(KeyData{idx: K::Idx::from_usize(idx),generation: x.generation}),
                         a.deref())),
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

    /// a more efficient Clone operation than the Clone::clone implementation. Since done with a mutable reference, the `Clone` implementation of `Derefable` cannot mutate the map without unsafe code,
    /// so `clone_efficiently_mut` is safe
    #[inline]
    pub fn clone_efficiently_mut(&mut self) -> Self where Derefable: Clone {
        unsafe {
            Self{
                num_elements: self.num_elements.clone(),
                phantom: PhantomData,
                next_free: self.next_free.clone(),
                slots: UnsafeCell::new(self.slots.get_mut().iter_mut().map(|x| x.clone()).collect()),
            }
        }
    }
    /// A more efficient Clone operation than the Clone::clone implementation, but if the `Clone` implementation of `Derefable` mutates the map, UB occurs
    #[inline]
    pub unsafe  fn clone_efficiently(&self) -> Self where Derefable: Clone {
        Self{
            num_elements: self.num_elements.clone(),
            phantom: PhantomData,
            next_free: self.next_free.clone(),
            slots: UnsafeCell::new((&*self.slots.get()).iter().map(|x| x.clone()).collect()),
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
    pub fn get(&self, k: K) -> Option<&Derefable::Target> {

        let key_data = k.data();
        let slot = unsafe { &*self.slots.get() }.get(key_data.idx.into_usize())?;
        if  slot.generation == key_data.generation {
            match &slot.item {
                Occupied(item) => {
                    unsafe { Some(&*(item.deref() as *const Derefable::Target)) }
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
    pub fn get_mut(&mut self, k: K) -> Option<&mut Derefable::Target> where Derefable: DerefMut {

        let key_data = k.data();
        let slot = self.slots.get_mut().get_mut(key_data.idx.into_usize())?;
        if  slot.generation == key_data.generation {
            match &mut slot.item {
                Occupied(ref mut item) => {
                    // SAFETY: value is live; we never move the Box's allocation.
                    Some(item.deref_mut())
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
    pub fn remove(&mut self, k: K) -> Option<Derefable> {
        let key_data = k.data();
        let slot = self.slots.get_mut().get_mut(key_data.idx.into_usize())?;
        if slot.generation != key_data.generation { return None; }

        let smart_ptr = slot.item.take_occupied()?;
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
        Some(smart_ptr)

    }


    /// Returns the total amount of elements in the map
    #[inline]
    pub fn len(&self) -> usize {
        self.num_elements.get()
    }


    /// How much elements (Occupied or Vacant, doesn't matter), the deref_stable_gen_map can hold before reallocating
    #[inline]
    pub fn capacity(&self) -> usize {
        unsafe { &*self.slots.get() }.capacity()
    }

    /// Inserts a value given by the inputted function into the map. The key where the
    /// value will be stored is passed into the inputted function.
    /// This is useful to store values that contain their own key.
    /// # Examples
    /// ```
    /// # use stable_gen_map::key::DefaultKey;///
    /// use stable_gen_map::stable_deref_gen_map::StableDerefGenMap;
    /// let mut sm = StableDerefGenMap::new();
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
    pub fn insert_with_key(&self, func: impl FnOnce(K) -> Derefable) -> (K, &Derefable::Target){
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
    /// use stable_gen_map::stable_deref_gen_map::StableDerefGenMap;
    ///
    /// #[derive(Eq, PartialEq, Debug)]
    /// struct KeyHolder {
    ///     key: DefaultKey,
    /// }
    ///
    /// let sm = StableDerefGenMap::new();
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
        func: impl FnOnce(K) -> Result<Derefable, E>,
    ) -> Result<(K, &Derefable::Target), E> {
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
                slot.item = Occupied(value_box);
                self.num_elements.set(self.num_elements.get() + 1);

                // Build &T from the AliasableBox.
                let value_ref: &Derefable::Target = match &slot.item {
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

                slot.item = Occupied(value_box);
                self.num_elements.set(self.num_elements.get() + 1);

                let value_ref: &Derefable::Target = match &slot.item {
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
    /// use stable_gen_map::stable_deref_gen_map::StableDerefGenMap;
    /// let sm = StableDerefGenMap::<DefaultKey,_>::new();
    /// let (key, reference) = sm.insert(Box::new(4));
    /// assert_eq!(*reference, 4);
    /// assert_eq!(*sm.get(key).unwrap(), 4);
    ///```
    #[inline]
    pub fn insert(&self, value: Derefable) -> (K, &Derefable::Target) {
        self.insert_with_key(|_| value)
    }

}

