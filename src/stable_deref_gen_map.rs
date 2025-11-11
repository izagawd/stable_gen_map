use crate::key::{is_occupied_by_generation, Key, KeyData};
use crate::numeric::Numeric;
use num_traits::{CheckedAdd, One, Zero};
use std::cell::{Cell, UnsafeCell};
use std::cmp::PartialEq;
use std::collections::TryReserveError;

use std::marker::PhantomData;
use std::mem::ManuallyDrop;
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

pub unsafe trait SmartPtrCloneable: DerefGenMapPromise + Clone{

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

impl<Derefable, K: Key> Drop for Slot<Derefable, K> {
    fn drop(&mut self) {
        if is_occupied_by_generation(self.generation) {
          unsafe{  ManuallyDrop::drop(&mut self.item.occupied) }
        }
    }
}
impl<Derefable, K: Key> Slot<Derefable, K> {
    #[inline]
    fn take_occupied(&mut self) -> Option<Derefable> {
        use std::mem;
        unsafe{
            let gotten = mem::replace(&mut self.item, SlotVariant{vacant: None});
            if is_occupied_by_generation(self.generation){
                return Some(ManuallyDrop::into_inner(gotten.occupied));
            } else{
                return None;
            }
        }

    }
}

/// NOTE: IMPLEMENTING THIS TRAIT IS A PROMISE THAT THE `Deref` IMPLEMENTATION (also `DerefMut` implementation if it has that too) DOES NOT MUTATE ANY `SHARED` STABLE GEN MAPS (eg with `insert`) <br>
/// IT IS ALSO A PROMISE THAT THE DEREF OF THE SMART POINTER IS STABLE, MEANING THE POINTER IT DEREFS TO DOES NOT CHANGE<br><br>
/// IF THESE PROMISES ARE VIOLATED, THERE MAY BE UNDEFINED BEHAVIOR
pub unsafe trait DerefGenMapPromise: Deref {

}

unsafe impl<T: ?Sized> DerefGenMapPromise for Box<T>{}
unsafe impl<T: ?Sized> DerefGenMapPromise for Rc<T>{}
unsafe impl<T: ?Sized> DerefGenMapPromise for Arc<T>{}
unsafe impl<'a,T: ?Sized> DerefGenMapPromise for &'a T{}
impl<Derefable: DerefGenMapPromise + Clone, K: Key>  Slot<Derefable, K> {
    #[inline]
    unsafe fn clone(&self) -> Self {

        Self{
            generation: self.generation,
            item: if is_occupied_by_generation(self.generation){
                SlotVariant{occupied: self.item.occupied.clone()}
            } else {
                SlotVariant{
                    vacant: self.item.vacant
                }
            },
        }
    }
}

pub struct IterMut<'a, K: Key, Derefable: DerefGenMapPromise + 'a> {
    ptr: *mut UnsafeCell<Slot<Derefable,K>>,
    len: usize,
    idx: usize,
    _marker: PhantomData<&'a mut Derefable::Target>,
    _key_marker: PhantomData<K>,
}
pub type BoxStableDerefGenMap<K, T> = StableDerefGenMap<K, Box<T>>;
impl<K: Key, Derefable: DerefGenMapPromise> StableDerefGenMap<K, Derefable> where K::Idx : Zero {
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


impl<K: Key, Derefable: DerefGenMapPromise + SmartPtrCloneable> Clone for StableDerefGenMap< K, Derefable>  {
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
                .map(|(_slot_idx, slot)| {
                    let slot = &*slot.get();
                    ( slot.generation,
                    if is_occupied_by_generation(slot.generation) {
                        RefOrNextFree::<K, Derefable>::Ref(slot.item.occupied.deref())
                    } else {
                        RefOrNextFree::Next(slot.item.vacant)
                    }
                )})
            );
            Self{
                num_elements: Cell::new(num_elements),
                next_free,
                slots: UnsafeCell::new(slots_ref
                    .into_iter()
                    .map(|x| {
                        UnsafeCell::new(
                            Slot{
                                generation: x.0,
                                item: match x.1 {
                                    RefOrNextFree::Ref(the_ref) => SlotVariant{occupied: ManuallyDrop::new(Derefable::clone_from_reference(the_ref).unwrap()) } ,
                                    RefOrNextFree::Next(next_free) => SlotVariant{vacant: next_free}
                                }
                            }
                        )
                    })
                    .collect()),
                phantom: PhantomData,
            }
        }

    }
}

impl<'a, K: Key + 'a , Derefable: DerefGenMapPromise + DerefMut> Iterator for IterMut<'a, K, Derefable> where K::Idx : Numeric, K::Gen: Numeric {
    type Item = (K, &'a mut Derefable::Target);

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.len {
            let idx = self.idx;
            self.idx += 1;

            let slot: &mut Slot<Derefable, K> = unsafe { (&mut *self.ptr.add(idx)).get_mut() };

            let smart_ptr =
                if is_occupied_by_generation(slot.generation) {
                    unsafe { slot.item.occupied.deref_mut() }
                } else {
                continue;
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

impl<'a, K: Key, Derefable: DerefGenMapPromise + DerefMut> IntoIterator for &'a mut StableDerefGenMap<K, Derefable> where K::Idx : Numeric, <K as Key>::Gen: Numeric {
    type Item = (K, &'a mut Derefable::Target);
    type IntoIter = IterMut<'a, K, Derefable>;


    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}





pub struct StableDerefGenMap<K: Key, Derefable: DerefGenMapPromise> {
    slots: UnsafeCell<Vec<UnsafeCell<Slot<Derefable, K>>>>,
    phantom: PhantomData<fn(K)>,
    next_free: Cell<Option<K::Idx>>,
    num_elements: Cell<usize>,
}

impl<K: Key, Derefable: DerefGenMapPromise> Index<K> for StableDerefGenMap<K,Derefable> {
    type Output = Derefable::Target;
    fn index(&self, key: K) -> &Self::Output{
        self.get(key).unwrap()
    }
}
impl<K: Key,Derefable: DerefGenMapPromise + DerefMut> IndexMut<K> for StableDerefGenMap<K,Derefable> {

    fn index_mut(&mut self, key: K) -> &mut Self::Output{
        self.get_mut(key).unwrap()
    }
}


union SlotVariant<Derefable, K: Key>{
    occupied: ManuallyDrop<Derefable>,
    vacant: Option<K::Idx>,
}

pub struct IntoIter<K: Key, Derefable> {
    slots: std::vec::IntoIter<UnsafeCell<Slot<Derefable, K>>>,
    idx: usize,
    _marker: PhantomData<K>,
}

impl<K: Key, Derefable: DerefGenMapPromise> Iterator for IntoIter<K, Derefable> where <K as Key>::Idx : Numeric{
    type Item = (K, Derefable);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(mut slot) = self.slots.next() {

            let idx = self.idx;
            self.idx += 1;

            let alias = if is_occupied_by_generation(slot.get_mut().generation) {
                unsafe { ManuallyDrop::take(&mut slot.get_mut().item.occupied)}
            } else {
                continue;
            };

            let key_data = KeyData {
                idx: K::Idx::from_usize(idx),
                generation: slot.get_mut().generation,
            };
            std::mem::forget(slot); // we have taken out the occupied item. no need for drop to be called
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

impl<K: Key, Derefable: DerefGenMapPromise> IntoIterator for StableDerefGenMap<K, Derefable> where <K as Key>::Idx: Numeric{
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
struct FreeGuard<'a, K: Key, Derefable: DerefGenMapPromise> {
    map: &'a StableDerefGenMap<K, Derefable>,
    idx: K::Idx,
}

impl<'a, K: Key, Derefable: DerefGenMapPromise> FreeGuard<'a, K, Derefable> {
    fn commit(self) {

        std::mem::forget(self);
    }
}

impl<'a, K: Key, Derefable: DerefGenMapPromise> Drop for FreeGuard<'a, K, Derefable> {
    fn drop(&mut self) {

        unsafe {

            let slots_mut = &mut *self.map.slots.get();
            // increment generation to invalidate previous indexes
            let generation = &mut slots_mut.get_unchecked_mut(self.idx.into_usize()).get_mut().generation;
            let checked_add_maybe = generation.checked_add(&(K::Gen::one() + K::Gen::one())); // we add 2 to maintain even, cuz even means vacant
            if let Some(checked_add) = checked_add_maybe {
                *generation  = checked_add;
                let old_head = self.map.next_free.get();
                slots_mut.get_unchecked_mut(self.idx.into_usize()).get_mut().item.vacant = old_head;
                self.map.next_free.set(Some(self.idx));


            }

        }
    }
}




struct RemoveArguments<'a, K: Key, Derefable>{
    slot: &'a mut Slot<Derefable, K>,
    num_elements: &'a Cell<usize>,
    next_free: &'a Cell<Option<K::Idx>>,
    key: K
}
impl<K: Key,Derefable: DerefGenMapPromise> StableDerefGenMap<K,Derefable> {





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
                let x = &*x.get();
                if is_occupied_by_generation(x.generation) {
                    Some((K::from(KeyData{idx: K::Idx::from_usize(idx),generation: x.generation}),
                     x.item.occupied.deref().deref()))
                } else {
                    None
                }
            })

    }

    /// Removes all elements from the map
    #[inline]
    pub fn clear(&mut self){
        unsafe{
            let slots_len = self.slots.get_mut().len();
            for idx in 0..slots_len {
                let generation = self.slots.get_mut().get_unchecked_mut(idx).get_mut().generation;
                let key = K::from(KeyData{generation: generation, idx: K::Idx::from_usize(idx) });
                self.remove(key);
            };
        }
        debug_assert_eq!(self.len(), 0);
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
                slots: UnsafeCell::new(self.slots.get_mut().iter_mut().map(|x|  UnsafeCell::new(x.get_mut().clone())).collect()),
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
            slots: UnsafeCell::new((&*self.slots.get()).iter().map(|x| UnsafeCell::new((&*x.get()).clone())).collect()),
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


    /// gets by index, ignores generational count
    #[inline]
    pub fn get_by_index_only(&self, idx: K::Idx) -> Option<(K,&Derefable::Target)> {
        let slot = unsafe { &*((&*self.slots.get()) .get(idx.into_usize())?.get())};
        unsafe{

            if is_occupied_by_generation(slot.generation) {
                Some((K::from(KeyData{generation: slot.generation, idx}),  &*(slot.item.occupied.deref().deref() as *const Derefable::Target)))
            } else {
                None
            }
        }

    }
    /// gets by index, ignores generational count
    #[inline]
    pub fn get_by_index_only_mut(&mut self, idx: K::Idx) -> Option<(K,&mut Derefable::Target)> where Derefable: DerefMut {
        let slot = self.slots.get_mut().get_mut(idx.into_usize())?;

        unsafe{
            let slot = &mut *slot.get();
            if is_occupied_by_generation(slot.generation) {
                Some((K::from(KeyData{generation: slot.generation, idx}), slot.item.occupied.deref_mut().deref_mut() ))
            } else {
                None
            }
        }
    }
    /// Shared access to a value by key (no guard, plain &T).
    #[inline]
    pub fn get(&self, k: K) -> Option<&Derefable::Target> {

        let key_data = k.data();
        let slot = unsafe { &*self.slots.get() }.get(key_data.idx.into_usize())?;
        let slot = unsafe { &*slot.get() };
        if  slot.generation == key_data.generation {
            unsafe { Some(slot.item.occupied.deref().deref()) }
        }
        else {
            None
        }
    }



    /// Gets a unique reference to a value when supplied a key
    #[inline]
    pub fn get_mut(&mut self, k: K) -> Option<&mut Derefable::Target> where Derefable: DerefMut {

        let key_data = k.data();
        let slot = self.slots.get_mut().get_mut(key_data.idx.into_usize())?.get_mut();

        if  slot.generation == key_data.generation {
            unsafe { Some(slot.item.occupied.deref_mut().deref_mut())}
        }
        else {
            None
        }
    }

    /// Retains only elements for which `f(key, &mut value)` returns true.
    pub fn retain<F>(&mut self, mut f: F)
    where
        Derefable: DerefMut,
        F: FnMut(K, &mut Derefable::Target) -> bool,
    {
        unsafe {
            let slots: &mut Vec<_> = self.slots.get_mut();

            for (idx_usize, slot) in slots.iter_mut().enumerate() {
                let slot = slot.get_mut();
                // Only care about occupied slots.
                if is_occupied_by_generation(slot.generation)  {
                    let smart_ptr = slot.item.occupied.deref_mut();
                    // Build the key for this slot.
                    let idx = K::Idx::from_usize(idx_usize);
                    let key_data = KeyData {
                        idx,
                        generation: slot.generation,
                    };
                    let key = K::from(key_data);

                    // Get &mut Target from the smart pointer.
                    let value: &mut Derefable::Target = smart_ptr.deref_mut();

                    // Decide whether to keep it.
                    if !f(key, value) {
                        Self::remove_split_data::<false>(RemoveArguments{
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


    /// Splitting the logic into fields so borrow checker doesn't complain
    #[inline]
    unsafe fn remove_split_data<const DO_GENERATION_CHECK: bool>(remove_arguments: RemoveArguments<K,Derefable>) -> Option<Derefable>{
        let slot = remove_arguments.slot;
        let k = remove_arguments.key;
        let num_elements = remove_arguments.num_elements;
        let next_free = remove_arguments.next_free;
        let key_data = k.data();

        if DO_GENERATION_CHECK {
            if slot.generation != key_data.generation { return None; }
        }

        let smart_ptr = slot.take_occupied()?;
        num_elements.set(num_elements.get() - 1);
        match slot.generation.checked_add(&K::Gen::one()) {
            Some(generation) => {
                slot.generation = generation;

                // 3. Link this vacant slot into the intrusive free list.
                //    head = Some(idx); slot.next_free = old_head.
                let old_head =  next_free.get();
                slot.item.vacant = old_head;
                next_free.set(Some(key_data.idx));
            }
            None => {

            }
        }
        Some(smart_ptr)
    }
    /// Removes an element of the supplied key from the map, and returns its owned value.
    /// Removes only with &mut self. This is safe because the borrow checker
    /// prevents calling this while any &'_ T derived from &self is alive.
    /// A use case will be in, for example, freeing memory after the end of a frame in a video game 
    #[inline]
    pub fn remove(&mut self, k: K) -> Option<Derefable> {
        unsafe {
            Self::remove_split_data::<true>(RemoveArguments{
                slot: self.slots.get_mut().get_mut(k.data().idx.into_usize())?.get_mut(),
                key: k,
                num_elements: &self.num_elements,
                next_free: &self.next_free,
            })
        }

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
            let (idx, generation) = if let Some(idx) = self.next_free.get() {
                let i = idx.into_usize();
                let slot = &mut *slots.get_unchecked(i).get();

                // Pop this slot from the free list.
                let next = slot.item.vacant;
                self.next_free.set(next);

                // Mark as reserved: not linked in the free list anymore.
                slot.item.vacant = None;

                let generation = slot.generation;
                 (idx,generation)
            } else {
                // Case 2: no free slot; append a new slot at the end.
                let idx = K::Idx::from_usize(slots.len());
                let generation = K::Gen::zero();


                // Push an initially vacant/reserved slot.
                slots.push(UnsafeCell::new(Slot {
                    generation,
                    item: SlotVariant{vacant: None},
                }));
                 (idx, generation)
            };
            let key = K::from(KeyData {
                idx,
                generation: generation.checked_add(&K::Gen::one()).unwrap() // increment only the keys gen by 1, so the key of the inserter isn't valid until after the slot 
                // has incremented their key, which would be after it confirms the func call didn't have any errors/panics  
            });
            // RAII guard: if func panics/returns Err, put this index
            // back into the free list using the *current* head.
            let guard = FreeGuard { map: self, idx };

            let value_box = func(key)?;  // may panic / return Err

            // Success: don't put it back into free list.
            guard.commit();

            // Re-borrow slots because func(key) may have re-entered and
            // caused reallocations / new slots etc.
            let slots = &mut *self.slots.get();
            let slot = &mut *slots.get_unchecked(idx.into_usize()).get();

            // Store value as occupied.
            slot.item.occupied = ManuallyDrop::new(value_box);

            // no need for overflow check here, as that was done when incrementing generation for key
            slot.generation += K::Gen::one(); // add one to match up with keys idx, since the function succeeded from here. 
            self.num_elements.set(self.num_elements.get() + 1);

            // Build &T from the AliasableBox.
            let value_ref: &Derefable::Target = slot.item.occupied.deref().deref();

            Ok((key, value_ref))
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

