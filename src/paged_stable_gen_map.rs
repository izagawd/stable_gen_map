use crate::numeric::Numeric;

use crate::key::{Key, KeyData};
use aliasable::boxed::AliasableBox;
use num_traits::{CheckedAdd, One, Zero};
use std::cell::{Cell, UnsafeCell};
use std::marker::PhantomData;
use std::mem::{ManuallyDrop, MaybeUninit};
use std::ops::{Deref, Index, IndexMut};



struct Page<T, K: Key>{
    slots:  AliasableBox<[UnsafeCell<MaybeUninit<Slot<T, K::Gen>>>]>,
    length_used: usize,
}

impl<T, K: Key> Page<T, K>{


    #[inline]
    unsafe fn insert_slot(&mut self, slot: Slot<T, K::Gen>) -> usize  {
        let gotten = self.slots.get_unchecked(self.length_used);
        let index = self.length_used;
        self.length_used += 1;
         *gotten.get() = MaybeUninit::new(slot);
        index
    }
    #[inline]
    unsafe fn new(size: usize) -> Self{

        Self{
            slots: AliasableBox::from_unique((0..size).map(|_| UnsafeCell::new(MaybeUninit::uninit())).collect()),
            length_used: 0,
        }
    }
    #[inline]
    fn get_slot(&self, slot_idx: usize) -> Option<&Slot<T, K::Gen>> {
        if self.length_used <= slot_idx{
            None
        } else {
            self.slots.get(slot_idx).map(|x| unsafe {(&*x.get()).assume_init_ref()})
        }
    }

    #[inline]
    fn get_slot_mut(&mut self, slot_num: usize) -> Option<&mut Slot<T, K::Gen>> {
        if self.length_used <= slot_num{
            None
        } else {
            self.slots.get_mut(slot_num).map(|x| unsafe {x.get_mut().assume_init_mut()})
        }
    }
    // gets an index that is free, if possible
    #[inline]
    fn has_free_index(&self) -> bool{
        self.slots.len() > self.length_used
    }
}
impl<T, K: Key> Drop for Page<T, K>{
    #[inline]
    fn drop(&mut self) {
        unsafe {

            for slot in self.slots.iter_mut(){
                if self.length_used == 0{
                    break
                }
                self.length_used -= 1;
                if let Some(ref mut slot_item) = &mut slot.get_mut().assume_init_mut().item.get_mut() {
                   ManuallyDrop::drop(slot_item)
                }
            }
        }

    }
}

struct Slot<T, Gen>{
    generation: Gen,
    item: UnsafeCell<Option<ManuallyDrop<T>>>
}

pub struct PagedStableGenMapAbstract<K: Key, T, const SLOTS_NUM_PER_PAGE: usize = DEFAULT_SLOTS_NUM_PER_PAGE> {
    pub(crate) pages: UnsafeCell<Vec<Page<T, K>>>,
    free:  UnsafeCell<Vec<K::Idx>>,
    phantom: PhantomData<fn(K)>,
    num_elements: Cell<usize>,
}


pub type PagedStableGenMap<K,T> = PagedStableGenMapAbstract<K,T,DEFAULT_SLOTS_NUM_PER_PAGE>;
impl<K: Key,T, const SLOTS_NUM_PER_PAGE: usize> Index<K> for PagedStableGenMapAbstract<K,T, SLOTS_NUM_PER_PAGE> {
    type Output = T;
    fn index(&self, key: K) -> &Self::Output{
        self.get(key).unwrap()
    }
}

impl<K: Key,T, const SLOTS_NUM_PER_PAGE: usize> IndexMut<K> for PagedStableGenMapAbstract<K,T, SLOTS_NUM_PER_PAGE> {

    fn index_mut(&mut self, key: K) -> &mut Self::Output{
        self.get_mut(key).unwrap()
    }
}



pub struct IterMut<'a, K: Key, T, const SLOTS_NUM_PER_PAGE: usize> {
    map: &'a PagedStableGenMapAbstract<K, T, SLOTS_NUM_PER_PAGE>,
    page: usize,
    idx: usize,
    _marker: PhantomData<&'a mut T>,
}

impl<K: Key, T, const SLOTS_NUM_PER_PAGE: usize> PagedStableGenMapAbstract<K, T, SLOTS_NUM_PER_PAGE> {
    
    /// Gets a mutable iterator of the map, allowing mutable iteration between all elements
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, T, SLOTS_NUM_PER_PAGE> {
        IterMut {
            map: self,
            page: 0,
            idx: 0,
            _marker: PhantomData,
        }
    }
}

impl<'a, K: Key, T, const SLOTS_NUM_PER_PAGE: usize> Iterator for IterMut<'a, K, T, SLOTS_NUM_PER_PAGE> {
    type Item = (K, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let pages: &Vec<Page<T, K>> = unsafe { &*self.map.pages.get() };

            if self.page >= pages.len() {
                return None;
            }

            let page_idx = self.page;
            let page = &pages[page_idx];

            if self.idx >= page.length_used {
                self.page += 1;
                self.idx = 0;
                continue;
            }

            let slot_idx = self.idx;
            self.idx += 1;

            let slot = match page.get_slot(slot_idx) {
                Some(s) => s,
                None => continue,
            };

            // Get &mut Option<ManuallyDrop<T>>
            let opt_ref: &mut Option<ManuallyDrop<T>> =
                unsafe { &mut *slot.item.get() };

            let md = match opt_ref.as_mut() {
                Some(m) => m,
                None => continue,
            };

            let value: &mut T = &mut *md;

            // IMPORTANT: idx is now the *encoded* global index, not slot_idx.
            let idx = encode_index::<K::Idx>(page_idx, slot_idx, SLOTS_NUM_PER_PAGE);

            let key_data = KeyData {
                generation: slot.generation,
                idx,
            };
            let key = K::from(key_data);

            return Some((key, value));
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, None)
    }
}


pub struct IntoIter<K: Key, T, const SLOTS_NUM_PER_PAGE: usize> {
    pages: Vec<Page<T, K>>,
    page_idx: usize,
    slot_idx: usize,
    len: usize,
    _marker: PhantomData<K>,
}

impl<K: Key, T, const  SLOTS_NUM_PER_PAGE: usize> Iterator for IntoIter<K, T, SLOTS_NUM_PER_PAGE> {
    type Item = (K, T);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.page_idx >= self.pages.len() {
                return None;
            }

            let page_idx = self.page_idx;
            let page = &mut self.pages[page_idx];

            if self.slot_idx >= page.length_used {
                self.page_idx += 1;
                self.slot_idx = 0;
                continue;
            }

            let idx_in_page = self.slot_idx;
            self.slot_idx += 1;

            let slot = match page.get_slot_mut(idx_in_page) {
                Some(s) => s,
                None => continue,
            };

            let opt = slot.item.get_mut();
            let md = match opt.take() {
                Some(m) => m,
                None => continue,
            };

            let value = ManuallyDrop::into_inner(md);

            // Again, **encode** (page, slot) into K::Idx
            let idx = encode_index::<K::Idx>(page_idx, idx_in_page, SLOTS_NUM_PER_PAGE);

            let key_data = KeyData {
                generation: slot.generation,
                idx,
            };
            let key = K::from(key_data);

            return Some((key, value));
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, None)
    }

}
impl<K: Key, T, const SLOTS_NUM_PER_PAGE: usize> IntoIterator for PagedStableGenMapAbstract<K, T, SLOTS_NUM_PER_PAGE> {
    type Item = (K, T);
    type IntoIter = IntoIter<K, T, SLOTS_NUM_PER_PAGE>;

    /// Converts the map into an iterator that owns all elements. This operation consumes the map
    fn into_iter(self) -> Self::IntoIter {
        let pages_vec = self.pages.into_inner();
        IntoIter {
            len: self.num_elements.get(),
            pages: pages_vec,
            page_idx: 0,
            slot_idx: 0,
            _marker: PhantomData,
        }
    }

}


impl<'a, K: Key, T, const SLOTS_NUM_PER_PAGE: usize> IntoIterator for &'a mut PagedStableGenMapAbstract<K, T, SLOTS_NUM_PER_PAGE> {
    type Item = (K, &'a mut T);
    type IntoIter = IterMut<'a, K, T, SLOTS_NUM_PER_PAGE>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}



// RAII "reservation" for a single index in `free`.
struct FreeGuard<'a, K: Key, T, const SLOTS_NUM_PER_PAGE: usize> {
    map: &'a PagedStableGenMapAbstract<K, T, SLOTS_NUM_PER_PAGE>,
    idx: K::Idx,
}

impl<'a, K: Key, T, const SLOTS_NUM_PER_PAGE: usize> FreeGuard<'a, K, T, SLOTS_NUM_PER_PAGE> {
    fn commit(self) {
        std::mem::forget(self);
    }
}

pub struct SplitIdx {
    pub(crate) page_idx: usize,
    pub(crate) slot_idx: usize
}

/// compresses the index of a page and the index of a slot into one, which is stored in keys
#[inline]
pub fn encode_index<Idx: Numeric>(page_idx: usize, slot_idx: usize, slots_num_per_page: usize) -> Idx {

    debug_assert!(slot_idx < slots_num_per_page);
    let combined = (page_idx << slot_bits_from_capacity(slots_num_per_page)) | slot_idx;
    Idx::from_usize(combined)
}



pub const DEFAULT_SLOTS_NUM_PER_PAGE: usize = 32;

#[inline]
const fn slot_mask_from_capacity(cap: usize) -> usize {
    // cap must be a power of two, so mask is cap - 1
    cap - 1
}

#[inline]
const fn slot_bits_from_capacity(cap: usize) -> usize {
    // Ensure it's > 0 and a power of two.
    assert!(cap.is_power_of_two());
    (usize::BITS - 1 - cap.leading_zeros()) as usize
}


#[inline]
pub(crate) fn decode_index<Idx: Numeric>(idx: Idx, slots_num_per_page: usize) -> SplitIdx {
    let idx = idx.into_usize();

    let slot = idx & slot_mask_from_capacity(slots_num_per_page);
    let page = idx >> slot_bits_from_capacity(slots_num_per_page);
    SplitIdx{
        page_idx: page,
        slot_idx: slot
    }
}

impl<'a, K: Key, T, const SLOTS_NUM_PER_PAGE: usize> Drop for FreeGuard<'a, K, T, SLOTS_NUM_PER_PAGE> {
    fn drop(&mut self) {

        unsafe {
            // Put the index back on the free list.
            let as_slot_and_page = decode_index::<_>(self.idx, SLOTS_NUM_PER_PAGE);
            let generation = &mut (&mut *self.map.pages.get()).get_unchecked_mut(as_slot_and_page.page_idx).slots.get_unchecked_mut(as_slot_and_page.slot_idx).get_mut().assume_init_mut().generation;
            let checked_add_maybe = generation.checked_add(&K::Gen::one());
            if let Some(checked_add) = checked_add_maybe {
                *generation  = checked_add;
                let free = &mut *self.map.free.get();
                free.push(self.idx);
            }
        }
    }
}

impl<K: Key,T, const SLOTS_NUM_PER_PAGE: usize> PagedStableGenMapAbstract<K,T, SLOTS_NUM_PER_PAGE> {


    /// Creates a new, empty PagedStableGenMap
    #[inline]
    pub const fn new() -> Self {
        const {
            assert!(SLOTS_NUM_PER_PAGE.is_power_of_two()); // this must be a power of 2 to allow the idx to be safetly split into page_idx and slot_idx
        }
        Self {
            pages: UnsafeCell::new(Vec::new()),
            free: UnsafeCell::new(Vec::new()),
            phantom: PhantomData,
            num_elements: Cell::new(0),
        }
    }

    /// Gets a unique reference to an element
    #[inline]
    pub fn get_mut(&mut self, k: K) -> Option<&mut T> {

        let key_data = k.data();
        let as_page_slot_idx = decode_index::<_>(key_data.idx, SLOTS_NUM_PER_PAGE);
        let page = self.pages.get_mut().get_mut(as_page_slot_idx.page_idx)?;

        let slot = page.get_slot_mut(as_page_slot_idx.slot_idx)?;
        if  slot.generation == key_data.generation {
            // SAFETY: value is live; we never move the Box's allocation.
            Some(slot.item.get_mut().as_mut()?)
        }
        else {
            None
        }
    }
    /// Gets a shared reference to an element
    #[inline]
    pub fn get(&self, k: K) -> Option<&T> {

        let key_data = k.data();
        let as_page_slot_idx = decode_index::<_>(key_data.idx, SLOTS_NUM_PER_PAGE);
        let page = unsafe { &*self.pages.get() }.get(as_page_slot_idx.page_idx)?;

        let slot = page.get_slot(as_page_slot_idx.slot_idx)?;
        if  slot.generation == key_data.generation {
            // SAFETY: value is live; we never move the Box's allocation.
            Some(unsafe { &*(&**(&*slot.item.get()).as_ref()? as *const T) })
        }
        else {
            None
        }
    }

    /// Empties the map, removing all elements
    #[inline]
    pub fn clear(&mut self) {
        self.free.get_mut().clear();
        self.pages.get_mut().clear();
        self.num_elements.set(0);
    }

    /// Gets the number of elements in the map
    #[inline]
    pub fn len(&self) -> usize {
        self.num_elements.get()
    }


    /// Removes an element of the supplied key from the map, and returns its owned value
    /// Removes only with &mut self. This is safe because the borrow checker
    /// prevents calling this while any &'_ T derived from &self is alive.
    /// A use case will be in, for example, freeing memory after the end of a frame in a video game */
    #[inline]
    pub fn remove(&mut self, k: K) -> Option<T> {
        let key_data = k.data();
        let as_slot_page_idx = decode_index::<_>(key_data.idx, SLOTS_NUM_PER_PAGE);
        let page = self.pages.get_mut().get_mut(as_slot_page_idx.page_idx)?;

        let slot = page.get_slot_mut(as_slot_page_idx.slot_idx)?;
        if slot.generation != key_data.generation { return None; }
        let retrieved =slot.item.get_mut().take()?;
        self.num_elements.set(self.num_elements.get() - 1);

        match slot.generation.checked_add(&K::Gen::one()) {
            Some(generation) => {
                slot.generation = generation;
                self.free.get_mut().push(key_data.idx);
                Some(ManuallyDrop::into_inner(retrieved))
            }
            None => {
                 Some(ManuallyDrop::into_inner(retrieved))
            }
        }
    }



    /// Inserts a value given by the inputted function into the map. The key where the
    /// value will be stored is passed into the inputted function.
    /// This is useful to store values that contain their own key.
    /// # Examples
    /// ```
    /// # use stable_gen_map::key::DefaultKey;
    /// use stable_gen_map::paged_stable_gen_map::PagedStableGenMap;
    /// let mut sm = PagedStableGenMap::new();
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
    pub fn insert_with_key(&self, func: impl FnOnce(K) -> T) -> (K, &T){
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
    /// use stable_gen_map::paged_stable_gen_map::PagedStableGenMap;
    ///
    /// #[derive(Eq, PartialEq, Debug)]
    /// struct KeyHolder {
    ///     key: DefaultKey,
    /// }
    ///
    /// let sm = PagedStableGenMap::new();
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
    pub fn try_insert_with_key<E>(&self, func: impl FnOnce(K) -> Result<T,E>) -> Result<(K, &T), E> {
        unsafe{
            let pages =  &mut *self.pages.get();

            let free_spaces = &mut *self.free.get();

            if let Some(free) = free_spaces.pop() {
                let as_slot_page_idx = decode_index::<_>(free, SLOTS_NUM_PER_PAGE);
                let page = pages.get_mut(as_slot_page_idx.page_idx).unwrap_unchecked();
                let the_slot = page.get_slot_mut(as_slot_page_idx.slot_idx).unwrap_unchecked();
                let generation = the_slot.generation;
                let key = K::from(KeyData { idx: free,  generation, });



                // to avoid memory leaks if func(key) panics
                let free_guard = FreeGuard{
                    map: self,
                    idx: free
                };
                let value = func(key)?;


                free_guard.commit();

                /* SAFETY: We are reassigning  here, to avoid double mut ub, since func can re-enter "try_insert_with_key"*/

                let pages = &mut *self.pages.get();
                let page = pages.get_unchecked_mut(as_slot_page_idx.page_idx);


                /*
                SAFETY: func(key) might have caused a resize, changing the memory address of the_slot, so this is necessary
                to ensure we are pointing to valid memory
                 */
                let the_slot = page.get_slot(as_slot_page_idx.slot_idx).unwrap();


                *the_slot.item.get() = Some(ManuallyDrop::new(value));
                self.num_elements.set(self.num_elements.get() + 1);
                let items_ref = (&*the_slot.item.get()).as_ref().map(|x| ManuallyDrop::deref(x)).unwrap();
                let ptr = items_ref as *const T;
                Ok((key, &*ptr ))
            } else {

                let add_new_page = |pages: &mut Vec<Page<T,K>>| {
                    pages.push(
                        Page::new(SLOTS_NUM_PER_PAGE)
                    );
                };
                if pages.last_mut().is_none()  {
                    add_new_page(pages);
                }

                let mut last = pages.last_mut().unwrap_unchecked();

                if !last.has_free_index() {
                    add_new_page(pages);
                    last = pages.last_mut().unwrap_unchecked();
                }

                let slot_idx =
                    last.insert_slot( Slot {
                        item: UnsafeCell::new(None),
                        generation: K::Gen::zero(),
                    });

                let page_idx =pages.len() - 1;
                let idx = encode_index(page_idx, slot_idx, SLOTS_NUM_PER_PAGE);
                let key_data = KeyData { idx: idx, generation: K::Gen::zero() };
                let key = K::from(key_data);
                let free_guard = FreeGuard{
                    map: self,
                    idx: key_data.idx
                };
                let created = func(key)?;
                free_guard.commit();
                let created = created;

                /* SAFETY: We are reassigning  here, to avoid double mut ub, since func can re-enter "try_insert_with_key"*/
                let pages = &mut *self.pages.get();
                let page =pages.get_unchecked_mut(page_idx);


                let the_slot =  page.get_slot(slot_idx).unwrap_unchecked();

                *the_slot.item.get() = Some(ManuallyDrop::new(created));
                self.num_elements.set(self.num_elements.get() + 1);
                Ok((key,  (&*the_slot.item.get()).as_ref().unwrap_unchecked()))
        }

        }
    }

    /// Simple insert. When it inserts, it returns the key and reference
    /// # Examples
    /// ```rust
    /// use stable_gen_map::key::DefaultKey;
    /// use stable_gen_map::paged_stable_gen_map::PagedStableGenMap;
    /// let sm = PagedStableGenMap::<DefaultKey,_>::new();
    /// let (key, reference) = sm.insert(4);
    /// assert_eq!(*reference, 4);
    /// assert_eq!(*sm.get(key).unwrap(), 4);
    ///```
    #[inline]
    pub fn insert(&self, value: T) -> (K, &T) {
        self.insert_with_key(|_| value)
    }

}

