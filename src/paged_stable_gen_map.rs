use aliasable::boxed::AliasableBox;
use std::cell::UnsafeCell;
use std::marker::PhantomData;
use std::mem::{ManuallyDrop, MaybeUninit};
use std::ops::{Deref, Index, IndexMut};
use crate::stable_gen_map::{Key, StableGenMap};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PagedKeyData{
    pub(crate) generation: usize,
    pub(crate) idx: usize,
    pub(crate) page: usize,
}
pub unsafe trait PagedKey : Copy + From<PagedKeyData> {
    fn data(&self) -> PagedKeyData;
}
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct DefaultPagedKey{
    pub(crate) key_data: PagedKeyData,
}


struct Page<T>{
    slots:  AliasableBox<[UnsafeCell<MaybeUninit<Slot<T>>>]>,
    length_used:  usize,
}

impl From<PagedKeyData> for DefaultPagedKey {
    fn from(value: PagedKeyData) -> Self {
        Self{
            key_data: value,
        }
    }
}

unsafe impl PagedKey for DefaultPagedKey {
    fn data(&self) -> PagedKeyData {
        self.key_data
    }
}

impl<T> Page<T>{


    #[inline]
    unsafe fn insert_slot_unchecked(&mut self,  slot: Slot<T>) -> usize  {
        let gotten = self.slots.get_unchecked(self.length_used);
        let index = self.length_used;
        self.length_used = self.length_used.wrapping_add(1);
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
    fn get_slot(&self, idx: usize) -> Option<&Slot<T>> {
        if self.length_used <= idx{
            None
        } else {
            self.slots.get(idx).map(|x| unsafe {(&*x.get()).assume_init_ref()})
        }
    }

    #[inline]
    fn get_slot_mut(&mut self, idx: usize) -> Option<&mut Slot<T>> {
        if self.length_used <= idx{
            None
        } else {
            self.slots.get_mut(idx).map(|x| unsafe {x.get_mut().assume_init_mut()})
        }
    }
    // gets an index that is free, if possible
    #[inline]
    fn get_free_index(&self) -> Option<usize>{
        if self.slots.len() <= self.length_used{
            None
        } else {
            Some(self.length_used)
        }
    }
}
impl<T> Drop for Page<T>{
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

struct Slot<T>{
    generation: usize,
    item: UnsafeCell<Option<ManuallyDrop<T>>>
}
#[derive(Copy,Clone,Debug,Eq,Hash,PartialEq)]
struct FreeSpace{
    page: usize,
    idx: usize,
}
pub struct PagedStableGenMap<K: PagedKey, T> {
    pages: UnsafeCell<Vec<Page<T>>>,
    free:  UnsafeCell<Vec<FreeSpace>>,
    phantom: PhantomData<fn(K)>,
}
impl<K: PagedKey,T> Index<K> for PagedStableGenMap<K,T> {
    type Output = T;
    fn index(&self, key: K) -> &Self::Output{
        self.get(key).unwrap()
    }
}

impl<K: PagedKey,T> IndexMut<K> for PagedStableGenMap<K,T> {

    fn index_mut(&mut self, key: K) -> &mut Self::Output{
        self.get_mut(key).unwrap()
    }
}



pub struct IterMut<'a, K: PagedKey, T> {
    map: &'a PagedStableGenMap<K, T>,
    page_idx: usize,
    slot_idx: usize,
    _marker: PhantomData<&'a mut T>,
}

impl<K: PagedKey, T> PagedStableGenMap<K, T> {
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, T> {
        IterMut {
            map: self,
            page_idx: 0,
            slot_idx: 0,
            _marker: PhantomData,
        }
    }
}

impl<'a, K: PagedKey, T> Iterator for IterMut<'a, K, T> {
    type Item = (K, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let pages: &Vec<Page<T>> = unsafe { &*self.map.pages.get() };

            if self.page_idx >= pages.len() {
                return None;
            }

            let page = &pages[self.page_idx];

            if self.slot_idx >= page.length_used {
                self.page_idx += 1;
                self.slot_idx = 0;
                continue;
            }

            let idx_in_page = self.slot_idx;
            self.slot_idx += 1;

            let slot = match page.get_slot(idx_in_page) {
                Some(s) => s,
                None => continue,
            };

            // UnsafeCell gives us mutable access to the Option<ManuallyDrop<T>>
            let opt_ref: &mut Option<ManuallyDrop<T>> =
                unsafe { &mut *slot.item.get() };

            let md = match opt_ref.as_mut() {
                Some(m) => m,
                None => continue,
            };

            let value: &mut T = &mut *md;

            let key_data = PagedKeyData {
                generation: slot.generation,
                idx: idx_in_page,
                page: self.page_idx,
            };
            let key = K::from(key_data);

            return Some((key, value));
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, None)
    }
}


pub struct IntoIter<K: PagedKey, T> {
    pages: Vec<Page<T>>,
    page_idx: usize,
    slot_idx: usize,
    _marker: PhantomData<K>,
}

impl<K: PagedKey, T> Iterator for IntoIter<K, T> {
    type Item = (K, T);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.page_idx >= self.pages.len() {
                return None;
            }

            let page = &mut self.pages[self.page_idx];

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

            let key_data = PagedKeyData {
                generation: slot.generation,
                idx: idx_in_page,
                page: self.page_idx,
            };
            let key = K::from(key_data);

            return Some((key, value));
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, None)
    }
}

impl<K: PagedKey, T> IntoIterator for PagedStableGenMap<K, T> {
    type Item = (K, T);
    type IntoIter = IntoIter<K, T>;

    fn into_iter(self) -> Self::IntoIter {
        let pages_vec = self.pages.into_inner();
        IntoIter {
            pages: pages_vec,
            page_idx: 0,
            slot_idx: 0,
            _marker: PhantomData,
        }
    }
}


impl<'a, K: PagedKey, T> IntoIterator for &'a mut PagedStableGenMap<K, T> {
    type Item = (K, &'a mut T);
    type IntoIter = IterMut<'a, K, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}



// RAII "reservation" for a single index in `free`.
struct FreeGuard<'a, K: PagedKey, T> {
    map: &'a PagedStableGenMap<K, T>,
    free: FreeSpace,
}

impl<'a, K: PagedKey, T> FreeGuard<'a, K, T> {
    fn commit(self) {
        std::mem::forget(self);
    }
}

impl<'a, K: PagedKey, T> Drop for FreeGuard<'a, K, T> {
    fn drop(&mut self) {

        unsafe {
            // Put the index back on the free list.
            let free = &mut *self.map.free.get();
            free.push(self.free);
            let generation = &mut (&mut *self.map.pages.get()).get_unchecked_mut(self.free.page).slots.get_unchecked_mut(self.free.idx).get_mut().assume_init_mut().generation;
            *generation = generation.wrapping_add(1);
            // increment generation to invalidate previous indexes
        }
    }
}

impl<K: PagedKey,T> PagedStableGenMap<K,T> {


    #[inline]
    pub const fn new() -> Self {
        Self {
            pages: UnsafeCell::new(Vec::new()),
            free: UnsafeCell::new(Vec::new()),
            phantom: PhantomData,
        }
    }

    #[inline]
    pub fn get_mut(&mut self, k: K) -> Option<&mut T> {

        let key_data = k.data();
        let page = self.pages.get_mut().get_mut(key_data.page)?;

        let slot = page.get_slot_mut(key_data.idx)?;
        if  slot.generation == key_data.generation {
            // SAFETY: value is live; we never move the Box's allocation.
            Some(slot.item.get_mut().as_mut()?)
        }
        else {
            None
        }
    }
    /// Shared access to a value by key (no guard, plain &T).
    #[inline]
    pub fn get(&self, k: K) -> Option<&T> {

        let key_data = k.data();
        let page = unsafe { &*self.pages.get() }.get(key_data.page)?;

        let slot = page.get_slot(key_data.idx)?;
        if  slot.generation == key_data.generation {
            // SAFETY: value is live; we never move the Box's allocation.
            Some(unsafe { &*(&**(&*slot.item.get()).as_ref()? as *const T) })
        }
        else {
            None
        }
    }


    #[inline]
    pub fn clear(&mut self) {
        self.free.get_mut().clear();
        self.pages.get_mut().clear();
    }

    /* Remove only with &mut self. This is safe because the borrow checker
    prevents calling this while any &'_ T derived from &self is alive.
    A use case will be in, for example, freeing memory after the end of a frame in a video game */
    #[inline]
    pub fn remove(&mut self, k: K) -> Option<T> {
        let key_data = k.data();
        let page = self.pages.get_mut().get_mut(key_data.page)?;

        let slot = page.get_slot_mut(key_data.idx)?;
        if slot.generation != key_data.generation { return None; }
        let retrieved =slot.item.get_mut().take()?;
        slot.generation = slot.generation.wrapping_add(1);
        self.free.get_mut().push(FreeSpace{idx: key_data.idx, page: key_data.page});
        Some(ManuallyDrop::into_inner(retrieved))
    }
    #[inline]
    pub fn insert_with_key(&self, func: impl FnOnce(K) -> T) -> (K, &T){
        self.try_insert_with_key::<()>(|key| Ok(func(key))).unwrap()
    }
    #[inline]
    pub fn try_insert_with_key<E>(&self, func: impl FnOnce(K) -> Result<T,E>) -> Result<(K, &T), E> {
        unsafe{
            let pages =  &mut *self.pages.get();

            let free_spaces = &mut *self.free.get();

            if let Some(free) = free_spaces.pop() {
                let page = pages.get_mut(free.page).unwrap();
                let the_slot = page.get_slot_mut(free.idx).unwrap();
                let generation = the_slot.generation;
                let key = K::from(PagedKeyData { idx: free.idx,page: free.page,  generation, });



                // to avoid memory leaks if func(key) panics
                let free_guard = FreeGuard{
                    map: self,
                    free
                };
                let value = func(key)?;
          
          
                free_guard.commit();
                
                /* SAFETY: We are reassigning  here, to avoid double mut ub, since func can re-enter "try_insert_with_key"*/

                let pages = &mut *self.pages.get();
                let page = pages.get_unchecked_mut(free.page);


                /*
                SAFETY: func(key) might have caused a resize, changing the memory address of the_slot, so this is necessary
                to ensure we are pointing to valid memory
                 */
                let the_slot = page.get_slot(free.idx).unwrap();


                *the_slot.item.get() = Some(ManuallyDrop::new(value));
                let items_ref = (&*the_slot.item.get()).as_ref().map(|x| ManuallyDrop::deref(x)).unwrap();
                let ptr = items_ref as *const T;
                Ok((key, &*ptr ))
            } else {
                let add_new_page = |pages: &mut Vec<Page<T>>| {
                    pages.push(
                        Page::new(pages.last().map(|x| x.slots.len() * 2).unwrap_or(32))
                    );
                };
                if pages.last_mut().is_none()  {
                    add_new_page(pages);
                }

                let mut last = pages.last_mut().unwrap_unchecked();

                if last.get_free_index().is_none() {
                    add_new_page(pages);
                    last = pages.last_mut().unwrap_unchecked();
                }

                let inserted_index =
                    last.insert_slot_unchecked( Slot {
                        item: UnsafeCell::new(None),
                        generation: 0
                    });

   
                let key_data = PagedKeyData { idx: inserted_index, generation: 0, page: pages.len() - 1 };
                let key = K::from(key_data);
                let free_guard = FreeGuard{
                    map: self,
                    free: FreeSpace{
                        idx: key_data.idx,
                        page: key_data.page
                    }
                };
                let created = func(key)?;
                free_guard.commit();
                let created = created;
                
                /* SAFETY: We are reassigning  here, to avoid double mut ub, since func can re-enter "try_insert_with_key"*/
                let pages = &mut *self.pages.get();
                let page =pages.get_unchecked_mut(key_data.page);


                let the_slot =  page.get_slot(key_data.idx).unwrap_unchecked();

                *the_slot.item.get() = Some(ManuallyDrop::new(created));

                Ok((key,  (&*the_slot.item.get()).as_ref().unwrap_unchecked()))
        }

        }
    }
    #[inline]
    pub fn insert(&self, value: T) -> (K, &T) {
        self.insert_with_key(|_| value)
    }

}

