use crate::numeric::Numeric;
use crate::stable_gen_map::Key;
use aliasable::boxed::AliasableBox;
use num_traits::{CheckedAdd, One, Zero};
use std::cell::{Cell, UnsafeCell};
use std::marker::PhantomData;
use std::mem::{ManuallyDrop, MaybeUninit};
use std::ops::{Deref, Index, IndexMut};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PagedKeyData<Page, Idx,Gen>{
    pub(crate) idx: Idx,
    pub(crate) page: Page,
    pub(crate) generation: Gen,
}
pub unsafe trait PagedKey : Copy + From<PagedKeyData<Self::Page, Self::Idx, Self::Gen>> {
    type Page: Numeric;
    type Idx: Numeric;
    type Gen: Numeric;
    fn data(&self) -> PagedKeyData<Self::Page, Self::Idx,Self::Gen>;
}
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct DefaultPagedKey{
    pub(crate) key_data: PagedKeyData<u16,u32,u32>,
}


struct Page<T, K: PagedKey>{
    slots:  AliasableBox<[UnsafeCell<MaybeUninit<Slot<T, K::Gen>>>]>,
    length_used: usize,
}

impl From<PagedKeyData<u16,u32,u32>> for DefaultPagedKey {
    fn from(value: PagedKeyData<u16,u32,u32>) -> Self {
        Self{
            key_data: value,
        }
    }
}

unsafe impl PagedKey for DefaultPagedKey {
    type Page = u16;
    type Idx = u32;
    type Gen = u32;

    fn data(&self) -> PagedKeyData<u16,u32,u32> {
        self.key_data
    }
}

impl<T, K: PagedKey> Page<T, K>{


    #[inline]
    unsafe fn insert_slot(&mut self, slot: Slot<T, K::Gen>) -> K::Idx  {
        let gotten = self.slots.get_unchecked(self.length_used);
        let index = self.length_used;
        self.length_used += 1;
         *gotten.get() = MaybeUninit::new(slot);
        K::Idx::from_usize(index)
    }
    #[inline]
    unsafe fn new(size: K::Idx) -> Self{

        Self{
            slots: AliasableBox::from_unique((0..size.into_usize()).map(|_| UnsafeCell::new(MaybeUninit::uninit())).collect()),
            length_used: 0,
        }
    }
    #[inline]
    fn get_slot(&self, idx: K::Idx) -> Option<&Slot<T, K::Gen>> {
        if self.length_used <= idx.into_usize(){
            None
        } else {
            self.slots.get(idx.into_usize()).map(|x| unsafe {(&*x.get()).assume_init_ref()})
        }
    }

    #[inline]
    fn get_slot_mut(&mut self, idx: K::Idx) -> Option<&mut Slot<T, K::Gen>> {
        if self.length_used <= idx.into_usize(){
            None
        } else {
            self.slots.get_mut(idx.into_usize()).map(|x| unsafe {x.get_mut().assume_init_mut()})
        }
    }
    // gets an index that is free, if possible
    #[inline]
    fn has_free_index(&self) -> bool{
        self.slots.len() > self.length_used
    }
}
impl<T, K: PagedKey> Drop for Page<T, K>{
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
#[derive(Copy,Clone,Debug,Eq,Hash,PartialEq)]
struct FreeSpace<K: PagedKey>{
    page: K::Page,
    idx: K::Idx,
}
pub struct PagedStableGenMap<K: PagedKey, T> {
    pages: UnsafeCell<Vec<Page<T, K>>>,
    free:  UnsafeCell<Vec<FreeSpace<K>>>,
    phantom: PhantomData<fn(K)>,
    num_elements: Cell<usize>,
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
    page: usize,
    idx: usize,
    _marker: PhantomData<&'a mut T>,
}

impl<K: PagedKey, T> PagedStableGenMap<K, T> {
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, T> {
        IterMut {
            map: self,
            page: 0,
            idx: 0,
            _marker: PhantomData,
        }
    }
}

impl<'a, K: PagedKey, T> Iterator for IterMut<'a, K, T> {
    type Item = (K, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let pages: &Vec<Page<T, K>> = unsafe { &*self.map.pages.get() };

            if self.page >= pages.len() {
                return None;
            }

            let page = &pages[self.page];

            if self.idx >= page.length_used {
                self.page += 1;
                self.idx = 0;
                continue;
            }

            let idx_in_page =K::Idx::from_usize(self.idx);
            self.idx += 1;

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
                page: K::Page::from_usize(self.page),
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
    pages: Vec<Page<T, K>>,
    page: usize,
    idx: usize,
    _marker: PhantomData<K>,
}

impl<K: PagedKey, T> Iterator for IntoIter<K, T> {
    type Item = (K, T);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.page >= self.pages.len() {
                return None;
            }

            let page = &mut self.pages[self.page];

            if self.idx >= page.length_used {
                self.page += 1;
                self.idx = 0;
                continue;
            }

            let idx_in_page = K::Idx::from_usize(self.idx);
            self.idx += 1;

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
                page: K::Page::from_usize(self.page),
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
            page: 0,
            idx: 0,
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
    free: FreeSpace<K>,
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

            let generation = &mut (&mut *self.map.pages.get()).get_unchecked_mut(self.free.page.into_usize()).slots.get_unchecked_mut(self.free.idx.into_usize()).get_mut().assume_init_mut().generation;
            let checked_add_maybe = generation.checked_add(&K::Gen::one());
            if let Some(checked_add) = checked_add_maybe {
                *generation  = checked_add;
                let free = &mut *self.map.free.get();
                free.push(self.free);
            }
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
            num_elements: Cell::new(0),
        }
    }

    #[inline]
    pub fn get_mut(&mut self, k: K) -> Option<&mut T> {

        let key_data = k.data();
        let page = self.pages.get_mut().get_mut(key_data.page.into_usize())?;

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
        let page = unsafe { &*self.pages.get() }.get(key_data.page.into_usize())?;

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
        self.num_elements.set(0);
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.num_elements.get()
    }


    /* Remove only with &mut self. This is safe because the borrow checker
    prevents calling this while any &'_ T derived from &self is alive.
    A use case will be in, for example, freeing memory after the end of a frame in a video game */
    #[inline]
    pub fn remove(&mut self, k: K) -> Option<T> {
        let key_data = k.data();
        let page = self.pages.get_mut().get_mut(key_data.page.into_usize())?;

        let slot = page.get_slot_mut(key_data.idx)?;
        if slot.generation != key_data.generation { return None; }
        let retrieved =slot.item.get_mut().take()?;
        self.num_elements.set(self.num_elements.get() - 1);

        match slot.generation.checked_add(&K::Gen::one()) {
            Some(generation) => {
                slot.generation = generation;
                self.free.get_mut().push(FreeSpace{idx: key_data.idx, page: key_data.page});
                Some(ManuallyDrop::into_inner(retrieved))
            }
            None => {
                 Some(ManuallyDrop::into_inner(retrieved))
            }
        }
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
                let page = pages.get_mut(free.page.into_usize()).unwrap_unchecked();
                let the_slot = page.get_slot_mut(free.idx).unwrap_unchecked();
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
                let page = pages.get_unchecked_mut(free.page.into_usize());


                /*
                SAFETY: func(key) might have caused a resize, changing the memory address of the_slot, so this is necessary
                to ensure we are pointing to valid memory
                 */
                let the_slot = page.get_slot(free.idx).unwrap();


                *the_slot.item.get() = Some(ManuallyDrop::new(value));
                self.num_elements.set(self.num_elements.get() + 1);
                let items_ref = (&*the_slot.item.get()).as_ref().map(|x| ManuallyDrop::deref(x)).unwrap();
                let ptr = items_ref as *const T;
                Ok((key, &*ptr ))
            } else {

                let add_new_page = |pages: &mut Vec<Page<T,K>>| {
                    pages.push(
                        Page::new(pages.last().map(|x| K::Idx::from_usize(x.slots.len() * 2)).unwrap_or(K::Idx::from_usize(32)))
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

                let inserted_index =
                    last.insert_slot( Slot {
                        item: UnsafeCell::new(None),
                        generation: K::Gen::zero(),
                    });


                let key_data = PagedKeyData { idx: inserted_index, generation: K::Gen::zero(), page: K::Page::from_usize(pages.len() - 1)};
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
                let page =pages.get_unchecked_mut(key_data.page.into_usize());


                let the_slot =  page.get_slot(key_data.idx).unwrap_unchecked();

                *the_slot.item.get() = Some(ManuallyDrop::new(created));
                self.num_elements.set(self.num_elements.get() + 1);
                Ok((key,  (&*the_slot.item.get()).as_ref().unwrap_unchecked()))
        }

        }
    }
    #[inline]
    pub fn insert(&self, value: T) -> (K, &T) {
        self.insert_with_key(|_| value)
    }

}

