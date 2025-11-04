use aliasable::boxed::AliasableBox;
use std::cell::UnsafeCell;
use std::marker::PhantomData;
use std::mem::{ManuallyDrop, MaybeUninit};
use std::ops::{Deref, Index};


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

impl<K: PagedKey,T> PagedStableGenMap<K,T> {


    #[inline]
    pub const fn new() -> Self {
        Self {
            pages: UnsafeCell::new(Vec::new()),
            free: UnsafeCell::new(Vec::new()),
            phantom: PhantomData,
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
    pub fn insert_with(&self, func: impl FnOnce(K) -> T) -> (K, &T) {
        unsafe{
            let pages =  &mut *self.pages.get();

            let free_spaces = &mut *self.free.get();

            if let Some(free) = free_spaces.pop() {
                let page = pages.get_mut(free.page).unwrap();
                let the_slot = page.get_slot_mut(free.idx).unwrap();
                let generation = the_slot.generation;
                let key = K::from(PagedKeyData { idx: free.idx,page: free.page,  generation, });


                let value = func(key);


                /* SAFETY: We are reassigning  here, to avoid double mut ub, since func can re-enter "insert_with"*/

                let pages = &mut *self.pages.get();
                let page = pages.get_mut(free.page).unwrap();


                /*
                SAFETY: func(key) might have caused a resize, changing the memory address of the_slot, so this is necessary
                to ensure we are pointing to valid memory
                 */
                let the_slot = page.get_slot(free.idx).unwrap();


                *the_slot.item.get() = Some(ManuallyDrop::new(value));
                let items_ref = (&*the_slot.item.get()).as_ref().map(|x| ManuallyDrop::deref(x)).unwrap();
                let ptr = items_ref as *const T;
                (key, &*ptr )
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

                let created = func(key);

                /* SAFETY: We are reassigning  here, to avoid double mut ub, since func can re-enter "insert_with"*/

                let pages = &mut *self.pages.get();
                let page =pages.get_unchecked_mut(key_data.page);


                let the_slot =  page.get_slot(key_data.idx).unwrap_unchecked();

                *the_slot.item.get() = Some(ManuallyDrop::new(created));

                (key,  (&*the_slot.item.get()).as_ref().unwrap_unchecked())
        }

        }
    }
    #[inline]
    pub fn insert(&self, value: T) -> (K, &T) {
        self.insert_with(|_| value)
    }

}

