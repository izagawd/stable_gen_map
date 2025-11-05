use std::ops::{Deref, Index, IndexMut};
use std::cell::{UnsafeCell};
use std::collections::TryReserveError;
use std::marker::PhantomData;
use aliasable::boxed::AliasableBox;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct KeyData{
    pub(crate) generation: usize,
    pub(crate) idx: usize
}
pub unsafe trait Key : Copy + From<KeyData> {
    fn data(&self) -> KeyData;
}
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct DefaultKey{
    pub(crate) key_data: KeyData,
}

impl From<KeyData> for DefaultKey{
    fn from(key_data: KeyData) -> Self {
        DefaultKey{key_data: key_data}
    }
}

unsafe impl Key for DefaultKey{
    fn data(&self) -> KeyData{
        self.key_data
    }
}
struct Slot<T: ?Sized> {
    generation: usize,
    item: Option<AliasableBox<T>>,
}
impl<T: Clone> Clone for Slot<T> {
    fn clone(&self) -> Self {
        Self{
            generation: self.generation,
            item:  self.item.as_ref().map(|x| AliasableBox::from_unique(Box::new( (*x).clone())) ),
        }
    }
}
pub struct StableGenMap<K: Key, T: ?Sized> {
    slots: UnsafeCell<Vec<Slot<T>>>,
    free:  UnsafeCell<Vec<usize>>,
    phantom: PhantomData<fn(K)>,
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
impl<K: Key,T: Clone> Clone for StableGenMap<K,T> {
    fn clone(&self) -> Self {
        unsafe{
            Self{
                slots: UnsafeCell::new((&*self.slots.get()).clone()),
                free: UnsafeCell::new((&*self.free.get()).clone()),
                phantom: PhantomData,
            }
        }

    }
}
impl<K: Key,T: ?Sized> StableGenMap<K,T> {

    #[inline]
    pub fn clear(&mut self){
        self.slots.get_mut().clear();
        self.free.get_mut().clear();

    }
    #[inline]
    pub const fn new() -> Self {
        Self {
            slots: UnsafeCell::new(Vec::new()),
            free: UnsafeCell::new(Vec::new()),
            phantom: PhantomData,
        }
    }
    #[inline]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
       unsafe { &mut *self.slots.get() }.try_reserve(additional)
    }
    #[inline]
    pub fn reserve(&self, additional_size: usize){
        unsafe { &mut *self.slots.get() }.reserve(additional_size);
    }
    /// Shared access to a value by key (no guard, plain &T).
    #[inline]
    pub fn get(&self, k: K) -> Option<&T> {

        let key_data = k.data();
        let slot = unsafe { &*self.slots.get() }.get(key_data.idx)?;
        if  slot.generation == key_data.generation {
            // SAFETY: value is live; we never move the Box's allocation.
            Some(unsafe { &*(&**slot.item.as_ref()? as *const T) })
        }
        else {
            None
        }
    }

    #[inline]
    pub fn get_mut(&mut self, k: K) -> Option<&mut T> {

        let key_data = k.data();
        let slot = self.slots.get_mut().get_mut(key_data.idx)?;
        if  slot.generation == key_data.generation {
            // SAFETY: value is live; we never move the Box's allocation.
            Some(slot.item.as_mut()?.as_mut())
        }
        else {
            None
        }
    }

    /* Remove only with &mut self. This is safe because the borrow checker
    prevents calling this while any &'_ T derived from &self is alive.
    A use case will be in, for example, freeing memory after the end of a frame in a video game */
    #[inline]
    pub fn remove(&mut self, k: K) -> Option<Box<T>> {
        let key_data = k.data();
        let slot = self.slots.get_mut().get_mut(key_data.idx)?;
        if slot.generation != key_data.generation { return None; }
        let boxed = slot.item.take()?;
        slot.generation = slot.generation.wrapping_add(1);
        self.free.get_mut().push(key_data.idx);
        Some(AliasableBox::into_unique(boxed))
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        unsafe { &*self.slots.get() }.capacity()
    }
    #[inline]
    pub fn insert_with_key(&self, func: impl FnOnce(K) -> Box<T>) -> (K, &T){
        self.try_insert_with_key::<()>(|key| Ok(func(key))).unwrap()
    }
    #[inline]
    pub fn try_insert_with_key<E>(&self, func: impl FnOnce(K) -> Result<Box<T>,E>) -> Result<(K, &T),E> {
        unsafe {
            let slots = unsafe { &mut *self.slots.get() };
            let free  = unsafe { &mut *self.free.get() };

            if let Some(idx) = free.pop() {
                let mut the_slot = unsafe { slots.get_unchecked_mut(idx) };
                let generation = the_slot.generation;
                let key = K::from(KeyData { idx, generation });


                let value = func(key);
                let mut free = &mut *self.free.get();
                if let Err(error) =  value{
                    free.push(idx);
                    return Err(error);
                }
                let value = unsafe{ value.unwrap_unchecked()};
                /* SAFETY: We are reassigning slots here, to avoid double mut ub, since func can re-enter "insert_with"*/

                let slots = unsafe { &mut *self.slots.get() };


                /*
                SAFETY: func(key) might have caused a resize, changing the memory address of the_slot, so this is necessary
                to ensure we are pointing to valid memory
                 */
                the_slot = unsafe {slots.get_unchecked_mut(idx)};


                the_slot.item = Some(AliasableBox::from(value));
                let the_box = &*the_slot.item.as_ref().unwrap();
                let ptr = the_box.deref() as *const T;
                Ok((key, unsafe { &*ptr }))
            } else {
                let idx = slots.len();
                let key = K::from(KeyData { idx, generation: 0 });



                let created = func(key);
                if let Err(error) =  created {
                    return Err(error);
                }
                let created = created.unwrap_unchecked();
                //SAFETY: we are reassigning slot here, to avoid double mut ub, since func can re-enter "insert_with"
                let slots = unsafe { &mut *self.slots.get() };

                slots.push(Slot {
                    generation: 0,
                    item: None,
                });

                let acquired : & mut _ = unsafe {slots.get_unchecked_mut(idx)};


                acquired.item = Some(AliasableBox::from(created));

                Ok((key, unsafe{ acquired.item.as_ref().unwrap_unchecked().deref()}))
            }
        }
    }

    #[inline]
    pub fn insert(&self, value: Box<T>) -> (K, &T) {
        self.insert_with_key(|_| value)
    }

}

