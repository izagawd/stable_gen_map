use aliasable::boxed::AliasableBox;
use std::cell::UnsafeCell;
use std::collections::TryReserveError;
use std::marker::PhantomData;
use std::ops::{Deref, Index, IndexMut};

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

pub struct IterMut<'a, K: Key, T: ?Sized> {
    ptr: *mut Slot<T>,
    len: usize,
    idx: usize,
    _marker: PhantomData<&'a mut T>,
    _key_marker: PhantomData<K>,
}

impl<K: Key, T: ?Sized> StableGenMap<K, T> {
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

impl<'a, K: Key, T: ?Sized> Iterator for IterMut<'a, K, T> {
    type Item = (K, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.len {
            let idx = self.idx;
            self.idx += 1;

            let slot: &mut Slot<T> = unsafe { &mut *self.ptr.add(idx) };

            let boxed = match slot.item.as_mut() {
                Some(b) => b,
                None => continue,
            };

            let key_data = KeyData {
                idx,
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

impl<'a, K: Key, T: ?Sized> IntoIterator for &'a mut StableGenMap<K, T> {
    type Item = (K, &'a mut T);
    type IntoIter = IterMut<'a, K, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
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


pub struct IntoIter<K: Key, T: ?Sized> {
    slots: std::vec::IntoIter<Slot<T>>,
    idx: usize,
    _marker: PhantomData<K>,
}

impl<K: Key, T: ?Sized> Iterator for IntoIter<K, T> {
    type Item = (K, Box<T>);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(slot) = self.slots.next() {
            let idx = self.idx;
            self.idx += 1;

            let alias = match slot.item {
                Some(a) => a,
                None => continue,
            };

            let key_data = KeyData {
                idx,
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

impl<K: Key, T: ?Sized> IntoIterator for StableGenMap<K, T> {
    type Item = (K, Box<T>);
    type IntoIter = IntoIter<K, T>;

    fn into_iter(self) -> Self::IntoIter {
        let slots_vec = self.slots.into_inner();
        IntoIter {
            slots: slots_vec.into_iter(),
            idx: 0,
            _marker: PhantomData,
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
    pub fn with_capacity(size: usize) -> Self {
        Self{
            slots: UnsafeCell::new(Vec::with_capacity(size)),
            free: UnsafeCell::new(Vec::new()),
            phantom: PhantomData
        }
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




            let slots = &mut *self.slots.get();
            let free  = &mut *self.free.get();

            if let Some(idx) = free.pop() {
                let mut the_slot = slots.get_unchecked_mut(idx);
                let generation = the_slot.generation;
                let key = K::from(KeyData { idx, generation });

                // RAII "reservation" for a single index in `free`.
                struct FreeGuard<'a, K: Key, T: ?Sized> {
                    map: &'a StableGenMap<K, T>,
                    idx: usize,
                }

                impl<'a, K: Key, T: ?Sized> FreeGuard<'a, K, T> {
                    fn commit(self) {
                        std::mem::forget(self);
                    }
                }

                impl<'a, K: Key, T: ?Sized> Drop for FreeGuard<'a, K, T> {
                    fn drop(&mut self) {

                        unsafe {
                            // Put the index back on the free list.
                            let free = &mut *self.map.free.get();
                            free.push(self.idx);
                            let generation = &mut (&mut *self.map.slots.get()).get_unchecked_mut(self.idx).generation;
                            *generation = generation.wrapping_add(1);
                            // increment generation to invalidate previous indexes
                        }
                    }
                }

                // to avoid memory leaks if func(key) panics
                let mut free_guard = FreeGuard{
                    map: self,
                    idx,
                };
                let value = func(key);

                if let Err(error) =  value{
                    return Err(error);
                }
                free_guard.commit();
                let value = value.unwrap_unchecked();
                /* SAFETY: We are reassigning slots here, to avoid double mut ub, since func can re-enter "try_insert_with_key"*/

                let slots = &mut *self.slots.get();


                /*
                SAFETY: func(key) might have caused a resize, changing the memory address of the_slot, so this is necessary
                to ensure we are pointing to valid memory
                 */
                the_slot = slots.get_unchecked_mut(idx);


                the_slot.item = Some(AliasableBox::from(value));
                let the_box = &*the_slot.item.as_ref().unwrap();
                let ptr = the_box.deref() as *const T;
                Ok((key,&*ptr ))
            } else {
                let idx = slots.len();
                let key = K::from(KeyData { idx, generation: 0 });
                slots.push(Slot {
                    generation: 0,
                    item: None,
                });


                let created = func(key);
                if let Err(error) =  created {
                    return Err(error);
                }
                let created = created.unwrap_unchecked();


                let acquired : & mut _ = slots.get_unchecked_mut(idx);


                acquired.item = Some(AliasableBox::from(created));

                Ok((key, acquired.item.as_ref().unwrap_unchecked().deref()))
            }
        }
    }

    #[inline]
    pub fn insert(&self, value: Box<T>) -> (K, &T) {
        self.insert_with_key(|_| value)
    }

}

