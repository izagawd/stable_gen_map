use std::ops::Deref;
use std::cell::{Cell, UnsafeCell};
use std::marker::PhantomData;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct KeyData{
    pub(crate) generation: u32,
    pub(crate) idx: usize
}
pub unsafe trait Key : Copy + From<KeyData>{
    fn data(&self) -> KeyData;
}
#[derive(Copy, Clone)]
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
    generation: u32,
    is_inserting: Cell<bool>,
    val: Option<Box<T>>,
}


pub struct StableGenMap<K: Key, T: ?Sized> {
    slots: UnsafeCell<Vec<Slot<T>>>,
    free:  UnsafeCell<Vec<usize>>,
    phantom: PhantomData<fn(K)>,
}

impl<K: Key,T: ?Sized> StableGenMap<K,T> {
    pub const fn new() -> Self {
        Self {
            slots: UnsafeCell::new(Vec::new()),
            free: UnsafeCell::new(Vec::new()),
            phantom: PhantomData,
        }
    }


    /// Shared access to a value by key (no guard, plain &T).
    pub fn get(&self, k: K) -> Option<&T> {

        let key_data = k.data();
        let slot = unsafe { &*self.slots.get() }.get(key_data.idx)?;
        if slot.is_inserting.get(){
            None
        }
        else if slot.generation == key_data.generation {
            // SAFETY: value is live; we never move the Box's allocation.
            Some(unsafe { &*(&**slot.val.as_ref()? as *const T) })
        } else {
            None
        }
    }

    /* Remove only with &mut self. This is safe because the borrow checker
    prevents calling this while any &'_ T derived from &self is alive.
    A use case will be in, for example, freeing memory after the end of a frame in a video game */
    pub fn remove(&mut self, k: K) -> Option<Box<T>> {

        let slot = self.slots.get_mut().get_mut(k.data().idx)?;
        if slot.generation != k.data().generation { return None; }
        let boxed = slot.val.take()?;
        slot.generation = slot.generation.wrapping_add(1);
        self.free.get_mut().push(k.data().idx);
        Some(boxed)
    }
    #[inline]
    pub fn insert_with(&self, func: impl FnOnce(K) -> Box<T>) -> (K, &T) {
        let slots = unsafe { &mut *self.slots.get() };
        let free  = unsafe { &mut *self.free.get() };

        if let Some(idx) = free.pop() {
            let mut the_slot = &mut slots[idx];
            let generation = the_slot.generation;
            let key = K::from(KeyData { idx, generation });

            the_slot.is_inserting.set(true);
            let value = func(key);


            /* SAFETY: We are reassigning slots here, to avoid double mut ub, since func can re-enter "insert_with"*/

            let slots = unsafe { &mut *self.slots.get() };


            /*
            SAFETY: func(key) might have caused a resize, changing the memory address of the_slot, so this is necessary
            to ensure we are pointing to valid memory
             */
            the_slot = &mut slots[idx];


            the_slot.is_inserting.set(false);
            the_slot.val = Some(value);
            let the_box = &*the_slot.val.as_ref().unwrap();
            let ptr = the_box.deref() as *const T;
            (key, unsafe { &*ptr })
        } else {
            let idx = slots.len();
            let key = K::from(KeyData { idx, generation: 0 });


            slots.push(Slot {
                generation: 0,
                is_inserting: Cell::new(true),
                val: None,
            });
            let created = func(key);

            //SAFETY: we are reassigning slot here, to avoid double mut ub, since func can re-enter "insert_with"
            let slots = unsafe { &mut *self.slots.get() };

            let acquired : & mut _ = &mut slots[idx];
            acquired.is_inserting.set(false);
            acquired.val = Some(created);

            (key, unsafe{ acquired.val.as_ref().unwrap_unchecked().deref()})
        }
    }
    #[inline]
    pub fn insert(&self, value: Box<T>) -> (K, &T) {
        self.insert_with(|key| value)
    }

}

