use crate::key::{Key, KeyData};
use crate::numeric::Numeric;
use aliasable::boxed::AliasableBox;
use num_traits::{CheckedAdd, One, Zero};
use std::array::from_fn;
use std::cell::{Cell, UnsafeCell};
use std::hint;
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::ops::{Deref, Index, IndexMut};

pub const DEFAULT_SLOTS_NUM_PER_PAGE: usize = 32;

#[inline]
const fn slot_mask_from_capacity(cap: usize) -> usize {
    // cap must be a power of two, so mask is cap - 1
    cap - 1
}

#[inline]
const fn slot_bits_from_capacity(cap: usize) -> usize {
    // Ensure it's > 0 and a power of two.
    debug_assert!(cap.is_power_of_two());
    (usize::BITS - 1 - cap.leading_zeros()) as usize
}

pub struct SplitIdx {
    pub(crate) page_idx: usize,
    pub(crate) slot_idx: usize,
}

/// compresses the index of a page and the index of a slot into one, which is stored in keys
#[inline]
pub fn encode_index<Idx: Numeric>(page_idx: usize, slot_idx: usize, slots_num_per_page: usize) -> Idx {
    debug_assert!(slot_idx < slots_num_per_page);
    let combined = (page_idx << slot_bits_from_capacity(slots_num_per_page)) | slot_idx;
    Idx::from_usize(combined)
}

#[inline]
pub fn decode_index<Idx: Numeric>(idx: Idx, slots_num_per_page: usize) -> SplitIdx {
    let idx = idx.into_usize();

    let slot = idx & slot_mask_from_capacity(slots_num_per_page);
    let page = idx >> slot_bits_from_capacity(slots_num_per_page);
    SplitIdx {
        page_idx: page,
        slot_idx: slot,
    }
}

pub type StableGenMap<K: Key, T> = StablePagedGenMap<K, T, 1>;

/// Occupancy + intrusive free list
enum SlotVariant<T, K: Key> {
    /// Occupied slot with a value.
    Occupied(T),
    /// Vacant slot; `Option<K::Idx>` is the next free index, or None for end of free list.
    Vacant(Option<K::Idx>),
}

impl<T, K: Key> SlotVariant<T, K> {
    #[inline]
    fn is_occupied(&self) -> bool {
        matches!(self, SlotVariant::Occupied(_))
    }

    /// If occupied, take the value and make this slot Vacant(None).
    /// If already vacant, leave as-is and return None.
    #[inline]
    fn take_occupied(&mut self) -> Option<T> {
        use std::mem;
        match mem::replace(self, SlotVariant::Vacant(None)) {
            SlotVariant::Occupied(md) => Some(md),
            vacant @ SlotVariant::Vacant(_) => {
                // Restore old vacant state.
                *self = vacant;
                None
            }
        }
    }

    /// Get next_free from a vacant slot; UB if called on Occupied.
    #[inline]
    unsafe fn next_free_unchecked(&self) -> Option<K::Idx> {
        match self {
            SlotVariant::Vacant(next) => *next,
            SlotVariant::Occupied(_) => hint::unreachable_unchecked(),
        }
    }
}

struct Slot<T, K: Key> {
    item: UnsafeCell<SlotVariant<T, K>>,
    generation: K::Gen,
}

pub(crate) struct Page<T, K: Key, const SLOTS_NUM_PER_PAGE: usize> {
    slots: AliasableBox<[UnsafeCell<MaybeUninit<Slot<T, K>>>; SLOTS_NUM_PER_PAGE]>,
    length_used: usize,
}

impl<T: Clone, K: Key, const SLOTS_NUM_PER_PAGE: usize>  Page<T, K,SLOTS_NUM_PER_PAGE> {
    #[inline]
    unsafe fn clone(&self) -> Self {

            Self{
                slots: AliasableBox::from_unique(Box::new(
                    from_fn(|index|{
                        if self.length_used <= index {
                            UnsafeCell::new(MaybeUninit::uninit())
                        } else {
                            let assumed_init = (&*self.slots.as_ref().deref()[index].get()).assume_init_ref();
                            UnsafeCell::new(
                                MaybeUninit::new(
                                    Slot{
                                        generation: assumed_init.generation,
                                        item: UnsafeCell::new((&*assumed_init.item.get()).clone())
                                    }
                                )

                            )
                        }
                    }))
                ),
                length_used: self.length_used,
            }

    }
}
impl<T: Clone, K: Key> SlotVariant<T, K> {
    #[inline]
    unsafe fn clone(&self) -> Self{
        match self {
            Self::Occupied(item) => Self::Occupied(item.clone()),
            Self::Vacant(vacant) => Self::Vacant(vacant.clone()),
        }
    }
}
impl<T, K: Key,  const SLOTS_NUM_PER_PAGE: usize> Page<T, K, SLOTS_NUM_PER_PAGE> {
    #[inline]
    unsafe fn insert_slot(&mut self, slot: Slot<T, K>) -> usize {
        let gotten = self.slots.get_unchecked(self.length_used);
        let index = self.length_used;
        self.length_used += 1;
        *gotten.get() = MaybeUninit::new(slot);
        index
    }

    #[inline]
    unsafe fn new() -> Self {
        Self {
            slots: AliasableBox::from_unique(
                Box::new(
                    from_fn(|_|  UnsafeCell::new(MaybeUninit::uninit()))
                )
            ),
            length_used: 0,
        }
    }

    #[inline]
    fn get_slot(&self, slot_idx: usize) -> Option<&Slot<T, K>> {
        unsafe {
            if self.length_used <= slot_idx {
                None
            } else {
                Some(unsafe{ self.get_slot_unchecked(slot_idx) })
            }
        }

    }
    #[inline]
    unsafe fn get_slot_unchecked(&self, slot_idx: usize) -> &Slot<T, K> {

        (&*self.slots.get_unchecked(slot_idx).get()).assume_init_ref()

    }
    #[inline]
    unsafe fn get_slot_unchecked_mut(&mut self, slot_num: usize) -> &mut Slot<T, K> {

        self.slots
            .get_unchecked_mut(slot_num)
            .get_mut()
            .assume_init_mut()

    }

    #[inline]
    fn get_slot_mut(&mut self, slot_num: usize) -> Option<&mut Slot<T, K>> {
        if self.length_used <= slot_num {
            None
        } else {
            Some(unsafe { self.get_slot_unchecked_mut(slot_num) })
        }
    }

    // gets an index that is free, if possible
    #[inline]
    fn has_free_index(&self) -> bool {
        self.slots.len() > self.length_used
    }
}

impl<T, K: Key, const SLOTS_NUM_PER_PAGE: usize> Drop for Page<T, K, SLOTS_NUM_PER_PAGE> {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            for slot_cell in self.slots.iter_mut() {
                if self.length_used == 0 {
                    break;
                }
                self.length_used -= 1;
                slot_cell.get_mut().assume_init_read(); // dropped
            }
        }
    }
}

/// Paged Stable Gen Map with intrusive free list.
pub struct StablePagedGenMap<K: Key, T, const SLOTS_NUM_PER_PAGE: usize = DEFAULT_SLOTS_NUM_PER_PAGE> {
    pub(crate) pages: UnsafeCell<Vec<Page<T, K, SLOTS_NUM_PER_PAGE>>>,
    next_free: Cell<Option<K::Idx>>, // head of free-list
    phantom: PhantomData<fn(K)>,
    num_elements: Cell<usize>,
}

pub type DefaultStablePagedGenMap<K, T> = StablePagedGenMap<K, T, DEFAULT_SLOTS_NUM_PER_PAGE>;

impl<K: Key, T, const SLOTS_NUM_PER_PAGE: usize> Index<K>
for StablePagedGenMap<K, T, SLOTS_NUM_PER_PAGE>
{
    type Output = T;
    fn index(&self, key: K) -> &Self::Output {
        self.get(key).unwrap()
    }
}

impl<K: Key, T, const SLOTS_NUM_PER_PAGE: usize> IndexMut<K>
for StablePagedGenMap<K, T, SLOTS_NUM_PER_PAGE>
{
    fn index_mut(&mut self, key: K) -> &mut Self::Output {
        self.get_mut(key).unwrap()
    }
}

pub struct IterMut<'a, K: Key, T, const SLOTS_NUM_PER_PAGE: usize> {
    map: &'a StablePagedGenMap<K, T, SLOTS_NUM_PER_PAGE>,
    page_idx: usize,
    slot_idx: usize,
    _marker: PhantomData<&'a mut T>,
}

impl<K: Key, T, const SLOTS_NUM_PER_PAGE: usize> StablePagedGenMap<K, T, SLOTS_NUM_PER_PAGE>
{

    /// Returns a snapshot of the map at the current moment. it ignores future inserts
    /// NOTE: this does a heap allocation, and a heap deallocation when the snapshot drops
    /// #[inline]
    pub fn snapshot(&self) -> Vec<(K, &T)> {
        unsafe{
            let mut vec = Vec::with_capacity(self.len());
            vec.extend(self.iter_unsafe());
            vec
        }
    }

    #[inline]
    /// Iteration with this method is only safe if no mutation of the map occurs while iterating, which can happen even with safe code. For example, inserting while iterating with this is UB
    pub unsafe fn iter_unsafe(&self) -> impl Iterator<Item=(K, &T)> {
        (&*self.pages.get())
            .iter()
            .enumerate()
            .map(|(page_idx, page)| {
                page.slots
                    .iter()
                    .enumerate()
                    .filter_map(move |(slot_idx, slot)| unsafe {
                        if slot_idx  >= page.length_used {
                            return None;
                        }
                        let slot_pure = unsafe {(&*slot.get()).assume_init_ref()};
                        match  &*slot_pure.item.get() {
                            SlotVariant::Occupied(ref a) => Some(
                                (K::from(KeyData{idx: encode_index(page_idx,slot_idx,SLOTS_NUM_PER_PAGE),generation: slot_pure.generation}),
                                 a)),
                            _ => None
                        }
                    })
            })
            .flatten()
    }
    /// Returns a snapshot of the map at the current moment. it ignores future inserts
    /// NOTE: this does a heap allocation, and a heap deallocation when the snapshot drops
    #[inline]
    pub fn snapshot_iter(&self) -> <Vec<(K, &T)> as IntoIterator>::IntoIter {
        self.snapshot().into_iter()
    }

    /// Returns a snapshot of the current value references only (no keys).
    /// Future inserts are ignored. Allocates a single `Vec<&T>`.
    #[inline]
    pub fn snapshot_ref_only(&self) -> Vec<&T> {

        unsafe{
            let mut vec = Vec::with_capacity(self.len());
            vec.extend(
                self
                    .iter_unsafe()
                    .map(|x| x.1)
            );
            vec
        }
    }

    /// Returns a snapshot of the current keys only (no references).
    /// Future inserts are ignored. Allocates a single `Vec<K>`.
    #[inline]
    pub fn snapshot_key_only(&self) -> Vec<K> {
        unsafe{
            let mut vec = Vec::with_capacity(self.len());
            vec.extend(
                self
                    .iter_unsafe()
                    .map(|x| x.0)
            );
            vec
        }

    }


    /// Creates a new, empty PagedStableGenMap
    #[inline]
    pub const fn new() -> Self {
        const {
            assert!(SLOTS_NUM_PER_PAGE.is_power_of_two());
        }
        Self {
            pages: UnsafeCell::new(Vec::new()),
            next_free: Cell::new(None),
            phantom: PhantomData,
            num_elements: Cell::new(0),
        }
    }

    /// Gets a mutable iterator of the map, allowing mutable iteration between all elements
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, T, SLOTS_NUM_PER_PAGE> {
        IterMut {
            map: self,
            page_idx: 0,
            slot_idx: 0,
            _marker: PhantomData,
        }
    }


    /// A more efficient Clone operation than the Clone::clone implementation, but if the `Clone` implementation of `T` mutates the map, UB occurs
    #[inline]
    pub unsafe fn clone_efficiently(&self) -> Self where T: Clone {
        Self{
            num_elements: self.num_elements.clone(),
            phantom: PhantomData,
            next_free: self.next_free.clone(),
            pages: UnsafeCell::new((&*self.pages.get()).iter().map(|x| x.clone()).collect()),
        }
    }
    /// a more efficient Clone operation than the Clone::clone implementation. since done with a mutable reference, the `Clone` implementation of `T` cannot mutate the map without unsafe code
    /// so `clone_efficiently_mut` is safe
    #[inline]
    pub fn clone_efficiently_mut(&mut self) -> Self where T: Clone {
        unsafe {
            self.clone_efficiently()
        }

    }
    /// Gets a unique reference to an element
    #[inline]
    pub fn get_mut(&mut self, k: K) -> Option<&mut T> {
        let key_data = k.data();
        let split = decode_index::<K::Idx>(key_data.idx, SLOTS_NUM_PER_PAGE);
        let pages = self.pages.get_mut();
        let page = pages.get_mut(split.page_idx)?;

        let slot;


        if SLOTS_NUM_PER_PAGE == 1 {
            debug_assert!(split.slot_idx == 0);

            // Safety: Optimization. if the amount of slots per page is 1, the slot_idx will always be 0
            // and a page that only has a maximum of one slot, will always have that one slot to be initialized, based on the
            // insert logic
            slot = unsafe{  page.get_slot_unchecked_mut(0) };
        } else{
            slot = page.get_slot_mut(split.slot_idx)?
        }


        if slot.generation != key_data.generation {
            return None;
        }

        let variant: &mut SlotVariant<T, K> = slot.item.get_mut();
        match variant {
            SlotVariant::Occupied(ref mut md) => {
                // SAFETY: value is live; we never move the allocation.
                Some(md)
            }
            SlotVariant::Vacant(_) => None,
        }
    }
    /// Gets a shared reference to an element
    #[inline]
    pub fn get(&self, k: K) -> Option<&T> {
        let key_data = k.data();
        let split = decode_index::<K::Idx>(key_data.idx, SLOTS_NUM_PER_PAGE);
        let pages = unsafe { &*self.pages.get() };
        let page = pages.get(split.page_idx)?;

        let slot;

        if SLOTS_NUM_PER_PAGE == 1 {
            debug_assert!(split.slot_idx == 0);

            // Safety: Optimization. if the amount of slots per page is 1, the slot_idx will always be 0
            // and a page that only has a maximum of one slot, will always have that one slot to be initialized, based on the
            // insert logic
           slot = unsafe{  page.get_slot_unchecked(0) };
        } else{
            slot = page.get_slot(split.slot_idx)?
        }

        if slot.generation == key_data.generation {
            match unsafe { &*slot.item.get() } {
                SlotVariant::Occupied(md) => {
                    // SAFETY: ManuallyDrop<T> holds a valid T, never moved.
                    let ptr = md.deref() as *const T;
                    Some(unsafe { &*ptr })
                }
                SlotVariant::Vacant(_) => None,
            }
        } else {
            None
        }
    }

    /// Empties the map, removing all elements
    #[inline]
    pub fn clear(&mut self) {
        // Number of pages cannot change during `clear` because we never insert.
        let pages_len = self.pages.get_mut().len();

        for page_idx in 0..pages_len {

            let length_used = unsafe {
                let pages = self.pages.get_mut();
                pages.get_unchecked(page_idx).length_used
            };

            for slot_idx in 0..length_used {

                let generation = unsafe {
                    let pages = self.pages.get_mut();
                    pages.get_unchecked(page_idx)
                        .get_slot_unchecked(slot_idx)
                        .generation
                };


                let idx = encode_index::<K::Idx>(page_idx, slot_idx, SLOTS_NUM_PER_PAGE);
                let key = K::from(KeyData { idx, generation });

                let _ = self.remove(key);
            }
        }

        debug_assert_eq!(self.len(), 0);
    }

    /// Gets the number of elements in the map
    #[inline]
    pub fn len(&self) -> usize {
        self.num_elements.get()
    }

    /// Removes an element by key, returning its owned value.
    /// Removes only with &mut self. This is safe because the borrow checker
    /// prevents calling this while any &'_ T derived from &self is alive.
    /// A use case will be in, for example, freeing memory after the end of a frame in a video game
    #[inline]
    pub fn remove(&mut self, k: K) -> Option<T> {
        let key_data = k.data();
        let split = decode_index::<K::Idx>(key_data.idx, SLOTS_NUM_PER_PAGE);

        let pages = self.pages.get_mut();
        let page = pages.get_mut(split.page_idx)?;

        let slot = page.get_slot_mut(split.slot_idx)?;
        if slot.generation != key_data.generation {
            return None;
        }

        let variant = slot.item.get_mut();
        let md = variant.take_occupied()?;
        self.num_elements.set(self.num_elements.get() - 1);

        match slot.generation.checked_add(&K::Gen::one()) {
            Some(new_gen) => {
                slot.generation = new_gen;
                let old_head = self.next_free.get();
                *slot.item.get_mut() = SlotVariant::Vacant(old_head);
                self.next_free.set(Some(key_data.idx));
            }
            None => {
                // retire slot, keep it vacant and not in free list
                *slot.item.get_mut() = SlotVariant::Vacant(None);
            }
        }

        Some(md)
    }

    /// Inserts a value given by the inputted function into the map. The key where the
    /// value will be stored is passed into the inputted function.\
    /// # Examples
    /// ```
    /// # use stable_gen_map::key::DefaultKey;
    /// use stable_gen_map::stable_paged_gen_map::{ DefaultStablePagedGenMap};
    /// let mut sm = DefaultStablePagedGenMap::new();
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
    pub fn insert_with_key(&self, func: impl FnOnce(K) -> T) -> (K, &T) {
        self.try_insert_with_key::<()>(|key| Ok(func(key))).unwrap()
    }

    /// Same as insert_with_key but allowing the closure to return a Result.
    /// Inserts a value given by the inputted function into the map. The key where the
    /// value will be stored is passed into the inputted function.
    /// This is useful to store values that contain their own key.
    /// This version allows the closure to return a `Result`, so you can propagate errors.
    /// # Examples
    /// ```rust
    /// use stable_gen_map::key::DefaultKey;
    /// use stable_gen_map::stable_paged_gen_map::DefaultStablePagedGenMap;
    ///
    /// #[derive(Eq, PartialEq, Debug)]
    /// struct KeyHolder {
    ///     key: DefaultKey,
    /// }
    ///
    /// let sm = DefaultStablePagedGenMap::new();
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
    pub fn try_insert_with_key<E>(
        &self,
        func: impl FnOnce(K) -> Result<T, E>,
    ) -> Result<(K, &T), E> {
        unsafe {
            let pages = &mut *self.pages.get();

            // Case 1: reuse a free slot from the intrusive free list.
            if let Some(idx) = self.next_free.get() {
                let split = decode_index::<K::Idx>(idx, SLOTS_NUM_PER_PAGE);
                let page = pages.get_unchecked_mut(split.page_idx);
                let slot: &mut Slot<T, K> =
                    page.get_slot_mut(split.slot_idx).unwrap_unchecked();

                // Pop this slot from the free list.
                let next = (*slot.item.get()).next_free_unchecked();
                self.next_free.set(next);

                // Mark as reserved: not linked in the free list anymore.
                *slot.item.get_mut() = SlotVariant::Vacant(None);

                let generation = slot.generation;
                let key = K::from(KeyData { idx, generation });

                // RAII guard: if func panics/returns Err, put this index
                // back into the free list using the *current* head.
                let guard = FreeGuard {
                    map: self,
                    idx,
                };

                let value = func(key)?; // may panic / Err

                // Success: don't put it back into free list.
                guard.commit();

                // Re-borrow pages because func(key) may have re-entered and
                // caused pages to grow, etc.
                let pages = &mut *self.pages.get();
                let page = pages.get_unchecked_mut(split.page_idx);
                let slot: &mut Slot<T, K> =
                    page.get_slot_mut(split.slot_idx).unwrap_unchecked();

                *slot.item.get_mut() = SlotVariant::Occupied(value);
                self.num_elements.set(self.num_elements.get() + 1);

                // Build &T from ManuallyDrop.
                let value_ref: &T = match &*slot.item.get() {
                    SlotVariant::Occupied(md) => md,
                    SlotVariant::Vacant(_) => hint::unreachable_unchecked(),
                };

                Ok((key, value_ref))
            } else {
                // Case 2: no free slot; append into pages.
                let add_new_page = |pages: &mut Vec<Page<T, K, SLOTS_NUM_PER_PAGE>>| {
                    pages.push(Page::new());
                };

                if pages.last_mut().is_none() {
                    add_new_page(pages);
                }

                let mut last = pages.last_mut().unwrap_unchecked();
                if !last.has_free_index() {
                    add_new_page(pages);
                    last = pages.last_mut().unwrap_unchecked();
                }

                let slot_idx = last.insert_slot(Slot {
                    generation: K::Gen::zero(),
                    item: UnsafeCell::new(SlotVariant::Vacant(None)),
                });

                let page_idx = pages.len() - 1;
                let idx = encode_index(page_idx, slot_idx, SLOTS_NUM_PER_PAGE);
                let key_data = KeyData {
                    idx,
                    generation: K::Gen::zero(),
                };
                let key = K::from(key_data);

                // Guard: if func fails, this brand-new slot becomes a free slot.
                let guard = FreeGuard {
                    map: self,
                    idx: key_data.idx,
                };

                let created = func(key)?;
                guard.commit();

                let pages = &mut *self.pages.get();
                let page = pages.get_unchecked_mut(page_idx);
                let the_slot: &Slot<T, K> =
                    page.get_slot(slot_idx).unwrap_unchecked();

                *the_slot.item.get() = SlotVariant::Occupied(created);
                self.num_elements.set(self.num_elements.get() + 1);

                let value_ref: &T = match &*the_slot.item.get() {
                    SlotVariant::Occupied(md) => md,
                    SlotVariant::Vacant(_) => hint::unreachable_unchecked(),
                };

                Ok((key, value_ref))
            }
        }
    }

    /// Simple insert. When it inserts, it returns the key and reference.
    /// # Examples
    /// ```rust
    /// use stable_gen_map::key::DefaultKey;
    /// use stable_gen_map::stable_paged_gen_map::DefaultStablePagedGenMap;
    /// let sm = DefaultStablePagedGenMap::<DefaultKey,_>::new();
    /// let (key, reference) = sm.insert(4);
    /// assert_eq!(*reference, 4);
    /// assert_eq!(*sm.get(key).unwrap(), 4);
    ///```
    #[inline]
    pub fn insert(&self, value: T) -> (K, &T) {
        self.insert_with_key(|_| value)
    }
}

impl<K: Key, T: Clone, const SLOTS_NUM_PER_PAGE: usize> Clone for StablePagedGenMap<K, T, SLOTS_NUM_PER_PAGE>
{
    fn clone(&self) -> Self {
        unsafe {
            // Snapshot payload for each slot:
            // either a &T (for occupied) or the next_free index (for vacant).
            enum Snap<'a, K: Key, T> {
                Occupied(&'a T),
                Vacant(Option<K::Idx>),
            }

            let num_elements = self.len();
            let next_free = self.next_free.get();
            let pages_ref: &Vec<Page<T, K, SLOTS_NUM_PER_PAGE>> = &*self.pages.get();

            // 1) SNAPSHOT PHASE: read pages/slots once, no T::clone yet.
            //
            //    We gather, for each page:
            //      - its slot capacity
            //      - a Vec of (generation, Snap) for slots [0..length_used)
            //
            //    After this, we never touch self.pages / self.next_free again.
            let mut pages_snapshot: Vec< Vec<(K::Gen, Snap<'_, K, T>)>> =
                Vec::with_capacity(pages_ref.len());

            for page in pages_ref.iter() {

                let used = page.length_used;

                let mut slots_snap = Vec::with_capacity(used);
                for slot_idx in 0..used {
                    let slot: &Slot<T, K> = page
                        .get_slot(slot_idx)
                        .unwrap_unchecked();

                    let generation = slot.generation;
                    let variant: &SlotVariant<T, K> = &*slot.item.get();

                    let snap = match variant {
                        SlotVariant::Occupied(md) => {
                            // grab &T from ManuallyDrop<T>
                            Snap::Occupied(md)
                        }
                        SlotVariant::Vacant(next) => Snap::Vacant(*next),
                    };

                    slots_snap.push((generation, snap));
                }

                pages_snapshot.push(slots_snap);
            }

            // 2) REBUILD PHASE: build a fresh Vec<Page<..>> from the snapshot.
            //
            //    Now we *do* call T::clone, so user code can re-enter and
            //    mutate the ORIGINAL map via &self.insert(...). That’s fine:
            //    we never touch self.pages again, and we’re cloning from
            //    &T references which remain valid because inserts only
            //    use free slots / append and never overwrite existing Ts.
            let mut new_pages: Vec<Page<T, K, SLOTS_NUM_PER_PAGE>> =
                Vec::with_capacity(pages_snapshot.len());

            for slots_snap in pages_snapshot {
                // Recreate page with same capacity
                let mut new_page: Page<T, K, SLOTS_NUM_PER_PAGE> = Page::new();

                for (generation, snap) in slots_snap {
                    let item = match snap {
                        Snap::Occupied(vref) => {
                            // T::clone may re-enter and mutate the original map,
                            // but we only use the snapshot, so we’re safe.
                            SlotVariant::Occupied(vref.clone())
                        }
                        Snap::Vacant(next) => SlotVariant::Vacant(next),
                    };

                    let slot = Slot {
                        generation: generation,
                        item: UnsafeCell::new(item),
                    };

                    // writes Slot into the next uninit slot and bumps length_used
                    let _idx = new_page.insert_slot(slot);
                }

                new_pages.push(new_page);
            }

            Self {
                pages: UnsafeCell::new(new_pages),
                next_free: Cell::new(next_free),
                phantom: PhantomData,
                num_elements: Cell::new(num_elements),
            }
        }
    }
}

// Mutable iterator over paged map
impl<'a, K: Key, T, const SLOTS_NUM_PER_PAGE: usize> Iterator
for IterMut<'a, K, T, SLOTS_NUM_PER_PAGE>
{
    type Item = (K, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let pages: &Vec<Page<T, K, SLOTS_NUM_PER_PAGE>> = unsafe { &*self.map.pages.get() };

            if self.page_idx >= pages.len() {
                return None;
            }

            let page_idx = self.page_idx;
            let page = &pages[page_idx];

            if self.slot_idx >= page.length_used {
                self.page_idx += 1;
                self.slot_idx = 0;
                continue;
            }

            let slot_idx = self.slot_idx;
            self.slot_idx += 1;

            let slot = match page.get_slot(slot_idx) {
                Some(s) => s,
                None => continue,
            };

            // Get &mut SlotVariant<T, K> from &Slot<T, K> via UnsafeCell.
            let variant: &mut SlotVariant<T, K> =
                unsafe { &mut *slot.item.get() };

            let value: &mut T = match variant {
                SlotVariant::Occupied(ref mut md) => md,
                SlotVariant::Vacant(_) => continue,
            };

            // Encode global idx
            let idx =
                encode_index::<K::Idx>(page_idx, slot_idx, SLOTS_NUM_PER_PAGE);

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

// into_iter for &mut map uses IterMut
impl<'a, K: Key, T, const SLOTS_NUM_PER_PAGE: usize> IntoIterator
for &'a mut StablePagedGenMap<K, T, SLOTS_NUM_PER_PAGE>
{
    type Item = (K, &'a mut T);
    type IntoIter = IterMut<'a, K, T, SLOTS_NUM_PER_PAGE>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

// Owning iterator (consumes map)
pub struct IntoIter<K: Key, T, const SLOTS_NUM_PER_PAGE: usize> {
    pages: Vec<Page<T, K, SLOTS_NUM_PER_PAGE>>,
    page_idx: usize,
    slot_idx: usize,
    len: usize,
    _marker: PhantomData<K>,
}

impl<K: Key, T, const SLOTS_NUM_PER_PAGE: usize> Iterator
for IntoIter<K, T, SLOTS_NUM_PER_PAGE>
{
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

            let variant = slot.item.get_mut();
            let md = match std::mem::replace(
                variant,
                SlotVariant::Vacant(None),
            ) {
                SlotVariant::Occupied(md) => md,
                SlotVariant::Vacant(_) => continue,
            };

            let value = md;

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

impl<K: Key, T, const SLOTS_NUM_PER_PAGE: usize> IntoIterator
for StablePagedGenMap<K, T, SLOTS_NUM_PER_PAGE>
{
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

// RAII "reservation" for a single index in the intrusive free list.
struct FreeGuard<'a, K: Key, T, const SLOTS_NUM_PER_PAGE: usize> {
    map: &'a StablePagedGenMap<K, T, SLOTS_NUM_PER_PAGE>,
    idx: K::Idx,
}

impl<'a, K: Key, T, const SLOTS_NUM_PER_PAGE: usize> FreeGuard<'a, K, T, SLOTS_NUM_PER_PAGE> {
    fn commit(self) {
        std::mem::forget(self);
    }
}

impl<'a, K: Key, T, const SLOTS_NUM_PER_PAGE: usize> Drop
for FreeGuard<'a, K, T, SLOTS_NUM_PER_PAGE>
{
    fn drop(&mut self) {
        unsafe {
            let split = decode_index::<K::Idx>(self.idx, SLOTS_NUM_PER_PAGE);
            let pages = &mut *self.map.pages.get();
            let page = pages.get_unchecked_mut(split.page_idx);
            let slot: &mut Slot<T, K> =
                (&mut *page.slots.get_unchecked_mut(split.slot_idx).get_mut())
                    .assume_init_mut();

            // This guard is used only for reserved/vacant slots.
            debug_assert!(!matches!(
                &*slot.item.get(),
                SlotVariant::Occupied(_)
            ));

            // increment generation to invalidate previous indexes
            if let Some(checked_add) =
                slot.generation.checked_add(&K::Gen::one())
            {
                slot.generation = checked_add;

                let old_head = self.map.next_free.get();
                *slot.item.get_mut() = SlotVariant::Vacant(old_head);
                self.map.next_free.set(Some(self.idx));
            }
        }
    }
}
