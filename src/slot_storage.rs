use crate::key::Key;
use std::mem::ManuallyDrop;

// ─── SlotData (shared union) ─────────────────────────────────────────────────

/// The underlying union stored in each slot.
/// `S` is the stored payload type (`T` for BoxedSlot, `Ptr` for DerefSlot).
pub(crate) union SlotData<S, K: Key> {
    pub(crate) occupied: ManuallyDrop<S>,
    pub(crate) vacant: Option<K::Idx>,
}

// ─── trait: SlotStorage ─────────────────────────────────────────────────────────

/// Abstracts the per-slot storage strategy.
///
/// # Design: occupied and vacant share storage via a union
/// This trait is built around the expectation that an implementation overlaps
/// its occupied payload and its vacant free-list index in the **same** memory —
/// that is, a `union` is *involved* somewhere in the implementation. The
/// implementor itself need not be a union: the union may sit behind a `Box`
/// (as in [`BoxedSlot`](crate::boxed_slot::BoxedSlot)) or be nested in a field
/// (as in [`DerefSlot`](crate::deref_slot::DerefSlot)). A slot is never occupied
/// and vacant at the same time, so the two states can reuse one region and a
/// vacant slot costs no more than its payload.
///
/// Several method contracts follow directly from that design:
/// - Occupancy is **not** tracked by the storage; the owning `Slot` derives it
///   from its generation. So `get_vacant` / `set_vacant` / `write_occupied` /
///   `take_occupied` / `ref_output` / `stored_mut` cannot check the union tag
///   themselves and instead require the caller to promise the current state.
/// - The storage doesn't itself know whether it currently holds the occupied
///   payload or the vacant free index (the owning `Slot` tracks that via its
///   generation), so its own `Drop` can't tell which union field is live to
///   drop. The `Slot` instead drops the live field by hand through
///   [`drop_contents`](SlotStorage::drop_contents) — passing the occupancy it
///   knows — before the storage's `Drop` frees the surrounding allocation.
///
/// # Safety
/// Implementations must guarantee that references returned by
/// [`ref_output`](SlotStorage::ref_output) survive reallocation of the `Vec`
/// that owns the `Slot`.
pub unsafe trait SlotStorage: Sized {
    /// The key type used by the map that owns this slot.
    type Key: Key;

    /// What `insert` accepts and `remove` / `drain` return.
    type Stored;

    /// What shared references point to
    /// (`get` / `Index` return `&Self::Output`).
    type Output: ?Sized;

    fn new_vacant(next: Option<<Self::Key as Key>::Idx>) -> Self;

    /// # Safety
    /// Slot must be vacant.
    unsafe fn get_vacant(&self) -> Option<<Self::Key as Key>::Idx>;

    /// # Safety
    /// Slot must be vacant.
    unsafe fn set_vacant(&mut self, next: Option<<Self::Key as Key>::Idx>);

    /// # Safety
    /// Slot must be vacant / reserved (not occupied).
    unsafe fn write_occupied(&mut self, value: Self::Stored);

    /// Takes the value out, leaving the storage in a vacant-like state.
    /// # Safety
    /// Slot must be occupied.
    unsafe fn take_occupied(&mut self) -> Self::Stored;

    /// # Safety
    /// Slot must be occupied.
    unsafe fn ref_output(&self) -> &Self::Output;

    /// Mutable reference to the *stored* value (the `ManuallyDrop` payload).
    /// For `BoxedSlot` this is `&mut T`; for `DerefSlot` this is `&mut Ptr`.
    /// # Safety
    /// Slot must be occupied.
    unsafe fn stored_mut(&mut self) -> &mut Self::Stored;

    /// Manually drop whatever the storage holds depending on their `occupied` state.
    /// Designed to be used to drop state that is inside unions that rely on occupancy/
    ///
    /// This is **not** the storage's destructor. The type's own `Drop` still
    /// runs afterwards and frees any surrounding allocation (e.g.
    ///
    /// # Safety
    /// `is_occupied` must truthfully reflect the slot's current state, and the
    /// storage must not be used again afterwards.
    unsafe fn drop_contents(&mut self, is_occupied: bool);
}

/// Slot storage that can provide `&mut Self::Output`.
///
/// # Safety
/// Same pointer-stability guarantees as [`SlotStorage`].
pub unsafe trait SlotStorageMutOutput: SlotStorage {
    /// # Safety
    /// Slot must be occupied.
    unsafe fn mut_output(&mut self) -> &mut Self::Output;
}

/// Per-slot storage whose slots can be cloned. This is the *mechanical* clone
/// capability only: it says nothing about whether the clone is safe to run
/// while the owning map is borrowed.
///
/// Cloning an occupied slot may run arbitrary user code (e.g. `T::clone` for an
/// owned payload). The hazard is narrow: that code must not **mutate the map
/// being cloned** (for example, via `insert`) while the clone is in progress,
/// because the clone holds a borrow into the slot buffer and a mutation that
/// grows / reallocates it would dangle that borrow. Read-only re-entry is *not*
/// a problem — calling `get`, `len`, iterating, etc. on the same map is fine,
/// since it touches nothing about the buffer's allocation. Whether such a
/// mutation can happen depends on the caller's context, not on this trait:
/// - [`GenMap`](crate::gen_map::GenMap)'s `Clone` clones every slot in one pass
///   while holding a shared borrow into the slot buffer, so it requires the
///   extra [`NonMutatingSlotStorageClone`] promise (a re-entrant `insert` mid
///   pass would reallocate that buffer and dangle the borrow).
/// - [`GenMap::clone_mut`](crate::gen_map::GenMap::clone_mut) needs only this
///   trait: its `&mut self` borrow already rules out a concurrent `&self`
///   mutation such as `insert`.
/// - [`GenMap::unsafe_clone`](crate::gen_map::GenMap::unsafe_clone) needs only
///   this trait too, and shifts that obligation onto its caller.
///
/// # Safety
/// [`clone_storage`](Self::clone_storage) must faithfully reproduce the slot for
/// the stated occupancy. It carries no guarantee about mutating the map being
/// cloned; that is the job of [`NonMutatingSlotStorageClone`].
pub unsafe trait SlotStorageClone: SlotStorage {
    /// Clone the storage for the given occupancy. The occupied payload is
    /// duplicated when `is_occupied`, otherwise the vacant free-list index is
    /// copied.
    ///
    /// # Safety
    /// `is_occupied` must truthfully reflect the slot's current state.
    unsafe fn clone_storage(&self, is_occupied: bool) -> Self;
}

/// Promise that this storage's [`clone_storage`](SlotStorageClone::clone_storage)
/// **cannot mutate the [`GenMap`](crate::gen_map::GenMap) being cloned** (for
/// example, via `insert`/`reserve`) — so it is sound to call through a shared `&self`
/// during the map's single-pass clone. Only *mutation* matters here; a clone
/// that merely reads the map (`get`, `len`, iteration, …) is fine and does not
/// disqualify a storage.
///
/// This is the marker that unlocks `GenMap<C>: Clone`. Without it, a storage may
/// still cloneable through [`GenMap::clone_mut`](crate::gen_map::GenMap::clone_mut)
/// or the `unsafe` [`GenMap::unsafe_clone`](crate::gen_map::GenMap::unsafe_clone),
/// but not through the safe `&self` `Clone`.
///
/// The crate's storages obtain this by requiring their stored value to implement
/// [`CloneGenMapPromise`](crate::clone_gen_map_promise::CloneGenMapPromise),
/// which is exactly the value-level version of the same promise (a refcount bump
/// for `Rc`/`Arc`/`&T`, a `Copy`, or a deep clone whose contents are themselves
/// promised). A custom storage implements this directly, taking on the
/// obligation by hand.
///
/// # Safety
/// Implementing this for a storage whose [`clone_storage`](SlotStorageClone::clone_storage) implementation *can* mutate the map being cloned
/// (e.g. by `insert`ing into it) may allow
/// [`GenMap::clone`](crate::gen_map::GenMap) to trigger undefined behaviour.
pub unsafe trait NonMutatingSlotStorageClone: SlotStorageClone {}
