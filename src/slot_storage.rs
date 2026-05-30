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

    /// Manually drop whatever the storage holds for the given state, in place —
    /// the occupied payload when `is_occupied`, otherwise the vacant
    /// representation.
    ///
    /// The design overlaps the two states in a union (see the trait note), and
    /// union fields have no drop glue, so nothing is dropped automatically: the
    /// implementation must drop the field that is live for the reported state.
    /// The vacant side is usually just a `Copy` free index and so needs nothing
    /// dropped, but an implementation whose vacant data is droppable must drop it
    /// here too.
    ///
    /// This is **not** the storage's destructor. The type's own `Drop` still
    /// runs afterwards and frees any surrounding allocation (e.g.
    /// [`BoxedSlot`](crate::boxed_slot::BoxedSlot)'s `Box`); this method only
    /// clears the union contents, which is the part that differs by occupancy.
    ///
    /// # Safety
    /// `is_occupied` must truthfully reflect the slot's current state, and the
    /// storage must not be used again afterwards.
    unsafe fn drop_contents(&mut self, is_occupied: bool);
}

/// Slot srograges that can provide `&mut Self::Output`.
///
/// # Safety
/// Same pointer-stability guarantees as [`SlotStorage`].
pub unsafe trait SlotStorageMutOutput: SlotStorage {
    /// # Safety
    /// Slot must be occupied.
    unsafe fn mut_output(&mut self) -> &mut Self::Output;
}

/// Per-slot storage that a [`GenMap`](crate::gen_map::GenMap) can clone.
///
/// # Safety
/// [`clone_storage`](Self::clone_storage) **must never cause the owning map to
/// be mutated** — in particular it must not re-enter through `&self` `insert`.
///
/// Cloning runs a single pass over the live slot vector with `&self` pointing
/// *into that vector's backing buffer*. A re-entrant `insert` could grow the
/// map and reallocate the buffer, freeing the memory `&self` refers to while
/// `clone_storage` is still executing — instant undefined behaviour, even
/// though `&self` is only read. A refcount bump (`Rc`/`Arc`/`&T`) or a `Copy`
/// is fine because it runs no user code and cannot re-enter; an owned deep
/// clone (`Box<T>`, `T`) is sound here **only** if the cloned value's `Clone`
/// does not touch the map.
///
/// The crate's storages enforce this by construction: they implement
/// `SlotStorageClone` only when their stored value implements
/// [`CloneGenMapPromise`](crate::clone_gen_map_promise::CloneGenMapPromise),
/// which is precisely the promise that the value's
/// `Clone` cannot mutate a `GenMap`. A custom storage that implements
/// `SlotStorageClone` directly takes on the same obligation by hand.
pub unsafe trait SlotStorageClone: SlotStorage {
    /// Clone the storage for the given occupancy. The occupied payload is
    /// duplicated when `is_occupied`, otherwise the vacant free-list index is
    /// copied.
    ///
    /// # Safety
    /// `is_occupied` must truthfully reflect the slot's current state, and this
    /// call must not mutate / re-enter the owning map (see the trait note).
    unsafe fn clone_storage(&self, is_occupied: bool) -> Self;
}
