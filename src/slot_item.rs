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

    /// # Safety: slot must be vacant.
    unsafe fn get_vacant(&self) -> Option<<Self::Key as Key>::Idx>;

    /// # Safety: slot must be vacant.
    unsafe fn set_vacant(&mut self, next: Option<<Self::Key as Key>::Idx>);

    /// # Safety: slot must be vacant / reserved (not occupied).
    unsafe fn write_occupied(&mut self, value: Self::Stored);

    /// Takes the value out, leaving the storage in a vacant-like state.
    /// # Safety: slot must be occupied.
    unsafe fn take_occupied(&mut self) -> Self::Stored;

    /// # Safety: slot must be occupied.
    unsafe fn ref_output(&self) -> &Self::Output;

    /// Mutable reference to the *stored* value (the `ManuallyDrop` payload).
    /// For `BoxedSlot` this is `&mut T`; for `DerefSlot` this is `&mut Ptr`.
    /// # Safety: slot must be occupied.
    unsafe fn stored_mut(&mut self) -> &mut Self::Stored;

    /// Drop the occupied value in place.
    /// # Safety: slot must be occupied.
    unsafe fn drop_occupied(&mut self);
}

/// Slot items that can provide `&mut Self::Output`.
///
/// # Safety
/// Same pointer-stability guarantees as [`SlotStorage`].
pub unsafe trait SlotStorageMutOutput: SlotStorage {
    /// # Safety: slot must be occupied.
    unsafe fn mut_output(&mut self) -> &mut Self::Output;
}

/// Slot items that can be cloned without going through a two-phase snapshot.
///
/// # Safety
/// `clone_storage` must correctly reproduce the slot's payload.
pub unsafe trait SlotStorageClone: SlotStorage {
    /// Whether cloning an *occupied* slot runs user code that could re-enter
    /// the owning map (e.g. an owning payload whose `Output::clone` gets
    /// called).
    ///
    /// - `false` — cloning only duplicates the stored pointer / bumps a
    ///   refcount and cannot touch the map, so [`GenMap`](crate::gen_map::GenMap)'s
    ///   `Clone` uses a fast single pass (`clone_efficiently`).
    /// - `true` — cloning runs `Output::clone`, which may re-enter the map via
    ///   `&self` `insert`, so `GenMap`'s `Clone` uses a two-phase snapshot and
    ///   reconstructs each occupied slot through `clone_occupied_from_output`.
    const CLONE_MAY_REENTER: bool;

    /// Clone the slot storage.
    /// # Safety: `is_occupied` must truthfully reflect the slot state.
    unsafe fn clone_storage(&self, is_occupied: bool) -> Self;

    /// Reconstruct an *occupied* slot's storage from its pointer-stable
    /// [`Output`](SlotStorage::Output) reference rather than from the live slot.
    ///
    /// Only invoked by `GenMap`'s `Clone` when `CLONE_MAY_REENTER` is `true`:
    /// phase one captures the stable `&Output` (guaranteed stable by the
    /// [`SlotStorage`] safety contract), and phase two calls this to clone it,
    /// so any re-entrant `insert` triggered by `Output::clone` only mutates the
    /// *new* map. Storages with `CLONE_MAY_REENTER == false` never reach this
    /// and may leave the default.
    ///
    /// # Safety
    /// `output` must be the [`Output`](SlotStorage::Output) of an occupied slot
    /// of this storage type.
    unsafe fn clone_occupied_from_output(_output: &Self::Output) -> Self {
        unreachable!(
            "clone_occupied_from_output was called on a SlotStorage whose \
             CLONE_MAY_REENTER is false; this is a bug in the SlotStorage impl"
        )
    }
}
