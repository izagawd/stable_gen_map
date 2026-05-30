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

/// Slot items that can provide `&mut Self::Output`.
///
/// # Safety
/// Same pointer-stability guarantees as [`SlotStorage`].
pub unsafe trait SlotStorageMutOutput: SlotStorage {
    /// # Safety
    /// Slot must be occupied.
    unsafe fn mut_output(&mut self) -> &mut Self::Output;
}

/// Slot items that can be cloned without going through a two-phase snapshot.
///
/// # Safety
/// `clone_storage` must correctly reproduce the slot's payload.
pub unsafe trait SlotStorageClone: SlotStorage {
    /// Whether cloning an *occupied* slot runs user code that could re-enter
    /// the owning map.
    ///
    /// - `false` — cloning has no chance of mutating a [`GenMap`](crate::gen_map::GenMap) (ie via insert).
    ///   `Clone` uses a fast single pass ([`clone_efficiently`](crate::gen_map::GenMap::clone_efficiently)).
    /// - `true` — cloning may re-enter the map via
    ///   `&self` `insert`, so `GenMap`'s `Clone` uses a two-phase snapshot and
    ///   reconstructs each occupied slot through `clone_occupied_from_output`.
    const CLONE_MAY_REENTER: bool;

    /// Owned, per-slot side data captured during phase one of the two-phase
    /// clone, before any (possibly re-entrant) `Output::clone` runs.
    ///
    /// This exists so a storage can carry data that does **not** live behind
    /// its pointer-stable [`Output`](SlotStorage::Output) — for example a
    /// per-slot tag or `MapId` — and still reproduce it on clone. Because the
    /// type has no lifetime parameter, the compiler guarantees a
    /// [`snapshot_slot`](Self::snapshot_slot) value cannot borrow from the
    /// slot, so it survives any reallocation a re-entrant `insert` triggers.
    ///
    /// Storages with no extra per-slot data (and storages that never re-enter)
    /// use `()`.
    type CloneSnapshot;

    /// Clone the slot storage.
    /// # Safety
    /// `is_occupied` must truthfully reflect the slot state.
    unsafe fn clone_storage(&self, is_occupied: bool) -> Self;

    /// Phase one of the two-phase clone: capture this slot's owned side data
    /// ([`CloneSnapshot`](Self::CloneSnapshot)) by value.
    ///
    /// Called for **every** slot regardless of occupancy: the side data this
    /// captures lives outside the occupied/vacant payload, so it is reproduced
    /// for vacant slots ([`clone_vacant_from_snapshot`](Self::clone_vacant_from_snapshot))
    /// and occupied slots ([`clone_occupied_from_output`](Self::clone_occupied_from_output))
    /// alike. It must therefore read only occupancy-independent state — never
    /// the payload union.
    ///
    /// Runs before any `Output::clone`, so reading `&self` here is sound: no
    /// re-entrant `insert` has had a chance to reallocate the slot vector yet.
    /// The returned value is owned (it cannot borrow `self`), so phase two may
    /// keep it across the re-entrant clone.
    ///
    /// Implementations **must not** themselves mutate or re-enter the owning
    /// map. Only invoked when `CLONE_MAY_REENTER` is `true`; other storages may
    /// leave the default (it is never reached).
    ///
    /// # Safety
    /// No occupancy requirement; may be called on any slot of this storage.
    unsafe fn snapshot_slot(&self) -> Self::CloneSnapshot {
        unreachable!(
            "snapshot_slot was called on a SlotStorage whose \
             CLONE_MAY_REENTER is false; this is a bug in the SlotStorage impl"
        )
    }

    /// Phase two of the two-phase clone, occupied case: reconstruct an
    /// *occupied* slot from the owned [`snapshot`](Self::CloneSnapshot) captured
    /// in phase one plus the slot's pointer-stable
    /// [`Output`](SlotStorage::Output) reference, rather than from the live slot.
    ///
    /// Only invoked by `GenMap`'s `Clone` when `CLONE_MAY_REENTER` is `true`:
    /// phase one captures the stable `&Output` (guaranteed stable by the
    /// [`SlotStorage`] safety contract) together with `snapshot`, and phase two
    /// calls this to clone the payload, so any re-entrant `insert` triggered by
    /// `Output::clone` only mutates the *new* map. `snapshot` is owned, so it is
    /// equally safe to hold across that re-entry. Storages with
    /// `CLONE_MAY_REENTER == false` never reach this and may leave the default.
    ///
    /// # Safety
    /// `output` must be the [`Output`](SlotStorage::Output) of an occupied slot
    /// of this storage type, and `snapshot` must be the value returned by
    /// [`snapshot_slot`](Self::snapshot_slot) for that same slot.
    unsafe fn clone_occupied_from_output(
        _snapshot: Self::CloneSnapshot,
        _output: &Self::Output,
    ) -> Self {
        unreachable!(
            "clone_occupied_from_output was called on a SlotStorage whose \
             CLONE_MAY_REENTER is false; this is a bug in the SlotStorage impl"
        )
    }

    /// Phase two of the two-phase clone, vacant case: reconstruct a *vacant*
    /// slot from its owned [`snapshot`](Self::CloneSnapshot) and free-list
    /// successor index.
    ///
    /// The default ignores `snapshot` and defers to
    /// [`new_vacant`](SlotStorage::new_vacant), which is correct for storages
    /// whose side data is empty (`CloneSnapshot = ()`) or carried only by
    /// occupied slots. Override it to preserve per-slot side data (e.g. a tag)
    /// across the clone of a vacant slot. Only invoked when `CLONE_MAY_REENTER`
    /// is `true`.
    ///
    /// # Safety
    /// `snapshot` must be the value returned by
    /// [`snapshot_slot`](Self::snapshot_slot) for the slot being rebuilt.
    unsafe fn clone_vacant_from_snapshot(
        snapshot: Self::CloneSnapshot,
        next: Option<<Self::Key as Key>::Idx>,
    ) -> Self {
        let _ = snapshot;
        Self::new_vacant(next)
    }
}
