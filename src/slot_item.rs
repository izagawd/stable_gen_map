use crate::key::Key;
use std::mem::ManuallyDrop;

// ─── SlotData (shared union) ─────────────────────────────────────────────────

/// The underlying union stored in each slot.
/// `S` is the stored payload type (`T` for BoxedSlot, `D` for DerefSlot).
pub(crate) union SlotData<S, K: Key> {
    pub(crate) occupied: ManuallyDrop<S>,
    pub(crate) vacant: Option<K::Idx>,
}

// ─── trait: SlotItem ─────────────────────────────────────────────────────────

/// Abstracts the per-slot storage strategy.
///
/// # Safety
/// Implementations must guarantee that references returned by
/// [`ref_output`](SlotItem::ref_output) survive reallocation of the `Vec`
/// that owns the `Slot`.
pub unsafe trait SlotItem<K: Key>: Sized {
    /// What `insert` accepts and `remove` / `drain` return.
    type Stored;

    /// What shared references point to
    /// (`get` / `Index` return `&Self::Output`).
    type Output: ?Sized;

    fn new_vacant(next: Option<K::Idx>) -> Self;

    /// # Safety: slot must be vacant.
    unsafe fn get_vacant(&self) -> Option<K::Idx>;

    /// # Safety: slot must be vacant.
    unsafe fn set_vacant(&mut self, next: Option<K::Idx>);

    /// # Safety: slot must be vacant / reserved (not occupied).
    unsafe fn write_occupied(&mut self, value: Self::Stored);

    /// Takes the value out, leaving the item in a vacant-like state.
    /// # Safety: slot must be occupied.
    unsafe fn take_occupied(&mut self) -> Self::Stored;

    /// # Safety: slot must be occupied.
    unsafe fn ref_output(&self) -> &Self::Output;

    /// Mutable reference to the *stored* value (the `ManuallyDrop` payload).
    /// For `BoxedSlot` this is `&mut T`; for `DerefSlot` this is `&mut D`.
    /// # Safety: slot must be occupied.
    unsafe fn stored_mut(&mut self) -> &mut Self::Stored;

    /// Drop the occupied value in place.
    /// # Safety: slot must be occupied.
    unsafe fn drop_occupied(&mut self);
}

/// Slot items that can provide `&mut Self::Output`.
///
/// # Safety
/// Same pointer-stability guarantees as [`SlotItem`].
pub unsafe trait SlotItemMutOutput<K: Key>: SlotItem<K> {
    /// # Safety: slot must be occupied.
    unsafe fn mut_output(&mut self) -> &mut Self::Output;
}

/// Slot items that can be cloned without going through a two-phase snapshot.
///
/// # Safety
/// `clone_item` must correctly reproduce the slot's payload.
pub unsafe trait SlotItemClone<K: Key>: SlotItem<K> {
    /// Clone the slot item.
    /// # Safety: `is_occupied` must truthfully reflect the slot state.
    unsafe fn clone_item(&self, is_occupied: bool) -> Self;
}
