use std::rc::Rc;
use std::sync::Arc;

// ─── CloneGenMapPromise ──────────────────────────────────────────────────────

/// A promise that `Self`'s [`Clone`] implementation cannot **mutate** a
/// [`GenMap`](crate::core::gen_map::GenMap) — for example, by calling `insert` (or
/// anything else that grows / reallocates one) — directly or transitively while
/// it runs. Only mutation matters: a `Clone` that merely *reads* a map (`get`,
/// `len`, iteration, …) is fine, because reads touch nothing about the buffer's
/// allocation.
///
/// This is the cloning counterpart of
/// [`DerefGenMapPromise`](crate::slots::deref_slot::DerefGenMapPromise). It exists
/// because a `GenMap` clones its slots in a single pass while holding a shared
/// borrow into the slot buffer (see
/// [`SlotStorageClone`](crate::core::slot_storage::SlotStorageClone)); a stored value
/// whose `Clone` mutated and reallocated that buffer mid-clone would invalidate
/// the borrow — undefined behaviour. Requiring stored values to implement this
/// trait is how [`BoxedSlot`](crate::slots::boxed_slot::BoxedSlot) and
/// [`DerefSlot`](crate::slots::deref_slot::DerefSlot) earn the
/// [`NonMutatingSlotStorageClone`](crate::core::slot_storage::NonMutatingSlotStorageClone)
/// marker, and is why a `GenMap` of an owned payload whose `Clone` *might*
/// mutate the map is simply not `Clone` (though it is still `clone_mut`-able).
///
/// Shared handles (`Rc`/`Arc`/`&T`) qualify unconditionally — cloning them is a
/// refcount bump or a pointer copy and runs no user code. Owned containers
/// (`Box<T>`, `Vec<T>`, `Option<T>`) deep-clone their contents, so they qualify
/// exactly when the contents do. Scalars and `String` qualify because their
/// `Clone` only copies bytes or a heap buffer.
///
/// # Examples
/// A type that is `Clone` but **not** `CloneGenMapPromise` produces a `GenMap`
/// that is itself not `Clone` — this is the gate that keeps a clone that might
/// mutate the map out of [`GenMap::clone`](crate::core::gen_map::GenMap):
///
/// ```compile_fail
/// use stable_gen_map::slots::boxed_slot::StableGenMap;
/// use stable_gen_map::keys::key::DefaultKey;
///
/// #[derive(Clone)]
/// struct NotPromised(i32);
///
/// let m: StableGenMap<DefaultKey, NotPromised> = StableGenMap::new();
/// // error: `NotPromised: !CloneGenMapPromise`, so the map is not `Clone`.
/// let _ = m.clone();
/// ```
///
/// # Safety
/// Implementing this for a type whose `Clone` *can* mutate a `GenMap` (e.g. by
/// `insert`ing into it) allows [`GenMap::clone`](crate::core::gen_map::GenMap) to
/// trigger undefined behaviour.
pub unsafe trait CloneGenMapPromise: Clone {}

// Shared handles: clone is a refcount bump / copy — runs no user code, so it
// cannot mutate a map.
unsafe impl<T: ?Sized> CloneGenMapPromise for Rc<T> {}
unsafe impl<T: ?Sized> CloneGenMapPromise for Arc<T> {}
unsafe impl<T: ?Sized> CloneGenMapPromise for &T {}

// Owned containers: safe exactly when their contents are.
unsafe impl<T: CloneGenMapPromise> CloneGenMapPromise for Box<T> {}
unsafe impl<T: CloneGenMapPromise> CloneGenMapPromise for Box<[T]> {}
unsafe impl<T: CloneGenMapPromise> CloneGenMapPromise for Option<T> {}
unsafe impl<T: CloneGenMapPromise, E: CloneGenMapPromise> CloneGenMapPromise for Result<T, E> {}
unsafe impl<T: CloneGenMapPromise> CloneGenMapPromise for Vec<T> {}

// Scalars / owned leaves whose `Clone` copies bytes or a heap buffer.
macro_rules! clone_gen_map_promise_leaf {
    ($($t:ty)*) => { $( unsafe impl CloneGenMapPromise for $t {} )* };
}
clone_gen_map_promise_leaf!(
    () bool char
    u8 u16 u32 u64 u128 usize
    i8 i16 i32 i64 i128 isize
    f32 f64
    String
    Box<str>
);
