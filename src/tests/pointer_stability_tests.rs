//! Pointer-stability / aliasing tests for the crate's central invariant:
//! a `&Output` obtained from `get(&self)` must remain valid across
//! `insert(&self)` calls that reallocate the backing `Vec`.
//!
//! These are written to be run under Miri, ideally both borrow models:
//!   cargo +nightly miri test pointer_stability
//!   MIRIFLAGS="-Zmiri-tree-borrows" cargo +nightly miri test pointer_stability
//!
//! A plain `cargo test` only checks the values; Miri is what validates the
//! `UnsafeCell` reborrow + reallocation does not invalidate the held reference.

use crate::boxed_slot::StableGenMap;
use crate::deref_slot::StableDerefMap;
use crate::key::DefaultKey;
use std::rc::Rc;
use std::sync::Arc;

// Enough inserts to guarantee several growth/reallocation cycles of the Vec.
const N: i32 = 1_000;

// ─── BoxedSlot (StableGenMap) ────────────────────────────────────────────────

/// A reference taken *before* a long run of `insert(&self)` must survive the
/// reallocations those inserts trigger. This is the core promise of the crate.
#[test]
fn boxed_reference_survives_insert_reallocation() {
    let map: StableGenMap<DefaultKey, i32> = StableGenMap::new();

    let first = map.insert(1234);
    let first_ref: &i32 = map.get(first).unwrap();

    // Force many reallocations while the reference above is live.
    let mut keys = Vec::new();
    for i in 0..N {
        keys.push(map.insert(i));
    }

    // The pre-realloc reference must still point at the original value.
    assert_eq!(*first_ref, 1234);

    // Everything inserted afterwards is reachable too.
    for (i, k) in keys.iter().enumerate() {
        assert_eq!(*map.get(*k).unwrap(), i as i32);
    }
}

/// Many references, each taken between inserts, must *all* stay valid as later
/// inserts reallocate. Stresses that a new `get`/`insert` does not pop an
/// earlier reference's provenance off the borrow stack.
#[test]
fn boxed_many_references_survive_interleaved_inserts() {
    let map: StableGenMap<DefaultKey, String> = StableGenMap::new();

    let mut refs: Vec<&String> = Vec::new();
    for i in 0..500 {
        let k = map.insert(format!("value-{i}"));
        refs.push(map.get(k).unwrap());
    }

    for (i, r) in refs.iter().enumerate() {
        assert_eq!(*r, &format!("value-{i}"));
    }
}

// ─── DerefSlot (StableDerefMap) ──────────────────────────────────────────────

/// Same invariant for `Box`-backed deref storage: the `&Output` points into the
/// user's `Box` allocation, which must outlive `Vec` reallocation.
#[test]
fn deref_box_reference_survives_insert_reallocation() {
    let map: StableDerefMap<DefaultKey, Box<i32>> = StableDerefMap::new();

    let first = map.insert(Box::new(4321));
    let first_ref: &i32 = map.get(first).unwrap();

    for i in 0..N {
        map.insert(Box::new(i));
    }

    assert_eq!(*first_ref, 4321);
}

/// `Rc`-backed storage: the held `&Output` must survive reallocation, and the
/// stored `Rc`'s strong count must not be corrupted when the `Vec` memcpy's the
/// pointer during growth.
#[test]
fn deref_rc_reference_and_refcount_survive_reallocation() {
    let map: StableDerefMap<DefaultKey, Rc<i32>> = StableDerefMap::new();

    let outside = Rc::new(4321);
    let k = map.insert(Rc::clone(&outside));
    assert_eq!(Rc::strong_count(&outside), 2);

    let first_ref: &i32 = map.get(k).unwrap();

    for i in 0..N {
        map.insert(Rc::new(i));
    }

    assert_eq!(*first_ref, 4321);
    // Reallocation must not have touched the stored Rc's control block.
    assert_eq!(Rc::strong_count(&outside), 2);
}

/// `Arc`-backed storage, same as above.
#[test]
fn deref_arc_reference_and_refcount_survive_reallocation() {
    let map: StableDerefMap<DefaultKey, Arc<i32>> = StableDerefMap::new();

    let outside = Arc::new(4321);
    let k = map.insert(Arc::clone(&outside));
    assert_eq!(Arc::strong_count(&outside), 2);

    let first_ref: &i32 = map.get(k).unwrap();

    for i in 0..N {
        map.insert(Arc::new(i));
    }

    assert_eq!(*first_ref, 4321);
    assert_eq!(Arc::strong_count(&outside), 2);
}
