//! Pointer-stability and `remove`/`retype` round-trip tests for the cast maps.
//!
//! Run under Miri (ideally both borrow models):
//!   cargo +nightly miri test --features castable castable_pointer_stability
//!   MIRIFLAGS="-Zmiri-tree-borrows" cargo +nightly miri test --features castable castable_pointer_stability
//!
//! These cover:
//!   * a concrete `&T` from `get` surviving `insert(&self)` reallocation;
//!   * `remove` reconstructing the typed `Box<T>` / `Rc<T>` / `Arc<T>` from the
//!     erased storage, with `Rc`/`Arc` strong counts preserved (validates the
//!     `into_raw`/`from_raw` offset reasoning in `RetypePtr`);
//!   * `upcast` then `remove` reconstructing a valid `Box<dyn Any>` from a
//!     vtable (the fat-pointer retype path).

use crate::cast_key::StableCastKey;
use crate::deref_slot::DerefSlot;
use crate::key::DefaultKey;
use crate::stable_cast_map::{StableBoxCastMap, StableCastMap};
use std::any::Any;
use std::rc::Rc;
use std::sync::Arc;

type BoxCastMap = StableBoxCastMap<DefaultKey, dyn Any>;
type RcCastMap = StableCastMap<DerefSlot<DefaultKey, Rc<dyn Any>>>;
type ArcCastMap = StableCastMap<DerefSlot<DefaultKey, Arc<dyn Any>>>;

const N: i32 = 1_000;

#[derive(Debug, PartialEq)]
struct Dog {
    name: String,
}

// ─── reference stability across reallocation ─────────────────────────────────

/// A concrete typed `&Dog`, reconstructed from the erased `Box<dyn Any>` via the
/// cast key, must survive `insert(&self)` reallocations. The reference points
/// into the boxed `Dog` allocation, which is stable across `Vec` growth.
#[test]
fn castable_concrete_reference_survives_insert_reallocation() {
    let map: BoxCastMap = BoxCastMap::new();

    let dog_key = map.insert_sized(Box::new(Dog { name: "Rex".into() }));
    let dog_ref: &Dog = map.get(dog_key).unwrap();

    for i in 0..N {
        map.insert(Box::new(i) as Box<dyn Any>);
    }

    assert_eq!(dog_ref.name, "Rex");
}

// ─── remove / retype round-trips ─────────────────────────────────────────────

/// `Box`-backed: `remove` with a concrete key returns `Box<T>` with the right
/// value, and the slot is emptied.
#[test]
fn castable_remove_box_round_trip() {
    let mut map: BoxCastMap = BoxCastMap::new();

    let dog_key = map.insert_sized(Box::new(Dog { name: "Rex".into() }));
    let removed: Box<Dog> = map.remove(dog_key).unwrap();

    assert_eq!(*removed, Dog { name: "Rex".into() });
    assert_eq!(map.len(), 0);
    assert!(map.get(dog_key).is_none());
}

/// `Rc`-backed: `remove` returns `Rc<T>`. The strong count must be exactly
/// preserved through `into_raw`/`from_raw` — if the reconstructed allocation
/// offset were wrong, Miri would flag the control-block access.
#[test]
fn castable_remove_rc_preserves_strong_count() {
    let mut map: RcCastMap = RcCastMap::new();

    let outside = Rc::new(7i32);
    let key: StableCastKey<i32, DefaultKey> = map.insert_sized(Rc::clone(&outside));
    assert_eq!(Rc::strong_count(&outside), 2);

    let removed: Rc<i32> = map.remove(key).unwrap();
    assert_eq!(*removed, 7);
    // The map's strong ref was handed back retyped, not duplicated or leaked.
    assert_eq!(Rc::strong_count(&outside), 2);

    drop(removed);
    assert_eq!(Rc::strong_count(&outside), 1);
    assert!(map.remove(key).is_none());
}

/// `Arc`-backed: same as the `Rc` case.
#[test]
fn castable_remove_arc_preserves_strong_count() {
    let mut map: ArcCastMap = ArcCastMap::new();

    let outside = Arc::new(7i32);
    let key: StableCastKey<i32, DefaultKey> = map.insert_sized(Arc::clone(&outside));
    assert_eq!(Arc::strong_count(&outside), 2);

    let removed: Arc<i32> = map.remove(key).unwrap();
    assert_eq!(*removed, 7);
    assert_eq!(Arc::strong_count(&outside), 2);

    drop(removed);
    assert_eq!(Arc::strong_count(&outside), 1);
}

// ─── upcast then remove (fat-pointer retype) ─────────────────────────────────

/// Upcasting a concrete key to `dyn Any` and then removing reconstructs a valid
/// `Box<dyn Any>` from the stored vtable metadata; the recovered value must
/// still downcast to the original concrete type.
#[test]
fn castable_upcast_then_remove_reconstructs_dyn_any() {
    let mut map: BoxCastMap = BoxCastMap::new();

    let dog_key = map.insert_sized(Box::new(Dog { name: "Rex".into() }));
    let dyn_key = dog_key.upcast::<dyn Any>();

    let removed: Box<dyn Any> = map.remove(dyn_key).unwrap();
    assert_eq!(removed.downcast_ref::<Dog>().unwrap().name, "Rex");
    assert_eq!(map.len(), 0);
}
