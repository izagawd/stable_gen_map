//! Tests for `reset` on the cast maps.
//!
//! * [`StableCastMap::reset`](crate::cast::stable_cast_map::StableCastMap::reset)
//!   mints a fresh `MapId`, so pre-`reset` keys fail the id check and safe
//!   lookups return `None`.
//! * [`UnsafeCastMap::reset`](crate::cast::unsafe_cast_map::UnsafeCastMap::reset) has
//!   no `MapId`, so it carries the same key-collision hazard as
//!   `GenMap::reset`; the unsafe lookups already require valid metadata.
//!
//! Requires the `castable` feature.

use crate::cast::cast_key::StableCastKey;
use crate::keys::key::DefaultKey;
use crate::cast::stable_cast_map::StableBoxCastMap;
use crate::cast::unsafe_cast_map::UnsafeBoxCastMap;
use std::any::Any;

#[derive(Debug, PartialEq)]
struct Dog {
    name: String,
}

// ─── StableCastMap::reset ────────────────────────────────────────────────────

type SafeMap = StableBoxCastMap<DefaultKey, dyn Any>;

/// `reset` empties the map and keeps capacity.
#[test]
fn stable_cast_map_reset_empties_and_retains_capacity() {
    let mut map: SafeMap = SafeMap::new();
    for i in 0..16 {
        map.insert(Box::new(i as i32) as Box<dyn Any>);
    }
    assert_eq!(map.len(), 16);
    let cap_before = map.capacity();

    map.reset();

    assert_eq!(map.len(), 0);
    assert_eq!(
        map.capacity(),
        cap_before,
        "reset must not release capacity"
    );
}

/// `reset` mints a fresh `MapId`.
#[test]
fn stable_cast_map_reset_changes_map_id() {
    let mut map: SafeMap = SafeMap::new();
    let id_before = map.map_id();

    map.reset();

    assert_ne!(map.map_id(), id_before, "reset must assign a fresh MapId");
}

/// The safety guarantee: even though generations are wound back (so a stale
/// key's index+generation would match a recycled slot), the fresh `MapId` makes
/// the pre-`reset` key fail the id check, and a *safe* `get` returns `None`
/// instead of reinterpreting a slot of a different type.
#[test]
fn stable_cast_map_reset_invalidates_stale_keys_via_map_id() {
    let mut map: SafeMap = SafeMap::new();

    // Stash a String, then reset and recycle the slot with a different type.
    let key = map.insert(Box::new("hello".to_string()) as Box<dyn Any>);
    assert_eq!(
        map.get(key).unwrap().downcast_ref::<String>().unwrap(),
        "hello"
    );

    map.reset();

    // Recycle the same slot/generation with an i32.
    let _new = map.insert(Box::new(42i32) as Box<dyn Any>);

    // The stale key would generation-match, but the MapId check rejects it.
    assert!(
        map.get(key).is_none(),
        "stale key must fail the MapId check after reset"
    );
}

/// Keys issued after `reset` work normally.
#[test]
fn stable_cast_map_reset_then_insert_works() {
    let mut map: SafeMap = SafeMap::new();
    map.insert(Box::new(1i32) as Box<dyn Any>);

    map.reset();

    let dog_key: StableCastKey<Dog> = map.insert_sized(Box::new(Dog { name: "Rex".into() }));
    assert_eq!(map.get(dog_key).unwrap().name, "Rex");
    assert_eq!(map.len(), 1);
}

// ─── UnsafeCastMap::reset ────────────────────────────────────────────────────

type UnsafeMap = UnsafeBoxCastMap<DefaultKey, dyn Any>;

/// `reset` empties the map and keeps capacity.
#[test]
fn unsafe_cast_map_reset_empties_and_retains_capacity() {
    let mut map: UnsafeMap = UnsafeMap::new();
    for i in 0..16 {
        map.insert(Box::new(i as i32) as Box<dyn Any>);
    }
    assert_eq!(map.len(), 16);
    let cap_before = map.capacity();

    map.reset();

    assert_eq!(map.len(), 0);
    assert_eq!(
        map.capacity(),
        cap_before,
        "reset must not release capacity"
    );
}

/// The documented hazard: `UnsafeCastMap` has no `MapId`, so after `reset` a
/// stale key's generation can match a recycled slot again. Here we reinsert the
/// *same* concrete type (`Dog`), which keeps the reinterpretation sound, and
/// show the stale key now reads the new value through `get_unchecked`.
#[test]
fn unsafe_cast_map_reset_reuses_keys_same_type_is_sound() {
    let mut map: UnsafeMap = UnsafeMap::new();

    let key = map.insert_sized(Box::new(Dog { name: "Rex".into() }));
    unsafe {
        assert_eq!(map.get_unchecked(key).name, "Rex");
    }

    map.reset();

    // Recycle the slot with the SAME concrete type so the stale key's metadata
    // stays valid — only then is using the stale key sound.
    let key2 = map.insert_sized(Box::new(Dog {
        name: "Fido".into(),
    }));
    assert_eq!(key, key2, "reset winds generations back, so keys collide");

    unsafe {
        // Stale `key` now matches the recycled slot and reads the new value.
        assert_eq!(map.get_unchecked(key).name, "Fido");
    }
}

/// Keys issued after `reset` work normally.
#[test]
fn unsafe_cast_map_reset_then_insert_works() {
    let mut map: UnsafeMap = UnsafeMap::new();
    map.insert(Box::new(1i32) as Box<dyn Any>);

    map.reset();

    let key = map.insert(Box::new(7i32) as Box<dyn Any>);
    unsafe {
        assert_eq!(*map.get_unchecked(key).downcast_ref::<i32>().unwrap(), 7);
    }
    assert_eq!(map.len(), 1);
}
