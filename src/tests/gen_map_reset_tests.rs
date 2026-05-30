//! Tests for [`GenMap::reset`](crate::gen_map::GenMap::reset).
//!
//! `reset` empties the map, winds every slot's generation back to zero, and
//! keeps capacity. Unlike `clear`, it does **not** invalidate outstanding keys:
//! later inserts reproduce key values already handed out, so a pre-`reset` key
//! can silently resolve to a *different* value. Memory-safe, but a logic hazard.
//!
//! These tests are feature-independent — `GenMap` does not require `castable`.

use crate::boxed_slot::StableGenMap;
use crate::key::DefaultKey;

/// `reset` empties the map.
#[test]
fn gen_map_reset_empties_the_map() {
    let mut map: StableGenMap<DefaultKey, i32> = StableGenMap::new();
    for i in 0..32 {
        map.insert(i);
    }
    assert_eq!(map.len(), 32);

    map.reset();

    assert_eq!(map.len(), 0);
    assert!(map.is_empty());
}

/// `reset` keeps the allocated capacity.
#[test]
fn gen_map_reset_retains_capacity() {
    let mut map: StableGenMap<DefaultKey, i32> = StableGenMap::with_capacity(64);
    for i in 0..64 {
        map.insert(i);
    }
    let cap_before = map.capacity();
    assert!(cap_before >= 64);

    map.reset();

    assert_eq!(
        map.capacity(),
        cap_before,
        "reset must not release capacity"
    );
}

/// The documented hazard: a pre-`reset` key can match a slot again and resolve
/// to a *different* value, because generations are wound back to zero and the
/// next inserts reproduce key values already handed out.
#[test]
fn gen_map_reset_reuses_keys_and_is_a_silent_hazard() {
    let mut map: StableGenMap<DefaultKey, i32> = StableGenMap::new();

    let k = map.insert(1);
    assert_eq!(*map.get(k).unwrap(), 1);

    map.reset();

    // After reset the key no longer points at anything (map is empty)...
    assert!(map.get(k).is_none(), "map is empty right after reset");

    // ...but re-inserting reproduces the exact same key value, so the *stale*
    // key now silently resolves to the new value. This is the logic hazard the
    // docs warn about.
    let k2 = map.insert(999);
    assert_eq!(k, k2, "reset winds generations back, so keys collide");
    assert_eq!(
        *map.get(k).unwrap(),
        999,
        "stale key now resolves to a different value"
    );
}

/// Contrast with `clear`, which bumps generations so old keys stay invalid.
#[test]
fn gen_map_clear_invalidates_keys_unlike_reset() {
    let mut map: StableGenMap<DefaultKey, i32> = StableGenMap::new();

    let k = map.insert(1);
    map.clear();
    let k2 = map.insert(999);

    assert_ne!(k, k2, "clear must not reuse a previously-issued key");
    assert!(
        map.get(k).is_none(),
        "old key must stay invalid after clear"
    );
}

/// `reset` on an already-empty map is a harmless no-op.
#[test]
fn gen_map_reset_on_empty_is_noop() {
    let mut map: StableGenMap<DefaultKey, i32> = StableGenMap::new();
    map.reset();
    assert_eq!(map.len(), 0);

    let k = map.insert(7);
    assert_eq!(*map.get(k).unwrap(), 7);
}
