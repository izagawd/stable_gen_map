use crate::cast_key::{CastKey, StableCastKey};
use crate::key::DefaultKey;
use crate::stable_cast_map::StableBoxCastMap;
use crate::key::Key;

use std::any::Any;
use std::collections::HashSet;

type CastMap = StableBoxCastMap<DefaultKey, dyn Any>;

// ─── StableCastKey trait impls ──────────────────────────────────────────────

#[test]
fn cast_key_is_copy() {
    let map: CastMap = CastMap::new();
    let (key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let copy = key;
    assert_eq!(key, copy);
}

#[test]
fn cast_key_clone_equals_original() {
    let map: CastMap = CastMap::new();
    let (key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let clone = key.clone();
    assert_eq!(key, clone);
}

#[test]
fn cast_key_debug_does_not_panic() {
    let map: CastMap = CastMap::new();
    let (key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let _ = format!("{:?}", key);
}

#[test]
fn cast_key_hash_consistent_with_eq() {
    let map: CastMap = CastMap::new();
    let (k1, _) = map.insert(Box::new(1i32) as Box<dyn Any>);
    let (k2, _) = map.insert(Box::new(2i32) as Box<dyn Any>);

    let mut set = HashSet::new();
    set.insert(k1);
    assert!(set.contains(&k1));
    assert!(!set.contains(&k2));
}

#[test]
fn different_map_ids_produce_unequal_keys() {
    let map_a: CastMap = CastMap::new();
    let map_b: CastMap = CastMap::new();
    let (ka, _) = map_a.insert(Box::new(1i32) as Box<dyn Any>);
    let (kb, _) = map_b.insert(Box::new(1i32) as Box<dyn Any>);
    // keys have different map ids, so not equal even if same index
    assert_ne!(ka, kb);
}

// ─── inner_key ─────────────────────────────────────────────────────────────

#[test]
fn inner_key_strips_metadata() {
    let map: CastMap = CastMap::new();
    let (cast_key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);

    let inner: DefaultKey = cast_key.inner_key();
    assert_eq!(inner.data().idx, cast_key.key_data().idx);
    assert_eq!(inner.data().generation, cast_key.key_data().generation);
}

#[test]
fn inner_key_usable_for_get_by_inner_key() {
    let map: CastMap = CastMap::new();
    let (cast_key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);

    let inner = cast_key.inner_key();
    let val = map.get_by_inner_key(inner).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
}

// ─── upcast ─────────────────────────────────────────────────────────────────

trait Animal: Any {
    fn name(&self) -> &str;
}

#[derive(Debug)]
struct Dog {
    name: String,
}

impl Animal for Dog {
    fn name(&self) -> &str {
        &self.name
    }
}

#[test]
fn upcast_sized_to_dyn_any() {
    let map: CastMap = CastMap::new();
    let (dyn_key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let sized_key: StableCastKey<i32> = map.downcast_key::<i32>(dyn_key).unwrap();

    let back = sized_key.upcast::<dyn Any>();
    assert!(map.get(back).is_some());
}

#[test]
fn map_id_survives_upcast() {
    let map: CastMap = CastMap::new();
    let (dyn_key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let sized_key: StableCastKey<i32> = map.downcast_key::<i32>(dyn_key).unwrap();

    let upcasted = sized_key.upcast::<dyn Any>();
    assert_eq!(dyn_key.map_id(), upcasted.map_id());
}

#[test]
fn upcast_sized_to_dyn_trait() {
    type TraitMap = StableBoxCastMap<DefaultKey, dyn Animal>;
    let map: TraitMap = TraitMap::new();
    let (key, _) = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Animal>);

    let val = map.get(key).unwrap();
    assert_eq!(val.name(), "Rex");
}

#[test]
fn upcast_preserves_key_data() {
    let map: CastMap = CastMap::new();
    let (dyn_key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let sized_key = map.downcast_key::<i32>(dyn_key).unwrap();

    let upcasted = sized_key.upcast::<dyn Any>();
    assert_eq!(sized_key.key_data().idx, upcasted.key_data().idx);
    assert_eq!(
        sized_key.key_data().generation,
        upcasted.key_data().generation
    );
}

// ─── StableCastKey accessors ────────────────────────────────────────────────

#[test]
fn stable_cast_key_map_id_matches_map() {
    let map: CastMap = CastMap::new();
    let (key, _) = map.insert(Box::new(1i32) as Box<dyn Any>);
    assert_eq!(key.map_id(), map.map_id());
}

#[test]
fn all_keys_from_same_map_share_map_id() {
    let map: CastMap = CastMap::new();
    let (k1, _) = map.insert(Box::new(1i32) as Box<dyn Any>);
    let (k2, _) = map.insert(Box::new(2i32) as Box<dyn Any>);
    let (k3, _) = map.insert_sized(Box::new(Dog { name: "Rex".into() }));
    assert_eq!(k1.map_id(), k2.map_id());
    assert_eq!(k2.map_id(), k3.map_id());
}

#[test]
fn cast_key_accessor_returns_inner_without_map_id() {
    let map: CastMap = CastMap::new();
    let (stable_key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let bare: CastKey<dyn Any> = stable_key.cast_key();

    assert_eq!(bare.key_data(), stable_key.key_data());
}

// ─── downcast then upcast round-trip ────────────────────────────────────────

#[test]
fn downcast_then_upcast_round_trips() {
    let map: CastMap = CastMap::new();
    let (original, _) = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);

    let concrete = map.downcast_key::<Dog>(original).unwrap();
    let back = concrete.upcast::<dyn Any>();

    // the upcast key should still be usable
    let val = map.get(back).unwrap();
    assert_eq!(val.downcast_ref::<Dog>().unwrap().name, "Rex");
}
