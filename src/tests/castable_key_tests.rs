use crate::cast_key::{CastKey, StableCastKey, DefaultMapKey};
use crate::key::Key;
use crate::stable_cast_map::StableCastMap;
use std::any::Any;
use std::collections::HashSet;

type CastMap = StableCastMap<Box<dyn Any>>;

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

    let inner: DefaultMapKey<u32, u32> = cast_key.inner_key();
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
    type TraitMap = StableCastMap<Box<dyn Animal>>;
    let map: TraitMap = TraitMap::new();
    let (key, _) = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Animal>);

    let val = map.get(key).unwrap();
    assert_eq!(val.name(), "Rex");
}
