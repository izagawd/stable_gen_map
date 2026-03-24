use crate::cast_key::{CastKey, DefaultCastKey};
use crate::map_id::MapIdState;
use crate::stable_cast_map::StableCastMap;
use std::any::Any;

trait Animal: Any {
    fn speak(&self) -> &'static str;
}

trait Flyer {
    fn max_altitude(&self) -> u32;
}

struct Dog;
impl Animal for Dog {
    fn speak(&self) -> &'static str {
        "woof"
    }
}

struct Parrot;
impl Animal for Parrot {
    fn speak(&self) -> &'static str {
        "squawk"
    }
}
impl Flyer for Parrot {
    fn max_altitude(&self) -> u32 {
        500
    }
}

// ─── from_castable_parts round-trips ────────────────────────────────────────

#[test]
fn castable_parts_round_trip_sized() {
    let state = MapIdState::new();
    let map_id = state.ensure_id();
    let data = crate::key::KeyData {
        idx: 42u32,
        generation: 7u32,
    };

    let key = unsafe { DefaultCastKey::<Dog>::from_castable_parts(data, map_id, ()) };
    assert_eq!(key.key_data().idx, 42);
    assert_eq!(key.key_data().generation, 7);
    assert_eq!(key.map_id(), map_id);
    assert_eq!(key.metadata(), ());
}

#[test]
fn castable_parts_round_trip_dyn() {
    let state = MapIdState::new();
    let map_id = state.ensure_id();
    let data = crate::key::KeyData {
        idx: 10u32,
        generation: 3u32,
    };

    // Get a real dyn Any vtable from a concrete type
    let dog = Dog;
    let dog_ref: &dyn Any = &dog;
    let metadata = std::ptr::metadata(dog_ref as *const dyn Any);

    let key = unsafe { DefaultCastKey::<dyn Any>::from_castable_parts(data, map_id, metadata) };
    assert_eq!(key.key_data().idx, 10);
    assert_eq!(key.key_data().generation, 3);
    assert_eq!(key.map_id(), map_id);
}

// ─── Copy / Clone / Eq / Hash ───────────────────────────────────────────────

#[test]
fn castable_key_is_copy() {
    let state = MapIdState::new();
    let map_id = state.ensure_id();
    let data = crate::key::KeyData {
        idx: 1u32,
        generation: 1u32,
    };
    let key = unsafe { DefaultCastKey::<Dog>::from_castable_parts(data, map_id, ()) };
    let copy = key;
    assert_eq!(key, copy);
}

#[test]
fn castable_key_eq_ignores_metadata() {
    let state = MapIdState::new();
    let map_id = state.ensure_id();
    let data = crate::key::KeyData {
        idx: 5u32,
        generation: 3u32,
    };

    let dog = Dog;
    let parrot = Parrot;
    let dog_meta = std::ptr::metadata(&dog as &dyn Any as *const dyn Any);
    let parrot_meta = std::ptr::metadata(&parrot as &dyn Any as *const dyn Any);

    let key_a = unsafe { DefaultCastKey::<dyn Any>::from_castable_parts(data, map_id, dog_meta) };
    let key_b =
        unsafe { DefaultCastKey::<dyn Any>::from_castable_parts(data, map_id, parrot_meta) };
    // Same key_data + map_id → equal (metadata doesn't affect identity)
    assert_eq!(key_a, key_b);
}

#[test]
fn castable_key_hash_is_consistent_with_eq() {
    use std::collections::HashSet;
    let state = MapIdState::new();
    let map_id = state.ensure_id();
    let data = crate::key::KeyData {
        idx: 5u32,
        generation: 3u32,
    };

    let dog_meta = std::ptr::metadata(&Dog as &dyn Any as *const dyn Any);
    let parrot_meta = std::ptr::metadata(&Parrot as &dyn Any as *const dyn Any);

    let key_a = unsafe { DefaultCastKey::<dyn Any>::from_castable_parts(data, map_id, dog_meta) };
    let key_b =
        unsafe { DefaultCastKey::<dyn Any>::from_castable_parts(data, map_id, parrot_meta) };

    let mut set = HashSet::new();
    set.insert(key_a);
    assert!(set.contains(&key_b), "equal keys must hash the same");
}

// ─── Upcast via CoerceUnsized ───────────────────────────────────────────────

#[test]
fn upcast_sized_to_dyn_any() {
    let state = MapIdState::new();
    let map_id = state.ensure_id();
    let data = crate::key::KeyData {
        idx: 99u32,
        generation: 1u32,
    };

    let concrete_key = unsafe { DefaultCastKey::<Dog>::from_castable_parts(data, map_id, ()) };
    // Implicit coercion: Dog: Any, so DefaultCastKey<Dog> → DefaultCastKey<dyn Any>
    let dyn_key: DefaultCastKey<dyn Any> = concrete_key;

    assert_eq!(dyn_key.key_data().idx, 99);
    assert_eq!(dyn_key.map_id(), map_id);
}

#[test]
fn upcast_sized_to_dyn_trait() {
    let state = MapIdState::new();
    let map_id = state.ensure_id();
    let data = crate::key::KeyData {
        idx: 7u32,
        generation: 5u32,
    };

    let concrete_key = unsafe { DefaultCastKey::<Parrot>::from_castable_parts(data, map_id, ()) };
    let animal_key: DefaultCastKey<dyn Animal> = concrete_key;
    let flyer_key: DefaultCastKey<dyn Flyer> = concrete_key;

    assert_eq!(animal_key.key_data().idx, 7);
    assert_eq!(flyer_key.key_data().idx, 7);
    assert_eq!(animal_key.map_id(), map_id);
    assert_eq!(flyer_key.map_id(), map_id);
}

// ─── downcast_key (via map method) ──────────────────────────────────────────

type Map = StableCastMap<DefaultCastKey<dyn Any>, Box<dyn Any>>;

#[test]
fn downcast_key_succeeds_for_correct_type() {
    let map: Map = Map::new();
    let (dyn_key, _) = map.insert(Box::new(Dog) as Box<dyn Any>);

    let result: Option<DefaultCastKey<Dog>> = map.downcast_key::<Dog>(dyn_key);
    assert!(result.is_some());
    let back = result.unwrap();
    assert_eq!(back.key_data().idx, dyn_key.key_data().idx);
    assert_eq!(back.map_id(), dyn_key.map_id());
}

#[test]
fn downcast_key_fails_for_wrong_type() {
    let map: Map = Map::new();
    let (dyn_key, _) = map.insert(Box::new(Dog) as Box<dyn Any>);

    let result: Option<DefaultCastKey<Parrot>> =
        map.downcast_key::<Parrot>(dyn_key);
    assert!(result.is_none());
}

#[test]
fn downcast_key_preserves_key_data_and_map_id() {
    let map: Map = Map::new();
    let (dyn_key, _) = map.insert(Box::new(Parrot) as Box<dyn Any>);
    let back: DefaultCastKey<Parrot> = map.downcast_key::<Parrot>(dyn_key).unwrap();

    assert_eq!(back.key_data().idx, dyn_key.key_data().idx);
    assert_eq!(back.key_data().generation, dyn_key.key_data().generation);
    assert_eq!(back.map_id(), dyn_key.map_id());
}

// ─── map_id packing in NonNull ──────────────────────────────────────────────

#[test]
fn map_id_survives_upcast() {
    let state = MapIdState::new();
    let map_id = state.ensure_id();
    let data = crate::key::KeyData {
        idx: 0u32,
        generation: 1u32,
    };

    let concrete = unsafe { DefaultCastKey::<Dog>::from_castable_parts(data, map_id, ()) };
    let dyn_key: DefaultCastKey<dyn Any> = concrete;

    // The map_id is packed in the data-pointer half of NonNull.
    // It must survive the coercion (which only changes the metadata half).
    assert_eq!(dyn_key.map_id(), map_id);
}

#[test]
fn different_map_ids_produce_unequal_keys() {
    let a = MapIdState::new();
    let b = MapIdState::new();
    let data = crate::key::KeyData {
        idx: 1u32,
        generation: 1u32,
    };

    let key_a = unsafe { DefaultCastKey::<Dog>::from_castable_parts(data, a.ensure_id(), ()) };
    let key_b = unsafe { DefaultCastKey::<Dog>::from_castable_parts(data, b.ensure_id(), ()) };
    assert_ne!(key_a, key_b);
}