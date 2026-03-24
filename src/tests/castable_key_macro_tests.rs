use crate::cast_key::{CastKey, DefaultCastKey, DefaultMapKey};
use crate::key::Key;
use crate::map_id::MapIdState;
use crate::stable_cast_map::{StableBoxCastMap, StableCastMap};
use std::any::Any;
use std::collections::HashSet;

// ─── Macro invocations ─────────────────────────────────────────────────────

// Default form: u32/u32
crate::new_castable_key_type! {
    struct TestCastKey;
}

// Custom idx/gen types
crate::new_castable_key_type! {
    struct SmallCastKey(u16, u16);
}

// Multiple keys in one invocation
crate::new_castable_key_type! {
    struct CastKeyA;
    struct CastKeyB;
}

// Public visibility
crate::new_castable_key_type! {
    pub struct PubCastKey;
}

// Custom types with pub visibility
crate::new_castable_key_type! {
    pub struct PubSmallCastKey(u16, u16);
}

// ─── Test helpers ──────────────────────────────────────────────────────────

trait Animal: Any {
    fn speak(&self) -> &'static str;
}

#[derive(Debug, PartialEq)]
struct Dog {
    name: String,
}
impl Animal for Dog {
    fn speak(&self) -> &'static str {
        "woof"
    }
}

#[derive(Debug, PartialEq)]
struct Cat {
    name: String,
}
impl Animal for Cat {
    fn speak(&self) -> &'static str {
        "meow"
    }
}

// ─── Associated type checks ───────────────────────────────────────────────

#[test]
fn default_form_has_u32_u32() {
    assert_eq!(
        std::any::TypeId::of::<<TestCastKey<dyn Any> as CastKey>::Idx>(),
        std::any::TypeId::of::<u32>()
    );
    assert_eq!(
        std::any::TypeId::of::<<TestCastKey<dyn Any> as CastKey>::Gen>(),
        std::any::TypeId::of::<u32>()
    );
}

#[test]
fn custom_form_has_u16_u16() {
    assert_eq!(
        std::any::TypeId::of::<<SmallCastKey<dyn Any> as CastKey>::Idx>(),
        std::any::TypeId::of::<u16>()
    );
    assert_eq!(
        std::any::TypeId::of::<<SmallCastKey<dyn Any> as CastKey>::Gen>(),
        std::any::TypeId::of::<u16>()
    );
}

#[test]
fn inner_key_type_is_default_map_key() {
    // DefaultMapKey<u32, u32> for the default form
    assert_eq!(
        std::any::TypeId::of::<<TestCastKey<Dog> as CastKey>::InnerKey>(),
        std::any::TypeId::of::<DefaultMapKey<u32, u32>>()
    );
    // DefaultMapKey<u16, u16> for the custom form
    assert_eq!(
        std::any::TypeId::of::<<SmallCastKey<Dog> as CastKey>::InnerKey>(),
        std::any::TypeId::of::<DefaultMapKey<u16, u16>>()
    );
}

// ─── Copy / Clone / Debug / Eq / Hash ─────────────────────────────────────

#[test]
fn macro_key_is_copy() {
    let state = MapIdState::new();
    let map_id = state.ensure_id();
    let data = crate::key::KeyData {
        idx: 1u32,
        generation: 1u32,
    };
    let key = unsafe { TestCastKey::<Dog>::from_castable_parts(data, map_id, ()) };
    let copy = key;
    assert_eq!(key, copy);
}

#[test]
fn macro_key_clone_equals_original() {
    let state = MapIdState::new();
    let map_id = state.ensure_id();
    let data = crate::key::KeyData {
        idx: 5u32,
        generation: 3u32,
    };
    let key = unsafe { TestCastKey::<Dog>::from_castable_parts(data, map_id, ()) };
    let cloned = key.clone();
    assert_eq!(key, cloned);
}

#[test]
fn macro_key_debug_does_not_panic() {
    let state = MapIdState::new();
    let map_id = state.ensure_id();
    let data = crate::key::KeyData {
        idx: 42u32,
        generation: 7u32,
    };
    let key = unsafe { TestCastKey::<Dog>::from_castable_parts(data, map_id, ()) };
    let debug = format!("{:?}", key);
    assert!(debug.contains("TestCastKey"));
}

#[test]
fn macro_key_hash_consistent_with_eq() {
    let state = MapIdState::new();
    let map_id = state.ensure_id();
    let data = crate::key::KeyData {
        idx: 5u32,
        generation: 3u32,
    };

    let dog_meta = std::ptr::metadata(&Dog { name: "a".into() } as &dyn Any as *const dyn Any);
    let cat_meta = std::ptr::metadata(&Cat { name: "b".into() } as &dyn Any as *const dyn Any);

    let key_a = unsafe { TestCastKey::<dyn Any>::from_castable_parts(data, map_id, dog_meta) };
    let key_b = unsafe { TestCastKey::<dyn Any>::from_castable_parts(data, map_id, cat_meta) };

    // Same key_data + map_id → equal
    assert_eq!(key_a, key_b);

    let mut set = HashSet::new();
    set.insert(key_a);
    assert!(set.contains(&key_b), "equal keys must hash the same");
}

// ─── from_castable_parts round-trips ──────────────────────────────────────

#[test]
fn macro_key_parts_round_trip_sized() {
    let state = MapIdState::new();
    let map_id = state.ensure_id();
    let data = crate::key::KeyData {
        idx: 42u32,
        generation: 7u32,
    };

    let key = unsafe { TestCastKey::<Dog>::from_castable_parts(data, map_id, ()) };
    assert_eq!(key.key_data().idx, 42);
    assert_eq!(key.key_data().generation, 7);
    assert_eq!(key.map_id(), map_id);
    assert_eq!(key.metadata(), ());
}

#[test]
fn macro_key_parts_round_trip_dyn() {
    let state = MapIdState::new();
    let map_id = state.ensure_id();
    let data = crate::key::KeyData {
        idx: 10u32,
        generation: 3u32,
    };

    let dog = Dog { name: "Rex".into() };
    let dog_ref: &dyn Any = &dog;
    let metadata = std::ptr::metadata(dog_ref as *const dyn Any);

    let key = unsafe { TestCastKey::<dyn Any>::from_castable_parts(data, map_id, metadata) };
    assert_eq!(key.key_data().idx, 10);
    assert_eq!(key.key_data().generation, 3);
    assert_eq!(key.map_id(), map_id);
}

// ─── inner_key round-trips ────────────────────────────────────────────────

#[test]
fn macro_key_inner_key_preserves_data_and_map_id() {
    let state = MapIdState::new();
    let map_id = state.ensure_id();
    let data = crate::key::KeyData {
        idx: 99u32,
        generation: 5u32,
    };

    let key = unsafe { TestCastKey::<Dog>::from_castable_parts(data, map_id, ()) };
    let inner = key.inner_key();

    assert_eq!(inner.data().idx, 99);
    assert_eq!(inner.data().generation, 5);
    assert_eq!(inner.extra(), map_id);
}

#[test]
fn macro_key_from_inner_key_and_metadata_round_trips() {
    let state = MapIdState::new();
    let map_id = state.ensure_id();
    let data = crate::key::KeyData {
        idx: 7u32,
        generation: 3u32,
    };

    let original = unsafe { TestCastKey::<Dog>::from_castable_parts(data, map_id, ()) };
    let inner = original.inner_key();
    let reconstructed = unsafe { TestCastKey::<Dog>::from_inner_key_and_metadata(inner, ()) };

    assert_eq!(original, reconstructed);
    assert_eq!(reconstructed.key_data().idx, 7);
    assert_eq!(reconstructed.map_id(), map_id);
}

#[test]
fn macro_key_inner_key_matches_default_cast_key_inner_key() {
    // Ensure a macro-generated key's inner_key produces the same result
    // as a DefaultCastKey with the same data.
    let state = MapIdState::new();
    let map_id = state.ensure_id();
    let data = crate::key::KeyData {
        idx: 33u32,
        generation: 11u32,
    };

    let macro_key = unsafe { TestCastKey::<Dog>::from_castable_parts(data, map_id, ()) };
    let default_key = unsafe { DefaultCastKey::<Dog>::from_castable_parts(data, map_id, ()) };

    let macro_inner = macro_key.inner_key();
    let default_inner = default_key.inner_key();

    assert_eq!(macro_inner.data().idx, default_inner.data().idx);
    assert_eq!(
        macro_inner.data().generation,
        default_inner.data().generation
    );
    assert_eq!(macro_inner.extra(), default_inner.extra());
}

// ─── CoerceUnsized ────────────────────────────────────────────────────────

#[test]
fn macro_key_upcast_sized_to_dyn_any() {
    let state = MapIdState::new();
    let map_id = state.ensure_id();
    let data = crate::key::KeyData {
        idx: 99u32,
        generation: 1u32,
    };

    let concrete = unsafe { TestCastKey::<Dog>::from_castable_parts(data, map_id, ()) };
    let dyn_key: TestCastKey<dyn Any> = concrete;

    assert_eq!(dyn_key.key_data().idx, 99);
    assert_eq!(dyn_key.map_id(), map_id);
}

#[test]
fn macro_key_upcast_sized_to_dyn_trait() {
    let state = MapIdState::new();
    let map_id = state.ensure_id();
    let data = crate::key::KeyData {
        idx: 7u32,
        generation: 5u32,
    };

    let concrete = unsafe { TestCastKey::<Dog>::from_castable_parts(data, map_id, ()) };
    let animal_key: TestCastKey<dyn Animal> = concrete;

    assert_eq!(animal_key.key_data().idx, 7);
    assert_eq!(animal_key.map_id(), map_id);
}

#[test]
fn macro_key_map_id_survives_upcast() {
    let state = MapIdState::new();
    let map_id = state.ensure_id();
    let data = crate::key::KeyData {
        idx: 0u32,
        generation: 1u32,
    };

    let concrete = unsafe { TestCastKey::<Dog>::from_castable_parts(data, map_id, ()) };
    let dyn_key: TestCastKey<dyn Any> = concrete;
    assert_eq!(dyn_key.map_id(), map_id);
}

// ─── Use with StableCastMap ───────────────────────────────────────────────

type MacroMap = StableCastMap<TestCastKey<dyn Any>, Box<dyn Any>>;

#[test]
fn macro_key_insert_and_get() {
    let map: MacroMap = MacroMap::new();
    let (key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let val = map.get(key).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
}

#[test]
fn macro_key_insert_multiple_types() {
    let map: MacroMap = MacroMap::new();
    let (k1, _) = map.insert(Box::new(10u64) as Box<dyn Any>);
    let (k2, _) = map.insert(Box::new("hello".to_string()) as Box<dyn Any>);

    assert_eq!(*map.get(k1).unwrap().downcast_ref::<u64>().unwrap(), 10);
    assert_eq!(
        map.get(k2).unwrap().downcast_ref::<String>().unwrap(),
        "hello"
    );
}

#[test]
fn macro_key_remove() {
    let mut map: MacroMap = MacroMap::new();
    let (key, _) = map.insert(Box::new(99i32) as Box<dyn Any>);
    assert!(map.remove(key).is_some());
    assert!(map.get(key).is_none());
    assert_eq!(map.len(), 0);
}

#[test]
fn macro_key_stale_key_returns_none() {
    let mut map: MacroMap = MacroMap::new();
    let (key, _) = map.insert(Box::new(1i32) as Box<dyn Any>);
    map.remove(key);
    let _ = map.insert(Box::new(2i32) as Box<dyn Any>);
    assert!(map.get(key).is_none());
}

#[test]
fn macro_key_cross_map_rejection() {
    let map_a: MacroMap = MacroMap::new();
    let map_b: MacroMap = MacroMap::new();

    let (key_a, _) = map_a.insert(Box::new(1i32) as Box<dyn Any>);
    let _ = map_b.insert(Box::new(2i32) as Box<dyn Any>);

    assert!(map_b.get(key_a).is_none());
}

// ─── downcast_key with macro key ──────────────────────────────────────────

#[test]
fn macro_key_downcast_key_correct_type() {
    let map: MacroMap = MacroMap::new();
    let (dyn_key, _) = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);

    let dog_key: Option<TestCastKey<Dog>> = map.downcast_key::<Dog>(dyn_key);
    assert!(dog_key.is_some());

    let dog: &Dog = map.get(dog_key.unwrap()).unwrap();
    assert_eq!(dog.name, "Rex");
}

#[test]
fn macro_key_downcast_key_wrong_type() {
    let map: MacroMap = MacroMap::new();
    let (dyn_key, _) = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);

    let cat_key: Option<TestCastKey<Cat>> = map.downcast_key::<Cat>(dyn_key);
    assert!(cat_key.is_none());
}

// ─── Cross-typed get with upcast key ──────────────────────────────────────

#[test]
fn macro_key_get_with_trait_key() {
    let map: MacroMap = MacroMap::new();
    let (dyn_key, _) = map.insert(Box::new(Dog {
        name: "Buddy".into(),
    }) as Box<dyn Any>);

    let dog_key: TestCastKey<Dog> = map.downcast_key::<Dog>(dyn_key).unwrap();
    let animal_key: TestCastKey<dyn Animal> = dog_key;

    let animal: &dyn Animal = map.get(animal_key).unwrap();
    assert_eq!(animal.speak(), "woof");
}

#[test]
fn macro_key_get_mut_with_concrete_key() {
    let mut map: MacroMap = MacroMap::new();
    let (dyn_key, _) = map.insert(Box::new(Dog { name: "Old".into() }) as Box<dyn Any>);

    let dog_key: TestCastKey<Dog> = map.downcast_key::<Dog>(dyn_key).unwrap();

    let dog: &mut Dog = map.get_mut(dog_key).unwrap();
    dog.name = "New".into();

    let dog_again: &Dog = map.get(dog_key).unwrap();
    assert_eq!(dog_again.name, "New");
}

// ─── Inner key access via map ─────────────────────────────────────────────

#[test]
fn macro_key_get_by_inner_key() {
    let map: MacroMap = MacroMap::new();
    let (cast_key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);

    let inner = cast_key.inner_key();
    let val = map.get_by_inner_key(inner).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
}

#[test]
fn macro_key_get_mut_by_inner_key() {
    let mut map: MacroMap = MacroMap::new();
    let (cast_key, _) = map.insert(Box::new(Dog { name: "Old".into() }) as Box<dyn Any>);

    let inner = cast_key.inner_key();
    let val = map.get_mut_by_inner_key(inner).unwrap();
    val.downcast_mut::<Dog>().unwrap().name = "New".into();

    let check = map.get_by_inner_key(inner).unwrap();
    assert_eq!(check.downcast_ref::<Dog>().unwrap().name, "New");
}

#[test]
fn macro_key_remove_by_inner_key() {
    let mut map: MacroMap = MacroMap::new();
    let (cast_key, _) = map.insert(Box::new(77i32) as Box<dyn Any>);

    let inner = cast_key.inner_key();
    let removed = map.remove_by_inner_key(inner).unwrap();
    assert_eq!(*removed.downcast_ref::<i32>().unwrap(), 77);
    assert_eq!(map.len(), 0);
}

#[test]
fn macro_key_inner_key_stale_after_remove() {
    let mut map: MacroMap = MacroMap::new();
    let (cast_key, _) = map.insert(Box::new(1i32) as Box<dyn Any>);
    let inner = cast_key.inner_key();

    map.remove(cast_key);
    assert!(map.get_by_inner_key(inner).is_none());
}

#[test]
fn macro_key_inner_key_cross_map_rejection() {
    let map_a: MacroMap = MacroMap::new();
    let map_b: MacroMap = MacroMap::new();

    let (key_a, _) = map_a.insert(Box::new(1i32) as Box<dyn Any>);
    let _ = map_b.insert(Box::new(2i32) as Box<dyn Any>);

    let inner_a = key_a.inner_key();
    assert!(map_b.get_by_inner_key(inner_a).is_none());
}

// ─── Custom idx/gen key with StableCastMap ────────────────────────────────

type SmallMap = StableCastMap<SmallCastKey<dyn Any>, Box<dyn Any>>;

#[test]
fn small_cast_key_insert_and_get() {
    let map: SmallMap = SmallMap::new();
    let (key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let val = map.get(key).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
}

#[test]
fn small_cast_key_inner_key_round_trips() {
    let map: SmallMap = SmallMap::new();
    let (key, _) = map.insert(Box::new(99i32) as Box<dyn Any>);

    let inner = key.inner_key();
    let val = map.get_by_inner_key(inner).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 99);
}

#[test]
fn small_cast_key_downcast_and_get() {
    let map: SmallMap = SmallMap::new();
    let (dyn_key, _) = map.insert(Box::new(Dog {
        name: "Tiny".into(),
    }) as Box<dyn Any>);

    let dog_key: SmallCastKey<Dog> = map.downcast_key::<Dog>(dyn_key).unwrap();
    let dog: &Dog = map.get(dog_key).unwrap();
    assert_eq!(dog.name, "Tiny");
}

// ─── Multiple keys in one invocation ──────────────────────────────────────

#[test]
fn multiple_cast_keys_are_distinct_types() {
    assert_ne!(
        std::any::TypeId::of::<CastKeyA<Dog>>(),
        std::any::TypeId::of::<CastKeyB<Dog>>()
    );
}

#[test]
fn multiple_cast_keys_work_with_separate_maps() {
    type MapA = StableCastMap<CastKeyA<dyn Any>, Box<dyn Any>>;
    type MapB = StableCastMap<CastKeyB<dyn Any>, Box<dyn Any>>;

    let map_a: MapA = MapA::new();
    let map_b: MapB = MapB::new();

    let (ka, _) = map_a.insert(Box::new(1i32) as Box<dyn Any>);
    let (kb, _) = map_b.insert(Box::new(2i32) as Box<dyn Any>);

    assert_eq!(*map_a.get(ka).unwrap().downcast_ref::<i32>().unwrap(), 1);
    assert_eq!(*map_b.get(kb).unwrap().downcast_ref::<i32>().unwrap(), 2);
}

// ─── Iteration with macro key ─────────────────────────────────────────────

#[test]
fn macro_key_snapshot_keys_can_be_used_for_lookup() {
    let map: MacroMap = MacroMap::new();
    map.insert(Box::new(1i32) as Box<dyn Any>);
    map.insert(Box::new(2i32) as Box<dyn Any>);
    map.insert(Box::new(3i32) as Box<dyn Any>);

    let keys = map.snapshot_keys();
    assert_eq!(keys.len(), 3);
    for key in keys {
        assert!(map.get(key).is_some());
    }
}

#[test]
fn macro_key_drain_yields_all() {
    let mut map: MacroMap = MacroMap::new();
    map.insert(Box::new(10i32) as Box<dyn Any>);
    map.insert(Box::new(20i32) as Box<dyn Any>);

    let drained: Vec<_> = map.drain().collect();
    assert_eq!(drained.len(), 2);
    assert_eq!(map.len(), 0);
}

#[test]
fn macro_key_into_iter() {
    let map: MacroMap = MacroMap::new();
    map.insert(Box::new(1i32) as Box<dyn Any>);
    map.insert(Box::new(2i32) as Box<dyn Any>);

    let collected: Vec<_> = map.into_iter().collect();
    assert_eq!(collected.len(), 2);
}

// ─── remove_by with macro key ─────────────────────────────────────────────

#[test]
fn macro_key_remove_by_with_concrete_key() {
    let mut map: MacroMap = MacroMap::new();
    let (dyn_key, _) = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);

    let dog_key: TestCastKey<Dog> = map.downcast_key::<Dog>(dyn_key).unwrap();

    let removed = map.remove(dog_key).unwrap();
    assert!(removed.downcast_ref::<Dog>().is_some());
    assert_eq!(map.len(), 0);
}

// ─── StableBoxCastMap alias with macro key ────────────────────────────────

#[test]
fn macro_key_works_with_box_alias() {
    type BoxMap = StableBoxCastMap<TestCastKey<dyn Any>>;
    let map: BoxMap = BoxMap::new();

    let (key, _) = map.insert(Box::new(123i32) as Box<dyn Any>);
    let val = map.get(key).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 123);
}

// ─── insert_with_key with macro key ──────────────────────────────────────

#[test]
fn macro_key_insert_with_key() {
    let map: MacroMap = MacroMap::new();
    let (cast_key, val) = map.insert_with_key(|_inner_key| Box::new(42i32) as Box<dyn Any>);
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
    assert!(map.get(cast_key).is_some());
}

#[test]
fn macro_key_insert_with_key_inner_key_round_trips() {
    use crate::key::Key;

    let map: MacroMap = MacroMap::new();
    let (cast_key, _) = map.insert_with_key(|inner_key| {
        assert_ne!(inner_key.extra().0, 0);
        Box::new(77i32) as Box<dyn Any>
    });

    let inner = cast_key.inner_key();
    let val = map.get_by_inner_key(inner).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 77);
}

#[test]
fn macro_key_try_insert_with_key_ok() {
    let map: MacroMap = MacroMap::new();
    let result = map.try_insert_with_key::<()>(|_| Ok(Box::new(10i32) as Box<dyn Any>));
    assert!(result.is_ok());
    assert_eq!(map.len(), 1);
}

#[test]
fn macro_key_try_insert_with_key_err() {
    let map: MacroMap = MacroMap::new();
    let result = map.try_insert_with_key::<&str>(|_| Err("fail"));
    assert!(result.is_err());
    assert_eq!(map.len(), 0);
}

#[test]
fn small_cast_key_insert_with_key() {
    let map: SmallMap = SmallMap::new();
    let (key, val) = map.insert_with_key(|_inner_key| Box::new(55i32) as Box<dyn Any>);
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 55);
    assert!(map.get(key).is_some());
}

// ─── cast_key_of with macro key ──────────────────────────────────────────

#[test]
fn macro_key_cast_key_of_round_trips() {
    let map: MacroMap = MacroMap::new();
    let (cast_key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let inner = cast_key.inner_key();

    let recovered = map.cast_key_of(inner).unwrap();
    assert_eq!(recovered, cast_key);
}

#[test]
fn macro_key_cast_key_of_stale_returns_none() {
    let mut map: MacroMap = MacroMap::new();
    let (cast_key, _) = map.insert(Box::new(1i32) as Box<dyn Any>);
    let inner = cast_key.inner_key();
    map.remove(cast_key);
    assert!(map.cast_key_of(inner).is_none());
}

#[test]
fn small_cast_key_cast_key_of() {
    let map: SmallMap = SmallMap::new();
    let (cast_key, _) = map.insert(Box::new(99i32) as Box<dyn Any>);
    let inner = cast_key.inner_key();

    let recovered = map.cast_key_of(inner).unwrap();
    assert_eq!(recovered, cast_key);
}
