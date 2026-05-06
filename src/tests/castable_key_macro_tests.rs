use crate::cast_key::{CastKey, DefaultMapKey};
use crate::key::Key;
use crate::stable_cast_map::StableCastMap;
use std::any::Any;
use std::collections::HashSet;

// ─── Macro-generated key types ─────────────────────────────────────────────

// Default (u32/u32):
crate::new_castable_key_type! {
    struct MacroCastKey;
}

// Custom idx/gen:
crate::new_castable_key_type! {
    struct SmallCastKey(u16, u16);
}

// Multiple in one invocation:
crate::new_castable_key_type! {
    struct CastKeyA;
    struct CastKeyB;
}

// Custom inner key:
crate::new_key_type! {
    struct CustomInnerKey;
}
crate::new_castable_key_type! {
    struct CastKeyWithCustomInner inner_key CustomInnerKey;
}

// Custom idx/gen + custom inner key:
crate::new_key_type! {
    struct SmallCustomInnerKey(u16, u16);
}
crate::new_castable_key_type! {
    struct SmallCastKeyWithCustomInner(u16, u16) inner_key SmallCustomInnerKey;
}

// ─── Associated type checks ───────────────────────────────────────────────

#[test]
fn default_form_has_u32_u32() {
    assert_eq!(
        std::any::TypeId::of::<<MacroCastKey<dyn Any> as CastKey>::Idx>(),
        std::any::TypeId::of::<u32>()
    );
    assert_eq!(
        std::any::TypeId::of::<<MacroCastKey<dyn Any> as CastKey>::Gen>(),
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
fn inner_key_type_is_default_key_for_default_form() {
    assert_eq!(
        std::any::TypeId::of::<<MacroCastKey<dyn Any> as CastKey>::InnerKey>(),
        std::any::TypeId::of::<DefaultMapKey<u32, u32>>()
    );
}

#[test]
fn custom_inner_key_type_is_correct() {
    assert_eq!(
        std::any::TypeId::of::<<CastKeyWithCustomInner<dyn Any> as CastKey>::InnerKey>(),
        std::any::TypeId::of::<CustomInnerKey>()
    );
}

#[test]
fn custom_inner_key_is_not_default_key() {
    assert_ne!(
        std::any::TypeId::of::<<CastKeyWithCustomInner<dyn Any> as CastKey>::InnerKey>(),
        std::any::TypeId::of::<DefaultMapKey<u32, u32>>()
    );
}

#[test]
fn small_custom_inner_key_type_is_correct() {
    assert_eq!(
        std::any::TypeId::of::<<SmallCastKeyWithCustomInner<dyn Any> as CastKey>::InnerKey>(),
        std::any::TypeId::of::<SmallCustomInnerKey>()
    );
}

#[test]
fn multiple_cast_keys_are_distinct_types() {
    assert_ne!(
        std::any::TypeId::of::<CastKeyA<dyn Any>>(),
        std::any::TypeId::of::<CastKeyB<dyn Any>>()
    );
}

// ─── Trait impls (Copy, Clone, Debug, Eq, Hash) ───────────────────────────

type MacroMap = StableCastMap<MacroCastKey<dyn Any>, Box<dyn Any>>;

#[test]
fn macro_key_is_copy() {
    let map: MacroMap = MacroMap::new();
    let (key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let copy = key;
    assert_eq!(key, copy);
}

#[test]
fn macro_key_clone_equals_original() {
    let map: MacroMap = MacroMap::new();
    let (key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let clone = key.clone();
    assert_eq!(key, clone);
}

#[test]
fn macro_key_debug_does_not_panic() {
    let map: MacroMap = MacroMap::new();
    let (key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let _ = format!("{:?}", key);
}

#[test]
fn macro_key_hash_consistent_with_eq() {
    let map: MacroMap = MacroMap::new();
    let (k1, _) = map.insert(Box::new(1i32) as Box<dyn Any>);
    let (k2, _) = map.insert(Box::new(2i32) as Box<dyn Any>);

    let mut set = HashSet::new();
    set.insert(k1);
    assert!(set.contains(&k1));
    assert!(!set.contains(&k2));
}

// ─── Parts round-trip ──────────────────────────────────────────────────────

#[test]
fn macro_key_parts_round_trip_sized() {
    let map: MacroMap = MacroMap::new();
    let (dyn_key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let sized_key: MacroCastKey<i32> = map.downcast_key::<i32>(dyn_key).unwrap();

    let data = sized_key.key_data();
    let map_id = sized_key.map_id();
    let metadata = sized_key.metadata();

    let reconstructed =
        unsafe { MacroCastKey::<i32>::from_castable_parts(data, map_id, metadata) };
    assert_eq!(sized_key, reconstructed);
}

#[test]
fn macro_key_parts_round_trip_dyn() {
    let map: MacroMap = MacroMap::new();
    let (key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);

    let data = key.key_data();
    let map_id = key.map_id();
    let metadata = key.metadata();

    let reconstructed =
        unsafe { MacroCastKey::<dyn Any>::from_castable_parts(data, map_id, metadata) };
    assert_eq!(key, reconstructed);
}

// ─── CoerceUnsized ─────────────────────────────────────────────────────────

#[test]
fn macro_key_upcast_sized_to_dyn_any() {
    let map: MacroMap = MacroMap::new();
    let (dyn_key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let sized_key: MacroCastKey<i32> = map.downcast_key::<i32>(dyn_key).unwrap();

    let back: MacroCastKey<dyn Any> = sized_key;
    assert!(map.get(back).is_some());
}

#[test]
fn macro_key_map_id_survives_upcast() {
    let map: MacroMap = MacroMap::new();
    let (dyn_key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let sized_key: MacroCastKey<i32> = map.downcast_key::<i32>(dyn_key).unwrap();

    let upcasted: MacroCastKey<dyn Any> = sized_key;
    assert_eq!(dyn_key.map_id(), upcasted.map_id());
}

// ─── Basic map operations with macro key ──────────────────────────────────

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
}

#[test]
fn macro_key_stale_key_returns_none() {
    let mut map: MacroMap = MacroMap::new();
    let (key, _) = map.insert(Box::new(1i32) as Box<dyn Any>);
    map.remove(key);
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

// ─── downcast_key ──────────────────────────────────────────────────────────

#[derive(Debug, PartialEq)]
struct Dog { name: String }

#[derive(Debug, PartialEq)]
struct Cat { name: String }

#[test]
fn macro_key_downcast_key_correct_type() {
    let map: MacroMap = MacroMap::new();
    let (dyn_key, _) = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);

    let dog_key: MacroCastKey<Dog> = map.downcast_key::<Dog>(dyn_key).unwrap();
    let dog: &Dog = map.get(dog_key).unwrap();
    assert_eq!(dog.name, "Rex");
}

#[test]
fn macro_key_downcast_key_wrong_type() {
    let map: MacroMap = MacroMap::new();
    let (dyn_key, _) = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);
    assert!(map.downcast_key::<Cat>(dyn_key).is_none());
}

// ─── inner_key ─────────────────────────────────────────────────────────────

#[test]
fn macro_key_inner_key_preserves_data() {
    let map: MacroMap = MacroMap::new();
    let (cast_key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);

    let inner = cast_key.inner_key();
    assert_eq!(inner.data().idx, cast_key.key_data().idx);
    assert_eq!(inner.data().generation, cast_key.key_data().generation);
}

#[test]
fn macro_key_get_by_inner_key() {
    let map: MacroMap = MacroMap::new();
    let (key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);

    let inner = key.inner_key();
    let val = map.get_by_inner_key(inner).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
}

#[test]
fn macro_key_cast_key_of_round_trips() {
    let map: MacroMap = MacroMap::new();
    let (key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let inner = key.inner_key();

    let recovered = map.cast_key_of(inner).unwrap();
    assert_eq!(recovered, key);
}

// ─── insert_with_key ───────────────────────────────────────────────────────

#[test]
fn macro_key_insert_with_key() {
    use std::cell::Cell;

    let map: MacroMap = MacroMap::new();
    let captured = Cell::new(None);

    let (cast_key, _) = map.insert_with_key(|inner_key| {
        captured.set(Some(inner_key));
        Box::new(42i32) as Box<dyn Any>
    });

    let inner = captured.get().unwrap();
    assert_eq!(inner.data().idx, cast_key.key_data().idx);
}

// ─── Iteration ─────────────────────────────────────────────────────────────

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

// ─── Custom inner key map ──────────────────────────────────────────────────

type CustomInnerMap = StableCastMap<CastKeyWithCustomInner<dyn Any>, Box<dyn Any>>;

#[test]
fn custom_inner_insert_and_get() {
    let map: CustomInnerMap = CustomInnerMap::new();
    let (key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let val = map.get(key).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
}

#[test]
fn custom_inner_key_is_custom_type() {
    let map: CustomInnerMap = CustomInnerMap::new();
    let (cast_key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);

    let inner: CustomInnerKey = cast_key.inner_key();
    let val = map.get_by_inner_key(inner).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
}

#[test]
fn custom_inner_cross_map_rejection() {
    let map_a: CustomInnerMap = CustomInnerMap::new();
    let map_b: CustomInnerMap = CustomInnerMap::new();
    let (key_a, _) = map_a.insert(Box::new(1i32) as Box<dyn Any>);
    let _ = map_b.insert(Box::new(2i32) as Box<dyn Any>);
    assert!(map_b.get(key_a).is_none());
}

#[test]
fn custom_inner_downcast() {
    let map: CustomInnerMap = CustomInnerMap::new();
    let (dyn_key, _) = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);

    let dog_key: CastKeyWithCustomInner<Dog> = map.downcast_key::<Dog>(dyn_key).unwrap();
    let dog: &Dog = map.get(dog_key).unwrap();
    assert_eq!(dog.name, "Rex");
}

#[test]
fn custom_inner_cast_key_of_round_trips() {
    let map: CustomInnerMap = CustomInnerMap::new();
    let (cast_key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let inner = cast_key.inner_key();

    let recovered = map.cast_key_of(inner).unwrap();
    assert_eq!(recovered, cast_key);
}

// ─── Small custom inner key map ───────────────────────────────────────────

type SmallCustomInnerMap =
    StableCastMap<SmallCastKeyWithCustomInner<dyn Any>, Box<dyn Any>>;

#[test]
fn small_custom_inner_insert_and_get() {
    let map: SmallCustomInnerMap = SmallCustomInnerMap::new();
    let (key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let val = map.get(key).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
}

#[test]
fn small_custom_inner_key_is_correct_type() {
    let map: SmallCustomInnerMap = SmallCustomInnerMap::new();
    let (cast_key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);

    let inner: SmallCustomInnerKey = cast_key.inner_key();
    let val = map.get_by_inner_key(inner).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
}

#[test]
fn small_custom_inner_downcast() {
    let map: SmallCustomInnerMap = SmallCustomInnerMap::new();
    let (dyn_key, _) = map.insert(Box::new(Dog { name: "Tiny".into() }) as Box<dyn Any>);

    let dog_key: SmallCastKeyWithCustomInner<Dog> = map.downcast_key::<Dog>(dyn_key).unwrap();
    let dog: &Dog = map.get(dog_key).unwrap();
    assert_eq!(dog.name, "Tiny");
}

// ─── Maps with different key types are incompatible ───────────────────────

#[test]
fn different_macro_key_maps_are_separate_types() {
    type MapA = StableCastMap<CastKeyA<dyn Any>, Box<dyn Any>>;
    type MapB = StableCastMap<CastKeyB<dyn Any>, Box<dyn Any>>;

    let map_a: MapA = MapA::new();
    let map_b: MapB = MapB::new();

    let (ka, _) = map_a.insert(Box::new(1i32) as Box<dyn Any>);
    let (kb, _) = map_b.insert(Box::new(2i32) as Box<dyn Any>);

    assert_eq!(*map_a.get(ka).unwrap().downcast_ref::<i32>().unwrap(), 1);
    assert_eq!(*map_b.get(kb).unwrap().downcast_ref::<i32>().unwrap(), 2);
    // ka and kb are different types — can't mix them at compile time
}

// ─── Small cast key map (custom idx/gen, default inner key) ───────────────

type SmallMap = StableCastMap<SmallCastKey<dyn Any>, Box<dyn Any>>;

#[test]
fn small_cast_key_insert_and_get() {
    let map: SmallMap = SmallMap::new();
    let (key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let val = map.get(key).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
}

#[test]
fn small_cast_key_downcast_and_get() {
    let map: SmallMap = SmallMap::new();
    let (dyn_key, _) = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);

    let dog_key: SmallCastKey<Dog> = map.downcast_key::<Dog>(dyn_key).unwrap();
    let dog: &Dog = map.get(dog_key).unwrap();
    assert_eq!(dog.name, "Rex");
}

#[test]
fn small_cast_key_inner_key_round_trips() {
    let map: SmallMap = SmallMap::new();
    let (cast_key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let inner = cast_key.inner_key();

    let recovered = map.cast_key_of(inner).unwrap();
    assert_eq!(recovered, cast_key);
}
