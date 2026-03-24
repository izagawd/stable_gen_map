use crate::cast_key::{CastKey, DefaultMapKey};
use crate::key::Key;
use crate::stable_cast_map::StableCastMap;
use std::any::Any;

// ─── Define custom inner key types via new_key_type! ───────────────────────

// An identified key (Extra = MapId) — compatible as a cast key InnerKey.
crate::new_key_type! {
    struct CustomInnerKey identified;
}

// An identified key with custom idx/gen.
crate::new_key_type! {
    struct SmallCustomInnerKey(u16, u16) identified;
}

// ─── Macro invocations with custom inner keys ──────────────────────────────

// Default idx/gen, custom inner key
crate::new_castable_key_type! {
    struct CastKeyWithCustomInner inner_key CustomInnerKey;
}

// Custom idx/gen, custom inner key
crate::new_castable_key_type! {
    struct SmallCastKeyWithCustomInner(u16, u16) inner_key SmallCustomInnerKey;
}

// For comparison: default inner key (same idx/gen)
crate::new_castable_key_type! {
    struct CastKeyWithDefaultInner;
}

// ─── Test helpers ──────────────────────────────────────────────────────────

#[derive(Debug, PartialEq)]
struct Dog {
    name: String,
}

#[derive(Debug, PartialEq)]
struct Cat {
    name: String,
}

// ─── Associated type checks ───────────────────────────────────────────────

#[test]
fn custom_inner_key_type_is_correct() {
    assert_eq!(
        std::any::TypeId::of::<<CastKeyWithCustomInner<dyn Any> as CastKey>::InnerKey>(),
        std::any::TypeId::of::<CustomInnerKey>()
    );
}

#[test]
fn custom_inner_key_is_not_default_map_key() {
    // The custom inner key should be a distinct type from DefaultMapKey
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
fn default_inner_key_still_uses_default_map_key() {
    // Verify that the non-inner_key variant is unchanged
    assert_eq!(
        std::any::TypeId::of::<<CastKeyWithDefaultInner<dyn Any> as CastKey>::InnerKey>(),
        std::any::TypeId::of::<DefaultMapKey<u32, u32>>()
    );
}

#[test]
fn idx_gen_types_correct_for_custom_inner() {
    assert_eq!(
        std::any::TypeId::of::<<CastKeyWithCustomInner<dyn Any> as CastKey>::Idx>(),
        std::any::TypeId::of::<u32>()
    );
    assert_eq!(
        std::any::TypeId::of::<<CastKeyWithCustomInner<dyn Any> as CastKey>::Gen>(),
        std::any::TypeId::of::<u32>()
    );
}

#[test]
fn idx_gen_types_correct_for_small_custom_inner() {
    assert_eq!(
        std::any::TypeId::of::<<SmallCastKeyWithCustomInner<dyn Any> as CastKey>::Idx>(),
        std::any::TypeId::of::<u16>()
    );
    assert_eq!(
        std::any::TypeId::of::<<SmallCastKeyWithCustomInner<dyn Any> as CastKey>::Gen>(),
        std::any::TypeId::of::<u16>()
    );
}

// ─── Basic map operations with custom inner key ───────────────────────────

type CustomMap = StableCastMap<CastKeyWithCustomInner<dyn Any>, Box<dyn Any>>;

#[test]
fn insert_and_get() {
    let map: CustomMap = CustomMap::new();
    let (key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let val = map.get(key).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
}

#[test]
fn insert_multiple_types() {
    let map: CustomMap = CustomMap::new();
    let (k1, _) = map.insert(Box::new(10u64) as Box<dyn Any>);
    let (k2, _) = map.insert(Box::new("hello".to_string()) as Box<dyn Any>);

    assert_eq!(*map.get(k1).unwrap().downcast_ref::<u64>().unwrap(), 10);
    assert_eq!(
        map.get(k2).unwrap().downcast_ref::<String>().unwrap(),
        "hello"
    );
}

#[test]
fn remove() {
    let mut map: CustomMap = CustomMap::new();
    let (key, _) = map.insert(Box::new(99i32) as Box<dyn Any>);
    assert!(map.remove(key).is_some());
    assert!(map.get(key).is_none());
    assert_eq!(map.len(), 0);
}

#[test]
fn stale_key_returns_none() {
    let mut map: CustomMap = CustomMap::new();
    let (key, _) = map.insert(Box::new(1i32) as Box<dyn Any>);
    map.remove(key);
    let _ = map.insert(Box::new(2i32) as Box<dyn Any>);
    assert!(map.get(key).is_none());
}

#[test]
fn cross_map_rejection() {
    let map_a: CustomMap = CustomMap::new();
    let map_b: CustomMap = CustomMap::new();

    let (key_a, _) = map_a.insert(Box::new(1i32) as Box<dyn Any>);
    let _ = map_b.insert(Box::new(2i32) as Box<dyn Any>);

    assert!(map_b.get(key_a).is_none());
}

// ─── inner_key round-trips ────────────────────────────────────────────────

#[test]
fn inner_key_is_custom_type() {
    let map: CustomMap = CustomMap::new();
    let (cast_key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);

    let inner: CustomInnerKey = cast_key.inner_key();
    // Should be usable for lookup
    let val = map.get_by_inner_key(inner).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
}

#[test]
fn inner_key_from_inner_key_and_metadata_round_trips() {
    let map: CustomMap = CustomMap::new();
    let (original, _) = map.insert(Box::new(77i32) as Box<dyn Any>);

    let inner = original.inner_key();
    let reconstructed = unsafe {
        CastKeyWithCustomInner::<dyn Any>::from_inner_key_and_metadata(
            inner,
            original.metadata(),
        )
    };
    assert_eq!(original, reconstructed);
}

#[test]
fn cast_key_of_with_custom_inner() {
    let map: CustomMap = CustomMap::new();
    let (cast_key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let inner = cast_key.inner_key();

    let recovered = map.cast_key_of(inner).unwrap();
    assert_eq!(recovered, cast_key);
}

#[test]
fn get_mut_by_inner_key() {
    let mut map: CustomMap = CustomMap::new();
    let (cast_key, _) = map.insert(Box::new(Dog { name: "Old".into() }) as Box<dyn Any>);

    let inner = cast_key.inner_key();
    let val = map.get_mut_by_inner_key(inner).unwrap();
    val.downcast_mut::<Dog>().unwrap().name = "New".into();

    let check = map.get_by_inner_key(inner).unwrap();
    assert_eq!(check.downcast_ref::<Dog>().unwrap().name, "New");
}

#[test]
fn remove_by_inner_key() {
    let mut map: CustomMap = CustomMap::new();
    let (cast_key, _) = map.insert(Box::new(77i32) as Box<dyn Any>);

    let inner = cast_key.inner_key();
    let removed = map.remove_by_inner_key(inner).unwrap();
    assert_eq!(*removed.downcast_ref::<i32>().unwrap(), 77);
    assert_eq!(map.len(), 0);
}

// ─── downcast_key with custom inner key ───────────────────────────────────

#[test]
fn downcast_key_correct_type() {
    let map: CustomMap = CustomMap::new();
    let (dyn_key, _) = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);

    let dog_key: CastKeyWithCustomInner<Dog> = map.downcast_key::<Dog>(dyn_key).unwrap();
    let dog: &Dog = map.get(dog_key).unwrap();
    assert_eq!(dog.name, "Rex");
}

#[test]
fn downcast_key_wrong_type() {
    let map: CustomMap = CustomMap::new();
    let (dyn_key, _) = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);

    let cat_key: Option<CastKeyWithCustomInner<Cat>> = map.downcast_key::<Cat>(dyn_key);
    assert!(cat_key.is_none());
}

// ─── insert_with_key with custom inner key ────────────────────────────────

#[test]
fn insert_with_key_receives_custom_inner_key() {
    use std::cell::Cell;

    let map: CustomMap = CustomMap::new();
    let captured = Cell::new(None::<CustomInnerKey>);

    let (cast_key, _) = map.insert_with_key(|inner_key: CustomInnerKey| {
        captured.set(Some(inner_key));
        Box::new(42i32) as Box<dyn Any>
    });

    let captured = captured.get().unwrap();
    let from_cast = cast_key.inner_key();
    assert_eq!(captured.data().idx, from_cast.data().idx);
    assert_eq!(captured.data().generation, from_cast.data().generation);
    assert_eq!(captured.extra(), from_cast.extra());
}

#[test]
fn try_insert_with_key_ok() {
    let map: CustomMap = CustomMap::new();
    let result = map.try_insert_with_key::<()>(|_inner_key: CustomInnerKey| {
        Ok(Box::new(99i32) as Box<dyn Any>)
    });
    assert!(result.is_ok());
    assert_eq!(map.len(), 1);
}

#[test]
fn try_insert_with_key_err() {
    let map: CustomMap = CustomMap::new();
    let result = map.try_insert_with_key::<&str>(|_inner_key: CustomInnerKey| Err("fail"));
    assert!(result.is_err());
    assert_eq!(map.len(), 0);
}

// ─── Small custom inner key map ───────────────────────────────────────────

type SmallCustomMap = StableCastMap<SmallCastKeyWithCustomInner<dyn Any>, Box<dyn Any>>;

#[test]
fn small_custom_inner_insert_and_get() {
    let map: SmallCustomMap = SmallCustomMap::new();
    let (key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let val = map.get(key).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
}

#[test]
fn small_custom_inner_key_is_correct_type() {
    let map: SmallCustomMap = SmallCustomMap::new();
    let (cast_key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);

    let inner: SmallCustomInnerKey = cast_key.inner_key();
    let val = map.get_by_inner_key(inner).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
}

#[test]
fn small_custom_inner_downcast() {
    let map: SmallCustomMap = SmallCustomMap::new();
    let (dyn_key, _) = map.insert(Box::new(Dog { name: "Tiny".into() }) as Box<dyn Any>);

    let dog_key: SmallCastKeyWithCustomInner<Dog> = map.downcast_key::<Dog>(dyn_key).unwrap();
    let dog: &Dog = map.get(dog_key).unwrap();
    assert_eq!(dog.name, "Tiny");
}

// ─── CoerceUnsized with custom inner key ──────────────────────────────────

#[test]
fn upcast_sized_to_dyn_any() {
    let map: CustomMap = CustomMap::new();
    let (dyn_key, _) = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);

    let dog_key: CastKeyWithCustomInner<Dog> = map.downcast_key::<Dog>(dyn_key).unwrap();
    // Implicit coercion back to dyn Any
    let back: CastKeyWithCustomInner<dyn Any> = dog_key;
    assert!(map.get(back).is_some());
}

// ─── Iteration with custom inner key ──────────────────────────────────────

#[test]
fn snapshot_keys_round_trip() {
    let map: CustomMap = CustomMap::new();
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
fn drain_yields_all() {
    let mut map: CustomMap = CustomMap::new();
    map.insert(Box::new(10i32) as Box<dyn Any>);
    map.insert(Box::new(20i32) as Box<dyn Any>);

    let drained: Vec<_> = map.drain().collect();
    assert_eq!(drained.len(), 2);
    assert_eq!(map.len(), 0);
}

#[test]
fn into_iter_consumes() {
    let map: CustomMap = CustomMap::new();
    map.insert(Box::new(1i32) as Box<dyn Any>);
    map.insert(Box::new(2i32) as Box<dyn Any>);

    let collected: Vec<_> = map.into_iter().collect();
    assert_eq!(collected.len(), 2);
}

// ─── Maps with different inner key types are incompatible ─────────────────

#[test]
fn custom_and_default_inner_key_maps_are_separate_types() {
    // This is a compile-time guarantee — CastKeyWithCustomInner and
    // CastKeyWithDefaultInner have different InnerKey types, so they
    // produce different StableCastMap types. We just verify they can
    // coexist and don't interfere.
    type DefaultMap = StableCastMap<CastKeyWithDefaultInner<dyn Any>, Box<dyn Any>>;

    let custom_map: CustomMap = CustomMap::new();
    let default_map: DefaultMap = DefaultMap::new();

    let (ck, _) = custom_map.insert(Box::new(1i32) as Box<dyn Any>);
    let (dk, _) = default_map.insert(Box::new(2i32) as Box<dyn Any>);

    assert_eq!(
        *custom_map.get(ck).unwrap().downcast_ref::<i32>().unwrap(),
        1
    );
    assert_eq!(
        *default_map.get(dk).unwrap().downcast_ref::<i32>().unwrap(),
        2
    );
}
