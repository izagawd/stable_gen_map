use std::any::Any;
use crate::castable_map::{KeyCastableStableGenMap, KeyCastableBoxStableGenMap};
use crate::key::Key;
use crate::castable_key::{DefaultCastableKey, downcast_key, CastableKey};

trait Animal: Any {
    fn speak(&self) -> &'static str;
}

trait Flyer {
    fn max_altitude(&self) -> u32;
}

#[derive(Debug, PartialEq)]
struct Dog {
    name: String,
}
impl Animal for Dog {
    fn speak(&self) -> &'static str { "woof" }
}

#[derive(Debug, PartialEq)]
struct Parrot {
    color: String,
}
impl Animal for Parrot {
    fn speak(&self) -> &'static str { "squawk" }
}
impl Flyer for Parrot {
    fn max_altitude(&self) -> u32 { 500 }
}

type Map = KeyCastableStableGenMap<DefaultCastableKey<dyn Any>, Box<dyn Any>>;

// ─── Basic insert / get ─────────────────────────────────────────────────────

#[test]
fn insert_and_get_sized_through_dyn_any() {
    let map: Map = Map::new();
    let (key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let val = map.get(key).unwrap();
    assert!(val.downcast_ref::<i32>().is_some());
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
}

#[test]
fn insert_multiple_types() {
    let map: Map = Map::new();
    let (k1, _) = map.insert(Box::new(10u64) as Box<dyn Any>);
    let (k2, _) = map.insert(Box::new("hello".to_string()) as Box<dyn Any>);
    let (k3, _) = map.insert(Box::new(true) as Box<dyn Any>);

    assert_eq!(*map.get(k1).unwrap().downcast_ref::<u64>().unwrap(), 10);
    assert_eq!(
        map.get(k2).unwrap().downcast_ref::<String>().unwrap(),
        "hello"
    );
    assert_eq!(*map.get(k3).unwrap().downcast_ref::<bool>().unwrap(), true);
}

#[test]
fn get_returns_none_after_remove() {
    let mut map: Map = Map::new();
    let (key, _) = map.insert(Box::new(99i32) as Box<dyn Any>);
    assert!(map.get(key).is_some());
    map.remove(key);
    assert!(map.get(key).is_none());
}

#[test]
fn len_tracks_inserts_and_removes() {
    let mut map: Map = Map::new();
    assert_eq!(map.len(), 0);
    let (k1, _) = map.insert(Box::new(1i32) as Box<dyn Any>);
    let (k2, _) = map.insert(Box::new(2i32) as Box<dyn Any>);
    assert_eq!(map.len(), 2);
    map.remove(k1);
    assert_eq!(map.len(), 1);
    map.remove(k2);
    assert_eq!(map.len(), 0);
}

// ─── Upcast key: concrete → dyn Any ─────────────────────────────────────────

#[test]
fn insert_concrete_upcast_key_then_get() {
    let map: Map = Map::new();
    let dog = Dog { name: "Rex".into() };
    let (key, _) = map.insert(Box::new(dog) as Box<dyn Any>);
    // key is DefaultCastableKey<dyn Any>, get works directly
    let val = map.get(key).unwrap();
    let dog_ref = val.downcast_ref::<Dog>().unwrap();
    assert_eq!(dog_ref.name, "Rex");
}

// ─── downcast_key ───────────────────────────────────────────────────────────

#[test]
fn downcast_key_correct_type_then_get_as() {
    let map: Map = Map::new();
    let (dyn_key, _) = map.insert(Box::new(Dog { name: "Buddy".into() }) as Box<dyn Any>);

    let dog_key: DefaultCastableKey<Dog> =
        downcast_key::<Dog, _, DefaultCastableKey<Dog>>(dyn_key).unwrap();

    let dog: &Dog = map.get_as(dog_key).unwrap();
    assert_eq!(dog.name, "Buddy");
}

#[test]
fn downcast_key_wrong_type_returns_none() {
    let map: Map = Map::new();
    let (dyn_key, _) = map.insert(Box::new(Dog { name: "Fido".into() }) as Box<dyn Any>);

    let result: Option<DefaultCastableKey<Parrot>> =
        downcast_key::<Parrot, _, DefaultCastableKey<Parrot>>(dyn_key);
    assert!(result.is_none());
}

// ─── get_as with upcast key ─────────────────────────────────────────────────

#[test]
fn get_as_with_trait_key() {
    type AnimalMap = KeyCastableStableGenMap<DefaultCastableKey<dyn Any>, Box<dyn Any>>;
    let map: AnimalMap = AnimalMap::new();

    let parrot = Parrot { color: "green".into() };
    // Insert as dyn Any
    let (dyn_key, _) = map.insert(Box::new(parrot) as Box<dyn Any>);

    // Downcast key to concrete, then upcast to dyn Animal
    let concrete_key: DefaultCastableKey<Parrot> =
        downcast_key::<Parrot, _, DefaultCastableKey<Parrot>>(dyn_key).unwrap();
    let animal_key: DefaultCastableKey<dyn Animal> = concrete_key;

    let animal: &dyn Animal = map.get_as(animal_key).unwrap();
    assert_eq!(animal.speak(), "squawk");
}

#[test]
fn get_as_mut_modifies_value() {
    let mut map: Map = Map::new();
    let (dyn_key, _) = map.insert(Box::new(Dog { name: "Old".into() }) as Box<dyn Any>);

    let dog_key: DefaultCastableKey<Dog> =
        downcast_key::<Dog, _, DefaultCastableKey<Dog>>(dyn_key).unwrap();

    let dog: &mut Dog = map.get_as_mut(dog_key).unwrap();
    dog.name = "New".into();

    let dog_again: &Dog = map.get_as(dog_key).unwrap();
    assert_eq!(dog_again.name, "New");
}

// ─── Cross-map key rejection ────────────────────────────────────────────────

#[test]
fn key_from_different_map_returns_none() {
    let map_a: Map = Map::new();
    let map_b: Map = Map::new();

    let (key_a, _) = map_a.insert(Box::new(1i32) as Box<dyn Any>);
    let _ = map_b.insert(Box::new(2i32) as Box<dyn Any>);

    // key_a has map_a's id, should not work on map_b
    assert!(map_b.get(key_a).is_none());
}

#[test]
fn key_from_different_map_cannot_remove() {
    let mut map_a: Map = Map::new();
    let mut map_b: Map = Map::new();

    let (key_a, _) = map_a.insert(Box::new(100i32) as Box<dyn Any>);
    let _ = map_b.insert(Box::new(200i32) as Box<dyn Any>);

    assert!(map_b.remove(key_a).is_none());
    // map_a's element is untouched
    assert_eq!(map_a.len(), 1);
}

// ─── Stale key rejection (generation mismatch) ─────────────────────────────

#[test]
fn stale_key_returns_none() {
    let mut map: Map = Map::new();
    let (key, _) = map.insert(Box::new(1i32) as Box<dyn Any>);
    map.remove(key);
    let (_, _) = map.insert(Box::new(2i32) as Box<dyn Any>); // reuses slot
    assert!(map.get(key).is_none()); // old generation
}

// ─── Snapshot (single alloc) ────────────────────────────────────────────────

#[test]
fn snapshot_returns_all_elements_with_patched_keys() {
    let map: Map = Map::new();
    map.insert(Box::new(1i32) as Box<dyn Any>);
    map.insert(Box::new(2i32) as Box<dyn Any>);
    map.insert(Box::new(3i32) as Box<dyn Any>);

    let snap = map.snapshot();
    assert_eq!(snap.len(), 3);

    let mut values: Vec<i32> = snap
        .iter()
        .map(|(_, v)| *v.downcast_ref::<i32>().unwrap())
        .collect();
    values.sort();
    assert_eq!(values, vec![1, 2, 3]);
}

#[test]
fn snapshot_keys_can_be_used_for_lookup() {
    let map: Map = Map::new();
    map.insert(Box::new(42i32) as Box<dyn Any>);
    map.insert(Box::new(99i32) as Box<dyn Any>);

    let keys = map.snapshot_keys();
    for key in keys {
        assert!(map.get(key).is_some());
    }
}

#[test]
fn snapshot_refs_returns_correct_count() {
    let map: Map = Map::new();
    map.insert(Box::new(1i32) as Box<dyn Any>);
    map.insert(Box::new(2i32) as Box<dyn Any>);
    assert_eq!(map.snapshot_refs().len(), 2);
}

// ─── Drain ──────────────────────────────────────────────────────────────────

#[test]
fn drain_yields_all_and_empties_map() {
    let mut map: Map = Map::new();
    map.insert(Box::new(10i32) as Box<dyn Any>);
    map.insert(Box::new(20i32) as Box<dyn Any>);
    map.insert(Box::new(30i32) as Box<dyn Any>);

    let drained: Vec<_> = map.drain().collect();
    assert_eq!(drained.len(), 3);
    assert_eq!(map.len(), 0);
}

#[test]
fn drain_keys_have_correct_map_id() {
    let mut map: Map = Map::new();
    let (original_key, _) = map.insert(Box::new(1i32) as Box<dyn Any>);
    let map_id = original_key.map_id();

    for (key, _) in map.drain() {
        assert_eq!(key.map_id(), map_id);
    }
}

// ─── into_iter (owned) ─────────────────────────────────────────────────────

#[test]
fn into_iter_consumes_map() {
    let map: Map = Map::new();
    map.insert(Box::new(1i32) as Box<dyn Any>);
    map.insert(Box::new(2i32) as Box<dyn Any>);

    let collected: Vec<_> = map.into_iter().collect();
    assert_eq!(collected.len(), 2);
}

// ─── iter_mut ───────────────────────────────────────────────────────────────

#[test]
fn iter_mut_can_modify_values() {
    let mut map: Map = Map::new();
    let (k1, _) = map.insert(Box::new(Dog { name: "A".into() }) as Box<dyn Any>);
    let (k2, _) = map.insert(Box::new(Dog { name: "B".into() }) as Box<dyn Any>);

    for (_, stored) in map.iter_mut() {
        if let Some(dog) = stored.downcast_mut::<Dog>() {
            dog.name = format!("{}!", dog.name);
        }
    }

    let d1 = map.get(k1).unwrap().downcast_ref::<Dog>().unwrap();
    let d2 = map.get(k2).unwrap().downcast_ref::<Dog>().unwrap();
    assert!(d1.name.ends_with('!'));
    assert!(d2.name.ends_with('!'));
}

// ─── retain ─────────────────────────────────────────────────────────────────

#[test]
fn retain_keeps_matching_removes_rest() {
    let mut map: Map = Map::new();
    map.insert(Box::new(1i32) as Box<dyn Any>);
    map.insert(Box::new(2i32) as Box<dyn Any>);
    map.insert(Box::new(3i32) as Box<dyn Any>);
    map.insert(Box::new("hello".to_string()) as Box<dyn Any>);

    // Keep only i32 values
    map.retain(|_, stored| stored.downcast_ref::<i32>().is_some());
    assert_eq!(map.len(), 3);
}

// ─── clear ──────────────────────────────────────────────────────────────────

#[test]
fn clear_removes_all() {
    let mut map: Map = Map::new();
    map.insert(Box::new(1i32) as Box<dyn Any>);
    map.insert(Box::new(2i32) as Box<dyn Any>);
    map.clear();
    assert_eq!(map.len(), 0);
}

// ─── Index ──────────────────────────────────────────────────────────────────

#[test]
fn index_operator_works() {
    let map: Map = Map::new();
    let (key, _) = map.insert(Box::new(77i32) as Box<dyn Any>);
    let val = &map[key];
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 77);
}

#[test]
#[should_panic]
fn index_panics_on_invalid_key() {
    let mut map: Map = Map::new();
    let (key, _) = map.insert(Box::new(1i32) as Box<dyn Any>);
    map.remove(key);
    let _ = &map[key];
}

// ─── remove_by with cross-typed key ─────────────────────────────────────────

#[test]
fn remove_by_with_concrete_key() {
    let mut map: Map = Map::new();
    let (dyn_key, _) = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);

    let dog_key: DefaultCastableKey<Dog> =
        downcast_key::<Dog, _, DefaultCastableKey<Dog>>(dyn_key).unwrap();

    let removed = map.remove_by(dog_key).unwrap();
    assert!(removed.downcast_ref::<Dog>().is_some());
    assert_eq!(map.len(), 0);
}

// ─── Pointer stability ─────────────────────────────────────────────────────

#[test]
fn references_stable_across_inserts() {
    let map: Map = Map::new();
    let (_, ref1) = map.insert(Box::new(1i32) as Box<dyn Any>);
    let ptr1 = ref1 as *const dyn Any;

    // Insert more to potentially trigger vec growth
    for i in 0..100 {
        map.insert(Box::new(i as u64) as Box<dyn Any>);
    }

    let (k1_key, _) = map.snapshot()[0]; // re-get key for first element
    let ref1_again = map.get(k1_key).unwrap();
    let ptr1_again = ref1_again as *const dyn Any;

    // Data pointer should be identical (stable behind Box)
    assert_eq!(
        ptr1 as *const () as usize,
        ptr1_again as *const () as usize
    );
}

// ─── get_by_index_only ─────────────────────────────────────────────────────

#[test]
fn get_by_index_only_returns_occupied() {
    let map: Map = Map::new();
    let (key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let idx = key.key_data().idx;

    let (found_key, val) = map.get_by_index_only(idx).unwrap();
    assert_eq!(found_key.key_data().idx, idx);
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
}
