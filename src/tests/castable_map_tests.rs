use crate::cast_key::{CastKey, DefaultCastKey};
use crate::stable_cast_map::StableCastMap;
use std::any::Any;
use std::cell::Cell;

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
    fn speak(&self) -> &'static str {
        "woof"
    }
}

#[derive(Debug, PartialEq)]
struct Parrot {
    color: String,
}
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

type Map = StableCastMap<DefaultCastKey<dyn Any>, Box<dyn Any>>;

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
    // key is DefaultCastKey<dyn Any>, get works directly
    let val = map.get(key).unwrap();
    let dog_ref = val.downcast_ref::<Dog>().unwrap();
    assert_eq!(dog_ref.name, "Rex");
}

// ─── downcast_key ───────────────────────────────────────────────────────────

#[test]
fn downcast_key_correct_type_then_get() {
    let map: Map = Map::new();
    let (dyn_key, _) = map.insert(Box::new(Dog {
        name: "Buddy".into(),
    }) as Box<dyn Any>);

    let dog_key: DefaultCastKey<Dog> = map.downcast_key::<Dog>(dyn_key).unwrap();

    let dog: &Dog = map.get(dog_key).unwrap();
    assert_eq!(dog.name, "Buddy");
}

#[test]
fn downcast_key_wrong_type_returns_none() {
    let map: Map = Map::new();
    let (dyn_key, _) = map.insert(Box::new(Dog {
        name: "Fido".into(),
    }) as Box<dyn Any>);

    let result: Option<DefaultCastKey<Parrot>> =
        map.downcast_key::<Parrot>(dyn_key);
    assert!(result.is_none());
}

// ─── get with upcast key ─────────────────────────────────────────────────

#[test]
fn get_with_trait_key() {
    type AnimalMap = StableCastMap<DefaultCastKey<dyn Any>, Box<dyn Any>>;
    let map: AnimalMap = AnimalMap::new();

    let parrot = Parrot {
        color: "green".into(),
    };
    // Insert as dyn Any
    let (dyn_key, _) = map.insert(Box::new(parrot) as Box<dyn Any>);

    // Downcast key to concrete, then upcast to dyn Animal
    let concrete_key: DefaultCastKey<Parrot> =
        map.downcast_key::<Parrot>(dyn_key).unwrap();
    let animal_key: DefaultCastKey<dyn Animal> = concrete_key;

    let animal: &dyn Animal = map.get(animal_key).unwrap();
    assert_eq!(animal.speak(), "squawk");
}

#[test]
fn get_mut_modifies_value() {
    let mut map: Map = Map::new();
    let (dyn_key, _) = map.insert(Box::new(Dog { name: "Old".into() }) as Box<dyn Any>);

    let dog_key: DefaultCastKey<Dog> = map.downcast_key::<Dog>(dyn_key).unwrap();

    let dog: &mut Dog = map.get_mut(dog_key).unwrap();
    dog.name = "New".into();

    let dog_again: &Dog = map.get(dog_key).unwrap();
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

    let dog_key: DefaultCastKey<Dog> = map.downcast_key::<Dog>(dyn_key).unwrap();

    let removed = map.remove(dog_key).unwrap();
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
    assert_eq!(ptr1 as *const () as usize, ptr1_again as *const () as usize);
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

// ─── Clone ─────────────────────────────────────────────────────────────────

type RcMap = StableCastMap<DefaultCastKey<dyn Any>, std::rc::Rc<dyn Any>>;

#[test]
fn clone_old_key_works_on_both_maps() {
    let map: RcMap = RcMap::new();
    let (key, _) = map.insert(std::rc::Rc::new(42i32) as std::rc::Rc<dyn Any>);

    let cloned = map.clone();

    // old key works on the original
    let val = map.get(key).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);

    // old key works on the clone
    let val = cloned.get(key).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
}

#[test]
fn clone_new_insert_on_clone_not_visible_on_original() {
    let map: RcMap = RcMap::new();
    let (old_key, _) = map.insert(std::rc::Rc::new(1i32) as std::rc::Rc<dyn Any>);

    let cloned = map.clone();
    let (new_key, _) = cloned.insert(std::rc::Rc::new(99i32) as std::rc::Rc<dyn Any>);

    // new key works on the clone
    assert!(cloned.get(new_key).is_some());

    // new key does NOT work on the original
    assert!(map.get(new_key).is_none());

    // old key still works on both
    assert!(map.get(old_key).is_some());
    assert!(cloned.get(old_key).is_some());
}

#[test]
fn clone_new_insert_on_original_not_visible_on_clone() {
    let map: RcMap = RcMap::new();
    let (old_key, _) = map.insert(std::rc::Rc::new(1i32) as std::rc::Rc<dyn Any>);

    let cloned = map.clone();
    let (new_key, _) = map.insert(std::rc::Rc::new(77i32) as std::rc::Rc<dyn Any>);

    // new key works on the original
    assert!(map.get(new_key).is_some());

    // new key does NOT work on the clone
    assert!(cloned.get(new_key).is_none());

    // old key still works on both
    assert!(map.get(old_key).is_some());
    assert!(cloned.get(old_key).is_some());
}

#[test]
fn clone_preserves_len() {
    let map: RcMap = RcMap::new();
    map.insert(std::rc::Rc::new(1i32) as std::rc::Rc<dyn Any>);
    map.insert(std::rc::Rc::new(2i32) as std::rc::Rc<dyn Any>);
    map.insert(std::rc::Rc::new(3i32) as std::rc::Rc<dyn Any>);

    let cloned = map.clone();
    assert_eq!(cloned.len(), 3);
}

#[test]
fn clone_remove_on_clone_does_not_affect_original() {
    let map: RcMap = RcMap::new();
    let (key, _) = map.insert(std::rc::Rc::new(42i32) as std::rc::Rc<dyn Any>);

    let mut cloned = map.clone();
    cloned.remove(key);

    // gone from clone
    assert!(cloned.get(key).is_none());
    assert_eq!(cloned.len(), 0);

    // still in original
    assert!(map.get(key).is_some());
    assert_eq!(map.len(), 1);
}

#[test]
fn clone_diverges_after_remove_and_reinsert() {
    let map: RcMap = RcMap::new();
    let (key, _) = map.insert(std::rc::Rc::new(1i32) as std::rc::Rc<dyn Any>);

    let mut cloned = map.clone();

    // remove from clone, reinsert something else (reuses the slot)
    cloned.remove(key);
    let (new_key, _) = cloned.insert(std::rc::Rc::new(999i32) as std::rc::Rc<dyn Any>);

    // old key is stale on clone (generation mismatch)
    assert!(cloned.get(key).is_none());

    // new key from clone doesn't work on original
    assert!(map.get(new_key).is_none());

    // old key still works on original
    assert!(map.get(key).is_some());
}

// ─── insert_with_key ───────────────────────────────────────────────────────

#[test]
fn insert_with_key_returns_valid_cast_key() {
    let map: Map = Map::new();
    let (cast_key, val) = map.insert_with_key(|_inner_key| Box::new(42i32) as Box<dyn Any>);
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
    assert_eq!(
        *map.get(cast_key).unwrap().downcast_ref::<i32>().unwrap(),
        42
    );
}

#[test]
fn insert_with_key_inner_key_matches_returned_cast_key() {
    use crate::key::Key;

    let map: Map = Map::new();
    let (cast_key, _) = map.insert_with_key(|inner_key| {
        // inner_key should have valid data at this point
        assert_ne!(inner_key.extra().0, 0, "map_id must be non-zero");
        Box::new(99i32) as Box<dyn Any>
    });

    // The inner key extracted from the returned cast key should match
    // what the closure received
    let inner_from_cast = cast_key.inner_key();
    let reconstructed = map.get_by_inner_key(inner_from_cast).unwrap();
    assert_eq!(*reconstructed.downcast_ref::<i32>().unwrap(), 99);
}

#[test]
fn insert_with_key_closure_receives_correct_inner_key() {
    use crate::cast_key::DefaultMapKey;
    use crate::key::Key;
    use std::cell::Cell;

    let map: Map = Map::new();
    let captured_inner = Cell::new(None::<DefaultMapKey<u32, u32>>);

    let (cast_key, _) = map.insert_with_key(|inner_key| {
        captured_inner.set(Some(inner_key));
        Box::new(77i32) as Box<dyn Any>
    });

    let captured = captured_inner.get().unwrap();
    let from_cast = cast_key.inner_key();
    assert_eq!(captured.data().idx, from_cast.data().idx);
    assert_eq!(captured.data().generation, from_cast.data().generation);
    assert_eq!(captured.extra(), from_cast.extra());
}

#[test]
fn insert_with_key_can_store_inner_key_in_value() {
    use crate::cast_key::DefaultMapKey;
    use crate::key::Key;

    struct SelfAware {
        my_inner_key: DefaultMapKey<u32, u32>,
        data: i32,
    }

    let map: StableCastMap<DefaultCastKey<dyn Any>, Box<dyn Any>> = StableCastMap::new();
    let (cast_key, val) = map.insert_with_key(|inner_key| {
        Box::new(SelfAware {
            my_inner_key: inner_key,
            data: 123,
        }) as Box<dyn Any>
    });

    let sa = val.downcast_ref::<SelfAware>().unwrap();
    assert_eq!(sa.data, 123);

    // The stored inner key should match
    let inner_from_cast = cast_key.inner_key();
    assert_eq!(sa.my_inner_key.data().idx, inner_from_cast.data().idx);
    assert_eq!(
        sa.my_inner_key.data().generation,
        inner_from_cast.data().generation
    );
    assert_eq!(sa.my_inner_key.extra(), inner_from_cast.extra());
}

#[test]
fn insert_with_key_multiple_inserts() {
    let map: Map = Map::new();

    let (k1, _) = map.insert_with_key(|_| Box::new(1i32) as Box<dyn Any>);
    let (k2, _) = map.insert_with_key(|_| Box::new(2i32) as Box<dyn Any>);
    let (k3, _) = map.insert_with_key(|_| Box::new(3i32) as Box<dyn Any>);

    assert_eq!(map.len(), 3);
    assert_eq!(*map.get(k1).unwrap().downcast_ref::<i32>().unwrap(), 1);
    assert_eq!(*map.get(k2).unwrap().downcast_ref::<i32>().unwrap(), 2);
    assert_eq!(*map.get(k3).unwrap().downcast_ref::<i32>().unwrap(), 3);
}

#[test]
fn insert_with_key_after_remove_reuses_slot() {
    let mut map: Map = Map::new();
    let (k1, _) = map.insert_with_key(|_| Box::new(1i32) as Box<dyn Any>);
    map.remove(k1);

    let (k2, _) = map.insert_with_key(|_| Box::new(2i32) as Box<dyn Any>);
    assert_eq!(map.len(), 1);
    // Old key is stale
    assert!(map.get(k1).is_none());
    assert_eq!(*map.get(k2).unwrap().downcast_ref::<i32>().unwrap(), 2);
}

#[test]
fn insert_with_key_pointer_stability() {
    let map: Map = Map::new();
    let (_, ref1) = map.insert_with_key(|_| Box::new(1i32) as Box<dyn Any>);
    let ptr1 = ref1 as *const dyn Any as *const () as usize;

    // Insert many more to trigger growth
    for i in 0..100 {
        map.insert_with_key(|_| Box::new(i as u64) as Box<dyn Any>);
    }

    let (first_key, _) = map.snapshot()[0];
    let ref1_again = map.get(first_key).unwrap();
    let ptr1_again = ref1_again as *const dyn Any as *const () as usize;
    assert_eq!(ptr1, ptr1_again);
}

// ─── try_insert_with_key ───────────────────────────────────────────────────

#[test]
fn try_insert_with_key_ok() {
    let map: Map = Map::new();
    let result =
        map.try_insert_with_key::<String>(|_inner_key| Ok(Box::new(42i32) as Box<dyn Any>));
    assert!(result.is_ok());

    let (cast_key, val) = result.unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
    assert_eq!(
        *map.get(cast_key).unwrap().downcast_ref::<i32>().unwrap(),
        42
    );
    assert_eq!(map.len(), 1);
}

#[test]
fn try_insert_with_key_err_does_not_insert() {
    let map: Map = Map::new();
    let result =
        map.try_insert_with_key::<String>(|_inner_key| Err("something went wrong".to_string()));
    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), "something went wrong");
    assert_eq!(map.len(), 0);
}

#[test]
fn try_insert_with_key_err_slot_is_reusable() {
    let map: Map = Map::new();

    // Failed insert
    let _ = map.try_insert_with_key::<()>(|_| Err(()));

    // Successful insert should reuse the slot
    let (key, val) = map
        .try_insert_with_key::<()>(|_| Ok(Box::new(99i32) as Box<dyn Any>))
        .unwrap();

    assert_eq!(map.len(), 1);
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 99);
    assert!(map.get(key).is_some());
}

#[test]
fn try_insert_with_key_inner_key_matches() {
    use crate::cast_key::DefaultMapKey;
    use crate::key::Key;
    use std::cell::Cell;

    let map: Map = Map::new();
    let captured_inner = Cell::new(None::<DefaultMapKey<u32, u32>>);

    let (cast_key, _) = map
        .try_insert_with_key::<()>(|inner_key| {
            captured_inner.set(Some(inner_key));
            Ok(Box::new(55i32) as Box<dyn Any>)
        })
        .unwrap();

    let captured = captured_inner.get().unwrap();
    let from_cast = cast_key.inner_key();
    assert_eq!(captured.data().idx, from_cast.data().idx);
    assert_eq!(captured.data().generation, from_cast.data().generation);
    assert_eq!(captured.extra(), from_cast.extra());
}

#[test]
fn try_insert_with_key_ok_then_err_preserves_first() {
    let map: Map = Map::new();

    let (k1, _) = map
        .try_insert_with_key::<()>(|_| Ok(Box::new(1i32) as Box<dyn Any>))
        .unwrap();

    let _ = map.try_insert_with_key::<()>(|_| Err(()));

    assert_eq!(map.len(), 1);
    assert_eq!(*map.get(k1).unwrap().downcast_ref::<i32>().unwrap(), 1);
}

#[test]
fn try_insert_with_key_can_insert_during_closure() {
    // The closure can insert other elements (since insert takes &self)
    let map: Map = Map::new();

    let (outer_key, _) = map
        .try_insert_with_key::<()>(|_inner_key| {
            // Insert another element from within the closure
            map.insert(Box::new(100i32) as Box<dyn Any>);
            Ok(Box::new(200i32) as Box<dyn Any>)
        })
        .unwrap();

    assert_eq!(map.len(), 2);
    assert_eq!(
        *map.get(outer_key).unwrap().downcast_ref::<i32>().unwrap(),
        200
    );
}

// ─── cast_key_of ───────────────────────────────────────────────────────────

#[test]
fn cast_key_of_returns_same_as_insert() {
    let map: Map = Map::new();
    let (cast_key, _) = map.insert(Box::new(42i32) as Box<dyn Any>);
    let inner = cast_key.inner_key();

    let recovered = map.cast_key_of(inner).unwrap();
    assert_eq!(recovered, cast_key);
}

#[test]
fn cast_key_of_works_for_get() {
    let map: Map = Map::new();
    let (_, _) = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);
    let (cast_key, _) = map.insert(Box::new(99i32) as Box<dyn Any>);

    let inner = cast_key.inner_key();
    let recovered = map.cast_key_of(inner).unwrap();

    let val = map.get(recovered).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 99);
}

#[test]
fn cast_key_of_stale_inner_key_returns_none() {
    let mut map: Map = Map::new();
    let (cast_key, _) = map.insert(Box::new(1i32) as Box<dyn Any>);
    let inner = cast_key.inner_key();

    map.remove(cast_key);
    assert!(map.cast_key_of(inner).is_none());
}

#[test]
fn cast_key_of_cross_map_returns_none() {
    let map_a: Map = Map::new();
    let map_b: Map = Map::new();

    let (key_a, _) = map_a.insert(Box::new(1i32) as Box<dyn Any>);
    let _ = map_b.insert(Box::new(2i32) as Box<dyn Any>);

    let inner_a = key_a.inner_key();
    assert!(map_b.cast_key_of(inner_a).is_none());
}

#[test]
fn cast_key_of_from_insert_with_key() {
    use crate::cast_key::DefaultMapKey;
    use std::cell::Cell;

    let map: Map = Map::new();
    let captured = Cell::new(None::<DefaultMapKey<u32, u32>>);

    let (cast_key, _) = map.insert_with_key(|inner_key| {
        captured.set(Some(inner_key));
        Box::new(77i32) as Box<dyn Any>
    });

    // Recover the cast key from the captured inner key
    let recovered = map.cast_key_of(captured.get().unwrap()).unwrap();
    assert_eq!(recovered, cast_key);
}

#[test]
fn cast_key_of_downcast_round_trip() {
    // cast_key_of → downcast_key → get with concrete key
    let map: Map = Map::new();
    let (cast_key, _) = map.insert(Box::new(Dog {
        name: "Buddy".into(),
    }) as Box<dyn Any>);
    let inner = cast_key.inner_key();

    let recovered_dyn = map.cast_key_of(inner).unwrap();
    let dog_key: DefaultCastKey<Dog> = map
        .downcast_key::<Dog>(recovered_dyn)
        .unwrap();

    let dog: &Dog = map.get(dog_key).unwrap();
    assert_eq!(dog.name, "Buddy");
}

#[test]
fn cast_key_of_multiple_elements() {
    let map: Map = Map::new();
    let (k1, _) = map.insert(Box::new(1i32) as Box<dyn Any>);
    let (k2, _) = map.insert(Box::new(2i32) as Box<dyn Any>);
    let (k3, _) = map.insert(Box::new(3i32) as Box<dyn Any>);

    for original in [k1, k2, k3] {
        let inner = original.inner_key();
        let recovered = map.cast_key_of(inner).unwrap();
        assert_eq!(recovered, original);
    }
}