use crate::cast_key::StableCastKey;
use crate::key::DefaultKey;
use crate::key::Key;
use crate::stable_cast_map::{StableBoxCastMap, StableCastMap};
use crate::stable_deref_map::DerefSlot;
use std::any::Any;

type CastMap = StableBoxCastMap<DefaultKey, dyn Any>;

#[derive(Debug, PartialEq)]
struct Dog {
    name: String,
}

#[derive(Debug, PartialEq)]
struct Cat {
    name: String,
}

// ─── Insert & Get ──────────────────────────────────────────────────────────

#[test]
fn insert_and_get_sized_through_dyn_any() {
    let map: CastMap = CastMap::new();
    let key = map.insert(Box::new(42i32) as Box<dyn Any>);
    let val_ref = map.get(key).unwrap();
    assert_eq!(*val_ref.downcast_ref::<i32>().unwrap(), 42);
    let fetched = map.get(key).unwrap();
    assert_eq!(*fetched.downcast_ref::<i32>().unwrap(), 42);
}

#[test]
fn insert_multiple_types() {
    let map: CastMap = CastMap::new();
    let k1 = map.insert(Box::new(10u64) as Box<dyn Any>);
    let k2 = map.insert(Box::new("hello".to_string()) as Box<dyn Any>);
    let k3 = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);
    assert_eq!(*map.get(k1).unwrap().downcast_ref::<u64>().unwrap(), 10);
    assert_eq!(
        map.get(k2).unwrap().downcast_ref::<String>().unwrap(),
        "hello"
    );
    assert_eq!(
        map.get(k3).unwrap().downcast_ref::<Dog>().unwrap(),
        &Dog { name: "Rex".into() }
    );
}

// ─── Get with concrete key ─────────────────────────────────────────────────

#[test]
fn get_with_concrete_key() {
    let map: CastMap = CastMap::new();
    let dyn_key = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);
    let dog_key: StableCastKey<Dog> = map.downcast_key::<Dog>(dyn_key).unwrap();
    let dog: &Dog = map.get(dog_key).unwrap();
    assert_eq!(dog.name, "Rex");
}

// ─── Remove ────────────────────────────────────────────────────────────────

#[test]
fn remove_returns_value_and_invalidates_key() {
    let mut map: CastMap = CastMap::new();
    let key = map.insert(Box::new(99i32) as Box<dyn Any>);
    let removed = map.remove(key).unwrap();
    assert_eq!(*removed.downcast_ref::<i32>().unwrap(), 99);
    assert!(map.get(key).is_none());
    assert_eq!(map.len(), 0);
}

#[test]
fn remove_with_concrete_key() {
    let mut map: CastMap = CastMap::new();
    let dyn_key = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);
    let dog_key: StableCastKey<Dog> = map.downcast_key::<Dog>(dyn_key).unwrap();
    let removed = map.remove(dog_key).unwrap();
    assert_eq!(
        removed.downcast_ref::<Dog>().unwrap(),
        &Dog { name: "Rex".into() }
    );
}

// ─── Stale key ─────────────────────────────────────────────────────────────

#[test]
fn stale_key_returns_none() {
    let mut map: CastMap = CastMap::new();
    let key = map.insert(Box::new(1i32) as Box<dyn Any>);
    map.remove(key);
    let _ = map.insert(Box::new(2i32) as Box<dyn Any>);
    assert!(map.get(key).is_none());
}

// ─── Cross-map rejection ───────────────────────────────────────────────────

#[test]
fn key_from_different_map_returns_none() {
    let map_a: CastMap = CastMap::new();
    let map_b: CastMap = CastMap::new();
    let key_a = map_a.insert(Box::new(1i32) as Box<dyn Any>);
    let _ = map_b.insert(Box::new(2i32) as Box<dyn Any>);
    assert!(map_b.get(key_a).is_none());
}

#[test]
fn key_from_different_map_cannot_remove() {
    let map_a: CastMap = CastMap::new();
    let mut map_b: CastMap = CastMap::new();
    let key_a = map_a.insert(Box::new(1i32) as Box<dyn Any>);
    let _ = map_b.insert(Box::new(2i32) as Box<dyn Any>);
    assert!(map_b.remove(key_a).is_none());
    assert_eq!(map_b.len(), 1);
}

#[test]
fn cross_map_get_mut_returns_none() {
    let map_a: CastMap = CastMap::new();
    let mut map_b: CastMap = CastMap::new();
    let key_a = map_a.insert(Box::new(1i32) as Box<dyn Any>);
    let _ = map_b.insert(Box::new(2i32) as Box<dyn Any>);
    assert!(map_b.get_mut(key_a).is_none());
}

// ─── get_mut ───────────────────────────────────────────────────────────────

#[test]
fn get_mut_modifies_value() {
    let mut map: CastMap = CastMap::new();
    let key = map.insert(Box::new(Dog { name: "Old".into() }) as Box<dyn Any>);
    let val = map.get_mut(key).unwrap();
    val.downcast_mut::<Dog>().unwrap().name = "New".into();
    let check = map.get(key).unwrap();
    assert_eq!(check.downcast_ref::<Dog>().unwrap().name, "New");
}

#[test]
fn get_mut_with_concrete_key() {
    let mut map: CastMap = CastMap::new();
    let dyn_key = map.insert(Box::new(Dog { name: "Old".into() }) as Box<dyn Any>);
    let dog_key: StableCastKey<Dog> = map.downcast_key::<Dog>(dyn_key).unwrap();
    let dog: &mut Dog = map.get_mut(dog_key).unwrap();
    dog.name = "New".into();
    let check: &Dog = map.get(dog_key).unwrap();
    assert_eq!(check.name, "New");
}

// ─── len / clear ───────────────────────────────────────────────────────────

#[test]
fn len_tracks_inserts_and_removes() {
    let mut map: CastMap = CastMap::new();
    assert_eq!(map.len(), 0);
    let k1 = map.insert(Box::new(1i32) as Box<dyn Any>);
    let k2 = map.insert(Box::new(2i32) as Box<dyn Any>);
    assert_eq!(map.len(), 2);
    map.remove(k1);
    assert_eq!(map.len(), 1);
    map.remove(k2);
    assert_eq!(map.len(), 0);
}

#[test]
fn clear_removes_all() {
    let mut map: CastMap = CastMap::new();
    let k1 = map.insert(Box::new(1i32) as Box<dyn Any>);
    let k2 = map.insert(Box::new(2i32) as Box<dyn Any>);
    map.clear();
    assert_eq!(map.len(), 0);
    assert!(map.get(k1).is_none());
    assert!(map.get(k2).is_none());
}

// ─── downcast_key ──────────────────────────────────────────────────────────

#[test]
fn downcast_key_correct_type() {
    let map: CastMap = CastMap::new();
    let dyn_key = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);
    assert!(map.downcast_key::<Dog>(dyn_key).is_some());
}

#[test]
fn downcast_key_wrong_type_returns_none() {
    let map: CastMap = CastMap::new();
    let dyn_key = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);
    assert!(map.downcast_key::<Cat>(dyn_key).is_none());
}

#[test]
fn downcast_key_stale_returns_none() {
    let mut map: CastMap = CastMap::new();
    let dyn_key = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);
    map.remove(dyn_key);
    assert!(map.downcast_key::<Dog>(dyn_key).is_none());
}

#[test]
fn downcast_key_cross_map_returns_none() {
    let map_a: CastMap = CastMap::new();
    let map_b: CastMap = CastMap::new();
    let key_a = map_a.insert(Box::new(42i32) as Box<dyn Any>);
    let _ = map_b.insert(Box::new(42i32) as Box<dyn Any>);
    assert!(map_b.downcast_key::<i32>(key_a).is_none());
}

// ─── insert_with_key ───────────────────────────────────────────────────────

#[test]
fn insert_with_key_closure_receives_correct_inner_key() {
    use std::cell::Cell;
    let map: CastMap = CastMap::new();
    let captured = Cell::new(None);
    let cast_key = map.insert_with_key(|inner_key| {
        captured.set(Some(inner_key));
        Box::new(42i32) as Box<dyn Any>
    });
    let inner = captured.get().unwrap();
    assert_eq!(inner.data().idx, cast_key.key_data().idx);
    assert_eq!(inner.data().generation, cast_key.key_data().generation);
}

#[test]
fn insert_with_key_reference_is_stable() {
    let map: CastMap = CastMap::new();
    let key = map.insert(Box::new(1i32) as Box<dyn Any>);
    let ref1 = map.get(key).unwrap();
    let ref1_ptr = ref1 as *const dyn Any;
    for i in 0..100 {
        map.insert(Box::new(i) as Box<dyn Any>);
    }
    let ref1_again = unsafe { &*ref1_ptr };
    assert_eq!(*ref1_again.downcast_ref::<i32>().unwrap(), 1);
}

// ─── try_insert_with_key ───────────────────────────────────────────────────

#[test]
fn try_insert_with_key_ok() {
    let map: CastMap = CastMap::new();
    let result = map.try_insert_with_key::<()>(|_| Ok(Box::new(99i32) as Box<dyn Any>));
    assert!(result.is_ok());
    assert_eq!(map.len(), 1);
}

#[test]
fn try_insert_with_key_err_does_not_insert() {
    let map: CastMap = CastMap::new();
    let result = map.try_insert_with_key::<&str>(|_| Err("fail"));
    assert!(result.is_err());
    assert_eq!(map.len(), 0);
}

#[test]
fn try_insert_with_key_err_slot_is_reusable() {
    let map: CastMap = CastMap::new();
    let _ = map.try_insert_with_key::<&str>(|_| Err("fail"));
    let key = map.insert(Box::new(42i32) as Box<dyn Any>);
    let val = map.get(key).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
    assert_eq!(map.len(), 1);
}

// ─── insert_sized ──────────────────────────────────────────────────────────

#[test]
fn insert_sized_returns_concrete_key_and_ref() {
    let map: CastMap = CastMap::new();
    let dog_key = map.insert_sized(Box::new(Dog { name: "Rex".into() }));
    let dog_ref = map.get(dog_key).unwrap();
    assert_eq!(dog_ref.name, "Rex");
    let dog: &Dog = map.get(dog_key).unwrap();
    assert_eq!(dog.name, "Rex");
}

#[test]
fn insert_sized_key_can_upcast_to_dyn_any() {
    let map: CastMap = CastMap::new();
    let dog_key = map.insert_sized(Box::new(Dog { name: "Rex".into() }));
    let dyn_key = dog_key.upcast::<dyn Any>();
    let val = map.get(dyn_key).unwrap();
    assert_eq!(
        val.downcast_ref::<Dog>().unwrap(),
        &Dog { name: "Rex".into() }
    );
}

#[test]
fn insert_sized_with_key_receives_typed_key() {
    let map: CastMap = CastMap::new();
    let dog_key = map.insert_sized_with_key(|key: StableCastKey<Dog>| {
        let _ = key;
        Box::new(Dog { name: "Rex".into() })
    });
    let dog_ref = map.get(dog_key).unwrap();
    assert_eq!(dog_ref.name, "Rex");
    assert_eq!(map.get(dog_key).unwrap().name, "Rex");
}

#[test]
fn try_insert_sized_with_key_err_does_not_insert() {
    let map: CastMap = CastMap::new();
    let result: Result<_, &str> =
        map.try_insert_sized_with_key(|_: StableCastKey<Dog>| Err::<Box<Dog>, &str>("fail"));
    assert!(result.is_err());
    assert_eq!(map.len(), 0);
}

// ─── inner-key access ──────────────────────────────────────────────────────

#[test]
fn get_by_inner_key() {
    let map: CastMap = CastMap::new();
    let key = map.insert(Box::new(42i32) as Box<dyn Any>);
    let inner = key.inner_key();
    let val = map.get_by_inner_key(inner).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
}

#[test]
fn get_by_inner_key_mut() {
    let mut map: CastMap = CastMap::new();
    let key = map.insert(Box::new(Dog { name: "Old".into() }) as Box<dyn Any>);
    let inner = key.inner_key();
    let val = map.get_by_inner_key_mut(inner).unwrap();
    val.downcast_mut::<Dog>().unwrap().name = "New".into();
    assert_eq!(
        map.get_by_inner_key(inner)
            .unwrap()
            .downcast_ref::<Dog>()
            .unwrap()
            .name,
        "New"
    );
}

#[test]
fn remove_by_inner_key() {
    let mut map: CastMap = CastMap::new();
    let key = map.insert(Box::new(77i32) as Box<dyn Any>);
    let inner = key.inner_key();
    let removed = map.remove_by_inner_key(inner).unwrap();
    assert_eq!(*removed.downcast_ref::<i32>().unwrap(), 77);
    assert_eq!(map.len(), 0);
}

// ─── cast_key_of ───────────────────────────────────────────────────────────

#[test]
fn cast_key_of_returns_same_as_insert() {
    let map: CastMap = CastMap::new();
    let cast_key = map.insert(Box::new(42i32) as Box<dyn Any>);
    let inner = cast_key.inner_key();
    let recovered = map.cast_key_of(inner).unwrap();
    assert_eq!(recovered, cast_key);
}

#[test]
fn cast_key_of_stale_returns_none() {
    let mut map: CastMap = CastMap::new();
    let key = map.insert(Box::new(42i32) as Box<dyn Any>);
    let inner = key.inner_key();
    map.remove(key);
    assert!(map.cast_key_of(inner).is_none());
}

// ─── Index / IndexMut ──────────────────────────────────────────────────────

#[test]
fn index_operator_works() {
    let map: CastMap = CastMap::new();
    let key = map.insert(Box::new(42i32) as Box<dyn Any>);
    let val = &map[key];
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
}

#[test]
#[should_panic]
fn index_panics_on_invalid_key() {
    let map: CastMap = CastMap::new();
    let other: CastMap = CastMap::new();
    let key = other.insert(Box::new(42i32) as Box<dyn Any>);
    let _ = &map[key];
}

// ─── retain ────────────────────────────────────────────────────────────────

#[test]
fn retain_keeps_matching_removes_rest() {
    let mut map: CastMap = CastMap::new();
    let k1 = map.insert(Box::new(1i32) as Box<dyn Any>);
    let k2 = map.insert(Box::new(2i32) as Box<dyn Any>);
    let k3 = map.insert(Box::new(3i32) as Box<dyn Any>);
    map.retain(|_, val| {
        let v = *val.downcast_ref::<i32>().unwrap();
        v % 2 != 0
    });
    assert_eq!(map.len(), 2);
    assert!(map.get(k1).is_some());
    assert!(map.get(k2).is_none());
    assert!(map.get(k3).is_some());
}

// ─── snapshot ──────────────────────────────────────────────────────────────

#[test]
fn snapshot_returns_all_elements_with_valid_keys() {
    let map: CastMap = CastMap::new();
    map.insert(Box::new(1i32) as Box<dyn Any>);
    map.insert(Box::new(2i32) as Box<dyn Any>);
    map.insert(Box::new(3i32) as Box<dyn Any>);
    let snap = map.snapshot();
    assert_eq!(snap.len(), 3);
    for (key, _) in &snap {
        assert!(map.get(*key).is_some());
    }
}

#[test]
fn snapshot_keys_can_be_used_for_lookup() {
    let map: CastMap = CastMap::new();
    map.insert(Box::new(10i32) as Box<dyn Any>);
    map.insert(Box::new(20i32) as Box<dyn Any>);
    let keys = map.snapshot_keys();
    assert_eq!(keys.len(), 2);
    for key in keys {
        assert!(map.get(key).is_some());
    }
}

#[test]
fn snapshot_refs_returns_correct_count() {
    let map: CastMap = CastMap::new();
    map.insert(Box::new(1i32) as Box<dyn Any>);
    map.insert(Box::new(2i32) as Box<dyn Any>);
    assert_eq!(map.snapshot_refs().len(), 2);
}

// ─── iter_mut ──────────────────────────────────────────────────────────────

#[test]
fn iter_mut_can_modify_values() {
    let mut map: CastMap = CastMap::new();
    map.insert(Box::new(Dog { name: "A".into() }) as Box<dyn Any>);
    map.insert(Box::new(Dog { name: "B".into() }) as Box<dyn Any>);
    for (_, val) in map.iter_mut() {
        val.downcast_mut::<Dog>().unwrap().name = "Modified".into();
    }
    let snap = map.snapshot_refs();
    for val in snap {
        assert_eq!(val.downcast_ref::<Dog>().unwrap().name, "Modified");
    }
}

#[test]
fn iter_mut_keys_are_valid() {
    let mut map: CastMap = CastMap::new();
    map.insert(Box::new(1i32) as Box<dyn Any>);
    map.insert(Box::new(2i32) as Box<dyn Any>);
    let keys: Vec<_> = map.iter_mut().map(|(k, _)| k).collect();
    for key in keys {
        assert!(map.get(key).is_some());
    }
}

// ─── drain ─────────────────────────────────────────────────────────────────

#[test]
fn drain_yields_all_and_empties_map() {
    let mut map: CastMap = CastMap::new();
    map.insert(Box::new(10i32) as Box<dyn Any>);
    map.insert(Box::new(20i32) as Box<dyn Any>);
    let drained: Vec<_> = map.drain().collect();
    assert_eq!(drained.len(), 2);
    assert_eq!(map.len(), 0);
}

#[test]
fn drain_keys_have_correct_map_id() {
    let mut map: CastMap = CastMap::new();
    let existing = map.insert(Box::new(1i32) as Box<dyn Any>);
    let expected_map_id = existing.map_id();
    let drained: Vec<_> = map.drain().collect();
    for (key, _) in &drained {
        assert_eq!(key.map_id(), expected_map_id);
    }
}

// ─── into_iter ─────────────────────────────────────────────────────────────

#[test]
fn into_iter_consumes_map() {
    let map: CastMap = CastMap::new();
    map.insert(Box::new(1i32) as Box<dyn Any>);
    map.insert(Box::new(2i32) as Box<dyn Any>);
    let collected: Vec<_> = map.into_iter().collect();
    assert_eq!(collected.len(), 2);
}

// ─── Clone ─────────────────────────────────────────────────────────────────

type RcMap = StableCastMap<DerefSlot<DefaultKey, std::rc::Rc<dyn Any>>>;

#[test]
fn clone_produces_independent_map() {
    let map: RcMap = RcMap::new();
    let key = map.insert(std::rc::Rc::new(42i32) as std::rc::Rc<dyn Any>);
    let cloned = map.clone();
    // old key does NOT work on clone (fresh map id)
    assert!(cloned.get(key).is_none());
    assert_eq!(cloned.len(), map.len());
    let snap = cloned.snapshot();
    assert_eq!(snap.len(), 1);
    assert_eq!(*snap[0].1.downcast_ref::<i32>().unwrap(), 42);
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
fn clone_new_keys_work_on_clone_only() {
    let map: RcMap = RcMap::new();
    map.insert(std::rc::Rc::new(1i32) as std::rc::Rc<dyn Any>);
    let cloned = map.clone();
    let new_key = cloned.insert(std::rc::Rc::new(99i32) as std::rc::Rc<dyn Any>);
    assert!(cloned.get(new_key).is_some());
    assert!(map.get(new_key).is_none());
}

#[test]
fn clone_original_keys_do_not_work_on_clone() {
    let map: RcMap = RcMap::new();
    let key = map.insert(std::rc::Rc::new(42i32) as std::rc::Rc<dyn Any>);
    let cloned = map.clone();
    assert!(cloned.get(key).is_none());
}

#[test]
fn clone_remove_on_clone_does_not_affect_original() {
    let map: RcMap = RcMap::new();
    map.insert(std::rc::Rc::new(42i32) as std::rc::Rc<dyn Any>);
    let mut cloned = map.clone();
    let clone_keys = cloned.snapshot_keys();
    for k in clone_keys {
        cloned.remove(k);
    }
    assert_eq!(cloned.len(), 0);
    assert_eq!(map.len(), 1);
}

// ─── Pointer stability ────────────────────────────────────────────────────

#[test]
fn references_stable_across_inserts() {
    let map: CastMap = CastMap::new();
    let key = map.insert(Box::new(1i32) as Box<dyn Any>);
    let r1 = map.get(key).unwrap();
    let r1_ptr = r1 as *const dyn Any;
    for i in 0..50 {
        map.insert(Box::new(i) as Box<dyn Any>);
    }
    let r1_check = unsafe { &*r1_ptr };
    assert_eq!(*r1_check.downcast_ref::<i32>().unwrap(), 1);
}

// ─── insert_as ─────────────────────────────────────────────────────────────

trait Animal: Any {
    fn speak(&self) -> &str;
}

impl Animal for Dog {
    fn speak(&self) -> &str {
        "woof"
    }
}

impl Animal for Cat {
    fn speak(&self) -> &str {
        "meow"
    }
}

#[test]
fn insert_as_returns_typed_key_and_ref() {
    type AnimalMap = StableBoxCastMap<DefaultKey, dyn Any>;
    let map: AnimalMap = AnimalMap::new();
    let dog: Box<dyn Animal> = Box::new(Dog { name: "Rex".into() });
    let animal_key = map.insert_as(dog);
    let animal_ref = map.get(animal_key).unwrap();
    assert_eq!(animal_ref.speak(), "woof");
    let fetched: &dyn Animal = map.get(animal_key).unwrap();
    assert_eq!(fetched.speak(), "woof");
}

// ─── get_by_index_only ─────────────────────────────────────────────────────

#[test]
fn get_by_index_only_returns_occupied() {
    let map: CastMap = CastMap::new();
    let key = map.insert(Box::new(42i32) as Box<dyn Any>);
    let idx = key.key_data().idx;
    let (found_key, val) = map.get_by_index_only(idx).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
    assert_eq!(found_key, key);
}

#[test]
fn get_by_index_only_returns_none_for_vacant() {
    let mut map: CastMap = CastMap::new();
    let key = map.insert(Box::new(42i32) as Box<dyn Any>);
    map.remove(key);
    assert!(map.get_by_index_only(key.key_data().idx).is_none());
}

// ─── with_capacity / reserve ───────────────────────────────────────────────

#[test]
fn with_capacity_preallocates() {
    let map: CastMap = CastMap::with_capacity(100);
    assert!(map.capacity() >= 100);
    assert_eq!(map.len(), 0);
}

#[test]
fn reserve_increases_capacity() {
    let map: CastMap = CastMap::new();
    map.reserve(50);
    assert!(map.capacity() >= 50);
}

// ─── Empty map edge cases ──────────────────────────────────────────────────

#[test]
fn get_on_empty_map_returns_none() {
    let map_a: CastMap = CastMap::new();
    let map_b: CastMap = CastMap::new();
    let key = map_b.insert(Box::new(1i32) as Box<dyn Any>);
    assert!(map_a.get(key).is_none());
}

#[test]
fn drain_empty_map() {
    let mut map: CastMap = CastMap::new();
    let drained: Vec<_> = map.drain().collect();
    assert!(drained.is_empty());
}

#[test]
fn into_iter_empty_map() {
    let map: CastMap = CastMap::new();
    let collected: Vec<_> = map.into_iter().collect();
    assert!(collected.is_empty());
}

#[test]
fn snapshot_empty_map() {
    let map: CastMap = CastMap::new();
    assert!(map.snapshot().is_empty());
    assert!(map.snapshot_keys().is_empty());
    assert!(map.snapshot_refs().is_empty());
}

// ─── Slot reuse ────────────────────────────────────────────────────────────

#[test]
fn insert_after_remove_reuses_slot() {
    let mut map: CastMap = CastMap::new();
    let k1 = map.insert(Box::new(1i32) as Box<dyn Any>);
    let idx1 = k1.key_data().idx;
    map.remove(k1);
    let k2 = map.insert(Box::new(2i32) as Box<dyn Any>);
    let idx2 = k2.key_data().idx;
    assert_eq!(idx1, idx2);
    assert_ne!(k1, k2);
    assert!(map.get(k1).is_none());
    assert!(map.get(k2).is_some());
}

// ─── map_id ───────────────────────────────────────────────────────────────

#[test]
fn map_id_accessible() {
    let map: CastMap = CastMap::new();
    let _ = map.map_id();
}

#[test]
fn two_maps_have_different_ids() {
    let a: CastMap = CastMap::new();
    let b: CastMap = CastMap::new();
    assert_ne!(a.map_id(), b.map_id());
}

#[test]
fn clone_gets_fresh_map_id() {
    let map: RcMap = RcMap::new();
    map.insert(std::rc::Rc::new(1i32) as std::rc::Rc<dyn Any>);
    let cloned = map.clone();
    assert_ne!(map.map_id(), cloned.map_id());
}

// ─── upcast key used for get / remove ──────────────────────────────────────

#[test]
fn upcast_key_works_for_get() {
    let map: CastMap = CastMap::new();
    let sized_key = map.insert_sized(Box::new(Dog { name: "Rex".into() }));
    let dyn_key = sized_key.upcast::<dyn Any>();
    let val = map.get(dyn_key).unwrap();
    assert_eq!(val.downcast_ref::<Dog>().unwrap().name, "Rex");
}

#[test]
fn upcast_key_works_for_remove() {
    let mut map: CastMap = CastMap::new();
    let sized_key = map.insert_sized(Box::new(Dog { name: "Rex".into() }));
    let dyn_key = sized_key.upcast::<dyn Any>();
    let removed = map.remove(dyn_key).unwrap();
    assert_eq!(removed.downcast_ref::<Dog>().unwrap().name, "Rex");
}

#[test]
fn upcast_key_works_for_get_mut() {
    let mut map: CastMap = CastMap::new();
    let sized_key = map.insert_sized(Box::new(Dog { name: "Old".into() }));
    let dyn_key = sized_key.upcast::<dyn Any>();
    map.get_mut(dyn_key)
        .unwrap()
        .downcast_mut::<Dog>()
        .unwrap()
        .name = "New".into();
    assert_eq!(map.get(sized_key).unwrap().name, "New");
}

// ─── cross-map with upcast keys ────────────────────────────────────────────

#[test]
fn upcast_key_from_different_map_returns_none() {
    let map_a: CastMap = CastMap::new();
    let map_b: CastMap = CastMap::new();
    let sized_key = map_a.insert_sized(Box::new(42i32));
    let dyn_key = sized_key.upcast::<dyn Any>();
    let _ = map_b.insert(Box::new(99i32) as Box<dyn Any>);
    assert!(map_b.get(dyn_key).is_none());
}
