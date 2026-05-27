use crate::cast_key::StableCastKey;
use crate::key::DefaultKey;
use crate::stable_cast_map::StableBoxCastMap;

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
fn insert_sized_concrete_key_works_for_get_mut() {
    let mut map: CastMap = CastMap::new();
    let dog_key = map.insert_sized(Box::new(Dog { name: "Old".into() }));
    let dog: &mut Dog = map.get_mut(dog_key).unwrap();
    dog.name = "New".into();
    assert_eq!(map.get(dog_key).unwrap().name, "New");
}

#[test]
fn insert_sized_concrete_key_works_for_remove() {
    let mut map: CastMap = CastMap::new();
    let dog_key = map.insert_sized(Box::new(Dog { name: "Rex".into() }));
    let removed = map.remove(dog_key).unwrap();
    assert_eq!(
        removed.downcast_ref::<Dog>().unwrap(),
        &Dog { name: "Rex".into() }
    );
    assert_eq!(map.len(), 0);
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
fn insert_sized_multiple_types() {
    let map: CastMap = CastMap::new();
    let dk = map.insert_sized(Box::new(Dog { name: "Rex".into() }));
    let ck = map.insert_sized(Box::new(Cat {
        name: "Whiskers".into(),
    }));
    let dog: &Dog = map.get(dk).unwrap();
    let cat: &Cat = map.get(ck).unwrap();
    assert_eq!(dog.name, "Rex");
    assert_eq!(cat.name, "Whiskers");
}

#[test]
fn insert_sized_stale_key_returns_none() {
    let mut map: CastMap = CastMap::new();
    let dog_key = map.insert_sized(Box::new(Dog { name: "Rex".into() }));
    let dyn_key = dog_key.upcast::<dyn Any>();
    map.remove(dyn_key);
    assert!(map.get(dog_key).is_none());
}

#[test]
fn insert_sized_cross_map_key_rejected() {
    let map_a: CastMap = CastMap::new();
    let map_b: CastMap = CastMap::new();
    let dog_key = map_a.insert_sized(Box::new(Dog { name: "Rex".into() }));
    let _ = map_b.insert_sized(Box::new(Dog { name: "Rex".into() }));
    assert!(map_b.get(dog_key).is_none());
}

#[test]
fn insert_sized_inner_key_matches() {
    let map: CastMap = CastMap::new();
    let dog_key = map.insert_sized(Box::new(Dog { name: "Rex".into() }));
    let inner = dog_key.inner_key();
    let val = map.get_by_inner_key(inner).unwrap();
    assert_eq!(
        val.downcast_ref::<Dog>().unwrap(),
        &Dog { name: "Rex".into() }
    );
}

#[test]
fn insert_sized_pointer_stability() {
    let map: CastMap = CastMap::new();
    let tmp_key = map.insert_sized(Box::new(Dog { name: "Rex".into() }));
    let dog_ref = map.get(tmp_key).unwrap();
    let ptr = dog_ref as *const Dog;
    for i in 0..50 {
        map.insert(Box::new(i) as Box<dyn Any>);
    }
    let check = unsafe { &*ptr };
    assert_eq!(check.name, "Rex");
}

// ─── insert_sized_with_key ─────────────────────────────────────────────────

#[test]
fn insert_sized_with_key_closure_receives_typed_key() {
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
fn insert_sized_with_key_stores_own_key() {
    use std::cell::Cell;
    let map: CastMap = CastMap::new();
    let captured = Cell::new(None::<StableCastKey<Dog>>);
    let returned_key = map.insert_sized_with_key(|key: StableCastKey<Dog>| {
        captured.set(Some(key));
        Box::new(Dog { name: "Rex".into() })
    });
    assert_eq!(captured.get().unwrap(), returned_key);
}

#[test]
fn insert_sized_with_key_after_remove_reuses_slot() {
    let mut map: CastMap = CastMap::new();
    let key = map.insert_sized(Box::new(Dog { name: "Old".into() }));
    let old_idx = key.key_data().idx;
    let dyn_key = key.upcast::<dyn Any>();
    map.remove(dyn_key);
    let new_key = map.insert_sized(Box::new(Dog { name: "New".into() }));
    assert_eq!(new_key.key_data().idx, old_idx);
    assert_eq!(map.get(new_key).unwrap().name, "New");
    assert!(map.get(key).is_none());
}

// ─── try_insert_sized_with_key ─────────────────────────────────────────────

#[test]
fn try_insert_sized_with_key_ok() {
    let map: CastMap = CastMap::new();
    let result: Result<_, ()> =
        map.try_insert_sized_with_key(|_: StableCastKey<i32>| Ok(Box::new(42i32)));
    assert!(result.is_ok());
    assert_eq!(map.len(), 1);
}

#[test]
fn try_insert_sized_with_key_err_does_not_insert() {
    let map: CastMap = CastMap::new();
    let result: Result<_, &str> =
        map.try_insert_sized_with_key(|_: StableCastKey<i32>| Err::<Box<_>, &str>("fail"));
    assert!(result.is_err());
    assert_eq!(map.len(), 0);
}

#[test]
fn try_insert_sized_with_key_err_slot_reusable() {
    let map: CastMap = CastMap::new();
    let _: Result<_, &str> =
        map.try_insert_sized_with_key(|_: StableCastKey<i32>| Err::<Box<_>, &str>("fail"));
    let key = map.insert(Box::new(99i32) as Box<dyn Any>);
    let val = map.get(key).unwrap();
    assert_eq!(*val.downcast_ref::<i32>().unwrap(), 99);
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

type AnimalMap = StableBoxCastMap<DefaultKey, dyn Any>;

#[test]
fn insert_as_child_into_parent_map() {
    let map: AnimalMap = AnimalMap::new();
    let child: Box<dyn Animal> = Box::new(Dog { name: "Rex".into() });
    let animal_key = map.insert_as(child);
    let animal_ref = map.get(animal_key).unwrap();
    assert_eq!(animal_ref.speak(), "woof");
    let fetched: &dyn Animal = map.get(animal_key).unwrap();
    assert_eq!(fetched.speak(), "woof");
}

#[test]
fn insert_as_child_key_works_for_get() {
    let map: AnimalMap = AnimalMap::new();
    let child: Box<dyn Animal> = Box::new(Cat {
        name: "Whiskers".into(),
    });
    let animal_key = map.insert_as(child);
    let fetched: &dyn Animal = map.get(animal_key).unwrap();
    assert_eq!(fetched.speak(), "meow");
}

#[test]
fn insert_as_child_key_works_for_remove() {
    let mut map: AnimalMap = AnimalMap::new();
    let child: Box<dyn Animal> = Box::new(Dog { name: "Rex".into() });
    let animal_key = map.insert_as(child);
    assert!(map.remove(animal_key).is_some());
    assert_eq!(map.len(), 0);
}

#[test]
fn insert_as_stale_key_returns_none() {
    let mut map: AnimalMap = AnimalMap::new();
    let child: Box<dyn Animal> = Box::new(Dog { name: "Rex".into() });
    let animal_key = map.insert_as(child);
    map.remove(animal_key);
    assert!(map.get(animal_key).is_none());
}

#[test]
fn insert_as_cross_map_key_rejected() {
    let map_a: AnimalMap = AnimalMap::new();
    let map_b: AnimalMap = AnimalMap::new();
    let child: Box<dyn Animal> = Box::new(Dog { name: "Rex".into() });
    let key_a = map_a.insert_as(child);
    let _ = map_b.insert(Box::new(1i32) as Box<dyn Any>);
    assert!(map_b.get(key_a).is_none());
}

#[test]
fn insert_as_inner_key_matches() {
    let map: AnimalMap = AnimalMap::new();
    let child: Box<dyn Animal> = Box::new(Dog { name: "Rex".into() });
    let animal_key = map.insert_as(child);
    let inner = animal_key.inner_key();
    assert!(map.get_by_inner_key(inner).is_some());
}

#[test]
fn insert_as_pointer_stability() {
    let map: AnimalMap = AnimalMap::new();
    let child: Box<dyn Animal> = Box::new(Dog { name: "Rex".into() });
    let key = map.insert_as(child);
    let animal_ref = map.get(key).unwrap();
    let ptr = animal_ref as *const dyn Animal;
    for i in 0..50 {
        map.insert(Box::new(i) as Box<dyn Any>);
    }
    let check = unsafe { &*ptr };
    assert_eq!(check.speak(), "woof");
}

// ─── insert_as_with_key ────────────────────────────────────────────────────

#[test]
fn insert_as_with_key_closure_receives_inner_key() {
    use std::cell::Cell;
    let map: AnimalMap = AnimalMap::new();
    let captured = Cell::new(None::<DefaultKey>);
    let _ = map.insert_as_with_key(|inner_key: DefaultKey| {
        captured.set(Some(inner_key));
        Box::new(Dog { name: "Rex".into() }) as Box<dyn Animal>
    });
    assert!(captured.get().is_some());
}

#[test]
fn try_insert_as_with_key_ok() {
    let map: AnimalMap = AnimalMap::new();
    let result = map.try_insert_as_with_key::<Box<dyn Animal>, ()>(|_| {
        Ok(Box::new(Dog { name: "Rex".into() }) as Box<dyn Animal>)
    });
    assert!(result.is_ok());
    assert_eq!(map.len(), 1);
}

#[test]
fn try_insert_as_with_key_err_does_not_insert() {
    let map: AnimalMap = AnimalMap::new();
    let result = map.try_insert_as_with_key::<Box<dyn Animal>, &str>(|_| Err("fail"));
    assert!(result.is_err());
    assert_eq!(map.len(), 0);
}

// ─── Mixed insert styles ──────────────────────────────────────────────────

#[test]
fn mixed_insert_and_insert_sized_and_insert_as() {
    let map: AnimalMap = AnimalMap::new();
    let k1 = map.insert(Box::new(1i32) as Box<dyn Any>);
    let k2 = map.insert_sized(Box::new(Dog { name: "Rex".into() }));
    let child: Box<dyn Animal> = Box::new(Cat {
        name: "Whiskers".into(),
    });
    let k3 = map.insert_as(child);
    assert_eq!(map.len(), 3);
    assert!(map.get(k1).is_some());
    assert!(map.get(k2).is_some());
    assert!(map.get(k3).is_some());

    // all keys carry the same map id
    let dyn_k2 = k2.upcast::<dyn Any>();
    assert_eq!(k1.map_id(), dyn_k2.map_id());
    assert_eq!(k1.map_id(), k3.map_id());
}
