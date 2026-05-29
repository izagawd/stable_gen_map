use crate::cast_key::StableCastKey;
use crate::key::DefaultKey;
use crate::stable_cast_map::StableBoxCastMap;
use crate::unsafe_cast_map::UnsafeBoxCastMap;
use std::any::Any;

type SafeMap = StableBoxCastMap<DefaultKey, dyn Any>;
type UnsafeMap = UnsafeBoxCastMap<DefaultKey, dyn Any>;

#[derive(Debug, PartialEq)]
struct Dog {
    name: String,
}

#[derive(Debug, PartialEq)]
struct Cat {
    name: String,
}

// ─── UnsafeCastMap::get_unchecked ───────────────────────────────────────────

#[test]
fn unsafe_cast_map_get_unchecked_dyn_any() {
    let map: UnsafeMap = UnsafeMap::new();
    let key = map.insert(Box::new(42i32) as Box<dyn Any>);

    unsafe {
        let val = map.get_unchecked(key);
        assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
    }
}

#[test]
fn unsafe_cast_map_get_unchecked_with_concrete_key() {
    let map: UnsafeMap = UnsafeMap::new();
    let dog_key = map.insert_sized(Box::new(Dog { name: "Rex".into() }));

    unsafe {
        let dog: &Dog = map.get_unchecked(dog_key);
        assert_eq!(dog.name, "Rex");
    }
}

#[test]
fn unsafe_cast_map_get_unchecked_multiple_types() {
    let map: UnsafeMap = UnsafeMap::new();
    let k1 = map.insert_sized(Box::new(Dog { name: "Rex".into() }));
    let k2 = map.insert_sized(Box::new(Cat {
        name: "Whiskers".into(),
    }));
    let k3 = map.insert_sized(Box::new(100u64));

    unsafe {
        assert_eq!(map.get_unchecked(k1).name, "Rex");
        assert_eq!(map.get_unchecked(k2).name, "Whiskers");
        assert_eq!(*map.get_unchecked(k3), 100u64);
    }
}

#[test]
fn unsafe_cast_map_get_unchecked_agrees_with_get() {
    let map: UnsafeMap = UnsafeMap::new();
    let key = map.insert_sized(Box::new(Dog {
        name: "Buddy".into(),
    }));

    unsafe {
        let checked = map.get(key).unwrap();
        let unchecked: &Dog = map.get_unchecked(key);
        assert_eq!(checked, unchecked);
    }
}

// ─── UnsafeCastMap::get_unchecked_mut ───────────────────────────────────────

#[test]
fn unsafe_cast_map_get_unchecked_mut_modifies_value() {
    let mut map: UnsafeMap = UnsafeMap::new();
    let key = map.insert_sized(Box::new(Dog { name: "Rex".into() }));

    unsafe {
        let dog: &mut Dog = map.get_unchecked_mut(key);
        dog.name = "Max".into();
    }

    unsafe {
        let dog: &Dog = map.get(key).unwrap();
        assert_eq!(dog.name, "Max");
    }
}

#[test]
fn unsafe_cast_map_get_unchecked_mut_dyn_any() {
    let mut map: UnsafeMap = UnsafeMap::new();
    let key = map.insert(Box::new(10i32) as Box<dyn Any>);

    unsafe {
        let val = map.get_unchecked_mut(key);
        *val.downcast_mut::<i32>().unwrap() = 999;
    }

    unsafe {
        let val = map.get(key).unwrap();
        assert_eq!(*val.downcast_ref::<i32>().unwrap(), 999);
    }
}

// ─── UnsafeCastMap::get_slot / get_slot_unchecked ───────────────────────────

#[test]
fn unsafe_cast_map_get_slot_returns_occupied() {
    let map: UnsafeMap = UnsafeMap::new();
    let key = map.insert_sized(Box::new(Dog { name: "Rex".into() }));
    let idx = key.key_data().idx;

    unsafe {
        let slot = map.get_slot(idx).unwrap();
        assert_eq!(*slot.generation() % 2, 1);
        let val: &dyn Any = slot.ref_output();
        assert_eq!(val.downcast_ref::<Dog>().unwrap().name, "Rex");
    }
}

#[test]
fn unsafe_cast_map_get_slot_none_for_out_of_bounds() {
    let map: UnsafeMap = UnsafeMap::new();
    let _ = map.insert(Box::new(42i32) as Box<dyn Any>);

    unsafe {
        assert!(map.get_slot(999u32).is_none());
    }
}

#[test]
fn unsafe_cast_map_get_slot_vacant_after_remove() {
    let mut map: UnsafeMap = UnsafeMap::new();
    let key = map.insert(Box::new(42i32) as Box<dyn Any>);
    let idx = key.key_data().idx;
    unsafe { map.remove(key) };

    unsafe {
        let slot = map.get_slot(idx).unwrap();
        assert_eq!(*slot.generation() % 2, 0);
    }
}

#[test]
fn unsafe_cast_map_get_slot_unchecked_matches_get_slot() {
    let map: UnsafeMap = UnsafeMap::new();
    let key = map.insert_sized(Box::new(Cat {
        name: "Whiskers".into(),
    }));
    let idx = key.key_data().idx;

    unsafe {
        let checked = map.get_slot(idx).unwrap();
        let unchecked = map.get_slot_unchecked(idx);
        assert_eq!(*checked.generation(), *unchecked.generation());
    }
}

// ─── UnsafeCastMap::get_slot_as_cell ────────────────────────────────────────

#[test]
fn unsafe_cast_map_get_slot_as_cell() {
    let map: UnsafeMap = UnsafeMap::new();
    let key = map.insert(Box::new(42i32) as Box<dyn Any>);
    let idx = key.key_data().idx;

    unsafe {
        let cell = map.get_slot_as_cell(idx).unwrap();
        let slot = &*cell.get();
        assert_eq!(*slot.generation() % 2, 1);
    }
}

#[test]
fn unsafe_cast_map_get_slot_as_cell_unchecked() {
    let map: UnsafeMap = UnsafeMap::new();
    let key = map.insert(Box::new(42i32) as Box<dyn Any>);
    let idx = key.key_data().idx;

    unsafe {
        let cell = map.get_slot_as_cell_unchecked(idx);
        let slot = &*cell.get();
        assert_eq!(*slot.generation() % 2, 1);
    }
}

// ─── UnsafeCastMap::get_slot_mut ────────────────────────────────────────────

#[test]
fn unsafe_cast_map_get_slot_mut_can_modify() {
    let mut map: UnsafeMap = UnsafeMap::new();
    let key = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);
    let idx = key.key_data().idx;

    unsafe {
        let slot = map.get_slot_mut(idx).unwrap();
        let val: &mut dyn Any = slot.mut_output();
        val.downcast_mut::<Dog>().unwrap().name = "Max".into();
    }

    unsafe {
        assert_eq!(
            map.get(key).unwrap().downcast_ref::<Dog>().unwrap().name,
            "Max"
        );
    }
}

#[test]
fn unsafe_cast_map_get_slot_unchecked_mut_can_modify() {
    let mut map: UnsafeMap = UnsafeMap::new();
    let key = map.insert(Box::new(100i32) as Box<dyn Any>);
    let idx = key.key_data().idx;

    unsafe {
        let slot = map.get_slot_unchecked_mut(idx);
        let val: &mut dyn Any = slot.mut_output();
        *val.downcast_mut::<i32>().unwrap() = 200;
    }

    unsafe {
        assert_eq!(*map.get(key).unwrap().downcast_ref::<i32>().unwrap(), 200);
    }
}

// ─── StableCastMap::get_unchecked ──────────────────────────────────────────

#[test]
fn stable_cast_map_get_unchecked_dyn_any() {
    let map: SafeMap = SafeMap::new();
    let key = map.insert(Box::new(42i32) as Box<dyn Any>);

    unsafe {
        let val = map.get_unchecked(key);
        assert_eq!(*val.downcast_ref::<i32>().unwrap(), 42);
    }
}

#[test]
fn stable_cast_map_get_unchecked_with_concrete_key() {
    let map: SafeMap = SafeMap::new();
    let dyn_key = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);
    let dog_key: StableCastKey<Dog> = map.downcast_key::<Dog>(dyn_key).unwrap();

    unsafe {
        let dog: &Dog = map.get_unchecked(dog_key);
        assert_eq!(dog.name, "Rex");
    }
}

#[test]
fn stable_cast_map_get_unchecked_agrees_with_get() {
    let map: SafeMap = SafeMap::new();

    let mut keys = Vec::new();
    for i in 0..50 {
        let k = map.insert(Box::new(i as i32) as Box<dyn Any>);
        keys.push(k);
    }

    for (i, &k) in keys.iter().enumerate() {
        let checked = map.get(k).unwrap();
        let unchecked = unsafe { map.get_unchecked(k) };
        assert_eq!(
            *checked.downcast_ref::<i32>().unwrap(),
            *unchecked.downcast_ref::<i32>().unwrap()
        );
        assert_eq!(*unchecked.downcast_ref::<i32>().unwrap(), i as i32);
    }
}

// ─── StableCastMap::get_unchecked_mut ──────────────────────────────────────

#[test]
fn stable_cast_map_get_unchecked_mut_modifies_value() {
    let mut map: SafeMap = SafeMap::new();
    let dyn_key = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);
    let dog_key: StableCastKey<Dog> = map.downcast_key::<Dog>(dyn_key).unwrap();

    unsafe {
        let dog: &mut Dog = map.get_unchecked_mut(dog_key);
        dog.name = "Max".into();
    }

    let dog: &Dog = map.get(dog_key).unwrap();
    assert_eq!(dog.name, "Max");
}

#[test]
fn stable_cast_map_get_unchecked_mut_dyn_any() {
    let mut map: SafeMap = SafeMap::new();
    let key = map.insert(Box::new(String::from("hello")) as Box<dyn Any>);

    unsafe {
        let val = map.get_unchecked_mut(key);
        *val.downcast_mut::<String>().unwrap() = "goodbye".into();
    }

    let val = map.get(key).unwrap();
    assert_eq!(val.downcast_ref::<String>().unwrap(), "goodbye");
}

// ─── StableCastMap::get_slot / get_slot_unchecked ──────────────────────────

#[test]
fn stable_cast_map_get_slot_returns_occupied() {
    let map: SafeMap = SafeMap::new();
    let key = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);
    let idx = key.key_data().idx;

    unsafe {
        let slot = map.get_slot(idx).unwrap();
        assert_eq!(*slot.generation() % 2, 1);
        let val: &dyn Any = slot.ref_output();
        assert_eq!(val.downcast_ref::<Dog>().unwrap().name, "Rex");
    }
}

#[test]
fn stable_cast_map_get_slot_none_for_out_of_bounds() {
    let map: SafeMap = SafeMap::new();
    let _ = map.insert(Box::new(42i32) as Box<dyn Any>);

    unsafe {
        assert!(map.get_slot(999u32).is_none());
    }
}

#[test]
fn stable_cast_map_get_slot_unchecked_matches_get_slot() {
    let map: SafeMap = SafeMap::new();
    let key = map.insert(Box::new(100u64) as Box<dyn Any>);
    let idx = key.key_data().idx;

    unsafe {
        let checked = map.get_slot(idx).unwrap();
        let unchecked = map.get_slot_unchecked(idx);
        assert_eq!(*checked.generation(), *unchecked.generation());
    }
}

#[test]
fn stable_cast_map_get_slot_vacant_after_remove() {
    let mut map: SafeMap = SafeMap::new();
    let key = map.insert(Box::new(42i32) as Box<dyn Any>);
    let idx = key.key_data().idx;
    map.remove(key);

    unsafe {
        let slot = map.get_slot(idx).unwrap();
        assert_eq!(*slot.generation() % 2, 0);
    }
}

// ─── StableCastMap::get_slot_as_cell ───────────────────────────────────────

#[test]
fn stable_cast_map_get_slot_as_cell() {
    let map: SafeMap = SafeMap::new();
    let key = map.insert(Box::new(42i32) as Box<dyn Any>);
    let idx = key.key_data().idx;

    unsafe {
        let cell = map.get_slot_as_cell(idx).unwrap();
        let slot = &*cell.get();
        assert_eq!(*slot.generation() % 2, 1);
    }
}

#[test]
fn stable_cast_map_get_slot_as_cell_unchecked() {
    let map: SafeMap = SafeMap::new();
    let key = map.insert(Box::new(42i32) as Box<dyn Any>);
    let idx = key.key_data().idx;

    unsafe {
        let cell = map.get_slot_as_cell_unchecked(idx);
        let slot = &*cell.get();
        assert_eq!(*slot.generation() % 2, 1);
    }
}

// ─── StableCastMap::get_slot_mut ───────────────────────────────────────────

#[test]
fn stable_cast_map_get_slot_mut_can_modify() {
    let mut map: SafeMap = SafeMap::new();
    let key = map.insert(Box::new(Dog { name: "Rex".into() }) as Box<dyn Any>);
    let idx = key.key_data().idx;

    unsafe {
        let slot = map.get_slot_mut(idx).unwrap();
        let val: &mut dyn Any = slot.mut_output();
        val.downcast_mut::<Dog>().unwrap().name = "Max".into();
    }

    let dog = map.get(key).unwrap().downcast_ref::<Dog>().unwrap();
    assert_eq!(dog.name, "Max");
}

#[test]
fn stable_cast_map_get_slot_unchecked_mut_can_modify() {
    let mut map: SafeMap = SafeMap::new();
    let key = map.insert(Box::new(100i32) as Box<dyn Any>);
    let idx = key.key_data().idx;

    unsafe {
        let slot = map.get_slot_unchecked_mut(idx);
        let val: &mut dyn Any = slot.mut_output();
        *val.downcast_mut::<i32>().unwrap() = 200;
    }

    assert_eq!(*map.get(key).unwrap().downcast_ref::<i32>().unwrap(), 200);
}

// ─── StableCastMap::get_unchecked after remove + reinsert ──────────────────

#[test]
fn stable_cast_map_get_unchecked_after_remove_reinsert() {
    let mut map: SafeMap = SafeMap::new();
    let k1 = map.insert(Box::new(100i32) as Box<dyn Any>);
    let k2 = map.insert(Box::new(200i32) as Box<dyn Any>);
    map.remove(k1);
    let k3 = map.insert(Box::new(300i32) as Box<dyn Any>);

    unsafe {
        assert_eq!(*map.get_unchecked(k2).downcast_ref::<i32>().unwrap(), 200);
        assert_eq!(*map.get_unchecked(k3).downcast_ref::<i32>().unwrap(), 300);
    }
}
