use crate::slots::boxed_slot::StableGenMap;
use crate::keys::key::DefaultKey;
use crate::keys::key::Key;

// ─── get_unchecked ──────────────────────────────────────────────────────────

#[test]
fn get_unchecked_returns_correct_value() {
    let map: StableGenMap<DefaultKey, i32> = StableGenMap::new();
    let k1 = map.insert(10);
    let k2 = map.insert(20);
    let k3 = map.insert(30);

    unsafe {
        assert_eq!(*map.get_unchecked(k1), 10);
        assert_eq!(*map.get_unchecked(k2), 20);
        assert_eq!(*map.get_unchecked(k3), 30);
    }
}

#[test]
fn get_unchecked_agrees_with_get() {
    let map: StableGenMap<DefaultKey, String> = StableGenMap::new();
    let mut keys = Vec::new();
    for i in 0..100 {
        let k = map.insert(format!("item_{i}"));
        keys.push(k);
    }

    for (i, &k) in keys.iter().enumerate() {
        let checked = map.get(k).unwrap();
        let unchecked = unsafe { map.get_unchecked(k) };
        assert_eq!(checked, unchecked);
        assert_eq!(unchecked, &format!("item_{i}"));
    }
}

#[test]
fn get_unchecked_after_remove_and_reinsert() {
    let mut map: StableGenMap<DefaultKey, i32> = StableGenMap::new();
    let k1 = map.insert(100);
    let k2 = map.insert(200);

    map.remove(k1);
    let k3 = map.insert(300);

    unsafe {
        assert_eq!(*map.get_unchecked(k2), 200);
        assert_eq!(*map.get_unchecked(k3), 300);
    }
}

// ─── get_unchecked_mut ──────────────────────────────────────────────────────

#[test]
fn get_unchecked_mut_returns_mutable_ref() {
    let mut map: StableGenMap<DefaultKey, i32> = StableGenMap::new();
    let k = map.insert(42);

    unsafe {
        *map.get_unchecked_mut(k) = 99;
    }
    assert_eq!(*map.get(k).unwrap(), 99);
}

#[test]
fn get_unchecked_mut_multiple_keys() {
    let mut map: StableGenMap<DefaultKey, String> = StableGenMap::new();
    let k1 = map.insert("hello".to_string());
    let k2 = map.insert("world".to_string());

    unsafe {
        map.get_unchecked_mut(k1).push_str("!");
        map.get_unchecked_mut(k2).push_str("?");
    }

    assert_eq!(map.get(k1).unwrap(), "hello!");
    assert_eq!(map.get(k2).unwrap(), "world?");
}

// ─── get_slot_as_cell ───────────────────────────────────────────────────────

#[test]
fn get_slot_as_cell_returns_cell() {
    let map: StableGenMap<DefaultKey, i32> = StableGenMap::new();
    let k = map.insert(42);
    let idx = k.data().idx;

    unsafe {
        let cell = map.get_slot_as_cell(idx).unwrap();
        let slot = &*cell.get();
        assert_eq!(*slot.generation() % 2, 1);
        assert_eq!(*slot.ref_output(), 42);
    }
}

#[test]
fn get_slot_as_cell_none_for_out_of_bounds() {
    let map: StableGenMap<DefaultKey, i32> = StableGenMap::new();
    let _ = map.insert(42);

    unsafe {
        assert!(map.get_slot_as_cell(999u32).is_none());
    }
}

#[test]
fn get_slot_as_cell_unchecked_matches() {
    let map: StableGenMap<DefaultKey, i32> = StableGenMap::new();
    let k = map.insert(77);
    let idx = k.data().idx;

    unsafe {
        let cell_checked = map.get_slot_as_cell(idx).unwrap();
        let cell_unchecked = map.get_slot_as_cell_unchecked(idx);
        let slot_a = &*cell_checked.get();
        let slot_b = &*cell_unchecked.get();
        assert_eq!(*slot_a.generation(), *slot_b.generation());
        assert_eq!(*slot_a.ref_output(), *slot_b.ref_output());
    }
}

// ─── get_slot_mut ───────────────────────────────────────────────────────────

#[test]
fn get_slot_mut_can_modify_value() {
    let mut map: StableGenMap<DefaultKey, i32> = StableGenMap::new();
    let k = map.insert(42);
    let idx = k.data().idx;

    unsafe {
        let slot = map.get_slot_mut(idx).unwrap();
        *slot.mut_output() = 99;
    }
    assert_eq!(*map.get(k).unwrap(), 99);
}

#[test]
fn get_slot_mut_none_for_out_of_bounds() {
    let mut map: StableGenMap<DefaultKey, i32> = StableGenMap::new();
    let _ = map.insert(42);

    unsafe {
        assert!(map.get_slot_mut(999u32).is_none());
    }
}

#[test]
fn get_slot_unchecked_mut_can_modify_value() {
    let mut map: StableGenMap<DefaultKey, i32> = StableGenMap::new();
    let k = map.insert(42);
    let idx = k.data().idx;

    unsafe {
        let slot = map.get_slot_unchecked_mut(idx);
        *slot.mut_output() = 123;
    }
    assert_eq!(*map.get(k).unwrap(), 123);
}

// ─── Slot::storage / Slot::storage_mut ────────────────────────────────────────────

#[test]
fn slot_storage_returns_slot_storage_ref() {
    let map: StableGenMap<DefaultKey, i32> = StableGenMap::new();
    let k = map.insert(55);
    let idx = k.data().idx;

    unsafe {
        let cell = map.get_slot_as_cell(idx).unwrap();
        let slot = &*cell.get();
        // item() returns &BoxedSlot, ref_output() on item gives us the value
        let _item = slot.storage();
    }
}

#[test]
fn slot_generation_mut_can_be_read() {
    let mut map: StableGenMap<DefaultKey, i32> = StableGenMap::new();
    let k = map.insert(55);
    let idx = k.data().idx;

    unsafe {
        let slot = map.get_slot_mut(idx).unwrap();
        let gen = *slot.generation();
        let gen_mut = *slot.generation_mut();
        assert_eq!(gen, gen_mut);
    }
}

// ─── get_unchecked with StableDerefMap ───────────────────────────────────────

#[test]
fn get_unchecked_works_with_deref_map() {
    use crate::slots::deref_slot::BoxStableDerefMap;

    let map: BoxStableDerefMap<DefaultKey, String> = BoxStableDerefMap::new();
    let k = map.insert(Box::new("hello".to_string()));

    unsafe {
        assert_eq!(map.get_unchecked(k), "hello");
    }
}

#[test]
fn get_unchecked_mut_works_with_deref_map() {
    use crate::slots::deref_slot::BoxStableDerefMap;

    let mut map: BoxStableDerefMap<DefaultKey, String> = BoxStableDerefMap::new();
    let k = map.insert(Box::new("hello".to_string()));

    unsafe {
        map.get_unchecked_mut(k).push_str(" world");
    }
    assert_eq!(map.get(k).unwrap(), "hello world");
}

#[test]
fn get_slot_mut_on_deref_map() {
    use crate::slots::deref_slot::BoxStableDerefMap;

    let mut map: BoxStableDerefMap<DefaultKey, i32> = BoxStableDerefMap::new();
    let k = map.insert(Box::new(77));
    let idx = k.data().idx;

    unsafe {
        let slot = map.get_slot_mut(idx).unwrap();
        *slot.mut_output() = 88;
    }
    assert_eq!(*map.get(k).unwrap(), 88);
}
