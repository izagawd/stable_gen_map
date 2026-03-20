use crate::key::Key;
use crate::stable_gen_map::StableGenMap;
use std::any::TypeId;
use std::collections::HashSet;

// Default form: u32/u32
crate::new_key_type! {
    struct TestKey;
}

// Custom idx/gen types
crate::new_key_type! {
    struct SmallKey(u16, u16);
}

// Multiple keys in one invocation
crate::new_key_type! {
    struct KeyA;
    struct KeyB;
}

// Public visibility
crate::new_key_type! {
    pub struct PubKey;
}

// Custom types with pub visibility
crate::new_key_type! {
    pub struct PubSmallKey(u16, u16);
}

#[test]
fn default_key_type_has_correct_assoc_types() {
    assert_eq!(TypeId::of::<<TestKey as Key>::Idx>(), TypeId::of::<u32>());
    assert_eq!(TypeId::of::<<TestKey as Key>::Gen>(), TypeId::of::<u32>());

    let map = StableGenMap::<TestKey, i32>::new();
    let (k, _) = map.insert(42);
    let data = k.data();
    let k2 = TestKey::from(data);
    assert_eq!(k, k2);
}

#[test]
fn custom_key_type_has_correct_assoc_types() {
    assert_eq!(TypeId::of::<<SmallKey as Key>::Idx>(), TypeId::of::<u16>());
    assert_eq!(TypeId::of::<<SmallKey as Key>::Gen>(), TypeId::of::<u16>());

    let map = StableGenMap::<SmallKey, &str>::new();
    let (k, v) = map.insert("hello");
    assert_eq!(*v, "hello");
    assert_eq!(*map.get(k).unwrap(), "hello");

    let data = k.data();
    let k2 = SmallKey::from(data);
    assert_eq!(k, k2);
}

#[test]
fn multiple_keys_in_one_invocation() {
    assert_eq!(TypeId::of::<<KeyA as Key>::Idx>(), TypeId::of::<u32>());
    assert_eq!(TypeId::of::<<KeyB as Key>::Idx>(), TypeId::of::<u32>());

    let map_a = StableGenMap::<KeyA, i32>::new();
    let map_b = StableGenMap::<KeyB, i32>::new();

    let (ka, _) = map_a.insert(1);
    let (kb, _) = map_b.insert(2);

    assert_eq!(map_a[ka], 1);
    assert_eq!(map_b[kb], 2);
}

#[test]
fn pub_small_key_has_correct_assoc_types() {
    assert_eq!(TypeId::of::<<PubSmallKey as Key>::Idx>(), TypeId::of::<u16>());
    assert_eq!(TypeId::of::<<PubSmallKey as Key>::Gen>(), TypeId::of::<u16>());
}

#[test]
fn macro_key_is_copy_clone_debug_eq_hash() {
    let map = StableGenMap::<TestKey, i32>::new();
    let (k, _) = map.insert(10);

    // Copy
    let k2 = k;
    assert_eq!(k, k2);

    // Clone
    let k3 = k.clone();
    assert_eq!(k, k3);

    // Debug
    let _debug = format!("{:?}", k);

    // Hash - insert into HashSet
    let mut set = HashSet::new();
    set.insert(k);
    assert!(set.contains(&k));
}

#[test]
fn insert_remove_with_macro_key() {
    let mut map = StableGenMap::<TestKey, String>::new();
    let (k1, _) = map.insert("one".to_string());
    let (k2, _) = map.insert("two".to_string());
    let (k3, _) = map.insert("three".to_string());

    assert_eq!(map.len(), 3);
    assert_eq!(map.remove(k2), Some("two".to_string()));
    assert_eq!(map.len(), 2);
    assert!(map.get(k2).is_none());
    assert_eq!(map[k1], "one");
    assert_eq!(map[k3], "three");
}

#[test]
fn insert_remove_with_small_key() {
    let mut map = StableGenMap::<SmallKey, i32>::new();
    let (k1, _) = map.insert(100);
    let (k2, _) = map.insert(200);

    assert_eq!(map.remove(k1), Some(100));
    assert_eq!(map.len(), 1);

    // Slot reuse after remove
    let (k3, v3) = map.insert(300);
    assert_eq!(*v3, 300);
    assert_eq!(map.len(), 2);

    // Old key should be stale
    assert!(map.get(k1).is_none());
    assert_eq!(map[k2], 200);
    assert_eq!(map[k3], 300);
}

#[test]
fn stale_key_returns_none() {
    let mut map = StableGenMap::<TestKey, i32>::new();
    let (k, _) = map.insert(1);
    map.remove(k);

    assert!(map.get(k).is_none());
}

#[test]
fn snapshot_with_macro_key() {
    let map = StableGenMap::<TestKey, i32>::new();
    map.insert(10);
    map.insert(20);
    map.insert(30);

    let snap = map.snapshot();
    assert_eq!(snap.len(), 3);
    let values: Vec<i32> = snap.iter().map(|(_, v)| **v).collect();
    assert!(values.contains(&10));
    assert!(values.contains(&20));
    assert!(values.contains(&30));
}