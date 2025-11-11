use crate::key::{DefaultKey, Key};
use crate::numeric::Numeric;
use crate::stable_deref_gen_map::{BoxStableDerefGenMap, StableDerefGenMap};

type Map = BoxStableDerefGenMap<DefaultKey, i32>;

#[test]
fn retain_keeps_all_and_can_mutate_values() {
    let mut map: Map = StableDerefGenMap::new();

    let (k1, _) = map.insert(Box::new(10));
    let (k2, _) = map.insert(Box::new(20));

    // Keep everything, mutate values.
    map.retain(|_, v| {
        **v += 1;
        true
    });

    assert_eq!(*map.get(k1).unwrap(), 11);
    assert_eq!(*map.get(k2).unwrap(), 21);
    assert_eq!(map.len(), 2);
}

#[test]
fn retain_removes_some_and_len_tracks() {
    let mut map: Map = StableDerefGenMap::new();

    let (k1, _) = map.insert(Box::new(1));
    let (k2, _) = map.insert(Box::new(2));
    let (k3, _) = map.insert(Box::new(3));

    // Keep only even values.
    map.retain(|_, v| **v % 2 == 0);

    assert!(map.get(k1).is_none());
    assert!(map.get(k3).is_none());

    let v2 = map.get(k2).unwrap();
    assert_eq!(*v2, 2);
    assert_eq!(map.len(), 1);
}

#[test]
fn retain_respects_generations_and_reuses_indices() {
    let mut map: Map = StableDerefGenMap::new();

    let (k1, _) = map.insert(Box::new(42));
    let k1_data = k1.data();

    // Remove k1 via retain.
    map.retain(|key, _| key != k1);

    // Old key must now be invalid.
    assert!(map.get(k1).is_none());
    assert_eq!(map.len(), 0);

    // Insert a new element; it should reuse the same idx but with bumped generation.
    let (k2, _) = map.insert(Box::new(99));
    let k2_data = k2.data();

    assert_eq!(k2_data.idx.into_usize(), k1_data.idx.into_usize());
    assert_ne!(k2_data.generation, k1_data.generation);
    assert_eq!(*map.get(k2).unwrap(), 99);
    assert_eq!(map.len(), 1);
}
