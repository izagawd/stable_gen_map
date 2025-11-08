use crate::key::DefaultKey;
use crate::stable_deref_gen_map::BoxStableDerefGenMap;
use std::collections::HashSet;

#[test]
fn snapshot_on_empty_map_is_empty() {
    let map = BoxStableDerefGenMap::<DefaultKey, i32>::new();

    let snap = map.snapshot();

    assert_eq!(map.len(), 0);
    assert!(snap.is_empty());
}

#[cfg(test)]
mod snapshot_stablegen_tests {
    use super::*;
    use crate::key::DefaultKey;
    use crate::stable_deref_gen_map::BoxStableDerefGenMap;
    use std::collections::HashSet;

    #[test]
    fn snapshot_empty() {
        let map = BoxStableDerefGenMap::<DefaultKey, i32>::new();

        assert_eq!(map.len(), 0);
        assert!(map.snapshot().is_empty());
        assert!(map.snapshot_ref_only().is_empty());
        assert!(map.snapshot_key_only().is_empty());
    }

    #[test]
    fn snapshot_contains_all_items_and_matches_get() {
        let map = BoxStableDerefGenMap::<DefaultKey, i32>::new();

        let (k1, r1) = map.insert(Box::new(10));
        let (k2, r2) = map.insert(Box::new(20));
        let (k3, r3) = map.insert(Box::new(30));

        assert_eq!(*r1, 10);
        assert_eq!(*r2, 20);
        assert_eq!(*r3, 30);
        assert_eq!(map.len(), 3);

        let snap = map.snapshot();
        assert_eq!(snap.len(), 3);

        let mut seen = HashSet::new();
        for (k, v) in &snap {
            // no duplicate keys
            assert!(seen.insert(*k), "duplicate key in snapshot");

            let from_map = map.get(*k).expect("key from snapshot not found in map");
            // same value
            assert_eq!(from_map, *v);
            // same address (we really captured &T from the map)
            assert!(std::ptr::eq::<i32>(from_map, *v));
        }
    }

    #[test]
    fn snapshot_ignores_future_inserts() {
        let map = BoxStableDerefGenMap::<DefaultKey, i32>::new();

        let (k1, _) = map.insert(Box::new(1));
        let (k2, _) = map.insert(Box::new(2));

        let snap = map.snapshot();
        let refs = map.snapshot_ref_only();
        let keys = map.snapshot_key_only();

        let (k3, _) = map.insert(Box::new(3)); // after snapshots

        assert_eq!(map.len(), 3);
        assert_eq!(snap.len(), 2);
        assert_eq!(refs.len(), 2);
        assert_eq!(keys.len(), 2);

        let snap_keys: HashSet<_> = snap.iter().map(|(k, _)| *k).collect();
        let key_set: HashSet<_> = keys.iter().copied().collect();

        assert!(snap_keys.contains(&k1));
        assert!(snap_keys.contains(&k2));
        assert!(!snap_keys.contains(&k3));

        assert_eq!(snap_keys, key_set);
    }




}


#[test]
fn snapshot_contains_all_items_and_matches_get() {
    let map = BoxStableDerefGenMap::<DefaultKey, i32>::new();

    let (_k1, r1) = map.insert(Box::new(10));
    let (_k2, r2) = map.insert(Box::new(20));
    let (_k3, r3) = map.insert(Box::new(30));

    assert_eq!(*r1, 10);
    assert_eq!(*r2, 20);
    assert_eq!(*r3, 30);
    assert_eq!(map.len(), 3);

    let snap = map.snapshot();
    assert_eq!(snap.len(), 3);

    // no duplicate keys, and snapshot refs match get()
    let mut seen = HashSet::new();
    for (k, v) in &snap {
        assert!(seen.insert(*k), "duplicate key in snapshot");

        let from_map = map.get(*k).expect("key from snapshot not found in map");
        assert_eq!(from_map, *v);
        assert!(std::ptr::eq::<i32>(from_map, *v));
    }
}

#[test]
fn snapshot_ignores_future_inserts() {
    let map = BoxStableDerefGenMap::<DefaultKey, i32>::new();

    let (k1, _) = map.insert(Box::new(1));
    let (k2, _) = map.insert(Box::new(2));

    let snap = map.snapshot();

    let (k3, _) = map.insert(Box::new(3)); // inserted after snapshot

    assert_eq!(map.len(), 3);
    assert_eq!(snap.len(), 2);

    let snap_keys: HashSet<_> = snap.iter().map(|(k, _)| *k).collect();
    assert!(snap_keys.contains(&k1));
    assert!(snap_keys.contains(&k2));
    assert!(!snap_keys.contains(&k3));
}


