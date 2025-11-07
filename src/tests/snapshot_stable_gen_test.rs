use crate::key::DefaultKey;
use crate::stable_gen_map::StableGenMap;
use std::collections::HashSet;

#[test]
fn snapshot_on_empty_map_is_empty() {
    let map = StableGenMap::<DefaultKey, i32>::new();

    let snap = map.snapshot();

    assert_eq!(map.len(), 0);
    assert!(snap.is_empty());
}

#[cfg(test)]
mod snapshot_stablegen_tests {
    use super::*;
    use crate::key::DefaultKey;
    use crate::stable_gen_map::StableGenMap;
    use std::collections::HashSet;

    #[test]
    fn snapshot_empty() {
        let map = StableGenMap::<DefaultKey, i32>::new();

        assert_eq!(map.len(), 0);
        assert!(map.snapshot().is_empty());
        assert!(map.snapshot_ref_only().is_empty());
        assert!(map.snapshot_key_only().is_empty());
    }

    #[test]
    fn snapshot_contains_all_items_and_matches_get() {
        let map = StableGenMap::<DefaultKey, i32>::new();

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
        let map = StableGenMap::<DefaultKey, i32>::new();

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

    #[test]
    fn snapshot_iter_matches_snapshot() {
        let map = StableGenMap::<DefaultKey, i32>::new();

        for i in 0..8 {
            map.insert(Box::new(i));
        }

        let via_snapshot = map.snapshot();
        let via_iter: Vec<_> = map.snapshot_iter().collect();

        assert_eq!(via_snapshot.len(), via_iter.len());
        for (a, b) in via_snapshot.iter().zip(via_iter.iter()) {
            assert_eq!(a.0, b.0);
            assert!(std::ptr::eq::<i32>(a.1, b.1));
        }
    }

    #[test]
    fn snapshot_ref_only_matches_snapshot_refs() {
        let map = StableGenMap::<DefaultKey, i32>::new();

        for i in 0..10 {
            map.insert(Box::new(i));
        }

        let pairs = map.snapshot();
        let refs = map.snapshot_ref_only();
        let via_iter: Vec<&i32> = map.snapshot_ref_only_iter().collect();

        assert_eq!(pairs.len(), refs.len());
        assert_eq!(refs.len(), via_iter.len());

        let from_pairs: HashSet<*const i32> =
            pairs.iter().map(|(_, v)| *v as *const i32).collect();
        let from_refs: HashSet<*const i32> =
            refs.iter().map(|v| *v as *const i32).collect();
        let from_iter: HashSet<*const i32> =
            via_iter.iter().map(|v| *v as *const i32).collect();

        assert_eq!(from_pairs, from_refs);
        assert_eq!(from_refs, from_iter);
    }

    #[test]
    fn snapshot_key_only_matches_snapshot_keys() {
        let map = StableGenMap::<DefaultKey, i32>::new();

        let mut inserted_keys = Vec::new();
        for i in 0..10 {
            let (k, _) = map.insert(Box::new(i));
            inserted_keys.push(k);
        }

        let pairs = map.snapshot();
        let keys = map.snapshot_key_only();
        let via_iter: Vec<_> = map.snapshot_key_only_iter().collect();

        assert_eq!(pairs.len(), keys.len());
        assert_eq!(keys.len(), via_iter.len());

        let from_pairs: HashSet<_> = pairs.iter().map(|(k, _)| *k).collect();
        let key_set: HashSet<_> = keys.iter().copied().collect();
        let iter_set: HashSet<_> = via_iter.iter().copied().collect();

        assert_eq!(from_pairs, key_set);
        assert_eq!(key_set, iter_set);
    }
}


#[test]
fn snapshot_contains_all_items_and_matches_get() {
    let map = StableGenMap::<DefaultKey, i32>::new();

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
    let map = StableGenMap::<DefaultKey, i32>::new();

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

#[test]
fn snapshot_iter_matches_snapshot() {
    let map = StableGenMap::<DefaultKey, i32>::new();

    for i in 0..8 {
        map.insert(Box::new(i));
    }

    let via_snapshot = map.snapshot();
    let via_iter: Vec<_> = map.snapshot_iter().collect();

    assert_eq!(via_snapshot.len(), via_iter.len());
    for (a, b) in via_snapshot.iter().zip(via_iter.iter()) {
        // (K, &T) pairs must match exactly in order
        assert_eq!(a.0, b.0);
        assert!(std::ptr::eq::<i32>(a.1, b.1));
    }
}