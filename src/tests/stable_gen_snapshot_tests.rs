use crate::key::DefaultKey;

use std::collections::HashSet;
use crate::stable_gen_map::StableGenMap;

const SLOTS: usize = 4;

    type Map = StableGenMap<DefaultKey, i32>;

    #[test]
    fn snapshot_on_empty_map_is_empty() {
        let map = Map::new();

        let snap = map.snapshot();

        assert_eq!(map.len(), 0);
        assert!(snap.is_empty());
    }

    #[test]
    fn snapshot_covers_all_items_and_matches_get() {
        let map = Map::new();

        // Insert enough to spill into multiple pages
        let mut keys = Vec::new();
        for i in 0..(SLOTS * 3 + 1) as i32 {
            let (k, r) = map.insert(i);
            assert_eq!(*r, i);
            keys.push(k);
        }

        assert_eq!(map.len(), keys.len());

        let snap = map.snapshot();
        assert_eq!(snap.len(), keys.len());

        // No duplicate keys
        let mut seen = HashSet::new();
        for (k, v) in &snap {
            assert!(seen.insert(*k), "duplicate key in normal_map snapshot");

            let from_map = map.get(*k).expect("key from normal_map snapshot not found in map");
            assert_eq!(from_map, *v);
            assert!(std::ptr::eq::<i32>(from_map, *v));
        }
    }

    #[test]
    fn snapshot_ignores_future_inserts() {
        let map = Map::new();

        let (k1, _) = map.insert(10);
        let (k2, _) = map.insert(20);

        let snap = map.snapshot();

        let (k3, _) = map.insert(30); // after snapshot

        assert_eq!(map.len(), 3);
        assert_eq!(snap.len(), 2);

        let snap_keys: HashSet<_> = snap.iter().map(|(k, _)| *k).collect();
        assert!(snap_keys.contains(&k1));
        assert!(snap_keys.contains(&k2));
        assert!(!snap_keys.contains(&k3));
    }


    #[test]
    fn snapshot_ref_only_empty() {
        let map = Map::new();

        let refs = map.snapshot_ref_only();
        let keys = map.snapshot_key_only();
        let pairs = map.snapshot();

        assert_eq!(map.len(), 0);
        assert!(refs.is_empty());
        assert!(keys.is_empty());
        assert!(pairs.is_empty());
    }

    #[test]
    fn snapshot_ref_only_contains_all_values() {
        let map = Map::new();

        // force multiple pages
        for i in 0..(SLOTS * 3 + 1) as i32 {
            map.insert(i);
        }

        assert_eq!(map.len(), SLOTS * 3 + 1);

        let pairs = map.snapshot();
        let refs = map.snapshot_ref_only();

        assert_eq!(pairs.len(), map.len());
        assert_eq!(refs.len(), map.len());

        // Compare by pointer set: same underlying &T
        let from_pairs: HashSet<*const i32> =
            pairs.iter().map(|(_, v)| *v as *const i32).collect();
        let from_refs: HashSet<*const i32> =
            refs.iter().map(|v| *v as *const i32).collect();

        assert_eq!(from_pairs, from_refs);
    }



    #[test]
    fn snapshot_ref_only_ignores_future_inserts() {
        let map = Map::new();

        map.insert(10);
        map.insert(20);

        let refs = map.snapshot_ref_only();

        map.insert(30); // after snapshot

        assert_eq!(map.len(), 3);
        assert_eq!(refs.len(), 2);
    }

    #[test]
    fn snapshot_key_only_contains_all_keys() {
        let map = Map::new();

        let mut inserted_keys = Vec::new();
        for i in 0..(SLOTS * 3 + 1) as i32 {
            let (k, _) = map.insert(i);
            inserted_keys.push(k);
        }

        let pairs = map.snapshot();
        let keys = map.snapshot_key_only();

        assert_eq!(pairs.len(), map.len());
        assert_eq!(keys.len(), map.len());

        let from_pairs: HashSet<_> = pairs.iter().map(|(k, _)| *k).collect();
        let from_keys: HashSet<_> = keys.iter().copied().collect();

        assert_eq!(from_pairs, from_keys);
    }



    #[test]
    fn snapshot_key_only_ignores_future_inserts() {
        let map = Map::new();

        let (k1, _) = map.insert(1);
        let (k2, _) = map.insert(2);

        let keys = map.snapshot_key_only();

        let (k3, _) = map.insert(3);

        assert_eq!(map.len(), 3);
        assert_eq!(keys.len(), 2);

        let set: HashSet<_> = keys.iter().copied().collect();
        assert!(set.contains(&k1));
        assert!(set.contains(&k2));
        assert!(!set.contains(&k3));
    }
    
    #[test]
    fn snapshot_iter_matches_snapshot() {
        let map = Map::new();

        for i in 0..(SLOTS * 2) as i32 {
            map.insert(i);
        }

        let via_snapshot = map.snapshot();
        let via_iter: Vec<_> = map.snapshot_iter().collect();

        assert_eq!(via_snapshot.len(), via_iter.len());
        for (a, b) in via_snapshot.iter().zip(via_iter.iter()) {
            assert_eq!(a.0, b.0);
            assert!(std::ptr::eq::<i32>(a.1, b.1));
        }
    }

