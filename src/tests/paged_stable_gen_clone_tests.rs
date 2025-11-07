use crate::key::{DefaultKey, Key};
use crate::paged_stable_gen_map::PagedStableGenMapAbstract;
use std::collections::{HashMap, HashSet};

const SLOTS: usize = 4;
type Map = PagedStableGenMapAbstract<DefaultKey, i32, SLOTS>;

#[test]
fn paged_clone_empty() {
    let m: Map = Map::new();
    assert_eq!(m.len(), 0);

    let c = m.clone();
    assert_eq!(c.len(), 0);
}

#[test]
fn paged_clone_basic_contents_equal_but_independent() {
    let mut m: Map = Map::new();

    let (k1, _) = m.insert(10);
    let (k2, _) = m.insert(20);
    let (k3, _) = m.insert(30);

    assert_eq!(m.len(), 3);

    let c = m.clone();
    assert_eq!(c.len(), 3);

    // cloned values
    assert_eq!(c.get(k1), Some(&10));
    assert_eq!(c.get(k2), Some(&20));
    assert_eq!(c.get(k3), Some(&30));

    // removing from original does not affect clone
    let removed = {

        m.remove(k2).unwrap()
    };
    assert_eq!(removed, 20);
    assert_eq!(m.get(k2), None);
    assert_eq!(c.get(k2), Some(&20));

    // inserting into original does not affect clone
    let (k4, _) = m.insert(40);
    assert_eq!(m.get(k4), Some(&40));
    assert_eq!(c.get(k4), None);
}

#[test]
fn paged_clone_preserves_all_keys_and_values() {
    let m: Map = Map::new();

    let mut inserted = HashMap::new();
    for i in 0..16 {
        let (k, _) = m.insert(i);
        inserted.insert(k, i);
    }

    let c = m.clone();
    assert_eq!(m.len(), c.len());
    assert_eq!(c.len(), inserted.len());

    // Every key/value in the clone matches what was in the original
    for (k, v) in inserted {
        assert_eq!(m.get(k), Some(&v));
        assert_eq!(c.get(k), Some(&v));
    }

    // Deep clone: pointers must differ
    for (k, _) in c.snapshot() {
        let p_orig = m.get(k).unwrap() as *const _;
        let p_clone = c.get(k).unwrap() as *const _;
        assert_ne!(p_orig, p_clone, "clone must allocate new storage for values");
    }
}

#[test]
fn paged_clone_respects_free_list_and_generations() {
    let mut m: Map = Map::new();

    let (_k1, _) = m.insert(1);
    let (k2, _) = m.insert(2);
    let (_k3, _) = m.insert(3);

    // Remove middle element to create a free slot
    let removed = m.remove(k2).unwrap();
    assert_eq!(removed, 2);
    assert_eq!(m.len(), 2);
    assert_eq!(m.get(k2), None);

    let removed_data = k2.data();

    // Clone after removal (so both maps have the same free list shape)
    let c = m.clone();

    // First insert in original should reuse the removed slot index
    let (k_new_orig, _) = m.insert(99);
    // First insert in clone should also reuse that same index
    let (k_new_clone, _) = c.insert(99);

    let new_orig_data = k_new_orig.data();
    let new_clone_data = k_new_clone.data();

    // Both new keys must reuse the old index
    assert_eq!(new_orig_data.idx, removed_data.idx);
    assert_eq!(new_clone_data.idx, removed_data.idx);

    // Generations must be bumped compared to the removed key
    assert_ne!(new_orig_data.generation, removed_data.generation);
    assert_ne!(new_clone_data.generation, removed_data.generation);
}

#[test]
fn paged_clone_multi_page() {
    let m: Map = Map::new();

    // Force multiple pages (SLOTS is small)
    let mut keys = Vec::new();
    for i in 0..(SLOTS * 5) as i32 {
        let (k, _) = m.insert(i);
        keys.push((k, i));
    }

    let c = m.clone();
    assert_eq!(m.len(), c.len());
    assert_eq!(m.len(), keys.len());

    // Make sure every key is present in both maps with same value
    for (k, v) in keys {
        assert_eq!(m.get(k), Some(&v));
        assert_eq!(c.get(k), Some(&v));
    }
}

#[test]
fn paged_clone_into_iter_matches_snapshot() {
    let m: Map = Map::new();

    for i in 0..20 {
        m.insert(i);
    }

    // snapshot from original (keys + values)
    let snap = m.snapshot();
    // consume a clone
    let collected: Vec<_> = m.clone().into_iter().collect();

    let snap_map: HashMap<_, _> = snap.into_iter().map(|(k, v)| (k, *v)).collect();
    let coll_map: HashMap<_, _> = collected.into_iter().collect();

    assert_eq!(snap_map.len(), coll_map.len());
    assert_eq!(snap_map, coll_map);
}

// ----- Re-entrant T::Clone that calls insert during cloning -----

// We use a thread-local pointer so Reentrant::clone can find the map.
thread_local! {
        static GLOBAL_MAP_PTR: std::cell::Cell<*const PagedStableGenMapAbstract<DefaultKey, Reentrant, SLOTS>> =
            std::cell::Cell::new(std::ptr::null());
    }

#[derive(Debug)]
struct Reentrant {
    val: i32,
}

impl Clone for Reentrant {
    fn clone(&self) -> Self {
        // On clone, insert a new element into the original map (if set).
        GLOBAL_MAP_PTR.with(|cell| {
            let ptr = cell.get();
            {
                unsafe {
                    let map = &*ptr;
                    let _ = map.insert(Reentrant { val: self.val + 1000 });
                }
            }
        });
        Reentrant { val: self.val }
    }
}

type MapReentrant = PagedStableGenMapAbstract<DefaultKey, Reentrant, SLOTS>;


#[test]
fn paged_clone_handles_reentrant_t_clone() {
    let m: MapReentrant = PagedStableGenMapAbstract::new();

    // allow Reentrant::clone to find this map
    GLOBAL_MAP_PTR.with(|cell| cell.set(&m as *const _));

    let (k1, _) = m.insert(Reentrant { val: 1 });
    let (k2, _) = m.insert(Reentrant { val: 2 });

    assert_eq!(m.len(), 2);

    let c = m.clone();

    // stop re-entrancy for the rest of the test
    GLOBAL_MAP_PTR.with(|cell| cell.set(std::ptr::null()));

    // original map may have more elements because of re-entrant inserts
    assert!(m.len() >= 2);

    // cloned map must reflect only the state at clone start -> 2 elements
    assert_eq!(c.len(), 2);

    let v1 = c.get(k1).unwrap();
    let v2 = c.get(k2).unwrap();
    assert_eq!(v1.val, 1);
    assert_eq!(v2.val, 2);

    // cloned keys set should be exactly {k1, k2}
    let cloned_keys: HashSet<_> = c.snapshot_key_only().into_iter().collect();
    assert_eq!(cloned_keys.len(), 2);
    assert!(cloned_keys.contains(&k1));
    assert!(cloned_keys.contains(&k2));
}