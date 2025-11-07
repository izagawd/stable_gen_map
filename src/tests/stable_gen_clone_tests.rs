use crate::key::DefaultKey;
use crate::stable_gen_map::StableGenMap;
use std::cell::Cell;
use std::collections::HashSet;

#[test]
fn clone_empty_map() {
    let m: StableGenMap<DefaultKey, i32> = StableGenMap::new();
    assert_eq!(m.len(), 0);

    let c = m.clone();
    assert_eq!(c.len(), 0);
}

#[cfg(test)]
mod clone_efficiently_stable_tests {
    use super::*;
    use crate::key::{DefaultKey, Key};

    // Sanity: cloning an empty map should give another empty map.
    #[test]
    fn clone_efficiently_empty_map() {
        let mut map: StableGenMap<DefaultKey, String> = StableGenMap::new();

        let clone = map.clone_efficiently_mut();

        assert_eq!(map.len(), 0);
        assert_eq!(clone.len(), 0);
        assert!(map.snapshot().is_empty());
        assert!(clone.snapshot().is_empty());
    }

    // Basic semantics: contents equal, deep cloned (no alias), len preserved.
    #[test]
    fn clone_efficiently_copies_all_live_entries_and_not_aliasing() {
        let mut map: StableGenMap<DefaultKey, String> = StableGenMap::new();

        let (k1, _) = map.insert(Box::new("one".to_owned()));
        let (k2, _) = map.insert(Box::new("two".to_owned()));
        let (k3, _) = map.insert(Box::new("three".to_owned()));

        // Create a hole in the free list.
        let removed = map.remove(k2).unwrap();
        assert_eq!(*removed, "two");

        let len_before = map.len();

        // Pointers from original map.
        let p1 = map.get(k1).unwrap() as *const String;
        let p3 = map.get(k3).unwrap() as *const String;

        let mut clone = map.clone_efficiently_mut();

        // Same logical contents.
        assert_eq!(clone.len(), len_before);
        assert_eq!(clone.len(), map.len());

        assert_eq!(clone.get(k1).unwrap(), "one");
        assert!(clone.get(k2).is_none());
        assert_eq!(clone.get(k3).unwrap(), "three");

        // Deep clone: different allocations for the *same* keys.
        let c1 = clone.get(k1).unwrap() as *const String;
        let c3 = clone.get(k3).unwrap() as *const String;
        assert_ne!(p1, c1, "clone_efficiently must deep-clone values, not share them");
        assert_ne!(p3, c3, "clone_efficiently must deep-clone values, not share them");

        // Mutate original; clone should be unaffected.
        *map.get_mut(k1).unwrap() = "ONE!".to_owned();
        assert_eq!(map.get(k1).unwrap(), "ONE!");
        assert_eq!(clone.get(k1).unwrap(), "one");
    }

    // Free-list behaviour: after cloning, inserting into each map should
    // reuse the same free index, but with independent generations & len.
    #[test]
    fn clone_efficiently_preserves_free_list_structure_but_independent() {
        let mut map: StableGenMap<DefaultKey, i32> = StableGenMap::new();

        let (k1, _) = map.insert(Box::new(10));
        let (k2, _) = map.insert(Box::new(20)); // we'll remove this one
        let (k3, _) = map.insert(Box::new(30));

        // Remove middle slot to seed the free list.
        let removed = map.remove(k2).unwrap();
        assert_eq!(*removed, 20);
        let len_before = map.len();

        let mut clone = map.clone_efficiently_mut();

        assert_eq!(clone.len(), len_before);
        assert_eq!(clone.get(k1), Some(&10));
        assert_eq!(clone.get(k3), Some(&30));
        assert!(clone.get(k2).is_none());

        // Insert into original: should reuse the freed slot.
        let (new_k_orig, _) = map.insert(Box::new(99));
        // Insert into clone: should reuse the *same* index in the clone.
        let (new_k_clone, _) = clone.insert(Box::new(99));

        let kd_old = k2.data();
        let kd_orig = new_k_orig.data();
        let kd_clone = new_k_clone.data();

        // Both maps reuse the same index.
        assert_eq!(kd_orig.idx, kd_clone.idx);
        assert_eq!(kd_orig.idx, kd_old.idx);

        // Generations must be strictly higher than the old generation
        // (we invalidated the old key when freeing).
        assert!(kd_orig.generation > kd_old.generation);
        assert!(kd_clone.generation > kd_old.generation);

        // But the maps are independent: lengths diverge if we modify only one side.
        assert_eq!(map.len(), len_before + 1);
        assert_eq!(clone.len(), len_before + 1);

        // Remove in original only.
        let _ = map.remove(new_k_orig);
        assert_eq!(map.len(), len_before);
        assert_eq!(clone.len(), len_before + 1);
    }
}


#[test]
fn clone_basic_contents_equal_but_independent() {
    let mut m: StableGenMap<DefaultKey, i32> = StableGenMap::new();

    let (k1, _) = m.insert(Box::new(10));
    let (k2, _) = m.insert(Box::new(20));
    let (k3, _) = m.insert(Box::new(30));

    assert_eq!(m.len(), 3);

    let c = m.clone();
    assert_eq!(c.len(), 3);

    // clone has same values
    assert_eq!(c.get(k1), Some(&10));
    assert_eq!(c.get(k2), Some(&20));
    assert_eq!(c.get(k3), Some(&30));

    // removing from original doesn't affect clone
    let removed = m.remove(k2).unwrap();
    assert_eq!(*removed, 20);
    assert_eq!(m.get(k2), None);
    assert_eq!(c.get(k2), Some(&20));

    // inserting into original doesn't affect clone
    let (k4, _) = m.insert(Box::new(40));
    assert_eq!(m.get(k4), Some(&40));
    assert_eq!(c.get(k4), None);
}

#[test]
fn clone_with_holes_preserves_logical_state() {
    let mut m: StableGenMap<DefaultKey, i32> = StableGenMap::new();

    let (k1, _) = m.insert(Box::new(1));
    let (k2, _) = m.insert(Box::new(2));
    let (k3, _) = m.insert(Box::new(3));

    // create a hole
    let removed = m.remove(k2).unwrap();

    assert_eq!(*removed, 2);
    assert_eq!(m.len(), 2);
    assert_eq!(m.get(k2), None);

    // possibly reuse the hole
    let (k4, _) = m.insert(Box::new(4));
    assert_eq!(m.len(), 3);

    let c = m.clone();

    assert_eq!(c.len(), 3);
    assert_eq!(c.get(k1), Some(&1));
    assert_eq!(c.get(k2), None); // was removed pre-clone
    assert_eq!(c.get(k3), Some(&3));
    assert_eq!(c.get(k4), Some(&4));
}

// Thread-local pointer to "the map being cloned".
// Reentrant::clone will use this to insert into the map.
thread_local! {
        static GLOBAL_MAP_PTR: Cell<*const StableGenMap<DefaultKey, Reentrant>> =
            Cell::new(std::ptr::null());
    }

#[derive(Debug)]
struct Reentrant {
    val: i32,
}

impl Clone for Reentrant {
    fn clone(&self) -> Self {
        // On clone, insert a new element into the original map (if any).
        GLOBAL_MAP_PTR.with(|cell| {
            let ptr = cell.get();
             {
                unsafe {
                    let map: &StableGenMap<DefaultKey, Reentrant> = &*ptr;
                    let _ = map.insert(Box::new(Reentrant {
                        val: self.val + 1000,
                    }));
                }
            }
        });

        Reentrant { val: self.val }
    }
}

type MapReentrant = StableGenMap<DefaultKey, Reentrant>;

#[test]
fn stable_clone_handles_reentrant_t_clone() {
    let m: MapReentrant = StableGenMap::new();

    // Let Reentrant::clone know which map to mutate.
    GLOBAL_MAP_PTR.with(|cell| cell.set(&m as *const _));

    let (k1, _) = m.insert(Box::new(Reentrant { val: 1 }));
    let (k2, _) = m.insert(Box::new(Reentrant { val: 2 }));

    // Before clone: 2 entries
    assert_eq!(m.len(), 2);

    // clone() will cause each Reentrant::clone to insert extra entries into *m*
    let c = m.clone();

    // Stop re-entrancy after cloning, so later code doesn't accidentally hit it.
    GLOBAL_MAP_PTR.with(|cell| cell.set(std::ptr::null()));

    // Original map now has at least as many entries as before (probably more).
    assert!(m.len() >= 2);

    // Cloned map must reflect the state at clone start → 2 logical elements.
    assert_eq!(c.len(), 2);

    // k1, k2 must exist in cloned map with original vals
    let v1 = c.get(k1).unwrap();
    let v2 = c.get(k2).unwrap();
    assert_eq!(v1.val, 1);
    assert_eq!(v2.val, 2);

    // cloned keys set should be exactly {k1, k2}
    let cloned_keys: HashSet<_> = {
        // if you already have snapshot_key_only(), use that:
        // c.snapshot_key_only().into_iter().collect()
        //
        // otherwise, approximate via snapshot of pairs:
        c.snapshot().into_iter().map(|(k, _)| k).collect()
    };

    assert_eq!(cloned_keys.len(), 2);
    assert!(cloned_keys.contains(&k1));
    assert!(cloned_keys.contains(&k2));
}