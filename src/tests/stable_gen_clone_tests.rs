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