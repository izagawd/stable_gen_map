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

struct Reentrant<'a> {
    map: &'a StableGenMap<DefaultKey, Reentrant<'a>>,
    val: i32,
    cloned_inserted: Cell<bool>,
}

impl Clone for Reentrant<'static> {
    fn clone(&self) -> Self {
        // On clone, insert a new element into the original map.
        let _ = self.map.insert(Box::new(Reentrant {
            map: self.map,
            val: self.val + 1000,
            cloned_inserted: Cell::new(false),
        }));
        self.cloned_inserted.set(true);

        Reentrant {
            map: self.map,
            val: self.val,
            cloned_inserted: Cell::new(false),
        }
    }
}

#[cfg_attr(miri, ignore)] // we make miri ignore the test, because its complaining about leaks. Might need to look back at this later
#[test]
fn clone_does_not_see_reentrant_inserts_from_t_clone() {
    let m:&'static StableGenMap<DefaultKey, Reentrant<'static>> =  Box::leak(Box::new(StableGenMap::new()));

    let (k1, _) = m.insert(Box::new(Reentrant {
        map: &m,
        val: 1,
        cloned_inserted: Cell::new(false),
    }));
    let (k2, _) = m.insert(Box::new(Reentrant {
        map: &m,
        val: 2,
        cloned_inserted: Cell::new(false),
    }));

    // Before clone: 2 entries
    assert_eq!(m.len(), 2);

    // clone() will cause each Reentrant::clone to insert extra entries into *m*
    let c = m.clone();

    // original map now has at least as many entries as before, probably 4
    assert!(m.len() >= 2);

    // cloned map must reflect state at clone start -> still 2 logical elements
    assert_eq!(c.len(), 2);

    // k1, k2 must exist in cloned map with original vals
    let v1 = c.get(k1).unwrap();
    let v2 = c.get(k2).unwrap();
    assert_eq!(v1.val, 1);
    assert_eq!(v2.val, 2);

    // cloned map should have exactly 2 keys: k1 and k2
    let cloned_keys: HashSet<_> = {
        // if you already have snapshot_key_only(), use that here.
        // Otherwise, approximate via snapshot of pairs:
        c.snapshot()
            .into_iter()
            .map(|(k, _)| k)
            .collect()
    };
    assert_eq!(cloned_keys.len(), 2);
    assert!(cloned_keys.contains(&k1));
    assert!(cloned_keys.contains(&k2));
}