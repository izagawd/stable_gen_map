use crate::deref_slot::BoxStableDerefMap;
use crate::key::DefaultKey;

#[test]
fn clone_empty_map() {
    let m: BoxStableDerefMap<DefaultKey, i32> = BoxStableDerefMap::new();
    assert_eq!(m.len(), 0);

    let c = m.clone();
    assert_eq!(c.len(), 0);
}

// ...

#[test]
fn clone_preserves_live_entries_and_len_and_allocates_new_boxes() {
    // Use the StableMap alias you already have:
    // type StableMap<T> = BoxStableDerefMap<DefaultKey, T>;
    let mut map = BoxStableDerefMap::<DefaultKey, i32>::new();

    let k1 = map.insert(Box::new(10));
    let k2 = map.insert(Box::new(20));
    let k3 = map.insert(Box::new(30));

    // Remove one entry to exercise the free-list state.
    assert!(map.remove(k2).is_some());
    assert_eq!(map.len(), 2);

    let mut cloned = map.clone();
    assert_eq!(
        cloned.len(),
        2,
        "clone must see the same number of live entries"
    );

    // Both maps see the same live keys and values.
    assert_eq!(*map.get(k1).unwrap(), 10);
    assert_eq!(*cloned.get(k1).unwrap(), 10);

    assert_eq!(*map.get(k3).unwrap(), 30);
    assert_eq!(*cloned.get(k3).unwrap(), 30);

    // Removed key stays dead in both.
    assert!(map.get(k2).is_none());
    assert!(cloned.get(k2).is_none());

    // But the boxed allocations themselves must be distinct.
    let p1_orig = map.get(k1).unwrap() as *const i32 as usize;
    let p1_clone = cloned.get(k1).unwrap() as *const i32 as usize;
    assert_ne!(
        p1_orig, p1_clone,
        "cloned map must allocate independent Box<T> for each slot"
    );

    // Mutating the clone must not affect the original.
    *cloned.get_mut(k1).unwrap() = 99;
    assert_eq!(*cloned.get(k1).unwrap(), 99);
    assert_eq!(
        *map.get(k1).unwrap(),
        10,
        "mutating cloned map must not change original"
    );
}

#[test]
fn clone_with_rc_clones_rc_not_inner_value() {
    use std::rc::Rc;

    // Map stores Box<Rc<String>> internally; Clone for the map should
    // clone the Rc (bump refcount), not deep-clone the inner String.
    let map: BoxStableDerefMap<DefaultKey, Rc<String>> = BoxStableDerefMap::new();

    let k = map.insert(Box::new(Rc::new("hello".to_string())));

    // One Rc in the map.
    assert_eq!(
        Rc::strong_count(map.get(k).unwrap()),
        1,
        "exactly one Rc before cloning the map"
    );

    let cloned = map.clone();

    // After cloning the map, the Rc for this slot should have been cloned once:
    // one Rc in `map`, one Rc in `cloned`.
    assert_eq!(
        Rc::strong_count(map.get(k).unwrap()),
        2,
        "cloning the map must clone the Rc, bumping the refcount"
    );

    let rc_orig = map.get(k).unwrap();
    let rc_cloned = cloned.get(k).unwrap();

    // Both Rc values should point to the same underlying allocation.
    assert!(
        Rc::ptr_eq(rc_orig, rc_cloned),
        "Rc inside original and cloned map must alias the same allocation"
    );
    assert_eq!(rc_orig.as_str(), "hello");
    assert_eq!(rc_cloned.as_str(), "hello");

    // Dropping the cloned map should drop exactly one Rc.
    drop(cloned);
    assert_eq!(
        Rc::strong_count(rc_orig),
        1,
        "dropping cloned map must decrement the Rc refcount back to 1"
    );
}

#[cfg(test)]
mod clone_stable_tests {
    use super::*;
    use crate::key::{DefaultKey, Key};

    // Sanity: cloning an empty map should give another empty map.
    #[test]
    fn clone_empty_map() {
        let map: BoxStableDerefMap<DefaultKey, String> = BoxStableDerefMap::new();

        let clone = map.clone();

        assert_eq!(map.len(), 0);
        assert_eq!(clone.len(), 0);
        assert!(map.snapshot().is_empty());
        assert!(clone.snapshot().is_empty());
    }

    // Basic semantics: contents equal, deep cloned (no alias), len preserved.
    #[test]
    fn clone_copies_all_live_entries_and_not_aliasing() {
        let mut map: BoxStableDerefMap<DefaultKey, String> = BoxStableDerefMap::new();

        let k1 = map.insert(Box::new("one".to_owned()));
        let k2 = map.insert(Box::new("two".to_owned()));
        let k3 = map.insert(Box::new("three".to_owned()));

        // Create a hole in the free list.
        let removed = map.remove(k2).unwrap();
        assert_eq!(*removed, "two");

        let len_before = map.len();

        // Pointers from original map.
        let p1 = map.get(k1).unwrap() as *const String;
        let p3 = map.get(k3).unwrap() as *const String;

        let clone = map.clone();

        // Same logical contents.
        assert_eq!(clone.len(), len_before);
        assert_eq!(clone.len(), map.len());

        assert_eq!(clone.get(k1).unwrap(), "one");
        assert!(clone.get(k2).is_none());
        assert_eq!(clone.get(k3).unwrap(), "three");

        // Deep clone: different allocations for the *same* keys.
        let c1 = clone.get(k1).unwrap() as *const String;
        let c3 = clone.get(k3).unwrap() as *const String;
        assert_ne!(
            p1, c1,
            "clone must deep-clone values, not share them"
        );
        assert_ne!(
            p3, c3,
            "clone must deep-clone values, not share them"
        );

        // Mutate original; clone should be unaffected.
        *map.get_mut(k1).unwrap() = "ONE!".to_owned();
        assert_eq!(map.get(k1).unwrap(), "ONE!");
        assert_eq!(clone.get(k1).unwrap(), "one");
    }

    // Free-list behaviour: after cloning, inserting into each map should
    // reuse the same free index, but with independent generations & len.
    #[test]
    fn clone_preserves_free_list_structure_but_independent() {
        let mut map: BoxStableDerefMap<DefaultKey, i32> = BoxStableDerefMap::new();

        let k1 = map.insert(Box::new(10));
        let k2 = map.insert(Box::new(20)); // we'll remove this one
        let k3 = map.insert(Box::new(30));

        // Remove middle slot to seed the free list.
        let removed = map.remove(k2).unwrap();
        assert_eq!(*removed, 20);
        let len_before = map.len();

        let clone = map.clone();

        assert_eq!(clone.len(), len_before);
        assert_eq!(clone.get(k1), Some(&10));
        assert_eq!(clone.get(k3), Some(&30));
        assert!(clone.get(k2).is_none());

        // Insert into original: should reuse the freed slot.
        let new_k_orig = map.insert(Box::new(99));
        // Insert into clone: should reuse the *same* index in the clone.
        let new_k_clone = clone.insert(Box::new(99));

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
    let mut m: BoxStableDerefMap<DefaultKey, i32> = BoxStableDerefMap::new();

    let k1 = m.insert(Box::new(10));
    let k2 = m.insert(Box::new(20));
    let k3 = m.insert(Box::new(30));

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
    let k4 = m.insert(Box::new(40));
    assert_eq!(m.get(k4), Some(&40));
    assert_eq!(c.get(k4), None);
}

#[test]
fn clone_with_holes_preserves_logical_state() {
    let mut m: BoxStableDerefMap<DefaultKey, i32> = BoxStableDerefMap::new();

    let k1 = m.insert(Box::new(1));
    let k2 = m.insert(Box::new(2));
    let k3 = m.insert(Box::new(3));

    // create a hole
    let removed = m.remove(k2).unwrap();

    assert_eq!(*removed, 2);
    assert_eq!(m.len(), 2);
    assert_eq!(m.get(k2), None);

    // possibly reuse the hole
    let k4 = m.insert(Box::new(4));
    assert_eq!(m.len(), 3);

    let c = m.clone();

    assert_eq!(c.len(), 3);
    assert_eq!(c.get(k1), Some(&1));
    assert_eq!(c.get(k2), None); // was removed pre-clone
    assert_eq!(c.get(k3), Some(&3));
    assert_eq!(c.get(k4), Some(&4));
}
