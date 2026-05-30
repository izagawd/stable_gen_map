use crate::boxed_slot::StableGenMap;
use crate::key::{DefaultKey, Key};
use std::collections::HashMap;

type Map = StableGenMap<DefaultKey, i32>;

#[test]
fn clone_empty() {
    let m: Map = Map::new();
    assert_eq!(m.len(), 0);

    let c = m.clone();
    assert_eq!(c.len(), 0);
}

#[test]
fn clone_basic_contents_equal_but_independent() {
    let mut m: Map = Map::new();

    let k1 = m.insert(10);
    let k2 = m.insert(20);
    let k3 = m.insert(30);

    assert_eq!(m.len(), 3);

    let c = m.clone();
    assert_eq!(c.len(), 3);

    // cloned values
    assert_eq!(c.get(k1), Some(&10));
    assert_eq!(c.get(k2), Some(&20));
    assert_eq!(c.get(k3), Some(&30));

    // removing from original does not affect clone
    let removed = { m.remove(k2).unwrap() };
    assert_eq!(removed, 20);
    assert_eq!(m.get(k2), None);
    assert_eq!(c.get(k2), Some(&20));

    // inserting into original does not affect clone
    let k4 = m.insert(40);
    assert_eq!(m.get(k4), Some(&40));
    assert_eq!(c.get(k4), None);
}

#[cfg(test)]
mod clone_tests {

    use crate::key::{DefaultKey, Key};

    use crate::boxed_slot::StableGenMap;

    type Map<T> = StableGenMap<DefaultKey, T>;

    #[test]
    fn clone_empty_map() {
        let map: Map<String> = StableGenMap::new();

        let clone = map.clone();

        assert_eq!(map.len(), 0);
        assert_eq!(clone.len(), 0);
        assert!(map.snapshot().is_empty());
        assert!(clone.snapshot().is_empty());
    }

    #[test]
    fn clone_copies_all_live_entries_and_not_aliasing() {
        let mut map: Map<String> = StableGenMap::new();

        // Insert enough elements to resize
        let mut keys = Vec::new();
        for i in 0..1000 {
            let k = map.insert(format!("val-{i}"));
            keys.push(k);
        }

        // Remove a few to create holes
        let removed_key_1 = keys[3];
        let removed_key_2 = keys[10]; // in a later slot
        assert_eq!(map.remove(removed_key_1).as_deref(), Some("val-3"));
        assert_eq!(
            map.remove(removed_key_2).as_deref(),
            Some(format!("val-{}", 10).as_str())
        );

        let len_before = map.len();

        // Take some reference pointers in the original map.
        let k_keep_1 = keys[0];
        let k_keep_2 = keys[9];

        let p1 = map.get(k_keep_1).unwrap() as *const String;
        let p2 = map.get(k_keep_2).unwrap() as *const String;

        let clone = map.clone();

        assert_eq!(clone.len(), len_before);
        assert_eq!(clone.len(), map.len());

        // Every live (k, v) pair from the original must appear with same value in clone.
        for (k, v) in map.snapshot() {
            assert_eq!(clone.get(k), Some(v), "clone must copy all live entries");
        }

        // Freed keys must still be invalid in the clone.
        assert!(clone.get(removed_key_1).is_none());
        assert!(clone.get(removed_key_2).is_none());

        // Deep clone: different allocations.
        let c1 = clone.get(k_keep_1).unwrap() as *const String;
        let c2 = clone.get(k_keep_2).unwrap() as *const String;
        assert_ne!(p1, c1);
        assert_ne!(p2, c2);

        // Mutate original; clone stays the same.
        *map.get_mut(k_keep_1).unwrap() = "mutated".to_owned();
        assert_eq!(map.get(k_keep_1).unwrap(), "mutated");
        assert_eq!(clone.get(k_keep_1).unwrap(), &format!("val-0"));
    }

    #[test]
    fn clone_preserves_free_list_structure_but_independent() {
        let mut map: Map<i32> = StableGenMap::new();

        let k1 = map.insert(10);
        let k2 = map.insert(20); // will be freed
        let k3 = map.insert(30);

        assert_eq!(map.len(), 3);

        let kd_old = k2.data();

        let removed = map.remove(k2).unwrap();
        assert_eq!(removed, 20);
        let len_before = map.len();
        assert_eq!(len_before, 2);

        let clone = map.clone();
        assert_eq!(clone.len(), len_before);

        // k2 should be invalid in both.
        assert!(map.get(k2).is_none());
        assert!(clone.get(k2).is_none());

        // Both maps should still see k1 and k3.
        assert_eq!(map.get(k1), Some(&10));
        assert_eq!(map.get(k3), Some(&30));
        assert_eq!(clone.get(k1), Some(&10));
        assert_eq!(clone.get(k3), Some(&30));

        // Insert in each: both should reuse the same encoded idx as k2 used,
        // but with generation bumped.
        let new_k_orig = map.insert(99);
        let new_k_clone = clone.insert(99);

        let kd_orig = new_k_orig.data();
        let kd_clone = new_k_clone.data();

        // Same physical slot reused.
        assert_eq!(kd_orig.idx, kd_clone.idx);
        assert_eq!(kd_orig.idx, kd_old.idx);

        // Generations must be strictly greater than old generation.
        assert!(kd_orig.generation > kd_old.generation);
        assert!(kd_clone.generation > kd_old.generation);

        // Maps are independent: removing from one does not affect the other.
        assert_eq!(map.len(), len_before + 1);
        assert_eq!(clone.len(), len_before + 1);

        let _ = map.remove(new_k_orig);
        assert_eq!(map.len(), len_before);
        assert_eq!(clone.len(), len_before + 1);
    }
}

#[test]
fn clone_preserves_all_keys_and_values() {
    let m: Map = Map::new();

    let mut inserted = HashMap::new();
    for i in 0..16 {
        let k = m.insert(i);
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
        assert_ne!(
            p_orig, p_clone,
            "clone must allocate new storage for values"
        );
    }
}

#[test]
fn clone_respects_free_list_and_generations() {
    let mut m: Map = Map::new();

    let _k1 = m.insert(1);
    let k2 = m.insert(2);
    let _k3 = m.insert(3);

    // Remove middle element to create a free slot
    let removed = m.remove(k2).unwrap();
    assert_eq!(removed, 2);
    assert_eq!(m.len(), 2);
    assert_eq!(m.get(k2), None);

    let removed_data = k2.data();

    // Clone after removal (so both maps have the same free list shape)
    let c = m.clone();

    // First insert in original should reuse the removed slot index
    let k_new_orig = m.insert(99);
    // First insert in clone should also reuse that same index
    let k_new_clone = c.insert(99);

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
fn clone_multi_slot() {
    let m: Map = Map::new();

    // Force multiple resizes (SLOTS is small)
    let mut keys = Vec::new();
    for i in 0..1000 as i32 {
        let k = m.insert(i);
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
fn clone_into_iter_matches_snapshot() {
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

// ── clone gate: positive direction ───────────────────────────────────────────
// A payload that implements `CloneGenMapPromise` makes the map `Clone`. The
// negative direction (a `Clone`-but-not-promised payload yields a non-`Clone`
// map) is a `compile_fail` doctest on `CloneGenMapPromise`.
const _: fn() = || {
    fn assert_clone<T: Clone>() {}
    assert_clone::<StableGenMap<DefaultKey, i32>>();
    assert_clone::<StableGenMap<DefaultKey, String>>();
};

// ── clone is drop-balanced, including across holes ───────────────────────────
// A drop-counting payload. Its `Clone` only clones an `Rc<Cell>` and copies an
// `i32`, so it cannot touch a map — hence the (sound) hand-written promise.
// This also exercises the user opt-in path for a custom payload.
struct DropTracked {
    drops: std::rc::Rc<std::cell::Cell<usize>>,
    val: i32,
}
impl Clone for DropTracked {
    fn clone(&self) -> Self {
        DropTracked {
            drops: self.drops.clone(),
            val: self.val,
        }
    }
}
impl Drop for DropTracked {
    fn drop(&mut self) {
        self.drops.set(self.drops.get() + 1);
    }
}
unsafe impl crate::clone_gen_map_promise::CloneGenMapPromise for DropTracked {}

#[test]
fn clone_then_drop_both_is_balanced_with_holes() {
    use std::cell::Cell;
    use std::rc::Rc;

    let drops = Rc::new(Cell::new(0usize));
    let mk = |v: i32| DropTracked {
        drops: drops.clone(),
        val: v,
    };

    let mut map: StableGenMap<DefaultKey, DropTracked> = StableGenMap::new();
    let k1 = map.insert(mk(1));
    let k2 = map.insert(mk(2));
    let k3 = map.insert(mk(3));
    let k4 = map.insert(mk(4));
    let k5 = map.insert(mk(5));

    // Remove two: leaves initialized-then-vacant slots, so clone and drop must
    // distinguish the occupied and vacant union arms per slot.
    map.remove(k2);
    map.remove(k4);
    assert_eq!(drops.get(), 2, "each removed value dropped exactly once");
    assert_eq!(map.len(), 3);

    // Clone duplicates only the 3 live slots (running Clone, never Drop) and
    // must not read the 2 vacant slots as occupied.
    let cloned = map.clone();
    assert_eq!(drops.get(), 2, "cloning runs Clone, not Drop");
    assert_eq!(cloned.len(), 3);

    // Clone is correct across the holes: live values present, removed absent.
    assert_eq!(cloned.get(k1).map(|t| t.val), Some(1));
    assert_eq!(cloned.get(k3).map(|t| t.val), Some(3));
    assert_eq!(cloned.get(k5).map(|t| t.val), Some(5));
    assert!(cloned.get(k2).is_none());
    assert!(cloned.get(k4).is_none());

    // Drop the original: exactly its 3 live values drop (vacant slots drop none).
    drop(map);
    assert_eq!(
        drops.get(),
        5,
        "dropping the original drops its 3 live values"
    );

    // Drop the clone: its own 3 live values drop. No double-free, no leak.
    drop(cloned);
    assert_eq!(
        drops.get(),
        8,
        "dropping the clone drops its own 3 live values"
    );
}
// ── clone_from: recycles self's slot buffer; result mirrors source ───────────

#[test]
fn clone_from_empty() {
    let mut dst: Map = Map::new();
    let src: Map = Map::new();
    dst.clone_from(&src);
    assert_eq!(dst.len(), 0);
    assert_eq!(dst.slots_len(), 0);
}

#[test]
fn clone_from_contents_equal_but_independent() {
    let mut dst: Map = Map::new();
    dst.insert(1);
    dst.insert(2);

    let mut src: Map = Map::new();
    let k1 = src.insert(10);
    let k2 = src.insert(20);
    let k3 = src.insert(30);

    dst.clone_from(&src);

    // dst now mirrors src
    assert_eq!(dst.len(), 3);
    assert_eq!(dst.get(k1), Some(&10));
    assert_eq!(dst.get(k2), Some(&20));
    assert_eq!(dst.get(k3), Some(&30));

    // independent: mutating src does not affect dst
    src.remove(k2);
    let k4 = src.insert(40);
    assert_eq!(dst.get(k2), Some(&20));
    assert_eq!(dst.get(k4), None);
}

#[test]
fn clone_from_matches_clone() {
    let mut src: Map = Map::new();
    let k1 = src.insert(1);
    let k2 = src.insert(2);
    let k3 = src.insert(3);
    src.remove(k2); // a hole

    let mut dst: Map = Map::new();
    dst.insert(99); // pre-existing content, discarded

    dst.clone_from(&src);
    let fresh = src.clone();

    assert_eq!(dst.len(), fresh.len());
    assert_eq!(dst.slots_len(), fresh.slots_len());
    assert_eq!(dst.get(k1), fresh.get(k1));
    assert_eq!(dst.get(k3), fresh.get(k3));
    assert_eq!(dst.get(k2), None);
}

#[test]
fn clone_from_overwrites_larger_dst() {
    // dst bigger than src: clone_from shrinks it to source's slot count.
    let mut dst: Map = Map::new();
    for i in 0..10 {
        dst.insert(i);
    }
    assert_eq!(dst.slots_len(), 10);

    let src: Map = Map::new();
    let a = src.insert(100);
    let b = src.insert(200);

    dst.clone_from(&src);
    assert_eq!(dst.len(), 2);
    assert_eq!(dst.slots_len(), 2, "dst shrinks to source's slot count");
    assert_eq!(dst.get(a), Some(&100));
    assert_eq!(dst.get(b), Some(&200));
}

#[test]
fn clone_from_grows_smaller_dst() {
    let mut dst: Map = Map::new();
    dst.insert(1);

    let src: Map = Map::new();
    let mut keys = Vec::new();
    for i in 0..50 {
        keys.push((src.insert(i), i));
    }

    dst.clone_from(&src);
    assert_eq!(dst.len(), 50);
    assert_eq!(dst.slots_len(), 50);
    for (k, v) in keys {
        assert_eq!(dst.get(k), Some(&v));
    }
}

#[test]
fn clone_from_preserves_holes() {
    let mut src: Map = Map::new();
    let k1 = src.insert(1);
    let k2 = src.insert(2);
    let k3 = src.insert(3);
    src.remove(k2); // vacant slot remains
    assert_eq!(src.len(), 2);
    assert_eq!(src.slots_len(), 3);

    let mut dst: Map = Map::new();
    dst.insert(9);
    dst.clone_from(&src);

    assert_eq!(dst.len(), 2);
    assert_eq!(dst.slots_len(), 3, "the hole is mirrored");
    assert_eq!(dst.get(k1), Some(&1));
    assert_eq!(dst.get(k3), Some(&3));
    assert!(dst.get(k2).is_none());
}

#[test]
fn clone_from_reuses_slot_buffer() {
    // White-box: with enough capacity already, clone_from recycles the existing
    // slot-vector allocation instead of reallocating.
    let mut dst: Map = Map::new();
    for i in 0..8 {
        dst.insert(i); // allocate a buffer with capacity >= 8
    }
    let ptr_before = unsafe { (*dst.slots.get()).as_ptr() };

    let src: Map = Map::new();
    for i in 0..4 {
        src.insert(i * 10); // fewer slots than dst's capacity
    }

    dst.clone_from(&src);
    let ptr_after = unsafe { (*dst.slots.get()).as_ptr() };
    assert_eq!(ptr_before, ptr_after, "clone_from reuses the slot buffer");
    assert_eq!(dst.len(), 4);
}

#[test]
fn clone_from_deep_clones_values() {
    let src: Map = Map::new();
    let k = src.insert(7);

    let mut dst: Map = Map::new();
    dst.insert(99);
    dst.clone_from(&src);

    let p_src = src.get(k).unwrap() as *const i32;
    let p_dst = dst.get(k).unwrap() as *const i32;
    assert_ne!(p_src, p_dst, "values are cloned into fresh storage");
    assert_eq!(dst.get(k), Some(&7));
}

#[test]
fn clone_from_is_drop_balanced() {
    use std::cell::Cell;
    use std::rc::Rc;

    let drops = Rc::new(Cell::new(0usize));
    let mk = |v: i32| DropTracked {
        drops: drops.clone(),
        val: v,
    };

    // dst with 3 live values, one removed -> a hole.
    let mut dst: StableGenMap<DefaultKey, DropTracked> = StableGenMap::new();
    dst.insert(mk(1));
    let r = dst.insert(mk(2));
    dst.insert(mk(3));
    dst.remove(r); // drops 1 -> counter 1
    assert_eq!(drops.get(), 1);

    // src with 2 live values.
    let src: StableGenMap<DefaultKey, DropTracked> = StableGenMap::new();
    let s1 = src.insert(mk(10));
    let s2 = src.insert(mk(20));

    // clone_from drops dst's 2 remaining live values (1 -> 3) and clones src's
    // 2 (running Clone, never Drop).
    dst.clone_from(&src);
    assert_eq!(drops.get(), 3, "clone_from drops dst's old live values once");
    assert_eq!(dst.len(), 2);
    assert_eq!(dst.get(s1).map(|t| t.val), Some(10));
    assert_eq!(dst.get(s2).map(|t| t.val), Some(20));

    // Drop both: src's 2 originals + dst's 2 clones. No double-free, no leak.
    drop(src);
    assert_eq!(drops.get(), 5);
    drop(dst);
    assert_eq!(drops.get(), 7, "drop-balanced: every value dropped once");
}
// ── clone_from panic-safety ──────────────────────────────────────────────────
// If a stored value's `Clone` panics partway through `clone_from`, the unwind
// must leave the map *valid* (not corrupt): inserting afterwards must append
// rather than index the now-stale free slot, and the live count must stay
// consistent so `remove`/`clear` don't underflow. (Most meaningful under Miri,
// which flags the out-of-bounds access the unfixed version would perform.)
#[test]
fn clone_from_panicking_clone_leaves_dst_valid() {
    use std::cell::Cell;
    use std::panic::{catch_unwind, AssertUnwindSafe};
    use std::rc::Rc;

    // Promised payload whose `Clone` panics for negative values.
    struct Boom {
        drops: Rc<Cell<usize>>,
        val: i32,
    }
    impl Clone for Boom {
        fn clone(&self) -> Self {
            assert!(self.val >= 0, "boom");
            Boom {
                drops: self.drops.clone(),
                val: self.val,
            }
        }
    }
    impl Drop for Boom {
        fn drop(&mut self) {
            self.drops.set(self.drops.get() + 1);
        }
    }
    unsafe impl crate::clone_gen_map_promise::CloneGenMapPromise for Boom {}

    let drops = Rc::new(Cell::new(0usize));
    let mk = |v: i32| Boom {
        drops: drops.clone(),
        val: v,
    };

    // dst: remove one so `next_free` points into the middle of a 5-slot buffer.
    let mut dst: StableGenMap<DefaultKey, Boom> = StableGenMap::new();
    dst.insert(mk(1));
    dst.insert(mk(2));
    dst.insert(mk(3));
    let r = dst.insert(mk(4));
    dst.insert(mk(5));
    dst.remove(r);
    assert_eq!(dst.slots_len(), 5);
    assert_eq!(dst.len(), 4);

    // src: the 2nd element's `Clone` panics.
    let src: StableGenMap<DefaultKey, Boom> = StableGenMap::new();
    src.insert(mk(10));
    src.insert(mk(-1)); // clone() panics here
    src.insert(mk(20));

    let result = catch_unwind(AssertUnwindSafe(|| dst.clone_from(&src)));
    assert!(result.is_err(), "the panicking clone propagates");

    // dst is left valid: insert must append (not reuse the stale free slot)…
    let k = dst.insert(mk(99));
    assert_eq!(dst.get(k).map(|b| b.val), Some(99));

    // …and the count stays consistent, so remove/clear don't underflow.
    let n = dst.len();
    assert!(dst.remove(k).is_some());
    assert_eq!(dst.len(), n - 1);
    dst.clear();
    assert_eq!(dst.len(), 0);

    // Dropping everything is safe: no double-free, no crash. (A partial copy may
    // leak on the panic path; leaks are not UB.)
    drop(dst);
    drop(src);
    assert!(drops.get() >= 1);
}
