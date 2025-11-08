use crate::key::{Key, KeyData};
use std::panic::{catch_unwind, AssertUnwindSafe};

#[test]
    fn stable_len_tracks_insert_remove_and_clear() {
        let map: StableMap<i32> = BoxStableDerefGenMap::new();
        assert_eq!(map.len(), 0, "new map must start empty");

        let (k1, _) = map.insert(Box::new(10));
        assert_eq!(map.len(), 1, "one insert increments len to 1");

        let (k2, _) = map.insert(Box::new(20));
        assert_eq!(map.len(), 2, "two inserts increments len to 2");

        // Move to a mutable binding for remove/clear.
        let mut map = map;

        // Removing a live key decrements len.
        assert_eq!(map.remove(k1).map(|b| *b), Some(10));
        assert_eq!(map.len(), 1, "remove must decrement len");

        // Removing again (already removed) must not change len.
        assert!(map.remove(k1).is_none());
        assert_eq!(map.len(), 1, "removing non-existent key must not change len");

        // Removing a bogus key (wrong idx/generation) must not change len.
        let mut bogus = k2;
        bogus.key_data.generation = bogus.key_data.generation.wrapping_add(1);
        assert!(map.remove(bogus).is_none());
        assert_eq!(map.len(), 1, "failed remove (generation mismatch) must not change len");

        // clear() must reset len to 0.
        map.clear();
        assert_eq!(map.len(), 0, "clear must reset len to 0");
    }

    #[test]
    fn stable_len_unchanged_on_try_insert_new_slot_err_and_panic() {
        let map: StableMap<i32> = BoxStableDerefGenMap::new();
        assert_eq!(map.len(), 0);

        // Map is empty → try_insert_with_key goes down the "new slot" branch.
        let res: Result<(DefaultKey, &i32), &'static str> =
            map.try_insert_with_key(|_k| -> Result<Box<i32>, &'static str> {
                Err("constructor failed")
            });

        assert!(res.is_err());
        assert_eq!(map.len(), 0, "len must stay 0 after Err in new-slot branch");

        // Same but with a panic inside the constructor.
        let res_panic = catch_unwind(AssertUnwindSafe(|| {
            let _ = map.try_insert_with_key::<()>(|_k| -> Result<Box<i32>, ()> {
                panic!("boom in new-slot constructor");
            });
        }));
        assert!(res_panic.is_err());
        assert_eq!(map.len(), 0, "len must stay 0 after panic in new-slot branch");

        // After those failures, a normal insert must still give len = 1.
        let (_k_ok, _v_ok) = map.insert(Box::new(123));
        assert_eq!(map.len(), 1, "successful insert after failures must bump len to 1");
    }
    #[test]
    fn stable_iter_mut_can_modify_all_values() {
        let mut map: StableMap<i32> = BoxStableDerefGenMap::new();

        for i in 0..5 {
            let (_k, _) = map.insert(Box::new(i));
        }

        for (_k, v) in map.iter_mut() {
            *v += 10;
        }

        let mut values: Vec<i32> = (&mut map).into_iter().map(|(_, v)| *v).collect();
        values.sort();
        assert_eq!(values, (10..15).collect::<Vec<_>>());
    }

    #[test]
    fn stable_into_iter_consumes_and_yields_boxes() {
        let mut map: StableMap<String> = BoxStableDerefGenMap::new();

        for i in 0..3 {
            let (_k, _) = map.insert(Box::new(format!("v{}", i)));
        }

        let mut seen: Vec<String> = map
            .into_iter()
            .map(|(_k, b)| *b) // Box<String> -> String
            .collect();

        seen.sort();
        assert_eq!(seen, vec!["v0", "v1", "v2"]);
    }
    #[test]
    fn stable_try_insert_with_key_ok_path_new_slot() {
        let map: StableMap<i32> = BoxStableDerefGenMap::new();

        // OK path on a fresh map (no free slots; uses "new slot" branch).
        let (k, v) = map
            .try_insert_with_key(|_k| -> Result<Box<i32>, &'static str> {
                Ok(Box::new(10))
            })
            .unwrap();

        assert_eq!(*v, 10);
        assert_eq!(*map.get(k).unwrap(), 10);
    }

    #[test]
    fn stable_try_insert_with_key_error_reuses_free_slot() {
        let map: StableMap<i32> = BoxStableDerefGenMap::new();

        // First insert via the simple insert API so we can remove it later.
        let (k1, _) = map.insert(Box::new(1));

        // Move to a mutable binding so we can call remove.
        let mut map = map;

        let old_data = k1.data();
        let removed = map.remove(k1).unwrap();
        assert_eq!(*removed, 1);
        assert!(map.get(k1).is_none());

        // Now we have one free slot at (idx = old_data.idx).
        // Call try_insert_with_key but make it return Err.
        let res_err: Result<(DefaultKey, &i32), &'static str> =
            (&map as &StableMap<i32>).try_insert_with_key(
                |_k| -> Result<Box<i32>, &'static str> {
                    Err("oops")
                },
            );

        assert!(res_err.is_err());

        // Slot should have been put back onto the free list.
        // Next successful insert should reuse the same idx, with the
        // incremented generation from the earlier remove.
        let (k2, v2) =
            (&map as &StableMap<i32>)
                .try_insert_with_key::<()>(|_k| Ok(Box::new(99)))
                .unwrap();

        let new_data = k2.data();

        // Same index reused, generation bumped once by remove (and not changed by the failed insert).
        assert_eq!(old_data.idx, new_data.idx);
        assert_ne!(old_data.generation, new_data.generation);

        assert_eq!(*v2, 99);
        assert_eq!(*map.get(k2).unwrap(), 99);

        // Old key remains stale.
        assert!(map.get(k1).is_none());
        assert!(map.get_mut(k1).is_none());
        assert!(map.remove(k1).is_none());
    }

    type StableMap<T> = BoxStableDerefGenMap<DefaultKey, T>;




    #[test]
    fn stable_ref_survives_many_vec_resizes() {
        // A big enough count to force multiple Vec growths.
        let map = BoxStableDerefGenMap::<DefaultKey, String>::new();

        let (k, r) = map.insert(Box::new("root".to_string()));
        let p_before = (r as *const String) as usize;

        for i in 0..1_000 {
            let s = i.to_string();
            let _ = map.insert(Box::new(s));
        }

        // The Box<T> allocation is stable; &T address must not change.
        let p_after = (map.get(k).unwrap() as *const String) as usize;
        assert_eq!(p_before, p_after);
        assert_eq!(map.get(k).unwrap().as_str(), "root");
    }

    #[test]
    fn reentrant_insert_with_reuses_freed_slot_even_if_vec_resizes() {
        // Hit the free-slot branch then cause a resize inside the closure.
        let mut map = BoxStableDerefGenMap::<DefaultKey, i32>::new();
        let (k_old, _) = map.insert(Box::new(111));
        let idx = k_old.key_data.idx;
        let gen_old = k_old.key_data.generation;

        // Free one slot.
        assert_eq!(map.remove(k_old).map(|b| *b), Some(111));

        // Reinsert into the freed slot using insert_with; inside, blow up the Vec.
        let (k_new, r_new) = map.insert_with_key(|k_self| {
            // While inserting, the slot is marked "inserting": get() must hide it.
            assert!(map.get(k_self).is_none());

            // Force many resizes while this slot is still "inserting".
            for i in 0..1_000 {
                let _ = map.insert(Box::new(i));
            }

            Box::new(222)
        });

        assert_eq!(*r_new, 222);
        assert_eq!(map.get(k_new).copied(), Some(222));

        // Same index should be reused, but generation must bump.
        assert_eq!(k_new.key_data.idx, idx);
        assert_ne!(k_new.key_data.generation, gen_old);
    }

    #[test]
    fn get_returns_none_during_insert_even_while_resizing() {
        let map = BoxStableDerefGenMap::<DefaultKey, String>::new();

        let (_k, r) = map.insert_with_key(|k_self| {
            // During the window where is_inserting=true, get() must return None.
            assert!(map.get(k_self).is_none());

            // Trigger considerable internal growth during that window.
            for i in 0..1_000 {
                let _ = map.insert(Box::new(i.to_string()));
            }

            Box::new("done".to_string())
        });

        assert_eq!(r.as_str(), "done");
    }

    #[test]
    fn remove_then_mass_insert_then_reuse_keeps_old_key_invalid() {
        let mut map = BoxStableDerefGenMap::<DefaultKey, i32>::new();

        let (k1, _) = map.insert(Box::new(1));
        assert_eq!(map.remove(k1).map(|b| *b), Some(1));
        assert!(map.get(k1).is_none()); // old key invalid

        // Force lots of growth; free list should be consumed at some point.
        for i in 0..1_000 {
            let _ = map.insert(Box::new(i as i32));
        }

        // Reuse any free slots; the old key must remain invalid (generation mismatch).
        assert!(map.get(k1).is_none());
    }

    #[test]
    fn trait_object_survives_resizes() {
        use core::fmt::Display;

        let map: BoxStableDerefGenMap<DefaultKey, dyn Display> = BoxStableDerefGenMap::new();
        let (k, r) = map.insert(Box::new(String::from("hello")) as Box<dyn Display>);
        let p_before = (r as *const dyn Display) as *const () as usize;

        for i in 0..1_000 {
            let _ = map.insert(Box::new(i.to_string()) as Box<dyn Display>);
        }

        let p_after = (map.get(k).unwrap() as *const dyn Display) as *const () as usize;
        assert_eq!(p_before, p_after);
        assert_eq!(map.get(k).unwrap().to_string(), "hello");
    }

    // New-slot branch + Err: index 0 must be reusable.
    #[test]
    fn stable_try_insert_with_key_err_reuses_reserved_new_slot() {
        let map: StableMap<i32> = BoxStableDerefGenMap::new();

        // No free slots yet → this uses the "push new slot" branch.
        let res: Result<(DefaultKey, &i32), &'static str> =
            map.try_insert_with_key(|_k| -> Result<Box<i32>, &'static str> {
                Err("oops in constructor")
            });

        assert!(res.is_err());

        // After the error, the reserved slot must have been returned
        // to the free list and be reusable as idx 0.
        let (k_ok, v_ok) = map.insert(Box::new(123));
        let kd = k_ok.data();

        assert_eq!(kd.idx, 0, "first live insert after error should reuse idx 0");
        assert_eq!(*v_ok, 123);
    }

    // New-slot branch + panic: index 0 must be reusable.
    #[test]
    fn stable_try_insert_with_key_panic_reuses_reserved_new_slot() {
        let map: StableMap<i32> = BoxStableDerefGenMap::new();

        // Again, empty map → "new slot" branch.
        let res = catch_unwind(AssertUnwindSafe(|| {
            let _ = map.try_insert_with_key::<()>(|_k| -> Result<Box<i32>, ()> {
                panic!("boom in new-slot branch");
            });
        }));
        assert!(res.is_err(), "panic should be caught by catch_unwind");

        // Next insert should reuse idx 0, not silently leak it.
        let (k_ok, v_ok) = map.insert(Box::new(123));
        let kd = k_ok.data();

        assert_eq!(kd.idx, 0, "first live insert after panic should reuse idx 0");
        assert_eq!(*v_ok, 123);
    }

use crate::key::DefaultKey;
use crate::stable_deref_gen_map::BoxStableDerefGenMap;
use std::cell::Cell;
use std::fmt::Display;
use std::sync::atomic::{AtomicUsize, Ordering};

#[test]
    fn get_during_insert_returns_none_and_reentrancy_is_ok() {
        let map = BoxStableDerefGenMap::<DefaultKey, String>::new();

        let (k_outer, r_outer) = map.insert_with_key(|k| {
            // During construction, the slot is marked inserting; get() must return None.
            assert!(map.get(k).is_none());

            // Re-entrant insert while the first slot is "inserting".
            let (_k2, r2) = map.insert(Box::new("inner".to_string()));
            assert_eq!(r2.as_str(), "inner");

            Box::new("outer".to_string())
        });

        assert_eq!(r_outer.as_str(), "outer");
        assert_eq!(map.get(k_outer).unwrap().as_str(), "outer");
    }

    #[test]
    fn stable_ref_across_vec_growth() {
        let map = BoxStableDerefGenMap::<DefaultKey, String>::new();

        let (k1, r1) = map.insert(Box::new("A".to_string()));
        let p1 = (r1 as *const String) as usize;

        // Force multiple Vec growths.
        for i in 0..1_000 {
            let _ = map.insert(Box::new(i.to_string()));
        }

        let p1_after = (map.get(k1).unwrap() as *const String) as usize;
        assert_eq!(p1, p1_after, "Boxed location must remain stable");
        assert_eq!(map.get(k1).unwrap().as_str(), "A");
    }

    #[test]
    fn remove_invalidates_old_key_and_reuse_bumps_generation() {
        let mut map = BoxStableDerefGenMap::<DefaultKey, i32>::new();

        let (k1, r1) = map.insert(Box::new(10));
        assert_eq!(*r1, 10);

        // Remove the only element; its index should go to the free list.
        let removed = map.remove(k1).map(|b| *b).unwrap();
        assert_eq!(removed, 10);

        // Old key is now invalid (generation mismatch).
        assert!(map.get(k1).is_none());

        // Insert again; free slot reused -> same idx, bumped generation.
        let (k2, r2) = map.insert(Box::new(20));
        assert_eq!(*r2, 20);

        // We can assert on private fields here because these are unit tests.
        assert_eq!(k1.key_data.idx, k2.key_data.idx, "same slot reused");
        assert_ne!(k1.key_data.generation, k2.key_data.generation, "generation must bump");
    }




    #[test]
    fn stable_get_mut_respects_generation() {
        let map: BoxStableDerefGenMap<DefaultKey, i32> = BoxStableDerefGenMap::new();
        let (k, _) = map.insert(Box::new(1));

        // Move into mutable binding.
        let mut map = map;

        // Mutate via get_mut on a live key.
        *map.get_mut(k).unwrap() = 10;
        assert_eq!(*map.get(k).unwrap(), 10);

        // Remove it; this increments generation and pushes index to free list.
        let removed = map.remove(k).unwrap();
        assert_eq!(*removed, 10);
        assert!(map.get(k).is_none());
        assert!(map.get_mut(k).is_none());

        // Next insert should reuse the same idx but with bumped generation.
        let (k_new, _) = map.insert(Box::new(99));
        let old = k.data();
        let new = k_new.data();

        assert_eq!(old.idx, new.idx);
        assert_ne!(old.generation, new.generation);

        // Stale key must not be usable.
        assert!(map.get(k).is_none());
        assert!(map.get_mut(k).is_none());

        // New key must work.
        assert_eq!(*map.get(k_new).unwrap(), 99);
        *map.get_mut(k_new).unwrap() = 123;
        assert_eq!(*map.get(k_new).unwrap(), 123);
    }

    #[test]
    fn unsized_trait_object_storage() {
        // Test T: ?Sized via a trait object.
        let map: BoxStableDerefGenMap<DefaultKey, dyn Display> = BoxStableDerefGenMap::new();

        let (k, r) = map.insert(Box::new(String::from("hello")) as Box<dyn Display>);
        assert_eq!(r.to_string(), "hello");
        assert_eq!(map.get(k).unwrap().to_string(), "hello");
    }

    #[test]
    fn remove_nonexistent_returns_none() {
        let mut map = BoxStableDerefGenMap::<DefaultKey, i32>::new();

        let bogus = DefaultKey { key_data: KeyData { idx: 999_999, generation: 0 } };
        assert!(map.remove(bogus).is_none());

        let (k, _) = map.insert(Box::new(1));
        let mut bad = k;
        bad.key_data.generation = bad.key_data.generation.wrapping_add(1);
        assert!(map.remove(bad).is_none(), "wrong generation should not remove");
    }


    #[test]
    fn stable_try_insert_with_key_panic_reuses_free_slot() {
        let mut map: StableMap<i32> = BoxStableDerefGenMap::new();

        // Insert one, then remove it so its index goes onto the free list.
        let (k1, _) = map.insert(Box::new(10));

        let old = k1.data();
        assert_eq!(map.remove(k1).map(|b| *b), Some(10));
        assert!(map.get(k1).is_none());

        // This try_insert_with_key will go down the free-slot path and then panic
        // inside the closure. After our fix, the popped index must be returned
        // to the free list even on panic.
        let res = catch_unwind(AssertUnwindSafe(|| {
            let _ = (&map as &StableMap<i32>).try_insert_with_key::<()>(
                |_k| -> Result<Box<i32>, ()> {
                    panic!("boom in free-slot branch");
                },
            );
        }));
        assert!(res.is_err());

        // Now insert again; it should reuse the same index that was freed earlier.
        let (k2, v2) = (&map as &StableMap<i32>)
            .try_insert_with_key::<()>(|_k| Ok(Box::new(99)))
            .unwrap();

        let new = k2.data();
        assert_eq!(new.idx, old.idx, "free-slot index must be reused after panic");
        assert_eq!(*v2, 99);
    }

    #[test]
    fn stable_try_insert_with_key_panic_reuses_reserved_slot() {
        let map: StableMap<i32> = BoxStableDerefGenMap::new();

        // No free slots; this call will go down the "new slot" path and panic
        // inside the closure. After our fix, that reserved slot is returned
        // to the free list and can be reused.
        let res = catch_unwind(AssertUnwindSafe(|| {
            let _ = map.try_insert_with_key::<()>(|_k| -> Result<Box<i32>, ()> {
                panic!("boom in new-slot branch");
            });
        }));
        assert!(res.is_err());

        // Now do a normal insert; it should reuse index 0 rather than silently
        // leaking the reserved slot.
        let (k_ok, v_ok) = map.insert(Box::new(123));
        let kd = k_ok.data();

        assert_eq!(kd.idx, 0, "first slot index should be reused after panic");
        assert_eq!(*v_ok, 123);
    }
    #[test]
    fn drops_happen_on_remove_and_on_map_drop() {
        static DROPS: AtomicUsize = AtomicUsize::new(0);

        struct CountDrop(&'static AtomicUsize);
        impl Drop for CountDrop {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        let drops = &DROPS;
        DROPS.store(0, Ordering::SeqCst);

        let mut map = BoxStableDerefGenMap::<DefaultKey, CountDrop>::new();
        let (k1, _) = map.insert(Box::new(CountDrop(drops)));
        let (_k2, _) = map.insert(Box::new(CountDrop(drops)));
        let (_k3, _) = map.insert(Box::new(CountDrop(drops)));

        // Removing one should drop exactly one.
        assert_eq!(map.remove(k1).is_some(), true);
        assert_eq!(DROPS.load(Ordering::SeqCst), 1);

        // Dropping the map should drop the remaining two.
        drop(map);
        assert_eq!(DROPS.load(Ordering::SeqCst), 3);
    }

#[cfg(test)]
mod tests {
    use super::*;
    use crate::key::DefaultKey;
    use crate::stable_deref_gen_map::BoxStableDerefGenMap;
    use std::collections::HashSet;

    /// After clear(), the map must not reuse any key that existed before.
    #[test]
    fn clear_does_not_reuse_keys_for_live_entries() {
        let mut map: BoxStableDerefGenMap<DefaultKey, i32> = BoxStableDerefGenMap::new();

        const N: usize = 128;

        // Insert N elements and record their keys.
        let mut old_keys = HashSet::new();
        for i in 0..N {
            let (k, r) = map.insert(Box::new(i as i32));
            assert_eq!(*r, i as i32);
            assert!(old_keys.insert(k), "duplicate key during initial inserts");
        }

        assert_eq!(map.len(), N);

        // Clear the map.
        map.clear();
        assert_eq!(map.len(), 0);

        // All old keys must be invalid now.
        for &k in &old_keys {
            assert!(
                map.get(k).is_none(),
                "old key {k:?} should be invalid after clear()"
            );
        }

        // Insert another N elements and collect new keys.
        let mut new_keys = HashSet::new();
        for i in 0..N {
            let (k, r) = map.insert(Box::new(10_000 + i as i32));
            assert_eq!(*r, 10_000 + i as i32);
            assert!(new_keys.insert(k), "duplicate key during second inserts");
        }

        // The sets of keys before and after clear() must be disjoint.
        assert!(
            old_keys.is_disjoint(&new_keys),
            "clear() reused at least one previously-issued key"
        );
    }

    /// Even with removes and reinserts before clear(), no key should be reused after clear().
    #[test]
    fn clear_does_not_reuse_any_previous_key_even_after_prior_removes() {
        let mut map: BoxStableDerefGenMap<DefaultKey, i32> = BoxStableDerefGenMap::new();
        const N: usize = 128;

        let mut all_keys_before_clear = HashSet::new();

        // Insert N, record keys.
        let mut keys = Vec::new();
        for i in 0..N {
            let (k, _) = map.insert(Box::new(i as i32));
            keys.push(k);
            all_keys_before_clear.insert(k);
        }

        // Remove every second key.
        for (idx, &k) in keys.iter().enumerate() {
            if idx % 2 == 0 {
                let removed = map.remove(k);
                assert!(removed.is_some(), "expected key {k:?} to be removable");
            }
        }

        // Insert some more; this will reuse free slots and bump generations.
        for i in 0..N {
            let (k, _) = map.insert(Box::new(1_000 + i as i32));
            all_keys_before_clear.insert(k);
        }

        // Now clear:
        map.clear();
        assert_eq!(map.len(), 0);

        // Insert a new batch after clear.
        let mut new_keys = HashSet::new();
        for i in 0..N {
            let (k, _) = map.insert(Box::new(10_000 + i as i32));
            new_keys.insert(k);
        }

        // No key that ever existed before clear() may be reused.
        assert!(
            all_keys_before_clear.is_disjoint(&new_keys),
            "A key that existed before clear() was reused afterward"
        );
    }
}


    #[test]
    fn nested_try_insert_with_key_uses_distinct_slots() {
        use std::cell::Cell;

        let map: BoxStableDerefGenMap<DefaultKey, i32> = BoxStableDerefGenMap::new();

        // Record the inner key created inside the outer try_insert_with_key closure.
        let inner_key_cell: Cell<Option<DefaultKey>> = Cell::new(None);

        let res: Result<(DefaultKey, &i32), ()> =
            map.try_insert_with_key::<_>(|_outer_key| {
                // Nested insert_with_key inside the closure.
                let (inner_key, inner_ref) =
                    map.insert_with_key(|_k| Box::new(111));
                inner_key_cell.set(Some(inner_key));
                assert_eq!(*inner_ref, 111);

                // Outer value.
                Ok::<Box<i32>, ()>(Box::new(222))
            });

        let (outer_key, outer_ref) = res.unwrap();
        let inner_key = inner_key_cell.get().expect("inner key must be recorded");

        // Both entries must exist and have the correct values.
        assert_eq!(*outer_ref, 222);
        assert_eq!(*map.get(inner_key).unwrap(), 111);

        // They must not alias the same slot anymore.
        let outer_data = outer_key.data();
        let inner_data = inner_key.data();
        assert_ne!(outer_data.idx, inner_data.idx, "outer and inner must use distinct indices");
    }

    #[test]
    fn insert_and_insert_with_match_semantics() {
        let map = BoxStableDerefGenMap::<DefaultKey, String>::new();

        let (k1, r1) = map.insert(Box::new("X".into()));
        let (k2, r2) = map.insert_with_key(|_| Box::new("Y".into()));

        assert_eq!(r1.as_str(), "X");
        assert_eq!(r2.as_str(), "Y");
        assert_eq!(map.get(k1).unwrap().as_str(), "X");
        assert_eq!(map.get(k2).unwrap().as_str(), "Y");
    }


