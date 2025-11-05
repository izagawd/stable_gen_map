pub mod stable_gen_map;
pub mod paged_stable_gen_map;



#[cfg(test)]
mod stable_gen_map_tests {

    // ============================
    // StableGenMap<T> tests
    // ============================

    #[test]
    fn stable_try_insert_with_key_ok_path_new_slot() {
        let map: StableMap<i32> = StableGenMap::new();

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
        let map: StableMap<i32> = StableGenMap::new();

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

    type StableMap<T> = StableGenMap<DefaultKey, T>;

    #[test]
    fn stable_try_insert_with_key_reentrant_and_error_miri_stress() {
        let map: StableMap<i32> = StableGenMap::new();

        // Seed one element that both map and clones can see.
        let (seed_key, _) = map.insert(Box::new(1));

        // We'll record an inner key created inside the closure.
        let inner_key_cell: Cell<Option<DefaultKey>> = Cell::new(None);

        // Outer try_insert_with_key:
        //  - re-enters via insert_with_key
        //  - clones the map inside the closure
        //  - finally returns Err to hit the error path of try_insert_with_key
        let res: Result<(DefaultKey, &i32), &'static str> =
            map.try_insert_with_key(|_outer_k| {
                // Re-entrant insertion into the same map using insert_with_key
                let (inner_k, inner_ref) =
                    map.insert_with_key(|_k2| Box::new(100));
                assert_eq!(*inner_ref, 100);

                inner_key_cell.set(Some(inner_k));

                // Clone inside the closure and read from it.
                let clone = map.clone();
                assert_eq!(*clone.get(seed_key).unwrap(), 1);
                assert_eq!(*clone.get(inner_k).unwrap(), 100);

                // Force the error path.
                Err("boom")
            });

        assert!(res.is_err());

        // After the failed outer insertion, the inner insertion must still be valid
        // and we must not have created a "phantom" extra live element.
        let inner_k = inner_key_cell.get().expect("inner key recorded");

        assert_eq!(*map.get(seed_key).unwrap(), 1);
        assert_eq!(*map.get(inner_k).unwrap(), 100);

        // Count live elements by probing all indices at generation 0.
        // We only inserted twice, never removed, so all live keys are gen=0.
        let mut live = 0;
        let cap = map.capacity();
        for idx in 0..cap {
            let key = DefaultKey {
                key_data: KeyData {
                    idx,
                    generation: 0,
                },
            };
            if map.get(key).is_some() {
                live += 1;
            }
        }

        assert_eq!(live, 2);
    }


    #[test]
    fn stable_ref_survives_many_vec_resizes() {
        // A big enough count to force multiple Vec growths.
        let map = StableGenMap::<DefaultKey, String>::new();

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
        let mut map = StableGenMap::<DefaultKey, i32>::new();
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
        let map = StableGenMap::<DefaultKey, String>::new();

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
        let mut map = StableGenMap::<DefaultKey, i32>::new();

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

        let map: StableGenMap<DefaultKey, dyn Display> = StableGenMap::new();
        let (k, r) = map.insert(Box::new(String::from("hello")) as Box<dyn Display>);
        let p_before = (r as *const dyn Display) as *const () as usize;

        for i in 0..1_000 {
            let _ = map.insert(Box::new(i.to_string()) as Box<dyn Display>);
        }

        let p_after = (map.get(k).unwrap() as *const dyn Display) as *const () as usize;
        assert_eq!(p_before, p_after);
        assert_eq!(map.get(k).unwrap().to_string(), "hello");
    }

    use crate::stable_gen_map::{DefaultKey, Key, KeyData, StableGenMap};
    use std::cell::Cell;
    use std::fmt::Display;
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[test]
    fn get_during_insert_returns_none_and_reentrancy_is_ok() {
        let map = StableGenMap::<DefaultKey, String>::new();

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
        let map = StableGenMap::<DefaultKey, String>::new();

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
        let mut map = StableGenMap::<DefaultKey, i32>::new();

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
    fn stable_clone_inside_insert_with() {
        let map: StableGenMap<DefaultKey, i32> = StableGenMap::new();

        // Seed with one value so we can check visibility from the clone.
        let (k1, _) = map.insert(Box::new(1));

        let (k2, v2) = map.insert_with_key(|k| {
            // Clone *inside* the insert_with closure.
            let clone = map.clone();

            // The clone should see the old element.
            assert_eq!(*clone.get(k1).unwrap(), 1);

            // For this in-progress insertion, the slot hasn't been written yet
            // at the moment we cloned, so it's fine (and expected) if it's None.
            assert!(clone.get(k).is_none());

            // We can freely use the clone: inserting into it should not affect `map`.
            let (ck, cv) = clone.insert(Box::new(999));
            assert_eq!(*cv, 999);
            assert_eq!(*clone.get(ck).unwrap(), 999);

            // Return the value for the original map's insert.
            Box::new(2)
        });

        // After insert_with finishes, the original map must be consistent.
        assert_eq!(*v2, 2);
        assert_eq!(*map.get(k1).unwrap(), 1);
        assert_eq!(*map.get(k2).unwrap(), 2);
    }
    #[test]
    fn stable_clone_and_get_mut_are_independent() {
        let map: StableGenMap<DefaultKey, i32> = StableGenMap::new();

        // Insert a couple of values; ignore the &T return so we don't keep borrows alive.
        let (k1, _) = map.insert(Box::new(10));
        let (k2, _) = map.insert(Box::new(20));

        // Clone while we still only have an &StableMap.
        let mut clone = map.clone();

        // Now move the original into a mutable binding.
        let mut map = map;

        // Sanity: both maps see the same initial values.
        assert_eq!(*map.get(k1).unwrap(), 10);
        assert_eq!(*map.get(k2).unwrap(), 20);
        assert_eq!(*clone.get(k1).unwrap(), 10);
        assert_eq!(*clone.get(k2).unwrap(), 20);

        // Mutate original via get_mut.
        *map.get_mut(k1).unwrap() = 100;
        *map.get_mut(k2).unwrap() = 200;

        // Original changed...
        assert_eq!(*map.get(k1).unwrap(), 100);
        assert_eq!(*map.get(k2).unwrap(), 200);

        // ...clone unchanged (deep copy, not shared storage).
        assert_eq!(*clone.get(k1).unwrap(), 10);
        assert_eq!(*clone.get(k2).unwrap(), 20);

        // Mutate clone separately, still no cross-effects.
        *clone.get_mut(k1).unwrap() = -1;
        assert_eq!(*clone.get(k1).unwrap(), -1);
        assert_eq!(*map.get(k1).unwrap(), 100);
    }

    #[test]
    fn stable_get_mut_respects_generation() {
        let map: StableGenMap<DefaultKey, i32> = StableGenMap::new();
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
        let map: StableGenMap<DefaultKey, dyn Display> = StableGenMap::new();

        let (k, r) = map.insert(Box::new(String::from("hello")) as Box<dyn Display>);
        assert_eq!(r.to_string(), "hello");
        assert_eq!(map.get(k).unwrap().to_string(), "hello");
    }

    #[test]
    fn remove_nonexistent_returns_none() {
        let mut map = StableGenMap::<DefaultKey, i32>::new();

        let bogus = DefaultKey { key_data: KeyData { idx: 999_999, generation: 0 } };
        assert!(map.remove(bogus).is_none());

        let (k, _) = map.insert(Box::new(1));
        let mut bad = k;
        bad.key_data.generation = bad.key_data.generation.wrapping_add(1);
        assert!(map.remove(bad).is_none(), "wrong generation should not remove");
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

        let mut map = StableGenMap::<DefaultKey, CountDrop>::new();
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

    #[test]
    fn insert_and_insert_with_match_semantics() {
        let map = StableGenMap::<DefaultKey, String>::new();

        let (k1, r1) = map.insert(Box::new("X".into()));
        let (k2, r2) = map.insert_with_key(|_| Box::new("Y".into()));

        assert_eq!(r1.as_str(), "X");
        assert_eq!(r2.as_str(), "Y");
        assert_eq!(map.get(k1).unwrap().as_str(), "X");
        assert_eq!(map.get(k2).unwrap().as_str(), "Y");
    }
}

#[cfg(test)]
mod paged_stable_gen_map_tests {
    use std::cell::Cell;
    use std::collections::BTreeSet;
    use std::sync::atomic::{AtomicUsize, Ordering};

    use crate::paged_stable_gen_map::{DefaultPagedKey, PagedKey, PagedKeyData, PagedStableGenMap};
    type PagedMap<T>  = PagedStableGenMap<DefaultPagedKey, T>;

    #[test]
    fn paged_try_insert_with_key_ok_path_new_page_slot() {
        let paged: PagedMap<i32> = PagedStableGenMap::new();

        // OK path with a brand new map (no free slots, allocate in first page).
        let (k, v) = paged
            .try_insert_with_key(|_k| -> Result<i32, &'static str> {
                Ok(10)
            })
            .unwrap();

        assert_eq!(*v, 10);
        assert_eq!(*paged.get(k).unwrap(), 10);
    }

    #[test]
    fn paged_try_insert_with_key_error_reuses_free_slot() {
        let paged: PagedMap<i32> = PagedStableGenMap::new();

        // First insert through the simple insert API so we can remove it.
        let (k1, _) = paged.insert(1);

        // Move to a mutable binding for remove.
        let mut paged = paged;

        let old_data = k1.data();
        let removed = paged.remove(k1).unwrap();
        assert_eq!(removed, 1);
        assert!(paged.get(k1).is_none());

        // Now there is exactly one free slot recorded in `free` for that (page, idx).
        let res_err: Result<(DefaultPagedKey, &i32), &'static str> =
            (&paged as &PagedMap<i32>)
                .try_insert_with_key(|_k| -> Result<i32, &'static str> {
                    Err("oops")
                });

        assert!(res_err.is_err());

        // Next successful try_insert_with_key should reuse the same (page, idx),
        // with the bumped generation from remove.
        let (k2, v2) =
            (&paged as &PagedMap<i32>)
                .try_insert_with_key::<()>(|_k| Ok(99))
                .unwrap();

        let new_data = k2.data();

        assert_eq!(old_data.page, new_data.page);
        assert_eq!(old_data.idx, new_data.idx);
        assert_ne!(old_data.generation, new_data.generation);

        assert_eq!(*v2, 99);
        assert_eq!(*paged.get(k2).unwrap(), 99);

        // Old key is stale.
        assert!(paged.get(k1).is_none());
        assert!(paged.get_mut(k1).is_none());
        assert!(paged.remove(k1).is_none());
    }

    #[test]
    fn paged_try_insert_with_key_reentrant_and_error_miri_stress() {
        let paged: PagedMap<i32> = PagedStableGenMap::new();

        // Seed one element.
        let (seed_key, _) = paged.insert(1);

        let inner_key_cell: Cell<Option<DefaultPagedKey>> = Cell::new(None);

        let res: Result<(DefaultPagedKey, &i32), &'static str> =
            paged.try_insert_with_key(|_outer_k| {
                // Re-entrant insertion into same map using insert_with_key.
                let (inner_k, inner_ref) =
                    paged.insert_with_key(|_k2| 100);
                assert_eq!(*inner_ref, 100);

                inner_key_cell.set(Some(inner_k));

                // Clone inside the closure and read keys.
                let clone = paged.clone();
                assert_eq!(*clone.get(seed_key).unwrap(), 1);
                assert_eq!(*clone.get(inner_k).unwrap(), 100);

                // Force the error path in the outer try_insert_with_key.
                Err("boom")
            });

        assert!(res.is_err());

        // After error, the inner insertion must still be valid.
        let inner_k = inner_key_cell.get().expect("inner key recorded");

        assert_eq!(*paged.get(seed_key).unwrap(), 1);
        assert_eq!(*paged.get(inner_k).unwrap(), 100);
    }
    #[test]
    fn paged_clone_inside_insert_with() {
        let paged: PagedStableGenMap<DefaultPagedKey, i32> = PagedStableGenMap::new();

        // Seed with one value.
        let (k1, _) = paged.insert(1);

        let (k2, v2) = paged.insert_with_key(|k| {
            // Clone *inside* the insert_with closure.
            let clone = paged.clone();

            // Clone must see the existing value.
            assert_eq!(*clone.get(k1).unwrap(), 1);

            // Same reasoning as above: the current insertion's slot doesn't
            // exist / isn't initialized yet in the clone.
            assert!(clone.get(k).is_none());

            // Use the clone independently.
            let (ck, cv) = clone.insert(999);
            assert_eq!(*cv, 999);
            assert_eq!(*clone.get(ck).unwrap(), 999);

            // Return the value for the original map.
            2
        });

        // Original paged map must be consistent after closure returns.
        assert_eq!(*v2, 2);
        assert_eq!(*paged.get(k1).unwrap(), 1);
        assert_eq!(*paged.get(k2).unwrap(), 2);
    }

    #[test]
    fn paged_clone_and_get_mut_are_independent() {
        let paged: PagedStableGenMap<DefaultPagedKey, i32> = PagedStableGenMap::new();

        // Insert enough elements to force multiple pages (first page size is 32).
        let mut keys = Vec::new();
        for i in 0..40 {
            let (k, _) = paged.insert(i as i32);
            keys.push(k);
        }

        // Clone while we only have &PagedMap.
        let mut clone = paged.clone();

        // Move original into a mutable binding.
        let mut paged = paged;

        // Mutate every even index in the original via get_mut.
        for (idx, &key) in keys.iter().enumerate() {
            if idx % 2 == 0 {
                *paged.get_mut(key).unwrap() += 1000;
            }
        }

        // Check that original changed only on even indices, clone is untouched.
        for (idx, &key) in keys.iter().enumerate() {
            let orig = *paged.get(key).unwrap();
            let cloned = *clone.get(key).unwrap();

            if idx % 2 == 0 {
                assert_eq!(cloned, idx as i32);              // clone unchanged
                assert_eq!(orig, idx as i32 + 1000);         // original modified
            } else {
                assert_eq!(orig, idx as i32);                // original untouched
                assert_eq!(cloned, idx as i32);              // clone same
            }
        }

        // Also check that removing from original doesn't affect clone.
        let k0 = keys[0];
        let removed = paged.remove(k0).unwrap();
        assert_eq!(removed, 0 + 1000);
        assert!(paged.get(k0).is_none());
        assert!(clone.get(k0).is_some());
        assert_eq!(*clone.get(k0).unwrap(), 0);
    }

    #[test]
    fn paged_get_mut_respects_generation() {
        let paged: PagedStableGenMap<DefaultPagedKey,i32> = PagedStableGenMap::new();

        let (k1, _) = paged.insert(1);
        let (k2, _) = paged.insert(2);

        let mut paged = paged;

        // Mutate via get_mut on live keys.
        *paged.get_mut(k1).unwrap() = 10;
        *paged.get_mut(k2).unwrap() = 20;
        assert_eq!(*paged.get(k1).unwrap(), 10);
        assert_eq!(*paged.get(k2).unwrap(), 20);

        // Remove k1; generation for that slot should bump and the slot becomes free.
        let removed = paged.remove(k1).unwrap();
        assert_eq!(removed, 10);
        assert!(paged.get(k1).is_none());
        assert!(paged.get_mut(k1).is_none());

        // Next insert should reuse the same (page, idx) with incremented generation.
        let (k1_new, _) = paged.insert(99);
        let old = k1.data();
        let new = k1_new.data();

        assert_eq!(old.page, new.page);
        assert_eq!(old.idx, new.idx);
        assert_ne!(old.generation, new.generation);

        // Stale key must fail.
        assert!(paged.get(k1).is_none());
        assert!(paged.get_mut(k1).is_none());

        // New key must work.
        assert_eq!(*paged.get(k1_new).unwrap(), 99);
        *paged.get_mut(k1_new).unwrap() = 123;
        assert_eq!(*paged.get(k1_new).unwrap(), 123);
    }

    // 1. First value’s reference must remain stable across many inserts
    //    (Vec<Page<T>> growth + page allocations).
    #[test]
    fn paged_stable_ref_survives_many_vec_and_page_resizes() {
        let map = PagedStableGenMap::<DefaultPagedKey, String>::new();

        let (k, r) = map.insert("root".to_string());
        let p_before = (r as *const String) as usize;

        // Force plenty of internal growth and new pages.
        for i in 0..1_000 {
            let s = i.to_string();
            let _ = map.insert(s);
        }

        let p_after = (map.get(k).unwrap() as *const String) as usize;
        assert_eq!(p_before, p_after, "reference address must remain stable");
        assert_eq!(map.get(k).unwrap().as_str(), "root");
    }

    // 2. Free list reuse + re-entrant insert_with while resizing.
    //    - Slot freed by remove is reused.
    //    - Generation is bumped.
    //    - Page + idx stay the same.
    //    - get() returns None during construction.
    #[test]
    fn paged_reentrant_insert_with_reuses_freed_slot_even_if_vec_resizes() {
        let mut map = PagedStableGenMap::<DefaultPagedKey, i32>::new();
        let (k_old, _) = map.insert(111);

        let idx_old = k_old.key_data.idx;
        let page_old = k_old.key_data.page;
        let gen_old = k_old.key_data.generation;

        // Free one slot.
        assert_eq!(map.remove(k_old), Some(111));

        // Reinsert into the freed slot using insert_with; inside, blow up the Vec.
        let (k_new, r_new) = map.insert_with_key(|k_self| {
            // While inserting, the slot must not be visible.
            assert!(map.get(k_self).is_none());

            // Cause many internal resizes while slot is still "inserting".
            for i in 0..1_000{
                let _ = map.insert(i);
            }

            222
        });

        assert_eq!(*r_new, 222);
        assert_eq!(map.get(k_new), Some(&222));

        // Same page + index should be reused, but generation must bump.
        assert_eq!(k_new.key_data.idx, idx_old, "same index reused");
        assert_eq!(k_new.key_data.page, page_old, "same page reused");
        assert_ne!(
            k_new.key_data.generation,
            gen_old,
            "generation must bump when slot is reused"
        );
    }

    // 3. get() returns None for the key being constructed inside insert_with,
    //    even if we trigger a lot of resizes while in-flight.
    #[test]
    fn paged_get_returns_none_during_insert_even_while_resizing() {
        let map = PagedStableGenMap::<DefaultPagedKey, String>::new();

        let (_k, r) = map.insert_with_key(|k_self| {
            // During the window where the slot is logically "inserting",
            // get() must not expose a partially-constructed value.
            assert!(map.get(k_self).is_none());

            for i in 0..1_000 {
                let _ = map.insert(i.to_string());
            }

            "done".to_string()
        });

        assert_eq!(r.as_str(), "done");
    }
    // Helper to make reading key internals less noisy.
    fn page_of(k: DefaultPagedKey) -> usize {
        k.key_data.page
    }
    fn idx_of(k: DefaultPagedKey) -> usize {
        k.key_data.idx
    }
    /// 1. First page should have capacity 32,assuming no initial page was allocated:
    ///    - The first 32 inserts must all be on page 0.
    ///    - Their indices are in [0, 32).
    ///    - The 33rd insert must be on page 1.
    #[test]
    fn paged_first_page_capacity_is_32() {
        let map = PagedStableGenMap::<DefaultPagedKey, u32>::new();

        let mut first_page_keys = Vec::new();

        for i in 0..32 {
            let (k, _) = map.insert(i);
            first_page_keys.push(k);
        }

        // All first 32 entries must be on page 0 and have idx < 32.
        for (i, k) in first_page_keys.iter().enumerate() {
            assert_eq!(
                page_of(*k),
                0,
                "key {} should still be on page 0 (first page)",
                i
            );
            assert!(
                idx_of(*k) < 32,
                "key {} should have idx < 32, got {}",
                i,
                idx_of(*k)
            );
        }

        // Next insert should land on the second page.
        let (k_next, _) = map.insert(32);
        assert_eq!(
            page_of(k_next),
            1,
            "33rd element should start a new page (page 1)"
        );
    }

    /// 2. Second page should have capacity 64, assuming no initial page was allocated:
    ///    - Inserts 32..(32+64) must be on page 1.
    ///    - Their idx are in [0, 64).
    #[test]
    fn paged_second_page_capacity_is_64() {
        let map = PagedStableGenMap::<DefaultPagedKey, u32>::new();

        // Fill first page.
        for i in 0..32 {
            let (_k, _) = map.insert(i);
        }

        let mut second_page_keys = Vec::new();
        for i in 32..(32 + 64) {
            let (k, _) = map.insert(i);
            second_page_keys.push(k);
        }

        for (i, k) in second_page_keys.iter().enumerate() {
            assert_eq!(
                page_of(*k),
                1,
                "value {} (global idx {}) should be on page 1",
                i,
                i + 32
            );
            assert!(
                idx_of(*k) < 64,
                "value {} on page 1 should have idx < 64, got {}",
                i,
                idx_of(*k)
            );
        }
    }
    // 4. Removing a key invalidates it forever, even after lots of inserts
    //    and page growth that reuse free slots.
    #[test]
    fn paged_remove_then_mass_insert_then_reuse_keeps_old_key_invalid() {
        let mut map = PagedStableGenMap::<DefaultPagedKey, i32>::new();

        let (k1, _) = map.insert(1);
        assert_eq!(map.remove(k1), Some(1));
        assert!(map.get(k1).is_none(), "old key must be invalid right after remove");

        // Force lots of growth; free list should be consumed at some point.
        for i in 0..1_000 {
            let _ = map.insert(i as i32);
        }

        // Even after reuse of internal slots, the old key must remain invalid.
        assert!(map.get(k1).is_none(), "old key must remain invalid after reuse");
    }

    // 5. Re-entrant insert_with that calls insert() inside the closure.
    //    get() must still return None during the outer insert, and both
    //    values must end up visible afterwards.
    #[test]
    fn paged_get_during_insert_returns_none_and_reentrancy_is_ok() {
        let map = PagedStableGenMap::<DefaultPagedKey, String>::new();

        let (k_outer, r_outer) = map.insert_with_key(|k| {
            // During construction, the slot is "inserting"; get() must return None.
            assert!(map.get(k).is_none());

            // Re-entrant insert while the first slot is "inserting".
            let (_k2, r2) = map.insert("inner".to_string());
            assert_eq!(r2.as_str(), "inner");

            "outer".to_string()
        });

        assert_eq!(r_outer.as_str(), "outer");
        assert_eq!(map.get(k_outer).unwrap().as_str(), "outer");
    }

    // 6. Explicitly check that multiple pages are created and that all
    //    keys still resolve correctly after crossing page boundaries.
    #[test]
    fn paged_multiple_pages_created_and_all_keys_stay_valid() {
        let map = PagedStableGenMap::<DefaultPagedKey, u32>::new();

        let mut keys = Vec::new();
        let total = 64u32;

        for i in 0..total {
            let (k, r) = map.insert(i);
            assert_eq!(*r, i);
            keys.push(k);
        }

        // We should have allocated at least two distinct pages.
        let mut pages = BTreeSet::new();
        for k in &keys {
            pages.insert(k.key_data.page);
        }

        assert!(
            pages.len() >= 2,
            "expected at least two pages for {} inserts, got pages: {:?}",
            total,
            pages
        );

        // All keys must still refer to the correct values.
        for (i, k) in keys.iter().enumerate() {
            assert_eq!(
                map.get(*k),
                Some(&(i as u32)),
                "key at index {} should map to {}",
                i,
                i
            );
        }
    }

    // 7. Remove invalidates the key, and reinsert reuses the same slot but
    //    with a bumped generation (and the same page).
    #[test]
    fn paged_remove_invalidates_old_key_and_reuse_bumps_generation() {
        let mut map = PagedStableGenMap::<DefaultPagedKey, i32>::new();

        let (k1, r1) = map.insert(10);
        assert_eq!(*r1, 10);

        let idx1 = k1.key_data.idx;
        let page1 = k1.key_data.page;
        let gen1 = k1.key_data.generation;

        // Remove the only element; its index should go to the free list.
        let removed = map.remove(k1).unwrap();
        assert_eq!(removed, 10);

        // Old key is now invalid (generation mismatch).
        assert!(map.get(k1).is_none());

        // Insert again; free slot reused -> same idx/page, bumped generation.
        let (k2, r2) = map.insert(20);
        assert_eq!(*r2, 20);

        assert_eq!(k2.key_data.idx, idx1, "same slot reused (idx)");
        assert_eq!(k2.key_data.page, page1, "same slot reused (page)");
        assert_ne!(
            k2.key_data.generation, gen1,
            "generation must bump when a slot is reused"
        );
    }

    // 8. Removing a bogus key (wrong page/idx or wrong generation) returns None.
    #[test]
    fn paged_remove_nonexistent_returns_none() {
        let mut map = PagedStableGenMap::<DefaultPagedKey, i32>::new();

        // Completely bogus page/idx.
        let bogus = DefaultPagedKey {
            key_data: PagedKeyData {
                idx: 999_999,
                page: 999_999,
                generation: 0,
            },
        };
        assert!(map.remove(bogus).is_none());

        // Wrong generation for an otherwise valid slot.
        let (k, _) = map.insert(1);
        let mut bad = k;
        bad.key_data.generation = bad.key_data.generation.wrapping_add(1);
        assert!(
            map.remove(bad).is_none(),
            "wrong generation should not remove anything"
        );
    }

    // 9. Drops:
    //    - Removing a value drops it once.
    //    - Dropping the map drops all remaining live values exactly once.
    #[test]
    fn paged_drops_happen_on_remove_and_on_map_drop() {
        static DROPS: AtomicUsize = AtomicUsize::new(0);

        struct CountDrop(&'static AtomicUsize, u32);
        impl Drop for CountDrop {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        let drops = &DROPS;
        DROPS.store(0, Ordering::SeqCst);

        let mut map = PagedStableGenMap::<DefaultPagedKey, CountDrop>::new();
        let (k1, _) = map.insert(CountDrop(drops, 1));

        let (_k2, _) = map.insert(CountDrop(drops, 2));
        let (_k3, _) = map.insert(CountDrop(drops, 3));

        // Removing one should drop exactly one.
        assert_eq!(map.remove(k1).is_some(), true);
        assert_eq!(DROPS.load(Ordering::SeqCst), 1);

        // Dropping the map should drop the remaining two.
        drop(map);
        assert_eq!(DROPS.load(Ordering::SeqCst), 3);
    }

    // 10. insert() and insert_with() must have consistent semantics.
    #[test]
    fn paged_insert_and_insert_with_match_semantics() {
        let map = PagedStableGenMap::<DefaultPagedKey, String>::new();

        let (k1, r1) = map.insert("X".into());
        let (k2, r2) = map.insert_with_key(|_| "Y".into());

        assert_eq!(r1.as_str(), "X");
        assert_eq!(r2.as_str(), "Y");
        assert_eq!(map.get(k1).unwrap().as_str(), "X");
        assert_eq!(map.get(k2).unwrap().as_str(), "Y");
    }

    // 11. Sanity check for the Index<K> impl.
    #[test]
    fn paged_index_operator_works() {
        let map = PagedStableGenMap::<DefaultPagedKey, String>::new();

        let (k1, _) = map.insert("hello".to_string());
        let (k2, _) = map.insert("world".to_string());

        assert_eq!(&map[k1], "hello");
        assert_eq!(&map[k2], "world");
    }
}
