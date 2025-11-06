mod paged_stable_gen_map_tests {
    use crate::key::DefaultKey;
    use crate::key::{Key, KeyData};
    use std::cell::Cell;
    use std::panic::{catch_unwind, AssertUnwindSafe};
    use std::sync::atomic::{AtomicUsize, Ordering};
    use crate::numeric::Numeric;
    use crate::paged_stable_gen_map::DEFAULT_SLOTS_NUM_PER_PAGE;
    // try_insert_with_key while iterating with iter()

    // iter() inside try_insert_with_key closure

    use crate::paged_stable_gen_map::{decode_index, encode_index, PagedStableGenMap};


    type PagedMap<T>  = PagedStableGenMap<DefaultKey, T>;

    // New-slot branch + Err: (page=0, idx=0) must be reusable.
    #[test]
    fn paged_try_insert_with_key_err_reuses_reserved_new_slot() {
        let map: PagedMap<i32> = PagedStableGenMap::new();

        // Empty map → allocates first page and first slot, then returns Err.
        let res: Result<(DefaultKey, &i32), &'static str> =
            map.try_insert_with_key(|_k| -> Result<i32, &'static str> {
                Err("oops in paged constructor")
            });

        assert!(res.is_err());

        // Next insert should reuse (page=0, idx=0).
        let (k_ok, v_ok) = map.insert(123);
        let kd = k_ok.data();

        assert_eq!(kd.idx, 0, "first live insert after error should reuse page 0, idx 0");
        assert_eq!(*v_ok, 123);
    }

    // New-slot branch + panic: (page=0, idx=0) must be reusable.
    #[test]
    fn paged_try_insert_with_key_panic_reuses_reserved_new_slot() {
        let map: PagedMap<i32> = PagedStableGenMap::new();

        // Empty map → "new slot" path, then panic inside func.
        let res = catch_unwind(AssertUnwindSafe(|| {
            let _ = map.try_insert_with_key::<()>(|_k| -> Result<i32, ()> {
                panic!("boom in paged new-slot branch");
            });
        }));
        assert!(res.is_err(), "panic should be caught by catch_unwind");

        // First real insert must reuse that first slot.
        let (k_ok, v_ok) = map.insert(123);
        let kd = k_ok.data();

        assert_eq!(kd.idx, 0, "first live insert after panic should reuse page 0, idx 0");
        assert_eq!(*v_ok, 123);
    }


    #[test]
    fn paged_nested_try_insert_with_key_uses_distinct_slots() {
        use std::cell::Cell;

        let map: PagedStableGenMap<DefaultKey, i32> = PagedStableGenMap::new();

        // Record the inner key created inside the outer try_insert_with_key closure.
        let inner_key_cell: Cell<Option<DefaultKey>> = Cell::new(None);

        let res: Result<(DefaultKey, &i32), ()> =
            map.try_insert_with_key::<()>(|_outer_key| {
                // Nested insert_with_key inside the closure.
                let (inner_key, inner_ref) = map.insert_with_key(|_k| 111);
                inner_key_cell.set(Some(inner_key));
                assert_eq!(*inner_ref, 111);

                // Outer value.
                Ok(222)
            });

        let (outer_key, outer_ref) = res.unwrap();
        let inner_key = inner_key_cell.get().expect("inner key must be recorded");

        // Both entries must exist and have the correct values.
        assert_eq!(*outer_ref, 222);
        assert_eq!(*map.get(inner_key).unwrap(), 111);

        // They must not alias the same (page, idx) slot anymore.
        let outer_data = outer_key.data();
        let inner_data = inner_key.data();
        assert!(
            outer_data.idx != inner_data.idx,
            "outer and inner must use distinct (page, idx) pairs"
        );
    }



    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
    struct TestKey {
        data: KeyData<u32, u32>, // adjust KeyData params if needed
    }

    unsafe impl Key for TestKey {
        type Idx = u32;
        type Gen = u32;

        #[inline]
        fn data(&self) -> KeyData<u32, u32> {
            self.data
        }
    }

    impl From<KeyData<u32, u32>> for TestKey {
        fn from(data: KeyData<u32, u32>) -> Self {
            Self { data }
        }
    }

    #[test]
    fn iter_mut_yields_valid_keys_and_values() {

        let mut map = PagedStableGenMap::<TestKey, i32>::new();

        // Insert enough items to span multiple pages
        let mut expected = Vec::new();
        for i in 0..1_000 {
            let (k, v) = map.insert(i);
            assert_eq!(*v, i);
            assert_eq!(i, *map.get(k).unwrap());
            expected.push((k, i));
        }

        expected.sort_by_key(|(k, _)| k.data().idx.into_usize());

        let len = map.len();
        let mut seen = Vec::new();
        for (k, v) in &mut map {
            // Key should decode to something valid
            let coords = decode_index::<_>(k.data().idx, DEFAULT_SLOTS_NUM_PER_PAGE);
            assert!(coords.page_idx < len);

            seen.push((k, *v));
        }

        seen.sort_by_key(|(k, _)| k.data().idx.into_usize());

        assert_eq!(seen.len(), expected.len());
        for ((k_exp, v_exp), (k_seen, v_seen)) in expected.into_iter().zip(seen.into_iter()) {
            assert_eq!(v_seen, v_exp);
            assert_eq!(k_seen.data().generation, k_exp.data().generation);
            assert_eq!(k_seen.data().idx.into_usize(), k_exp.data().idx.into_usize());
        }
    }


    #[test]
    fn remove_reuses_same_slot_with_bumped_generation() {

        let mut map = PagedStableGenMap::<TestKey, i32>::new();



        let (k1, v1) = map.insert(10);
        assert_eq!(*v1, 10);

        let coords1 = decode_index::<_>(k1.data().idx, DEFAULT_SLOTS_NUM_PER_PAGE);
        assert_eq!(map.len(), 1);

        // Remove: old key should become invalid.
        assert_eq!(map.remove(k1), Some(10));
        assert_eq!(map.len(), 0);
        assert!(map.get(k1).is_none());

        // Insert again: should reuse slot, but with a bumped generation.
        let (k2, v2) = map.insert(20);
        assert_eq!(*v2, 20);
        assert_eq!(map.len(), 1);

        let coords2 = decode_index::<_>(k2.data().idx,DEFAULT_SLOTS_NUM_PER_PAGE);

        // Same physical slot (page + slot) reused
        assert_eq!(coords1.page_idx, coords2.page_idx);
        assert_eq!(coords1.slot_idx, coords2.slot_idx);

        // Different generation
        assert_ne!(k1.data().generation, k2.data().generation);
    }


    #[test]
    fn paged_iter_mut_can_modify_all_values() {
        let mut map: PagedMap<i32> = PagedStableGenMap::new();

        for i in 0..40 {
            let (_k, _) = map.insert(i);
        }

        for (_k, v) in map.iter_mut() {
            *v += 1000;
        }

        let mut values: Vec<i32> = (&mut map).into_iter().map(|(_, v)| *v).collect();
        values.sort();
        assert_eq!(values, (1000..1040).collect::<Vec<_>>());
    }

    #[test]
    fn paged_into_iter_consumes_and_yields_owned_values() {
        let mut map: PagedMap<i32> = PagedStableGenMap::new();

        for i in 0..40 {
            let (_k, _) = map.insert(i);
        }

        let mut seen: Vec<i32> = map.into_iter().map(|(_k, v)| v).collect();
        seen.sort();
        assert_eq!(seen.len(), 40);
        assert_eq!(seen[0], 0);
        assert_eq!(seen[39], 39);
    }

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
    fn paged_len_tracks_insert_remove_and_clear() {
        let paged: PagedMap<i32> = PagedStableGenMap::new();
        assert_eq!(paged.len(), 0, "new paged map must start empty");

        let (k1, _) = paged.insert(10);
        assert_eq!(paged.len(), 1, "one insert increments len to 1");

        let (k2, _) = paged.insert(20);
        assert_eq!(paged.len(), 2, "two inserts increments len to 2");

        // Move into mutable binding.
        let mut paged = paged;

        // Removing a live key decrements len.
        assert_eq!(paged.remove(k1), Some(10));
        assert_eq!(paged.len(), 1, "remove must decrement len");

        // Removing again (already removed) must not change len.
        assert!(paged.remove(k1).is_none());
        assert_eq!(paged.len(), 1, "removing non-existent key must not change len");

        // Removing bogus generation must not change len.
        let mut bad = k2;
        bad.key_data.generation = bad.key_data.generation.wrapping_add(1);
        assert!(paged.remove(bad).is_none());
        assert_eq!(paged.len(), 1, "failed remove (generation mismatch) must not change len");

        // clear() must reset len to 0.
        paged.clear();
        assert_eq!(paged.len(), 0, "clear must reset len to 0");
    }

    #[test]
    fn paged_len_unchanged_on_try_insert_new_slot_err_and_panic() {
        let paged: PagedMap<i32> = PagedStableGenMap::new();
        assert_eq!(paged.len(), 0);

        // No free slots yet → this hits the "add new slot/page" branch.
        let res: Result<(DefaultKey, &i32), &'static str> =
            paged.try_insert_with_key(|_k| -> Result<i32, &'static str> {
                Err("oops in paged constructor")
            });

        assert!(res.is_err());
        assert_eq!(paged.len(), 0, "len must stay 0 after Err in new-slot branch");

        // Same idea, but closure panics.
        let res_panic = catch_unwind(AssertUnwindSafe(|| {
            let _ = paged.try_insert_with_key::<()>(|_k| -> Result<i32, ()> {
                panic!("boom in paged new-slot branch");
            });
        }));
        assert!(res_panic.is_err());
        assert_eq!(paged.len(), 0, "len must stay 0 after panic in new-slot branch");

        // After those failures, a normal insert must bump len to 1.
        let (_k_ok, _v_ok) = paged.insert(123);
        assert_eq!(paged.len(), 1, "successful insert after failures must bump len to 1");
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
        let res_err: Result<(DefaultKey, &i32), &'static str> =
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
    fn paged_get_mut_respects_generation() {
        let paged: PagedStableGenMap<DefaultKey,i32> = PagedStableGenMap::new();

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
        let map = PagedStableGenMap::<DefaultKey, String>::new();

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
        let mut map = PagedStableGenMap::<DefaultKey, i32>::new();
        let (k_old, _) = map.insert(111);

        let idx_old = k_old.key_data.idx;

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
        let map = PagedStableGenMap::<DefaultKey, String>::new();

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

    fn idx_of(k: DefaultKey) -> <DefaultKey as Key>::Idx {
        k.key_data.idx
    }


    // 4. Removing a key invalidates it forever, even after lots of inserts
    //    and page growth that reuse free slots.
    #[test]
    fn paged_remove_then_mass_insert_then_reuse_keeps_old_key_invalid() {
        let mut map = PagedStableGenMap::<DefaultKey, i32>::new();

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
        let map = PagedStableGenMap::<DefaultKey, String>::new();

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



    // 7. Remove invalidates the key, and reinsert reuses the same slot but
    //    with a bumped generation (and the same page).
    #[test]
    fn paged_remove_invalidates_old_key_and_reuse_bumps_generation() {
        let mut map = PagedStableGenMap::<DefaultKey, i32>::new();

        let (k1, r1) = map.insert(10);
        assert_eq!(*r1, 10);

        let idx1 = k1.key_data.idx;
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

        assert_ne!(
            k2.key_data.generation, gen1,
            "generation must bump when a slot is reused"
        );
    }

    // 8. Removing a bogus key (wrong page/idx or wrong generation) returns None.
    #[test]
    fn paged_remove_nonexistent_returns_none() {
        let mut map = PagedStableGenMap::<DefaultKey, i32>::new();

        // Completely bogus page/idx.
        let bogus = DefaultKey {
            key_data: KeyData {
                idx: 999_999,
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

        let mut map = PagedStableGenMap::<DefaultKey, CountDrop>::new();
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
        let map = PagedStableGenMap::<DefaultKey, String>::new();

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
        let map = PagedStableGenMap::<DefaultKey, String>::new();

        let (k1, _) = map.insert("hello".to_string());
        let (k2, _) = map.insert("world".to_string());

        assert_eq!(&map[k1], "hello");
        assert_eq!(&map[k2], "world");
    }
}
