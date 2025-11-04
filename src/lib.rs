pub mod stable_gen_map;
pub mod paged_stable_gen_map;



#[cfg(test)]
mod stable_gen_map_tests {


    #[test]
    fn stable_ref_survives_many_vec_resizes() {
        // A big enough count to force multiple Vec growths.
        let map = StableGenMap::<DefaultKey, String>::new();

        let (k, r) = map.insert(Box::new("root".to_string()));
        let p_before = (r as *const String) as usize;

        for i in 0..20_000 {
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
        let (k_new, r_new) = map.insert_with(|k_self| {
            // While inserting, the slot is marked "inserting": get() must hide it.
            assert!(map.get(k_self).is_none());

            // Force many resizes while this slot is still "inserting".
            for i in 0..15_000 {
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

        let (_k, r) = map.insert_with(|k_self| {
            // During the window where is_inserting=true, get() must return None.
            assert!(map.get(k_self).is_none());

            // Trigger considerable internal growth during that window.
            for i in 0..10_000 {
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
        for i in 0..8_000 {
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

        for i in 0..12_000 {
            let _ = map.insert(Box::new(i.to_string()) as Box<dyn Display>);
        }

        let p_after = (map.get(k).unwrap() as *const dyn Display) as *const () as usize;
        assert_eq!(p_before, p_after);
        assert_eq!(map.get(k).unwrap().to_string(), "hello");
    }

    use std::fmt::Display;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use crate::stable_gen_map::{DefaultKey, KeyData, StableGenMap};

    #[test]
    fn get_during_insert_returns_none_and_reentrancy_is_ok() {
        let map = StableGenMap::<DefaultKey, String>::new();

        let (k_outer, r_outer) = map.insert_with(|k| {
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
        for i in 0..20_000 {
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
        let (k2, r2) = map.insert_with(|_| Box::new("Y".into()));

        assert_eq!(r1.as_str(), "X");
        assert_eq!(r2.as_str(), "Y");
        assert_eq!(map.get(k1).unwrap().as_str(), "X");
        assert_eq!(map.get(k2).unwrap().as_str(), "Y");
    }
}

#[cfg(test)]
mod paged_stable_gen_map_tests {
    use std::collections::BTreeSet;
    use std::sync::atomic::{AtomicUsize, Ordering};

    use crate::paged_stable_gen_map::{
        PagedStableGenMap,
        DefaultPagedKey,
        PagedKeyData,
    };

    // 1. First value’s reference must remain stable across many inserts
    //    (Vec<Page<T>> growth + page allocations).
    #[test]
    fn paged_stable_ref_survives_many_vec_and_page_resizes() {
        let map = PagedStableGenMap::<DefaultPagedKey, String>::new();

        let (k, r) = map.insert("root".to_string());
        let p_before = (r as *const String) as usize;

        // Force plenty of internal growth and new pages.
        for i in 0..20_000 {
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
        let (k_new, r_new) = map.insert_with(|k_self| {
            // While inserting, the slot must not be visible.
            assert!(map.get(k_self).is_none());

            // Cause many internal resizes while slot is still "inserting".
            for i in 0..15_000 {
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

        let (_k, r) = map.insert_with(|k_self| {
            // During the window where the slot is logically "inserting",
            // get() must not expose a partially-constructed value.
            assert!(map.get(k_self).is_none());

            for i in 0..10_000 {
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
        for i in 0..8_000 {
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

        let (k_outer, r_outer) = map.insert_with(|k| {
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
        let (k2, r2) = map.insert_with(|_| "Y".into());

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
