pub mod stable_gen_map;



#[cfg(test)]
mod tests {


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

        struct CountDrop(&'static AtomicUsize, u32);
        impl Drop for CountDrop {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }

        let drops = &DROPS;
        DROPS.store(0, Ordering::SeqCst);

        let mut map = StableGenMap::<DefaultKey, CountDrop>::new();
        let (k1, _) = map.insert(Box::new(CountDrop(drops, 1)));
        let (_k2, _) = map.insert(Box::new(CountDrop(drops, 2)));
        let (_k3, _) = map.insert(Box::new(CountDrop(drops, 3)));

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
