use crate::key::{DefaultKey, Key};
use crate::numeric::Numeric;
use crate::stable_paged_gen_map::DefaultStablePagedGenMap;

type PagedMap = DefaultStablePagedGenMap<DefaultKey, i32>;

    #[test]
    fn retain_keeps_all_in_paged_map() {
        let mut map: PagedMap = DefaultStablePagedGenMap::new();
        let (k1, _) = map.insert(10);
        let (k2, _) = map.insert(20);

        map.retain(|_, v| {
            *v += 1;
            true
        });

        assert_eq!(*map.get(k1).unwrap(), 11);
        assert_eq!(*map.get(k2).unwrap(), 21);
        assert_eq!(map.len(), 2);
    }

    #[test]
    fn retain_removes_some_in_paged_map() {
        let mut map: PagedMap = DefaultStablePagedGenMap::new();

        let (k1, _) = map.insert(1);
        let (k2, _) = map.insert(2);
        let (k3, _) = map.insert(3);

        map.retain(|_, v| *v % 2 == 0);

        assert!(map.get(k1).is_none());
        assert!(map.get(k3).is_none());
        assert_eq!(*map.get(k2).unwrap(), 2);
        assert_eq!(map.len(), 1);
    }

    #[test]
    fn retain_reuses_indices_and_bumps_generation_in_paged_map() {
        let mut map: PagedMap = DefaultStablePagedGenMap::new();

        let (k1, _) = map.insert(42);
        let k1_data = k1.data();

        map.retain(|key, _| key != k1);
        assert!(map.get(k1).is_none());
        assert_eq!(map.len(), 0);

        let (k2, _) = map.insert(99);
        let k2_data = k2.data();

        // Index should be reused, generation must bump.
        assert_eq!(k2_data.idx.into_usize(), k1_data.idx.into_usize());
        assert_ne!(k2_data.generation, k1_data.generation);
        assert_eq!(*map.get(k2).unwrap(), 99);
    }

