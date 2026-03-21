use crate::key::{DefaultKey, Key};
use crate::key_piece::KeyPiece;
use crate::stable_gen_map::StableGenMap;

type Map = StableGenMap<DefaultKey, i32>;

#[test]
fn drain_empty_map() {
    let mut map: Map = StableGenMap::new();
    let items: Vec<_> = map.drain().collect();
    assert!(items.is_empty());
    assert_eq!(map.len(), 0);
}

#[test]
fn drain_yields_all_elements() {
    let mut map: Map = StableGenMap::new();
    let (k1, _) = map.insert(10);
    let (k2, _) = map.insert(20);
    let (k3, _) = map.insert(30);

    let mut items: Vec<_> = map.drain().collect();
    items.sort_by_key(|(_, v)| *v);

    assert_eq!(items.len(), 3);
    assert_eq!(items[0], (k1, 10));
    assert_eq!(items[1], (k2, 20));
    assert_eq!(items[2], (k3, 30));
    assert_eq!(map.len(), 0);
}

#[test]
fn drain_empties_map() {
    let mut map: Map = StableGenMap::new();
    let (k1, _) = map.insert(1);
    let (k2, _) = map.insert(2);

    let _ = map.drain();

    assert_eq!(map.len(), 0);
    assert!(map.get(k1).is_none());
    assert!(map.get(k2).is_none());
}

#[test]
fn drain_invalidates_old_keys() {
    let mut map: Map = StableGenMap::new();
    let (k1, _) = map.insert(42);
    let (k2, _) = map.insert(99);

    let _: Vec<_> = map.drain().collect();

    assert!(map.get(k1).is_none());
    assert!(map.get(k2).is_none());
}

#[test]
fn drain_allows_reuse_of_indices() {
    let mut map: Map = StableGenMap::new();
    let (k1, _) = map.insert(100);
    let k1_data = k1.data();

    let _: Vec<_> = map.drain().collect();

    let (k2, _) = map.insert(200);
    let k2_data = k2.data();

    // Index should be reused, generation must bump.
    assert_eq!(k2_data.idx.into_usize(), k1_data.idx.into_usize());
    assert_ne!(k2_data.generation, k1_data.generation);
    assert_eq!(*map.get(k2).unwrap(), 200);
    assert_eq!(map.len(), 1);
}

#[test]
fn drain_with_gaps_from_prior_removes() {
    let mut map: Map = StableGenMap::new();
    let (k1, _) = map.insert(1);
    let (_, _) = map.insert(2);
    let (k3, _) = map.insert(3);

    // Remove the middle element to create a gap.
    map.remove(k1);

    let mut items: Vec<_> = map.drain().collect();
    items.sort_by_key(|(_, v)| *v);

    assert_eq!(items.len(), 2);
    assert_eq!(items[0].1, 2);
    assert_eq!(items[1].1, 3);
    assert_eq!(map.len(), 0);
    assert!(map.get(k3).is_none());
}

#[test]
fn drain_drop_cleans_up_remaining() {
    let mut map: Map = StableGenMap::new();
    let (k1, _) = map.insert(1);
    let (k2, _) = map.insert(2);
    let (k3, _) = map.insert(3);

    // Only consume one element, then drop the iterator.
    {
        let mut drain = map.drain();
        let _ = drain.next(); // consume one
        // drop here — remaining elements should still be removed
    }

    assert_eq!(map.len(), 0);
    assert!(map.get(k1).is_none());
    assert!(map.get(k2).is_none());
    assert!(map.get(k3).is_none());
}

#[test]
fn drain_then_insert_works() {
    let mut map: Map = StableGenMap::new();
    map.insert(1);
    map.insert(2);

    let _: Vec<_> = map.drain().collect();
    assert_eq!(map.len(), 0);

    let (k, _) = map.insert(42);
    assert_eq!(map.len(), 1);
    assert_eq!(*map.get(k).unwrap(), 42);
}

#[test]
fn drain_drops_values() {
    use std::cell::Cell;
    use std::rc::Rc;

    let drop_count = Rc::new(Cell::new(0u32));

    struct DropCounter(Rc<Cell<u32>>);
    impl Drop for DropCounter {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }

    let mut map = StableGenMap::<DefaultKey, DropCounter>::new();
    map.insert(DropCounter(drop_count.clone()));
    map.insert(DropCounter(drop_count.clone()));
    map.insert(DropCounter(drop_count.clone()));

    assert_eq!(drop_count.get(), 0);

    // Drain but don't collect — drop the drain iterator immediately.
    drop(map.drain());

    assert_eq!(drop_count.get(), 3);
    assert_eq!(map.len(), 0);
}
