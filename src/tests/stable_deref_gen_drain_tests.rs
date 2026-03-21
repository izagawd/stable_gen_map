use crate::key::{DefaultKey, Key};
use crate::key_piece::KeyPiece;
use crate::stable_deref_gen_map::{BoxStableDerefGenMap, StableDerefGenMap};

type Map = BoxStableDerefGenMap<DefaultKey, i32>;

#[test]
fn drain_empty_map() {
    let mut map: Map = StableDerefGenMap::new();
    let items: Vec<_> = map.drain().collect();
    assert!(items.is_empty());
    assert_eq!(map.len(), 0);
}

#[test]
fn drain_yields_all_elements() {
    let mut map: Map = StableDerefGenMap::new();
    let (k1, _) = map.insert(Box::new(10));
    let (k2, _) = map.insert(Box::new(20));
    let (k3, _) = map.insert(Box::new(30));

    let mut items: Vec<_> = map.drain().collect();
    items.sort_by_key(|(_, v)| **v);

    assert_eq!(items.len(), 3);
    assert_eq!((items[0].0, *items[0].1), (k1, 10));
    assert_eq!((items[1].0, *items[1].1), (k2, 20));
    assert_eq!((items[2].0, *items[2].1), (k3, 30));
    assert_eq!(map.len(), 0);
}

#[test]
fn drain_empties_map() {
    let mut map: Map = StableDerefGenMap::new();
    let (k1, _) = map.insert(Box::new(1));
    let (k2, _) = map.insert(Box::new(2));

    let _ = map.drain();

    assert_eq!(map.len(), 0);
    assert!(map.get(k1).is_none());
    assert!(map.get(k2).is_none());
}

#[test]
fn drain_invalidates_old_keys() {
    let mut map: Map = StableDerefGenMap::new();
    let (k1, _) = map.insert(Box::new(42));
    let (k2, _) = map.insert(Box::new(99));

    let _: Vec<_> = map.drain().collect();

    assert!(map.get(k1).is_none());
    assert!(map.get(k2).is_none());
}

#[test]
fn drain_allows_reuse_of_indices() {
    let mut map: Map = StableDerefGenMap::new();
    let (k1, _) = map.insert(Box::new(100));
    let k1_data = k1.data();

    let _: Vec<_> = map.drain().collect();

    let (k2, _) = map.insert(Box::new(200));
    let k2_data = k2.data();

    assert_eq!(k2_data.idx.into_usize(), k1_data.idx.into_usize());
    assert_ne!(k2_data.generation, k1_data.generation);
    assert_eq!(*map.get(k2).unwrap(), 200);
    assert_eq!(map.len(), 1);
}

#[test]
fn drain_with_gaps_from_prior_removes() {
    let mut map: Map = StableDerefGenMap::new();
    let (k1, _) = map.insert(Box::new(1));
    let (_, _) = map.insert(Box::new(2));
    let (k3, _) = map.insert(Box::new(3));

    map.remove(k1);

    let mut items: Vec<_> = map.drain().collect();
    items.sort_by_key(|(_, v)| **v);

    assert_eq!(items.len(), 2);
    assert_eq!(*items[0].1, 2);
    assert_eq!(*items[1].1, 3);
    assert_eq!(map.len(), 0);
    assert!(map.get(k3).is_none());
}

#[test]
fn drain_drop_cleans_up_remaining() {
    let mut map: Map = StableDerefGenMap::new();
    let (k1, _) = map.insert(Box::new(1));
    let (k2, _) = map.insert(Box::new(2));
    let (k3, _) = map.insert(Box::new(3));

    {
        let mut drain = map.drain();
        let _ = drain.next();
    }

    assert_eq!(map.len(), 0);
    assert!(map.get(k1).is_none());
    assert!(map.get(k2).is_none());
    assert!(map.get(k3).is_none());
}

#[test]
fn drain_then_insert_works() {
    let mut map: Map = StableDerefGenMap::new();
    map.insert(Box::new(1));
    map.insert(Box::new(2));

    let _: Vec<_> = map.drain().collect();
    assert_eq!(map.len(), 0);

    let (k, _) = map.insert(Box::new(42));
    assert_eq!(map.len(), 1);
    assert_eq!(*map.get(k).unwrap(), 42);
}

#[test]
fn drain_drops_smart_pointers() {
    use std::cell::Cell;
    use std::rc::Rc;

    let drop_count = Rc::new(Cell::new(0u32));

    struct DropCounter(Rc<Cell<u32>>);
    impl Drop for DropCounter {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }

    let mut map = StableDerefGenMap::<DefaultKey, Box<DropCounter>>::new();
    map.insert(Box::new(DropCounter(drop_count.clone())));
    map.insert(Box::new(DropCounter(drop_count.clone())));
    map.insert(Box::new(DropCounter(drop_count.clone())));

    assert_eq!(drop_count.get(), 0);

    drop(map.drain());

    assert_eq!(drop_count.get(), 3);
    assert_eq!(map.len(), 0);
}
