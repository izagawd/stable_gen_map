use crate::key::{DefaultKey, Key};
use crate::key_piece::KeyPiece;
use crate::stable_deref_gen_map::{BoxStableDerefGenMap, StableDerefGenMap};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

type Map = BoxStableDerefGenMap<DefaultKey, i32>;

/// Shared ledger that records exactly which instances have been dropped,
/// and panics on double-drop so a test failure is immediate rather than
/// silently producing a wrong count.
#[derive(Clone)]
struct DropTracker {
    /// id → number of times drop was called
    drops: Rc<RefCell<HashMap<u32, u32>>>,
    next_id: Rc<RefCell<u32>>,
}

impl DropTracker {
    fn new() -> Self {
        Self {
            drops: Rc::new(RefCell::new(HashMap::new())),
            next_id: Rc::new(RefCell::new(0)),
        }
    }

    fn make_item(&self) -> Box<DropItem> {
        let mut next = self.next_id.borrow_mut();
        let id = *next;
        *next += 1;
        Box::new(DropItem {
            id,
            drops: self.drops.clone(),
        })
    }

    fn total_dropped(&self) -> usize {
        self.drops.borrow().len()
    }

    fn assert_all_dropped_exactly_once(&self, n: u32) {
        let drops = self.drops.borrow();
        for id in 0..n {
            let count = drops.get(&id).copied().unwrap_or(0);
            assert_eq!(
                count, 1,
                "instance {id} was dropped {count} times (expected exactly 1)"
            );
        }
        assert_eq!(drops.len(), n as usize);
    }

    fn assert_none_dropped(&self) {
        assert!(
            self.drops.borrow().is_empty(),
            "expected no drops yet, but {} instances were dropped",
            self.drops.borrow().len()
        );
    }
}

struct DropItem {
    id: u32,
    drops: Rc<RefCell<HashMap<u32, u32>>>,
}

impl Drop for DropItem {
    fn drop(&mut self) {
        let mut map = self.drops.borrow_mut();
        let count = map.entry(self.id).or_insert(0);
        *count += 1;
        assert!(
            *count <= 1,
            "DOUBLE DROP on instance {} (dropped {} times)",
            self.id,
            *count
        );
    }
}

// ── basic behaviour tests (Box<i32>, no drop tracking needed) ───────

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

// ── drop-correctness tests (per-instance tracking) ──────────────────

#[test]
fn drain_zero_consumption_drops_each_exactly_once() {
    let tracker = DropTracker::new();

    let mut map = StableDerefGenMap::<DefaultKey, Box<DropItem>>::new();
    map.insert(tracker.make_item());
    map.insert(tracker.make_item());
    map.insert(tracker.make_item());

    tracker.assert_none_dropped();

    drop(map.drain());

    tracker.assert_all_dropped_exactly_once(3);
    assert_eq!(map.len(), 0);
}

#[test]
fn drain_partial_consumption_drops_each_exactly_once() {
    let tracker = DropTracker::new();

    let mut map = StableDerefGenMap::<DefaultKey, Box<DropItem>>::new();
    for _ in 0..5 {
        map.insert(tracker.make_item());
    }

    tracker.assert_none_dropped();

    {
        let mut drain = map.drain();
        drop(drain.next().unwrap());
        drop(drain.next().unwrap());
        assert_eq!(tracker.total_dropped(), 2);
    }

    tracker.assert_all_dropped_exactly_once(5);
    assert_eq!(map.len(), 0);
}

#[test]
fn drain_full_consumption_drops_each_exactly_once() {
    let tracker = DropTracker::new();

    let mut map = StableDerefGenMap::<DefaultKey, Box<DropItem>>::new();
    for _ in 0..4 {
        map.insert(tracker.make_item());
    }

    tracker.assert_none_dropped();

    let collected: Vec<_> = map.drain().collect();
    tracker.assert_none_dropped();

    drop(collected);
    tracker.assert_all_dropped_exactly_once(4);
    assert_eq!(map.len(), 0);
}

#[test]
fn drain_with_gaps_drops_only_occupied_exactly_once() {
    let tracker = DropTracker::new();

    let mut map = StableDerefGenMap::<DefaultKey, Box<DropItem>>::new();
    let (k0, _) = map.insert(tracker.make_item()); // id 0
    let (_, _) = map.insert(tracker.make_item()); // id 1
    let (_, _) = map.insert(tracker.make_item()); // id 2

    map.remove(k0);
    assert_eq!(tracker.total_dropped(), 1);

    drop(map.drain());

    tracker.assert_all_dropped_exactly_once(3);
    assert_eq!(map.len(), 0);
}

#[test]
fn drain_does_not_double_drop_after_map_drop() {
    let tracker = DropTracker::new();

    let mut map = StableDerefGenMap::<DefaultKey, Box<DropItem>>::new();
    for _ in 0..3 {
        map.insert(tracker.make_item());
    }

    let collected: Vec<_> = map.drain().collect();

    // Dropping the map after drain must NOT re-drop the values.
    drop(map);
    tracker.assert_none_dropped();

    drop(collected);
    tracker.assert_all_dropped_exactly_once(3);
}
