use crate::map_id::MapId;

#[test]
fn different_map_id_next_calls_get_different_ids() {
    let a = MapId::next();
    let b = MapId::next();
    assert_ne!(a, b);
}

#[test]
fn map_id_is_copy_clone_debug_eq_hash() {
    let id = MapId::next();

    let copy = id;
    assert_eq!(id, copy);

    let clone = id.clone();
    assert_eq!(id, clone);

    let _ = format!("{:?}", id);

    let mut set = std::collections::HashSet::new();
    set.insert(id);
    assert!(set.contains(&id));
}

#[test]
fn from_usize_round_trips() {
    let id = MapId::next();
    let raw = id.get_underlying_non_zero_usize();
    let reconstructed = unsafe { MapId::from_non_zero_usize(raw) };
    assert_eq!(id, reconstructed);
}
