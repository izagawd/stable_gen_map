use crate::map_id::{MapId, MapIdState};

#[test]
fn map_id_starts_at_none() {
    let state = MapIdState::new();
    assert!(state.current_id().is_none());
}

#[test]
fn ensure_id_assigns_on_first_call() {
    let state = MapIdState::new();
    let id = state.ensure_id();
    assert!(id.get_underlying_usize() != 0);
    assert_eq!(state.current_id(), Some(id));
}

#[test]
fn ensure_id_returns_same_on_subsequent_calls() {
    let state = MapIdState::new();
    let first = state.ensure_id();
    let second = state.ensure_id();
    assert_eq!(first, second);
}

#[test]
fn different_states_get_different_ids() {
    let a = MapIdState::new();
    let b = MapIdState::new();
    assert_ne!(a.ensure_id(), b.ensure_id());
}

#[test]
fn many_states_all_unique() {
    let ids: Vec<MapId> = (0..100).map(|_| MapIdState::new().ensure_id()).collect();
    let set: std::collections::HashSet<MapId> = ids.iter().copied().collect();
    assert_eq!(set.len(), 100);
}

#[test]
fn map_id_is_copy_clone_debug_eq_hash() {
    let state = MapIdState::new();
    let id = state.ensure_id();

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
    let state = MapIdState::new();
    let id = state.ensure_id();
    let raw = id.get_underlying_usize();
    let reconstructed = unsafe { MapId::from_usize(raw) };
    assert_eq!(id, reconstructed);
}
