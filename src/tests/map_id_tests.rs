use crate::map_id::{MapId, MapIdState};
use crate::key::KeyExtra;

#[test]
fn map_id_starts_at_none() {
    let state = MapIdState::new();
    assert!(state.current_id().is_none());
}

#[test]
fn ensure_id_assigns_on_first_call() {
    let state = MapIdState::new();
    let id = state.ensure_id();
    assert!(id.0 != 0, "map id should never be 0");
    assert!(state.current_id().is_some());
    assert_eq!(state.current_id().unwrap(), id);
}

#[test]
fn ensure_id_returns_same_on_subsequent_calls() {
    let state = MapIdState::new();
    let first = state.ensure_id();
    let second = state.ensure_id();
    let third = state.ensure_id();
    assert_eq!(first, second);
    assert_eq!(second, third);
}

#[test]
fn different_states_get_different_ids() {
    let a = MapIdState::new();
    let b = MapIdState::new();
    let id_a = a.ensure_id();
    let id_b = b.ensure_id();
    assert_ne!(id_a, id_b);
}

#[test]
fn many_states_all_unique() {
    let states: Vec<_> = (0..1000).map(|_| MapIdState::new()).collect();
    let ids: Vec<_> = states.iter().map(|s| s.ensure_id()).collect();
    let unique: std::collections::HashSet<_> = ids.iter().copied().collect();
    assert_eq!(unique.len(), 1000);
}

#[test]
fn vacant_placeholder_is_zero() {
    assert_eq!(MapId::VACANT.0, 0);
}

#[test]
fn validate_matches_equal_ids() {
    let state = MapIdState::new();
    let id = state.ensure_id();
    assert!(MapId::validate(id, id));
}

#[test]
fn validate_rejects_different_ids() {
    let a = MapIdState::new();
    let b = MapIdState::new();
    assert!(!MapId::validate(a.ensure_id(), b.ensure_id()));
}

#[test]
fn validate_rejects_vacant() {
    let state = MapIdState::new();
    let id = state.ensure_id();
    assert!(!MapId::validate(id, MapId::VACANT));
    assert!(!MapId::validate(MapId::VACANT, id));
}

#[test]
fn produce_uses_ensure_id() {
    let state = MapIdState::new();
    let produced = MapId::produce(&state);
    assert_eq!(produced, state.current_id().unwrap());
    // subsequent produce returns same
    let again = MapId::produce(&state);
    assert_eq!(produced, again);
}

#[test]
fn empty_state_is_const() {
    // Just verify it compiles as const
    const _: MapIdState = MapId::EMPTY_STATE;
}
