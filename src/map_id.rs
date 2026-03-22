use crate::key::KeyExtra;
use std::cell::Cell;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Global counter for map identifiers. Starts at 1 so that 0 is never a valid
/// map id (used as the vacant-slot placeholder).
static NEXT_MAP_ID: AtomicUsize = AtomicUsize::new(1);

/// A map identifier stamped into every key and slot, binding them together.
///
/// Two maps never share the same `MapId` unless one was cloned from the other
/// (in which case the *slots* retain the original map's id while the clone's
/// state produces a fresh id for new inserts).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct MapId(pub(crate) usize);

impl MapId {
    /// The placeholder used for vacant slots. Never matches a real id.
    pub(crate) const VACANT: Self = MapId(0);
}

/// Per-map state that lazily assigns a [`MapId`] on the first insert.
///
/// A freshly constructed or cloned map starts with `None` and acquires an id
/// the first time [`KeyExtra::stamp`] is called.
pub struct MapIdState {
    id: Cell<Option<MapId>>,
}

impl MapIdState {
    pub(crate) const fn new() -> Self {
        Self {
            id: Cell::new(None),
        }
    }

    /// Returns the current id, if one has been assigned.
    pub fn current_id(&self) -> Option<MapId> {
        self.id.get()
    }
}

unsafe impl KeyExtra for MapId {
    type MapState = MapIdState;
    const EMPTY_MAP_STATE: MapIdState = MapIdState::new();

    #[inline]
    fn stamp(state: &MapIdState) -> Self {
        match state.id.get() {
            Some(id) => id,
            None => {
                let raw = NEXT_MAP_ID.fetch_add(1, Ordering::Relaxed);
                // Overflow past usize::MAX wraps to 0 which is our vacant
                // sentinel. In practice this is unreachable (would require
                // creating usize::MAX maps).
                assert!(raw != 0, "MapId counter overflow");
                let id = MapId(raw);
                state.id.set(Some(id));
                id
            }
        }
    }

    #[inline]
    fn validate(key_extra: Self, slot_extra: Self) -> bool {
        key_extra.0 == slot_extra.0
    }

    #[inline]
    fn vacant_placeholder() -> Self {
        MapId::VACANT
    }
}
