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
#[repr(transparent)]
pub struct MapId(pub(crate) usize);

impl MapId {
    /// The placeholder used for vacant slots. Never matches a real id.
    pub(crate) const VACANT: Self = MapId(0);

    /// Requests a fresh, globally unique map id.
    ///
    /// Ids start at 1; 0 is reserved as the invalid/vacant sentinel.
    pub(crate) fn next() -> Self {
        let raw = NEXT_MAP_ID.fetch_add(1, Ordering::Relaxed);
        assert!(raw != 0, "MapId counter overflow");
        MapId(raw)
    }
}

/// Per-map state that lazily assigns a [`MapId`] on the first insert.
///
/// A freshly constructed or cloned map starts with `None` and acquires an id
/// the first time [`ensure_id`](MapIdState::ensure_id) is called.
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

    /// Returns the current id, or requests a fresh one from the global
    /// counter if this state doesn't have one yet.
    ///
    /// Once an id is assigned it never changes.
    pub fn ensure_id(&self) -> MapId {
        match self.id.get() {
            Some(id) => id,
            None => {
                let id = MapId::next();
                self.id.set(Some(id));
                id
            }
        }
    }
}

unsafe impl KeyExtra for MapId {
    type State = MapIdState;
    const EMPTY_STATE: MapIdState = MapIdState::new();

    #[inline]
    fn produce(state: &MapIdState) -> Self {
        state.ensure_id()
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