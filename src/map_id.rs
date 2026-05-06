use std::cell::Cell;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Global counter for map identifiers. Starts at 1 so that 0 is never a valid
/// map id (used as the vacant-slot placeholder in `NonNull` encoding).
static NEXT_MAP_ID: AtomicUsize = AtomicUsize::new(1);

/// A unique map identifier, used by [`StableCastMap`](crate::stable_cast_map::StableCastMap)
/// to bind keys to the map that created them.
///
/// Encoded into the data-pointer half of a `NonNull<T>` inside cast keys,
/// so it must always be non-zero.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct MapId(pub(crate) usize);

impl MapId {
    /// Construct a `MapId` from a raw `usize`.
    ///
    /// # Safety
    /// The caller must ensure the value is a valid, previously issued map id.
    pub unsafe fn from_usize(number: usize) -> MapId {
        MapId(number)
    }

    /// Returns the underlying `usize` value.
    pub fn get_underlying_usize(&self) -> usize {
        self.0
    }

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
/// A freshly constructed map starts with `None` and acquires an id
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
