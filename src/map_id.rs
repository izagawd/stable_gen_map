use std::num::NonZeroUsize;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Global counter for map identifiers. Starts at 1 so that 0 is never a valid
/// map id (0 is never a valid map id).
static NEXT_MAP_ID: AtomicUsize = AtomicUsize::new(1);

/// A unique map identifier, used by [`StableCastMap`](crate::stable_cast_map::StableCastMap)
/// to bind keys to the map that created them.
///
/// Stored inside each [`StableCastKey`](crate::cast_key::StableCastKey) and
/// checked on every keyed access so that a key from one map cannot be used
/// on another.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct MapId(pub(crate) NonZeroUsize);

impl MapId {
    /// Construct a `MapId` from a raw `NonZeroUsize`.
    ///
    /// # Safety
    /// The caller must ensure the value is a valid, previously issued map id.
    #[inline]
    pub unsafe fn from_non_zero_usize(number: NonZeroUsize) -> MapId {
        MapId(number)
    }

    /// Returns the underlying `NonZeroUsize` value.
    #[inline]
    pub fn get_underlying_non_zero_usize(&self) -> NonZeroUsize {
        self.0
    }

    /// Requests a fresh, globally unique map id.
    ///
    /// Ids start at 1; 0 is reserved as the invalid/vacant sentinel.
    #[inline]
    pub fn next() -> Self {
        let raw = NEXT_MAP_ID
            .try_update(Ordering::Relaxed, Ordering::Relaxed, |raw| {
                if raw == 0 {
                    None
                } else {
                    Some(raw.wrapping_add(1))
                }
            })
            .unwrap_or_else(|_| panic!("MapId counter overflow"));

        debug_assert_ne!(raw, 0);
        MapId(NonZeroUsize::new(raw).expect("Map ID overflow"))
    }
}
