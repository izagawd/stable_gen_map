//! Map types whose keys carry a map identifier, preventing cross-map misuse.
//!
//! These are convenience aliases around the core [`GenMap`] with
//! [`Extra = MapId`](crate::map_id::MapId).
//!
//! # Clone semantics
//!
//! When a `KeyCastable*` map is cloned, all existing slots retain the original
//! map's identifier.  Old keys therefore still work on the clone.  New inserts
//! into the clone produce keys stamped with a fresh identifier, so keys minted
//! by the clone cannot accidentally be used on the original (or any other map).

use crate::gen_map::GenMap;
use crate::key::{Key, KeyData};
use crate::map_id::MapId;
use crate::stable_deref_gen_map::{BoxStableDerefGenMap, DerefSlot, DerefGenMapPromise, StableDerefGenMap};
use crate::stable_gen_map::{BoxedSlot, StableGenMap};

// ─── IdentifiedDefaultKey ───────────────────────────────────────────────────

/// A default key type that carries a [`MapId`], binding it to the map that
/// created it (or its clone-family).
///
/// Layout: `u32` idx + `u32` generation + `usize` map id = 16 bytes on 64-bit.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct IdentifiedDefaultKey {
    key_data: KeyData<u32, u32>,
    map_id: MapId,
}

unsafe impl Key for IdentifiedDefaultKey {
    type Idx = u32;
    type Gen = u32;
    type Extra = MapId;

    #[inline]
    fn data(&self) -> KeyData<u32, u32> {
        self.key_data
    }

    #[inline]
    fn extra(&self) -> MapId {
        self.map_id
    }

    #[inline]
    fn from_parts(data: KeyData<u32, u32>, extra: MapId) -> Self {
        Self {
            key_data: data,
            map_id: extra,
        }
    }
}

// ─── Type aliases ───────────────────────────────────────────────────────────

/// [`StableGenMap`] with map-id–bound keys (via [`IdentifiedDefaultKey`]).
///
/// Each value is stored behind a `Box` for pointer stability, and keys carry
/// the map's identity so they cannot be used on an unrelated map.
pub type KeyCastableStableGenMap<T> = StableGenMap<IdentifiedDefaultKey, T>;

/// [`StableDerefGenMap`] with map-id–bound keys (via [`IdentifiedDefaultKey`]).
///
/// Stores user-supplied smart pointers directly (`Box`, `Rc`, `Arc`, …),
/// and keys carry the map's identity.
pub type KeyCastableStableDerefGenMap<Derefable> =
    StableDerefGenMap<IdentifiedDefaultKey, Derefable>;

/// [`BoxStableDerefGenMap`] with map-id–bound keys.
pub type KeyCastableBoxStableDerefGenMap<T> =
    BoxStableDerefGenMap<IdentifiedDefaultKey, T>;
