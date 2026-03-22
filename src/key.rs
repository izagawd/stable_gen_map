use crate::key_piece::KeyPiece;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct KeyData<Idx, Generation> {
    pub(crate) idx: Idx,
    pub(crate) generation: Generation,
}

/// Odd means occupied, even means not occupied. this function does the check based on that
pub(crate) fn is_occupied_by_generation<Num: KeyPiece>(generation: Num) -> bool {
    generation % (Num::one() + Num::one()) != Num::zero()
}

/// Extra data carried in both the key and each slot, validated on access.
///
/// For `()` (the default), this is a no-op: zero size, always valid.
/// For [`MapId`](crate::map_id::MapId), this stores a map identifier so keys
/// are bound to the map (or clone-family) that created them.
///
/// # Safety
/// `validate` must return `false` for any key that should not be able to
/// access a slot.  A buggy `validate` that returns `true` incorrectly can
/// cause the map to hand out references to the wrong data.
pub unsafe trait KeyExtra: Copy + 'static {
    /// Associated state held by the container, used to produce `Self` values
    /// on insert. For `()` this is `()`, for `MapId` this is a lazily
    /// initialised identifier source.
    type State;

    /// A const-evaluable empty state, used at construction time.
    const EMPTY_STATE: Self::State;

    /// Produce the extra value for a newly inserted slot+key.
    fn produce(state: &Self::State) -> Self;

    /// Check a key's extra against a slot's extra. Returns `true` if valid.
    fn validate(key_extra: Self, slot_extra: Self) -> bool;

    /// Placeholder value for vacant slots (never validated against).
    fn vacant_placeholder() -> Self;
}

// ─── () implementation (no-op) ──────────────────────────────────────────────

unsafe impl KeyExtra for () {
    type State = ();
    const EMPTY_STATE: () = ();

    #[inline(always)]
    fn produce(_state: &()) -> Self {}

    #[inline(always)]
    fn validate(_key: Self, _slot: Self) -> bool {
        true
    }

    #[inline(always)]
    fn vacant_placeholder() -> Self {}
}

// ─── Key trait ───────────────────────────────────────────────────────────────

/// This trait should be implemented for any custom key that is desired.
///
/// # Safety
/// `from_parts` must produce a key whose `data()` and `extra()` round-trip
/// correctly.
pub unsafe trait Key: Copy {
    /// This type will be used as the Idx type for the key
    type Idx: KeyPiece;

    /// This type will be used as the Gen type for the key
    type Gen: KeyPiece;

    /// Extra per-key data (e.g. map identifier). Use `()` for none.
    type Extra: KeyExtra;

    fn data(&self) -> KeyData<Self::Idx, Self::Gen>;
    fn extra(&self) -> Self::Extra;
    fn from_parts(data: KeyData<Self::Idx, Self::Gen>, extra: Self::Extra) -> Self;
}

// ─── DefaultKey ─────────────────────────────────────────────────────────────

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct DefaultKey {
    pub(crate) key_data: KeyData<u32, u32>,
}

impl From<KeyData<u32, u32>> for DefaultKey {
    fn from(key_data: KeyData<u32, u32>) -> Self {
        DefaultKey { key_data }
    }
}

unsafe impl Key for DefaultKey {
    type Idx = u32;
    type Gen = u32;
    type Extra = ();

    #[inline]
    fn data(&self) -> KeyData<u32, u32> {
        self.key_data
    }

    #[inline]
    fn extra(&self) -> () {}

    #[inline]
    fn from_parts(data: KeyData<u32, u32>, _extra: ()) -> Self {
        Self { key_data: data }
    }
}

/// Macro for creating new key types, similar to slotmap's `new_key_type!`.
///
/// # Examples
/// ```
/// use stable_gen_map::new_key_type;
///
/// // Basic key (Extra = (), no map-id checking):
/// new_key_type! {
///     pub struct PlayerKey;
/// }
///
/// // Custom index/generation types:
/// new_key_type! {
///     pub struct SmallKey(u16, u16);
/// }
///
/// // Key with map-id checking (Extra = MapId):
/// new_key_type! {
///     pub struct IdentifiedPlayerKey identified;
/// }
///
/// // Custom index/generation with map-id:
/// new_key_type! {
///     pub struct SmallIdentifiedKey(u16, u16) identified;
/// }
/// ```
#[macro_export]
macro_rules! new_key_type {
    // ── basic key (Extra = ()) ──────────────────────────────────────────
    ( $(#[$attr:meta])* $vis:vis struct $name:ident ; $($rest:tt)* ) => {
        $(#[$attr])*
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
        $vis struct $name {
            key_data: $crate::key::KeyData<u32, u32>,
        }

        impl From<$crate::key::KeyData<u32, u32>> for $name {
            fn from(key_data: $crate::key::KeyData<u32, u32>) -> Self {
                Self { key_data }
            }
        }

        unsafe impl $crate::key::Key for $name {
            type Idx = u32;
            type Gen = u32;
            type Extra = ();

            fn data(&self) -> $crate::key::KeyData<u32, u32> {
                self.key_data
            }
            fn extra(&self) -> () {}
            fn from_parts(data: $crate::key::KeyData<u32, u32>, _extra: ()) -> Self {
                Self { key_data: data }
            }
        }

        $crate::new_key_type!($($rest)*);
    };

    // ── basic key with custom Idx/Gen (Extra = ()) ──────────────────────
    ( $(#[$attr:meta])* $vis:vis struct $name:ident ( $idx:ty , $gen:ty ) ; $($rest:tt)* ) => {
        $(#[$attr])*
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
        $vis struct $name {
            key_data: $crate::key::KeyData<$idx, $gen>,
        }

        impl From<$crate::key::KeyData<$idx, $gen>> for $name {
            fn from(key_data: $crate::key::KeyData<$idx, $gen>) -> Self {
                Self { key_data }
            }
        }

        unsafe impl $crate::key::Key for $name {
            type Idx = $idx;
            type Gen = $gen;
            type Extra = ();

            fn data(&self) -> $crate::key::KeyData<$idx, $gen> {
                self.key_data
            }
            fn extra(&self) -> () {}
            fn from_parts(data: $crate::key::KeyData<$idx, $gen>, _extra: ()) -> Self {
                Self { key_data: data }
            }
        }

        $crate::new_key_type!($($rest)*);
    };

    // ── identified key (Extra = MapId) ──────────────────────────────────
    ( $(#[$attr:meta])* $vis:vis struct $name:ident identified ; $($rest:tt)* ) => {
        $(#[$attr])*
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
        $vis struct $name {
            key_data: $crate::key::KeyData<u32, u32>,
            map_id: $crate::map_id::MapId,
        }

        unsafe impl $crate::key::Key for $name {
            type Idx = u32;
            type Gen = u32;
            type Extra = $crate::map_id::MapId;

            fn data(&self) -> $crate::key::KeyData<u32, u32> {
                self.key_data
            }
            fn extra(&self) -> $crate::map_id::MapId {
                self.map_id
            }
            fn from_parts(data: $crate::key::KeyData<u32, u32>, extra: $crate::map_id::MapId) -> Self {
                Self { key_data: data, map_id: extra }
            }
        }

        $crate::new_key_type!($($rest)*);
    };

    // ── identified key with custom Idx/Gen (Extra = MapId) ──────────────
    ( $(#[$attr:meta])* $vis:vis struct $name:ident ( $idx:ty , $gen:ty ) identified ; $($rest:tt)* ) => {
        $(#[$attr])*
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
        $vis struct $name {
            key_data: $crate::key::KeyData<$idx, $gen>,
            map_id: $crate::map_id::MapId,
        }

        unsafe impl $crate::key::Key for $name {
            type Idx = $idx;
            type Gen = $gen;
            type Extra = $crate::map_id::MapId;

            fn data(&self) -> $crate::key::KeyData<$idx, $gen> {
                self.key_data
            }
            fn extra(&self) -> $crate::map_id::MapId {
                self.map_id
            }
            fn from_parts(data: $crate::key::KeyData<$idx, $gen>, extra: $crate::map_id::MapId) -> Self {
                Self { key_data: data, map_id: extra }
            }
        }

        $crate::new_key_type!($($rest)*);
    };

    () => {};
}