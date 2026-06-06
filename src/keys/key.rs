use crate::keys::key_piece::KeyPiece;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct KeyData<Idx: KeyPiece, Generation: KeyPiece> {
    pub(crate) idx: Idx,
    pub(crate) generation: Generation::AsNonZero,
}

impl<Idx: KeyPiece, Generation: KeyPiece> KeyData<Idx, Generation> {
    #[inline]
    pub fn generation(&self) -> Generation {
        self.generation.into()
    }
    #[inline]
    pub fn generation_non_zero(&self) -> Generation::AsNonZero {
        self.generation
    }

    #[inline]
    pub fn index(&self) -> Idx {
        self.idx
    }
}

/// Odd means occupied, even means not occupied. this function does the check based on that
#[inline]
pub(crate) fn is_occupied_by_generation<Num: KeyPiece>(generation: Num) -> bool {
    generation % (Num::one() + Num::one()) != Num::zero()
}
/// This trait should be implemented for any custom key that is desired
/// # Safety
/// `data` must return the same [`KeyData`] on every call for a given key, and
/// that value must come directly from the key's stored fields. It must not be
/// computed conditionally, recomputed, or derived from indirection such as
/// `Option<KeyData>` or a stored closure. Callers rely on `data` being a pure,
/// stable accessor of the key's identity; violating this breaks the
/// generational invariants that keep lookups sound.
pub unsafe trait Key: Copy + From<KeyData<Self::Idx, Self::Gen>> {
    /// This type will be used as the Idx type for the key
    type Idx: KeyPiece;

    /// This type will be used as the Gen type for the key
    type Gen: KeyPiece;

    fn data(&self) -> KeyData<Self::Idx, Self::Gen>;
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct DefaultKey {
    pub(crate) key_data: KeyData<u32, u32>,
}

impl From<KeyData<u32, u32>> for DefaultKey {
    #[inline]
    fn from(key_data: KeyData<u32, u32>) -> Self {
        DefaultKey { key_data }
    }
}

unsafe impl Key for DefaultKey {
    type Idx = u32;
    type Gen = u32;

    #[inline]
    fn data(&self) -> KeyData<u32, u32> {
        self.key_data
    }
}

/// Macro for creating new key types, similar to slotmap's `new_key_type!`.
///
/// # Examples
/// ```
/// use stable_gen_map::new_key_type;
///
/// new_key_type! {
///     pub struct PlayerKey;
/// }
///
/// // With custom index/generation types:
/// new_key_type! {
///     pub struct SmallKey(u16, u16);
/// }
/// ```
#[macro_export]
macro_rules! new_key_type {
    ( $(#[$attr:meta])* $vis:vis struct $name:ident ; $($rest:tt)* ) => {
        $(#[$attr])*
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
        $vis struct $name {
            key_data: $crate::keys::key::KeyData<u32, u32>,
        }

        impl From<$crate::keys::key::KeyData<u32, u32>> for $name {
            #[inline]
            fn from(key_data: $crate::keys::key::KeyData<u32, u32>) -> Self {
                Self { key_data }
            }
        }

        unsafe impl $crate::keys::key::Key for $name {
            type Idx = u32;
            type Gen = u32;
            #[inline]
            fn data(&self) -> $crate::keys::key::KeyData<u32, u32> {
                self.key_data
            }
        }

        $crate::new_key_type!($($rest)*);
    };
    ( $(#[$attr:meta])* $vis:vis struct $name:ident ( $idx:ty , $gen:ty ) ; $($rest:tt)* ) => {
        $(#[$attr])*
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
        $vis struct $name {
            key_data: $crate::keys::key::KeyData<$idx, $gen>,
        }

        impl From<$crate::keys::key::KeyData<$idx, $gen>> for $name {
            fn from(key_data: $crate::keys::key::KeyData<$idx, $gen>) -> Self {
                Self { key_data }
            }
        }

        unsafe impl $crate::keys::key::Key for $name {
            type Idx = $idx;
            type Gen = $gen;

            fn data(&self) -> $crate::keys::key::KeyData<$idx, $gen> {
                self.key_data
            }
        }

        $crate::new_key_type!($($rest)*);
    };
    () => {};
}
