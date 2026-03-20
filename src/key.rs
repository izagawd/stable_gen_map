use crate::numeric::Numeric;

#[derive(Clone,Copy, Debug, PartialEq, Eq, Hash)]
pub struct KeyData<Idx, Generation>{
    pub(crate) idx: Idx,
    pub(crate) generation: Generation,
}

/// Odd means occupied, even means not occupied. this function does the check based on that
pub(crate) fn is_occupied_by_generation<Num: Numeric>(generation: Num) -> bool {
    generation % (Num::one() + Num::one()) != Num::zero()
}
/// This trait should be implemented for any custom key that is desired
pub unsafe trait Key : Copy + From<KeyData<Self::Idx, Self::Gen>> {


    /// This type will be used as the Idx type for the key
    type Idx : Numeric;

    /// This type will be used as the Gen type for the key
    type Gen : Numeric;

    fn data(&self) -> KeyData<Self::Idx, Self::Gen>;
}



#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct DefaultKey{
    pub(crate) key_data: KeyData<u32,u32>,
}

impl From<KeyData<u32,u32>> for DefaultKey{
    fn from(key_data: KeyData<u32,u32>) -> Self {
        DefaultKey{key_data: key_data}
    }
}

unsafe impl Key for DefaultKey{
    type Idx = u32;
    type Gen = u32;

    fn data(&self) -> KeyData<u32,u32>{
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

            fn data(&self) -> $crate::key::KeyData<u32, u32> {
                self.key_data
            }
        }

        $crate::new_key_type!($($rest)*);
    };
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

            fn data(&self) -> $crate::key::KeyData<$idx, $gen> {
                self.key_data
            }
        }

        $crate::new_key_type!($($rest)*);
    };
    () => {};
}