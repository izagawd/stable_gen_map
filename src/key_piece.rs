use num_traits::{CheckedAdd, Num, WrappingAdd};
use std::convert::TryFrom;
use std::ops::{Add, AddAssign, Div, Mul, Rem, Sub, SubAssign};

/// Trait for types that can be used as the index or generation component of a
/// key.
///
/// Implemented for `u8`, `u16`, `u32`, `u64`, `u128`, and `usize`. Smaller
/// types reduce per-key memory at the cost of fewer addressable slots or
/// generations before overflow.
///
/// # Safety
/// `into_usize` and `from_usize` must round-trip correctly for all values
/// that the map will actually produce. `from_usize` panics if the value
/// exceeds the type's range.
pub unsafe trait KeyPiece:
    Copy
    + Num
    + 'static
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + AddAssign<Self>
    + Div<Output = Self>
    + PartialOrd
    + SubAssign
    + WrappingAdd
    + Rem<Output = Self>
    + CheckedAdd
{
    fn into_usize(self: Self) -> usize;

    fn from_usize(v: usize) -> Self;
}

macro_rules! impl_key_piece {
    ($($t:ty)*) => {
        $(
            unsafe impl KeyPiece for $t {
                fn into_usize(self) -> usize {
                    self as usize // converting to usize is ok, since it is impossible for self to be higher than usize when used within this crate,
                    // unless a dev uses unsafe magic
                    //  It is up to the dev making the key size to consider if their choice of Gen/Idx type might go above usize. it wont cause UB if they dont.
                    // Just bugs, and it will only happen if someone decides to create a key outside insert
                }
                fn from_usize(v: usize) -> Self {
                    Self::try_from(v).unwrap_or_else(|_| panic!(
                        "KeyPiece::from_usize: value {} exceeds the maximum for {}",
                        v, std::any::type_name::<Self>()
                    )) // this should panic.
                    // if the value of usize is higher than the max value of self, using "as" to cast will cap it to the max value of self, which may cause UB, bugs
                }
            }
        )*

    }
}
impl_key_piece!(usize u8 u16 u32 u64 u128);
