use num_traits::{CheckedAdd, Num, WrappingAdd};
use std::convert::TryFrom;
use std::num::NonZero;
use std::ops::{Add, AddAssign, Div, Mul, Rem, Sub, SubAssign};

/// This trait is used to allow conversion between usize and most unsigned number types
/// This enables a key's Idx and Generation to have a variety of possible types, which enables a lot
/// of flexibility
/// # Safety
/// Types implementing this trait must not have any form of interior mutability.
/// As of the time this comment is written, that is impossible due to this trait requiring `Copy`, but you never know what could change in the future
pub unsafe trait KeyPiece:
    Copy
    + From<<Self as KeyPiece>::AsNonZero>
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
    + TryInto<Self::AsNonZero>
{
    type AsNonZero: 'static + Copy + Into<Self>;
    fn into_usize(self) -> usize;

    fn from_usize(v: usize) -> Self;
}

macro_rules! impl_key_piece {
    ($($t:ty)*) => {
        $(
            unsafe impl KeyPiece for $t {

                type AsNonZero = NonZero<$t> where Self::AsNonZero: Into<Self>;


                fn into_usize(self) -> usize {
                    self as usize // converting to usize is ok, since it is impossible for self to be higher than usize when used within this crate,
                    // unless a dev uses unsafe magic
                    //  It is up to the dev making the key size to consider if their choice of Gen/Idx type might go above usize. it won't cause UB if they don't.
                    // Just bugs, and it will only happen if someone decides to create a key outside insert
                }

                fn from_usize(v: usize) -> Self {
                    Self::try_from(v).unwrap_or_else(
                        |_|
                        panic!(
                            "{} does not fit in {}",
                            v,
                            std::any::type_name::<Self>()
                        )
                    ) // this should panic, if the value of usize is higher than the max value of self, using "as" to cast will cap it to the max value of self, which may cause bugs and/or UB
                }

            }
        )*

    }
}
impl_key_piece!(usize u8 u16 u32 u64 u128);
