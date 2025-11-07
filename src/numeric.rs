use num_traits::{CheckedAdd, Num, WrappingAdd};
use std::convert::TryFrom;
use std::ops::{Add, AddAssign, Div, Mul, Sub, SubAssign};



/// This trait is used to allow polymorphism between all number types
/// This enables the key type to have any type they want for their Idx and Generation, which enables a lot
/// of flexibility
pub unsafe trait Numeric:
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
+ CheckedAdd
{
    fn into_usize(self: Self) -> usize;

    fn from_usize(v: usize) -> Self;

}

macro_rules! impl_numeric {
    ($($t:ty)*) => {
        $(
            unsafe impl Numeric for $t {
                fn into_usize(self) -> usize {
                    self as usize // converting to usize is ok, since it is impossible for self to be higher than usize when used within this crate,
                    // unless a dev uses unsafe magic
                    //  It is up to the dev making the key size to consider if their choice of Gen/Idx/Page type might go above usize. it wont cause UB if they dont.
                    // Just bugs, and it will only happen if someone decides to create a key outside insert
                }
                fn from_usize(v: usize) -> Self {
                    Self::try_from(v).unwrap_or_else(|_| panic!("")) // this should panic.
                    // if the value of usize is higher than the max value of self, using "as" to cast will cap it to the max value of self, which may cause UB, bugs
                }
            }
        )*

    }
}
impl_numeric!(usize u8 u16 u32 u64 u128);