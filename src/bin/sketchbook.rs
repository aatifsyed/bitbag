use std::{any::type_name, convert::{TryFrom, TryInto}, marker::PhantomData, ops::{BitAnd, BitAndAssign, Not}};
use num::{PrimInt, Zero};
use strum::EnumIter;
use derive_more::{Into, Display};

trait BitBag<Flag, Prim>: 
TryFrom<Prim> // Must be able to try and build a set of flags from the primitive type
+ Into<Prim> // And covert that set back into the primitive type
+ Copy // Must be able to copy self for testing
where
Prim: BitAndAssign<Prim> + BitAnd<Prim, Output = Prim> + Not<Output = Prim>, // Bitwise ops on P
Prim: Eq + Copy,
Prim: Zero, // Zero for no flags
Flag: Into<Prim>, // Each flag must be representable as the primitive type
{
    /// Return `true` if the flag is set
    fn test(&self, flag: Flag) -> bool {
        let p: Prim = (*self).into();
        let f = flag.into();
        p.bitand(f) == f
    }
    /// Set the flag
    fn set(&mut self, flag: Flag) {
        let mut p: Prim = (*self).into();
        let f = flag.into();
        p.bitand_assign(f);
        // - self was a valid combination of F
        // - we've added an F
        // - TryFrom<P> for self must accept valid combinations of F
        match p.try_into() {
            Ok(p) => *self = p,
            Err(_) => unreachable!(),
        }
    }
    /// Unset the flag
    fn unset(&mut self, flag: Flag) {
        let mut p: Prim = (*self).into();
        let f = flag.into();
        p.bitand_assign(!f);
        // - self was a valid combination of F
        // - we've removed an F
        // - TryFrom<P> for self must accept valid combinations of F (including none at all)
        match p.try_into() {
            Ok(p) => *self = p,
            Err(_) => unreachable!(),
        }

    }
    /// Unset all flags
    fn clear_all(&mut self) {
        // - TryFrom<P> for self must accept valid combinations of F (including none at all)
        match Prim::zero().try_into() {
            Ok(p) => *self = p,
            Err(_) => unreachable!(),
        }
    }
    /// Create a new, empty bag
    fn cleared() -> Self {
        // - TryFrom<P> for self must accept valid combinations of F (including 0)
        match Prim::zero().try_into() {
            Ok(s) => s,
            Err(_) => unreachable!(),
        }
    }
}

struct InvalidFlag<T>{
    _phantom: PhantomData<T>
}


#[derive(Copy, Clone, Debug, Display, EnumIter)]
#[repr(u8)]
enum FooFlags {
    Bar = 0b00000001,
    Baz = 0b00000010,
}

impl Into<u8> for FooFlags {
    fn into(self) -> u8 {
        self as _
    }
}

#[derive(Clone, Copy, Into)]
#[repr(transparent)]
struct FooFlagsBag(u8);

impl TryFrom<u8> for FooFlagsBag {
    type Error = InvalidFlag<FooFlags>;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        todo!()
    }
}

impl BitBag<FooFlags, u8> for FooFlagsBag {}

fn main() {}
