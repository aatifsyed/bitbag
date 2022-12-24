//! This crate provides [`BitBag`], a type intended for tracking bitflags defined in a [field-less enum](https://doc.rust-lang.org/rust-by-example/custom_types/enum/c_like.html).
//! Get started like this:
//! ```
//! use bitbag::{BitBag, BitBaggable};
//! use strum::EnumIter;
//!
//! #[derive(BitBaggable, EnumIter, Clone, Copy)]
//! #[repr(u8)]
//! enum Flags {
//!     A = 0b0001,
//!     B = 0b0010,
//!     C = 0b0100,
//! }
//! ```
//! Basic functionality is provided by [`BitBag`]
//! ```
//! # use bitbag::{BitBag, BitBaggable};
//! # use strum::EnumIter;
//! # #[derive(BitBaggable, EnumIter, Clone, Copy)]
//! # #[repr(u8)]
//! # enum Flags {
//! #     A = 0b0001,
//! #     B = 0b0010,
//! #     C = 0b0100,
//! # }
//! let mut bag = BitBag::<Flags>::new_unchecked(0b0011);
//! assert!(bag.is_set(Flags::A));
//! assert!(bag.is_set(Flags::B));
//! assert!(!bag.is_set(Flags::C));
//!
//! bag.set(Flags::C);
//! assert_eq!(*bag.as_ref(), 0b0111);
//!
//! ```
//! Deriving [`BitBaggable`] will also give you very ergonomic constructors
//! ```
//! # use bitbag::{BitBag, BitBaggable};
//! # use strum::EnumIter;
//! # #[derive(BitBaggable, EnumIter, Clone, Copy)]
//! # #[repr(u8)]
//! # enum Flags {
//! #     A = 0b0001,
//! #     B = 0b0010,
//! #     C = 0b0100,
//! # }
//! use Flags::*;
//! let bag = A | B | C;
//! assert!(bag.is_set(Flags::A));
//! assert!(bag.is_set(Flags::B));
//! assert!(bag.is_set(Flags::C));
//! ```
//! Additionally deriving [`EnumIter`], and [`Copy`] will allow fallible creation, and iteration over the set flags
//! ```
//! # use bitbag::{BitBag, BitBaggable};
//! # use strum::EnumIter;
//! # #[derive(BitBaggable, EnumIter, Clone, Copy)]
//! # #[repr(u8)]
//! # enum Flags {
//! #     A = 0b0001,
//! #     B = 0b0010,
//! #     C = 0b0100,
//! # }
//! //                                  ⬇ this bit is not defined in Flags
//! let result = BitBag::<Flags>::new(0b1000);
//! assert!(matches!(
//!     result,
//!     Err(e) if e.given() == 0b1000
//! ));
//!
//! let bag = BitBag::<Flags>::new_unchecked(0b0110);
//! for flag in &bag {
//!     match flag {
//!         Flags::A => println!("Flag A was set"),
//!         Flags::B => println!("Flag B was set"),
//!         Flags::C => println!("Flag C was set"),
//!     }
//! };
//! ```
mod bitwise;
mod iter;
pub use bitbag_derive::BitBaggable;
pub use bitbag_derive::BoolBag;
use derive_more::{AsRef, Binary};
use num::{PrimInt, Zero};
use std::{
    any::type_name,
    fmt::{Binary, Debug, Display},
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign},
};
use strum::IntoEnumIterator;

#[cfg(doc)]
use strum::EnumIter;

/// The trait that allows an item to be placed inside a [`BitBag`].
///
/// The basic requirements are
/// - We must tell the type system the `primitive` in `#[repr(primitive)]`
/// - We must be able to convert (from any variant) into that primitive
///
/// You can derive this with the `BitBaggable` derive macro
pub trait BitBaggable: Into<Self::Repr> {
    type Repr: PrimInt;
}

/// Wraps a primitive, with helper methods for checking flags.
/// [`AsRef`]s to the primitive if you wish to access it
#[derive(Clone, Copy, Debug, Binary, AsRef, PartialEq, Eq)]
#[repr(transparent)]
pub struct BitBag<Flags: BitBaggable> {
    inner: Flags::Repr,
}

impl<Flags: BitBaggable> BitBag<Flags> {
    /// Get the inner primitive
    pub fn inner(&self) -> &Flags::Repr {
        &self.inner
    }
}

impl<Flags: BitBaggable> Default for BitBag<Flags> {
    /// The default has no flags set
    fn default() -> Self {
        Self {
            inner: Zero::zero(),
        }
    }
}

impl<Flag: BitBaggable> BitBag<Flag>
where
    Flag::Repr: BitAndAssign<Flag::Repr> + BitOrAssign<Flag::Repr>,
{
    /// Return `true` if the flag is set
    pub fn is_set(&self, flag: Flag) -> bool {
        let flag = flag.into();
        self.inner.bitand(flag) == flag
    }
    /// Set the flag
    pub fn set(&mut self, flag: Flag) -> &mut Self {
        let flag = flag.into();
        self.inner.bitor_assign(flag);
        self
    }
    /// Unset the flag
    pub fn unset(&mut self, flag: Flag) -> &mut Self {
        let flag = flag.into();
        self.inner.bitand_assign(!flag);
        self
    }
    /// Unset all flags
    pub fn clear_all(&mut self) -> &mut Self {
        self.inner.set_zero();
        self
    }
    /// Don't check the primitive for non-flag bits
    pub fn new_unchecked(prim: Flag::Repr) -> Self {
        Self { inner: prim }
    }
}

impl<Flag: BitBaggable> BitBag<Flag>
where
    Flag: IntoEnumIterator,
    Flag::Repr: BitAndAssign<Flag::Repr> + BitOrAssign<Flag::Repr>,
{
    /// Check the bits of `prim`, and return an [`NonFlagBits`] error if it has bits set which can't be represented by a flag.
    pub fn new(prim: Flag::Repr) -> Result<Self, NonFlagBits<Flag::Repr>> {
        let mask = Flag::iter()
            .map(Into::into)
            .fold(Flag::Repr::zero(), |accumulator, element| {
                accumulator.bitor(element)
            });
        match mask.bitor(prim) == mask {
            true => Ok(Self { inner: prim }),
            false => Err(NonFlagBits { given: prim, mask }),
        }
    }

    /// Set all flags defined in the enum
    pub fn set_all(&mut self) -> &mut Self {
        for flag in Flag::iter() {
            self.set(flag);
        }
        self
    }
}

/// The error returned when creating a [`BitBag`] from a primitive which contains bits set which aren't represented by flags
#[derive(Debug)]
pub struct NonFlagBits<Repr> {
    given: Repr,
    mask: Repr,
}

impl<Repr: Copy> NonFlagBits<Repr> {
    /// The primitive which contained non-flag bits
    pub fn given(&self) -> Repr {
        self.given
    }
}

impl<Repr: PrimInt + Binary> Display for NonFlagBits<Repr> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let excess = self.given.bitor(self.mask).bitxor(self.mask);
        write!(
            f,
            "The bits {:#b} are not accounted for in the enum {}",
            excess,
            type_name::<Repr>()
        )
    }
}

impl<Repr: Debug + PrimInt + Binary> std::error::Error for NonFlagBits<Repr> {}

#[cfg(test)]
pub(crate) mod tests {
    use std::collections::HashSet;

    use super::*;
    use crate as bitbag;
    use anyhow::Result;
    use strum::EnumIter;

    #[derive(Debug, Copy, Clone, EnumIter, PartialEq, Eq, Hash, BitBaggable, BoolBag)]
    #[repr(u8)]
    pub enum FooFlags {
        A = 0b0000_0001,
        B = 0b0000_0010,
        C = 0b0000_0100,
        D = 0b0000_1000,
    }

    #[test]
    fn new_single_flag() -> Result<()> {
        let bag = BitBag::<FooFlags>::new(0b0000_0001)?;
        let mut flags = bag.into_iter().collect::<Vec<_>>();
        assert!(flags.len() == 1);
        assert!(matches!(flags.pop(), Some(FooFlags::A)));
        Ok(())
    }

    #[test]
    fn new_multiple_flags() -> Result<()> {
        let bag = BitBag::<FooFlags>::new(0b0000_1101)?;
        let flags = bag.into_iter().collect::<HashSet<_>>();
        assert!(flags.len() == 3);
        assert!(flags.contains(&FooFlags::A));
        assert!(flags.contains(&FooFlags::C));
        assert!(flags.contains(&FooFlags::D));
        Ok(())
    }

    #[test]
    fn fail_new_single_non_flag() {
        let res = BitBag::<FooFlags>::new(0b1000_0000);
        assert!(matches!(res, Err(_)));
    }

    #[test]
    fn fail_new_mixed() {
        let res = BitBag::<FooFlags>::new(0b1000_0001);
        assert!(matches!(res, Err(_)));
    }

    #[test]
    fn unchecked() {
        let bag = BitBag::<FooFlags>::new_unchecked(0b1000_0001);
        let mut flags = bag.into_iter().collect::<Vec<_>>();
        assert!(flags.len() == 1);
        assert!(matches!(flags.pop(), Some(FooFlags::A)));
    }

    #[test]
    fn manually_set() {
        let mut bag = BitBag::<FooFlags>::default();
        bag.set(FooFlags::A).set(FooFlags::B);
        assert_eq!(*bag.inner(), 0b0000_0011);
    }

    #[test]
    fn manually_unset() {
        let mut bag = BitBag::<FooFlags>::new_unchecked(0b0000_0011);
        bag.unset(FooFlags::A);
        assert_eq!(*bag.inner(), 0b0000_0010);
    }

    #[test]
    fn empty_bitbag_to_boolbag() {
        let bitbag = BitBag::<FooFlags>::default();
        let boolbag = FooFlagsBoolBag {
            a: false,
            b: false,
            c: false,
            d: false,
        };
        assert_eq!(FooFlagsBoolBag::from(bitbag), boolbag)
    }

    #[test]
    fn single_bitbag_to_boolbag() {
        let mut bitbag = BitBag::<FooFlags>::default();
        bitbag.set(FooFlags::A);
        let boolbag = FooFlagsBoolBag {
            a: true,
            b: false,
            c: false,
            d: false,
        };
        assert_eq!(FooFlagsBoolBag::from(bitbag), boolbag)
    }

    #[test]
    fn empty_boolbag_to_bitbag() {
        let boolbag = FooFlagsBoolBag::default();
        let bitbag = boolbag.into();
        assert_eq!(BitBag::<FooFlags>::default(), bitbag)
    }

    #[test]
    fn single_boolbag_to_bitbag() {
        let boolbag = FooFlagsBoolBag {
            c: true,
            ..Default::default()
        };
        let bitbag: BitBag<_> = boolbag.into();
        assert!(!bitbag.is_set(FooFlags::A));
        assert!(!bitbag.is_set(FooFlags::B));
        assert!(bitbag.is_set(FooFlags::C));
        assert!(!bitbag.is_set(FooFlags::D));
    }
}
