//! This crate provides [`BitBag`], a type intended for abstracting over [field-less enums](https://doc.rust-lang.org/rust-by-example/custom_types/enum/c_like.html).
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
//! assert_eq!(*bag, 0b0111);
//!
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

pub use bitbag_derive::BitBaggable;
use derive_more::{AsRef, Binary, Deref};
use num::{PrimInt, Zero};
use std::{
    any::type_name,
    fmt::{Binary, Debug, Display},
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign},
};
use strum::IntoEnumIterator;

#[cfg(doc)]
use std::ops::Deref;
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
/// [`Deref`]s to the primitive if you wish to access it
#[derive(Clone, Copy, Debug, Deref, Binary, AsRef)]
#[repr(transparent)]
pub struct BitBag<Flags: BitBaggable> {
    inner: Flags::Repr,
}

impl<Flags: BitBaggable> Default for BitBag<Flags> {
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
}

impl<Flag: BitBaggable> IntoIterator for BitBag<Flag>
where
    Flag: IntoEnumIterator + Copy,
    Flag::Repr: BitAndAssign + BitOrAssign,
{
    type Item = Flag;

    type IntoIter = BitBagIterator<Flag>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            bag: self,
            flags_iterator: Flag::iter(),
        }
    }
}
impl<Flag: BitBaggable> IntoIterator for &BitBag<Flag>
where
    Flag: IntoEnumIterator + Copy,
    Flag::Repr: BitAndAssign + BitOrAssign,
    BitBag<Flag>: Copy,
{
    type Item = Flag;

    type IntoIter = BitBagIterator<Flag>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            bag: *self,
            flags_iterator: Flag::iter(),
        }
    }
}

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

pub struct BitBagIterator<Flag: BitBaggable>
where
    Flag: IntoEnumIterator,
{
    bag: BitBag<Flag>,
    flags_iterator: <Flag as IntoEnumIterator>::Iterator,
}

impl<Flag: BitBaggable> Iterator for BitBagIterator<Flag>
where
    Flag: IntoEnumIterator,
    Flag: Copy,
    Flag::Repr: BitAndAssign + BitOrAssign,
{
    type Item = Flag;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(flag) = self.flags_iterator.next() {
            if self.bag.is_set(flag) {
                return Some(flag);
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;
    use crate as bitbag;
    use anyhow::Result;
    use strum::EnumIter;

    #[derive(Debug, Copy, Clone, EnumIter, PartialEq, Eq, Hash, BitBaggable)]
    #[repr(u8)]
    enum FooFlags {
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
    fn fail_new_single_non_flag() -> Result<()> {
        let res = BitBag::<FooFlags>::new(0b1000_0000);
        assert!(matches!(res, Err(_)));
        Ok(())
    }

    #[test]
    fn fail_new_mixed() -> Result<()> {
        let res = BitBag::<FooFlags>::new(0b1000_0001);
        assert!(matches!(res, Err(_)));
        Ok(())
    }

    #[test]
    fn unchecked() -> Result<()> {
        let bag = BitBag::<FooFlags>::new_unchecked(0b1000_0001);
        let mut flags = bag.into_iter().collect::<Vec<_>>();
        assert!(flags.len() == 1);
        assert!(matches!(flags.pop(), Some(FooFlags::A)));
        Ok(())
    }

    #[test]
    fn manually_set() -> Result<()> {
        let mut bag = BitBag::<FooFlags>::default();
        bag.set(FooFlags::A).set(FooFlags::B);
        assert_eq!(*bag, 0b0000_0011);
        Ok(())
    }

    #[test]
    fn manually_unset() -> Result<()> {
        let mut bag = BitBag::<FooFlags>::new_unchecked(0b0000_0011);
        bag.unset(FooFlags::A);
        assert_eq!(*bag, 0b0000_0010);
        Ok(())
    }
}
