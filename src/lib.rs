//! This crate provides [`BitBag`], a type intended for abstracting over [field-less enums](https://doc.rust-lang.org/rust-by-example/custom_types/enum/c_like.html)

use derive_more::Deref;
use num::{PrimInt, Zero};
use std::{
    any::type_name,
    fmt::{Binary, Debug, Display},
    ops::{BitAnd, BitAndAssign, BitOr},
};
use strum::IntoEnumIterator;

#[allow(unused_imports)] // Doc
use std::ops::Deref;

/// For an enum to be put inside a [`BitBag`]
/// - We must tell the type system the primitive in `#[repr(primitive)]`
/// - We must be able to convert (from any variant) into that primitive
pub trait BitBaggable: Into<Self::Repr> {
    type Repr: PrimInt;
}

/// Wraps a primitive, with helper methods for checking flags.
/// [`Deref`]s to the primitive if you wish to access it
#[derive(Clone, Copy, Debug, Default, Deref)]
#[repr(transparent)]
pub struct BitBag<Flags: BitBaggable> {
    inner: Flags::Repr,
}

impl<Flag: BitBaggable> BitBag<Flag>
where
    Flag::Repr: BitAndAssign<Flag::Repr>,
    BitBag<Flag>: Copy,
{
    /// Return `true` if the flag is set
    pub fn is_set(&self, flag: Flag) -> bool {
        let flag = flag.into();
        self.inner.bitand(flag) == flag
    }
    /// Set the flag
    pub fn set(&mut self, flag: Flag) -> Self {
        let flag = flag.into();
        self.inner.bitand_assign(flag);
        *self
    }
    /// Unset the flag
    pub fn unset(&mut self, flag: Flag) -> Self {
        let flag = flag.into();
        self.inner.bitand_assign(!flag);
        *self
    }
    /// Unset all flags
    pub fn clear_all(&mut self) -> Self {
        self.inner.set_zero();
        *self
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
    ///
    /// Note that the [IntoIterator<Item = Flag>] must cycle through the enum variants for this to function correctly
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
    Flag::Repr: BitAndAssign,
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
    Flag::Repr: BitAndAssign,
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

impl<Repr> NonFlagBits<Repr> {
    /// The primitive which contained non-flag bits
    pub fn given(self) -> Repr {
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
    Flag::Repr: BitAndAssign,
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
    use anyhow::Result;
    use strum::EnumIter;

    #[derive(Debug, Copy, Clone, EnumIter, PartialEq, Eq, Hash)]
    #[repr(u8)]
    enum FooFlags {
        A = 0b0000_0001,
        B = 0b0000_0010,
        C = 0b0000_0100,
        D = 0b0000_1000,
    }

    impl BitBaggable for FooFlags {
        type Repr = u8;
    }

    impl Into<u8> for FooFlags {
        fn into(self) -> u8 {
            self as _
        }
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
}
