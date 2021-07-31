//! This crate provides [`BitBag`], a type intended for abstracting over [field-less enums](https://doc.rust-lang.org/rust-by-example/custom_types/enum/c_like.html)

use derive_more::Into;
use num::PrimInt;
use std::{
    any::type_name,
    fmt::{Binary, Debug, Display},
    marker::PhantomData,
    ops::BitAndAssign,
};
use strum::IntoEnumIterator;

/// A transparent wrapper over a primitive, with helper methods for checking flags
#[derive(Into, Clone, Copy, Debug, Default)]
#[repr(transparent)]
pub struct BitBag<Flag, Prim> {
    inner: Prim,
    flags: PhantomData<Flag>,
}

impl<Flag, Prim> BitBag<Flag, Prim>
where
    Prim: PrimInt + BitAndAssign<Prim>,
    Flag: Into<Prim> + Copy,
{
    /// Return `true` if the flag is set
    pub fn is_set(&self, flag: Flag) -> bool {
        let flag = flag.into();
        self.inner.bitand(flag) == flag
    }
    /// Set the flag
    pub fn set(&mut self, flag: Flag) {
        let flag = flag.into();
        self.inner.bitand_assign(flag);
    }
    /// Unset the flag
    pub fn unset(&mut self, flag: Flag) {
        let flag = flag.into();
        self.inner.bitand_assign(!flag);
    }
    /// Unset all flags
    pub fn clear_all(&mut self) {
        self.inner.set_zero()
    }
    /// Don't check the primitive for non-flag bits
    pub fn new_unchecked(prim: Prim) -> Self {
        Self {
            inner: prim,
            flags: PhantomData,
        }
    }
}

impl<Flag, Prim> BitBag<Flag, Prim>
where
    Prim: PrimInt + BitAndAssign<Prim>,
    Flag: Into<Prim> + IntoEnumIterator,
{
    /// Check the bits of `prim`, and return an [`InvalidFlag`] error if it has bits set
    /// which can't be represented by a flag.

    pub fn new(prim: Prim) -> Result<Self, InvalidFlag<Flag, Prim>> {
        let mask = Flag::iter()
            .map(Into::into)
            .fold(Prim::zero(), |accumulator, element| {
                accumulator.bitor(element)
            });
        match mask.bitor(prim) == mask {
            true => Ok(Self {
                inner: prim,
                flags: PhantomData,
            }),
            false => Err(InvalidFlag {
                given: prim,
                mask,
                flags: PhantomData,
            }),
        }
    }
}

impl<Flag, Prim> IntoIterator for BitBag<Flag, Prim>
where
    Prim: PrimInt + BitAndAssign<Prim>,
    Flag: Into<Prim> + IntoEnumIterator + Copy,
{
    type Item = Flag;

    type IntoIter = BitBagIterator<Flag, Prim>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            bag: self,
            flags_iterator: Flag::iter(),
        }
    }
}

impl<Flag, Prim> IntoIterator for &BitBag<Flag, Prim>
where
    Prim: PrimInt + BitAndAssign<Prim>,
    Flag: Into<Prim> + IntoEnumIterator + Copy,
{
    type Item = Flag;

    type IntoIter = BitBagIterator<Flag, Prim>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            bag: *self,
            flags_iterator: Flag::iter(),
        }
    }
}

#[derive(Debug)]
pub struct InvalidFlag<Flag, Prim> {
    given: Prim,
    mask: Prim,
    flags: PhantomData<Flag>,
}

impl<Flag, Prim> InvalidFlag<Flag, Prim> {
    /// The primitive which contained non-flag bits
    pub fn given(self) -> Prim {
        self.given
    }
}

impl<Flag, Prim: PrimInt + Binary> Display for InvalidFlag<Flag, Prim> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let excess = self.given.bitor(self.mask).bitxor(self.mask);
        write!(
            f,
            "The bits {:#b} are not accounted for in the enum {}",
            excess,
            type_name::<Flag>()
        )
    }
}

impl<Flag: Debug, Prim: Debug + PrimInt + Binary> std::error::Error for InvalidFlag<Flag, Prim> {}

pub struct BitBagIterator<Flag, Prim>
where
    Prim: PrimInt + BitAndAssign<Prim>,
    Flag: Into<Prim> + IntoEnumIterator,
{
    bag: BitBag<Flag, Prim>,
    flags_iterator: <Flag as IntoEnumIterator>::Iterator,
}

impl<Flag, Prim> Iterator for BitBagIterator<Flag, Prim>
where
    Prim: PrimInt + BitAndAssign<Prim>,
    Flag: Into<Prim> + IntoEnumIterator + Copy,
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

    impl Into<u8> for FooFlags {
        fn into(self) -> u8 {
            self as _
        }
    }

    #[test]
    fn new_single_flag() -> Result<()> {
        let bag = BitBag::<FooFlags, _>::new(0b0000_0001)?;
        let mut flags = bag.into_iter().collect::<Vec<_>>();
        assert!(flags.len() == 1);
        assert!(matches!(flags.pop(), Some(FooFlags::A)));
        Ok(())
    }

    #[test]
    fn new_multiple_flags() -> Result<()> {
        let bag = BitBag::<FooFlags, _>::new(0b0000_1101)?;
        let flags = bag.into_iter().collect::<HashSet<_>>();
        assert!(flags.len() == 3);
        assert!(flags.contains(&FooFlags::A));
        assert!(flags.contains(&FooFlags::C));
        assert!(flags.contains(&FooFlags::D));
        Ok(())
    }

    #[test]
    fn fail_new_single_non_flag() -> Result<()> {
        let res = BitBag::<FooFlags, _>::new(0b1000_0000);
        assert!(matches!(res, Err(_)));
        Ok(())
    }

    #[test]
    fn fail_new_mixed() -> Result<()> {
        let res = BitBag::<FooFlags, _>::new(0b1000_0001);
        assert!(matches!(res, Err(_)));
        Ok(())
    }

    #[test]
    fn unchecked() -> Result<()> {
        let bag = BitBag::<FooFlags, _>::new_unchecked(0b1000_0001);
        let mut flags = bag.into_iter().collect::<Vec<_>>();
        assert!(flags.len() == 1);
        assert!(matches!(flags.pop(), Some(FooFlags::A)));
        Ok(())
    }
}
