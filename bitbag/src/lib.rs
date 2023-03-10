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
//!     Err(e) if e.given == 0b1000
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
use itertools::Itertools;
use num::{PrimInt, Zero};
use std::collections::HashSet;
use std::fmt;
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
#[derive(Clone, Copy, Debug, Binary, AsRef, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct BitBag<Flags: BitBaggable> {
    inner: Flags::Repr,
}

impl<Flags: BitBaggable> BitBag<Flags> {
    /// Get the inner primitive
    pub fn into_inner(&self) -> Flags::Repr {
        self.inner
    }

    /// Unset all flags
    pub fn clear_all(&mut self) -> &mut Self {
        self.inner.set_zero();
        self
    }
    /// Don't check the primitive for non-flag bits
    pub fn new_unchecked(prim: Flags::Repr) -> Self {
        Self { inner: prim }
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

impl<Flags: BitBaggable> BitBag<Flags>
where
    Flags::Repr: BitAndAssign<Flags::Repr> + BitOrAssign<Flags::Repr>,
{
    /// Return `true` if the flag is set
    pub fn is_set(&self, flag: Flags) -> bool {
        let flag = flag.into();
        self.inner.bitand(flag) == flag
    }
    /// Set the flag
    pub fn set(&mut self, flag: Flags) -> &mut Self {
        let flag = flag.into();
        self.inner.bitor_assign(flag);
        self
    }
    /// Unset the flag
    pub fn unset(&mut self, flag: Flags) -> &mut Self {
        let flag = flag.into();
        self.inner.bitand_assign(!flag);
        self
    }
}

impl<Flags: BitBaggable> BitBag<Flags>
where
    Flags: IntoEnumIterator,
    Flags::Repr: BitAndAssign<Flags::Repr> + BitOrAssign<Flags::Repr>,
{
    /// Check the bits of `prim`, and return an [`NonFlagBits`] error if it has bits set which can't be represented by a flag.
    pub fn new(prim: Flags::Repr) -> Result<Self, NonFlagBits<Flags::Repr>> {
        let mask = Flags::iter()
            .map(Into::into)
            .fold(Flags::Repr::zero(), |accumulator, element| {
                accumulator.bitor(element)
            });
        match mask.bitor(prim) == mask {
            true => Ok(Self { inner: prim }),
            false => Err(NonFlagBits { given: prim, mask }),
        }
    }

    /// Set all flags defined in the enum
    pub fn set_all(&mut self) -> &mut Self {
        for flag in Flags::iter() {
            self.set(flag);
        }
        self
    }
}

impl<Flags: BitBaggable> BitBag<Flags>
where
    Flags: IntoEnumIterator + Clone,
    Flags::Repr: BitAnd<Flags::Repr> + BitOr<Flags::Repr> + Into<bit_iter::BitIter<Flags::Repr>>,
    bit_iter::BitIter<Flags::Repr>: Iterator<Item = usize>,
{
    pub fn check_nonoverlapping() -> Result<(), Overlapping<Flags>> {
        for mut v in Flags::iter().permutations(2) {
            let (a, b) = (v.remove(1), v.remove(0));
            let (a_repr, b_repr) = (a.clone().into(), b.clone().into());
            let (a_set_bits, b_set_bits) = (
                a_repr.into().collect::<HashSet<_>>(),
                b_repr.into().collect::<HashSet<_>>(),
            );
            if let Some(position) = a_set_bits
                .intersection(&b_set_bits)
                .next()
                .map(Clone::clone)
            {
                return Err(Overlapping { a, b, position });
            }
        }
        Ok(())
    }
}

impl<Flags: BitBaggable> fmt::Display for BitBag<Flags>
where
    Flags: IntoEnumIterator + fmt::Display + Clone,
    Flags::Repr: BitAndAssign<Flags::Repr> + BitOrAssign<Flags::Repr>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.inner.is_zero() {
            return f.write_str("<unset>");
        }

        let mut first = true;
        for flag in Flags::iter() {
            if self.is_set(flag.clone()) {
                match first {
                    true => {
                        f.write_fmt(format_args!("{}", flag))?;
                        first = false
                    }
                    false => f.write_fmt(format_args!(" | {}", flag))?,
                }
            }
        }

        if Self::new(self.inner).is_err() {
            match first {
                true => f.write_str("<unrecognised bits>")?,
                false => f.write_str(" | <unrecognised bits>")?,
            }
        }

        Ok(())
    }
}

/// The error returned when calling a [`BitBag`] from a primitive which contains bits set which aren't represented by flags
#[derive(Debug)]
pub struct NonFlagBits<Repr> {
    /// The primitive which contained non-flag bits
    pub given: Repr,
    mask: Repr,
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

/// The error returned when calling [`BitBag::check_nonoverlapping`]
#[derive(Debug)]
pub struct Overlapping<Flags> {
    pub a: Flags,
    pub b: Flags,
    pub position: usize,
}

impl<Flags> Display for Overlapping<Flags>
where
    Flags: Debug + BitBaggable + Clone,
    Flags::Repr: Binary + PrimInt,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { a, b, position } = self;
        f.write_fmt(format_args!(
            "{a:?} and {b:?} overlap at bit position {position}"
        ))?;
        let width = Flags::Repr::zero().count_zeros();
        macro_rules! print_wide_enough {
            ($width:ident, $($bits:expr),*) => {
                match $width {
                    $(
                        ..=$bits => {
                            f.write_fmt(format_args!(
                                concat!(":\n0b{:0", stringify!($bits), "b} ({:?})\n"),
                                a.clone().into(),
                                a
                            ))?;
                            f.write_fmt(format_args!(
                                concat!("0b{:0", stringify!($bits), "b} ({:?})\n"),
                                b.clone().into(),
                                b
                            ))?;
                            let pointer = std::iter::repeat(' ')
                                .take(width as usize - position + 1)
                                .chain(['^'])
                                .collect::<String>();
                            f.write_str(&pointer)?;
                        }
                    )*
                    _ => (),
                }
            };
        }

        print_wide_enough!(width, 8, 16, 32, 64, 128);
        Ok(())
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::collections::HashSet;

    use indoc::indoc;

    use super::*;
    use crate as bitbag;

    #[derive(
        Debug,
        Copy,
        Clone,
        strum::EnumIter,
        PartialEq,
        Eq,
        Hash,
        BitBaggable,
        BoolBag,
        strum::Display,
    )]
    #[repr(u8)]
    pub enum FooFlags {
        A = 0b0000_0001,
        B = 0b0000_0010,
        C = 0b0000_0100,
        D = 0b0000_1000,
    }

    #[test]
    fn new_single_flag() -> anyhow::Result<()> {
        let bag = BitBag::<FooFlags>::new(0b0000_0001)?;
        let mut flags = bag.into_iter().collect::<Vec<_>>();
        assert!(flags.len() == 1);
        assert!(matches!(flags.pop(), Some(FooFlags::A)));
        Ok(())
    }

    #[test]
    fn new_multiple_flags() -> anyhow::Result<()> {
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
        assert_eq!(bag.into_inner(), 0b0000_0011);
    }

    #[test]
    fn manually_unset() {
        let mut bag = BitBag::<FooFlags>::new_unchecked(0b0000_0011);
        bag.unset(FooFlags::A);
        assert_eq!(bag.into_inner(), 0b0000_0010);
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

    #[test]
    fn display() {
        let bitbag = FooFlags::A | FooFlags::B;
        assert_eq!("A | B", bitbag.to_string());
        let bitbag = BitBag::<FooFlags>::default();
        assert_eq!("<unset>", bitbag.to_string());
    }

    #[derive(Debug, Copy, Clone, strum::EnumIter, PartialEq, Eq, BitBaggable)]
    #[repr(u16)]
    pub enum BadFlags {
        A = 0b0000_0001,
        B = 0b0000_0010,
        C = 0b0000_0100,
        D = 0b0000_1100,
    }

    #[test]
    fn non_overlapping() {
        BitBag::<FooFlags>::check_nonoverlapping().unwrap();
        let e = BitBag::<BadFlags>::check_nonoverlapping().unwrap_err();
        assert_eq!(
            indoc!(
                "D and C overlap at bit position 2:
            0b0000000000001100 (D)
            0b0000000000000100 (C)
                           ^"
            ),
            e.to_string()
        );
    }
}
