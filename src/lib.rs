//! This crate provides [`BitBag`], a type intended for tracking bitflags defined in a [field-less enum](https://doc.rust-lang.org/rust-by-example/custom_types/enum/c_like.html).
//! Get started like this:
//! ```
//! use bitbag::{BitBag, BitBaggable};
//!
//! #[derive(BitBaggable)]
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
//! # #[derive(BitBaggable)]
//! # #[repr(u8)]
//! # enum Flags {
//! #     A = 0b0001,
//! #     B = 0b0010,
//! #     C = 0b0100,
//! # }
//! let mut bag = BitBag::<Flags>::new(0b0011);
//! assert!(bag.is_set(Flags::A));
//! assert!(bag.is_set(Flags::B));
//! assert!(!bag.is_set(Flags::C));
//!
//! bag.set(Flags::C);
//! assert_eq!(bag.get(), 0b0111);
//!
//! ```
//! Deriving [`BitOr`] will also give you very ergonomic constructors
//! ```
//! use bitbag::{BitBaggable, BitOr};
//! #[derive(BitBaggable, BitOr)]
//! /* snip */
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
//! You can also choose to reject unrecognised bits, and iterate over the set flags.
//! ```
//! # use bitbag::{BitBag, BitBaggable};
//! # #[derive(BitBaggable, Debug, Clone)]
//! # #[repr(u8)]
//! # enum Flags {
//! #     A = 0b0001,
//! #     B = 0b0010,
//! #     C = 0b0100,
//! # }
//! BitBag::<Flags>::new_strict(0b1000).unwrap_err();
//! // "The bits 0b1000 are not accounted for in the enum Flags"
//!
//! let bag = BitBag::<Flags>::new(0b0110);
//! for flag in bag {
//!     match flag {
//!         Flags::A => println!("Flag A was set"),
//!         Flags::B => println!("Flag B was set"),
//!         Flags::C => println!("Flag C was set"),
//!     }
//! };
//! ```
#![cfg_attr(not(feature = "std"), no_std)]

mod bitwise;
mod impls;
mod iter;
pub use bitbag_derive::{check, BitBaggable, BitOr};
use core::{
    any::type_name,
    fmt::{self, Binary, Debug, Display},
    ops::{BitAnd as _, BitOr as _, BitXor as _, Not as _},
};
use num::{PrimInt, Zero as _};

/// The trait that allows an enum to be placed inside a [`BitBag`].
///
/// You should derive this with the `BitBaggable` derive macro.
pub trait BitBaggable: Sized + 'static {
    /// The `primitive` in `#[repr(primitive)]`
    type ReprT: PrimInt;
    /// Convert from a variant to its primitive
    fn into_repr(self) -> Self::ReprT;
    /// names, values and discriminants
    const VARIANTS: &'static [(&'static str, Self, Self::ReprT)];
}

/// Wraps a primitive, with helper methods for checking and setting flags.
#[repr(transparent)]
pub struct BitBag<PossibleFlagsT: BitBaggable> {
    pub repr: PossibleFlagsT::ReprT,
}

/// Constructors
impl<PossibleFlagsT: BitBaggable> BitBag<PossibleFlagsT> {
    /// New bag, permitting (and preserving) unrecognised bits
    pub const fn new(prim: PossibleFlagsT::ReprT) -> Self {
        Self { repr: prim }
    }

    /// New bag with no bits set
    pub fn empty() -> Self {
        Self {
            repr: PossibleFlagsT::ReprT::zero(),
        }
    }

    /// New bag with all defined bits set
    pub fn all() -> Self {
        *Self::empty().set_all()
    }

    /// Check the bits of `prim`, and return a [`NonFlagBits`] error if it has bits set which aren't defined in the enum.
    pub fn new_strict(prim: PossibleFlagsT::ReprT) -> Result<Self, NonFlagBits<PossibleFlagsT>> {
        match unrecognised_bits::<PossibleFlagsT>(prim) {
            Some(unrecognised) => Err(NonFlagBits { unrecognised }),
            None => Ok(Self { repr: prim }),
        }
    }
}

/// Properties
impl<PossibleFlagsT: BitBaggable> BitBag<PossibleFlagsT> {
    pub fn is_empty(&self) -> bool {
        self.repr.is_zero()
    }

    pub fn is_set_raw(&self, raw: PossibleFlagsT::ReprT) -> bool {
        self.repr.bitand(raw) == raw
    }

    pub fn is_set(&self, flag: PossibleFlagsT) -> bool {
        self.is_set_raw(flag.into_repr())
    }

    pub fn unrecognised_bits(&self) -> Option<PossibleFlagsT::ReprT> {
        unrecognised_bits::<PossibleFlagsT>(self.repr)
    }

    pub fn has_unrecognised_bits(&self) -> bool {
        self.unrecognised_bits().is_some()
    }
}

/// Builder
impl<PossibleFlagsT: BitBaggable> BitBag<PossibleFlagsT> {
    pub fn set(&mut self, flag: PossibleFlagsT) -> &mut Self {
        self.set_raw(flag.into_repr())
    }

    pub fn set_raw(&mut self, raw: PossibleFlagsT::ReprT) -> &mut Self {
        self.repr = self.repr.bitor(raw);
        self
    }

    pub fn set_all(&mut self) -> &mut Self {
        for (_, _, repr) in PossibleFlagsT::VARIANTS {
            self.set_raw(*repr);
        }
        self
    }

    pub fn clear_all(&mut self) -> &mut Self {
        self.repr.set_zero();
        self
    }

    pub fn unset_raw(&mut self, raw: PossibleFlagsT::ReprT) -> &mut Self {
        self.repr = self.repr.bitand(raw.not());
        self
    }

    pub fn unset(&mut self, flag: PossibleFlagsT) -> &mut Self {
        self.unset_raw(flag.into_repr())
    }

    /// Get a copy of the inner primitive
    pub const fn get(&self) -> PossibleFlagsT::ReprT {
        self.repr
    }
}

/// The error returned when calling a [`BitBag`] from a primitive which contains bits set which aren't represented by flags
#[derive(Debug)]
#[non_exhaustive]
pub struct NonFlagBits<PossibleFlagsT: BitBaggable> {
    unrecognised: PossibleFlagsT::ReprT,
}

impl<PossibleFlagsT: BitBaggable> NonFlagBits<PossibleFlagsT> {
    /// The bits which weren't recognised
    pub fn unrecognised(&self) -> PossibleFlagsT::ReprT {
        self.unrecognised
    }
}

#[cfg(feature = "std")]
impl<PossibleFlagsT: BitBaggable> std::error::Error for NonFlagBits<PossibleFlagsT>
where
    PossibleFlagsT::ReprT: Binary + Debug,
    PossibleFlagsT: Debug,
{
}

impl<PossibleFlagsT: BitBaggable> Display for NonFlagBits<PossibleFlagsT>
where
    PossibleFlagsT::ReprT: Binary,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "The bits {:#b} are not accounted for in the enum {}",
            self.unrecognised,
            type_name::<PossibleFlagsT>()
        )
    }
}

fn mask<PossibleFlagsT: BitBaggable>() -> PossibleFlagsT::ReprT {
    PossibleFlagsT::VARIANTS.iter().fold(
        PossibleFlagsT::ReprT::zero(),
        |accumulator, (_, _, repr)| accumulator.bitor(*repr),
    )
}

fn unrecognised_bits<PossibleFlagsT: BitBaggable>(
    repr: PossibleFlagsT::ReprT,
) -> Option<PossibleFlagsT::ReprT> {
    let mask = mask::<PossibleFlagsT>();
    match mask.bitor(repr) == mask {
        true => None,
        false => Some(mask.bitor(repr).bitxor(repr)),
    }
}

impl<PossibleFlagsT: BitBaggable> fmt::Display for BitBag<PossibleFlagsT> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            return f.write_str("<unset>");
        }

        let mut first = true;

        for (name, _, repr) in PossibleFlagsT::VARIANTS {
            if self.is_set_raw(*repr) {
                match first {
                    true => {
                        f.write_fmt(format_args!("{name}"))?;
                        first = false
                    }
                    false => f.write_fmt(format_args!(" | {name}"))?,
                }
            }
        }

        if self.has_unrecognised_bits() {
            match first {
                true => f.write_str("<unrecognised bits>")?,
                false => f.write_str(" | <unrecognised bits>")?,
            }
        }

        Ok(())
    }
}

#[cfg(test)]
pub(crate) mod tests {
    #[cfg(feature = "std")]
    use std::collections::HashSet;

    use super::*;
    use crate as bitbag;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, BitBaggable, BitOr)]
    #[repr(u8)]
    pub enum FooFlags {
        A = 0b0000_0001,
        B = 0b0000_0010,
        C = 0b0000_0100,
        D = 0b0000_1000,
    }

    #[cfg(feature = "std")]
    #[test]
    fn new_single_flag() {
        let bag = BitBag::<FooFlags>::new_strict(0b0000_0001).unwrap();
        let mut flags = bag.into_iter().collect::<Vec<_>>();
        assert!(flags.len() == 1);
        assert!(matches!(flags.pop(), Some(FooFlags::A)));
    }

    #[cfg(feature = "std")]
    #[test]
    fn new_multiple_flags() {
        let bag = BitBag::<FooFlags>::new_strict(0b0000_1101).unwrap();
        let flags = bag.into_iter().collect::<HashSet<_>>();
        assert!(flags.len() == 3);
        assert!(flags.contains(&FooFlags::A));
        assert!(flags.contains(&FooFlags::C));
        assert!(flags.contains(&FooFlags::D));
    }

    #[test]
    fn fail_new_single_non_flag() {
        let res = BitBag::<FooFlags>::new_strict(0b1000_0000);
        assert!(matches!(res, Err(_)));
    }

    #[test]
    fn fail_new_mixed() {
        let res = BitBag::<FooFlags>::new_strict(0b1000_0001);
        assert!(matches!(res, Err(_)));
    }

    #[cfg(feature = "std")]
    #[test]
    fn unchecked() {
        let bag = BitBag::<FooFlags>::new(0b1000_0001);
        let mut flags = bag.into_iter().collect::<Vec<_>>();
        assert!(flags.len() == 1);
        assert!(matches!(flags.pop(), Some(FooFlags::A)));
    }

    #[test]
    fn manually_set() {
        let mut bag = BitBag::<FooFlags>::default();
        bag.set(FooFlags::A).set(FooFlags::B);
        assert_eq!(bag.get(), 0b0000_0011);
    }

    #[test]
    fn manually_unset() {
        let mut bag = BitBag::<FooFlags>::new(0b0000_0011);
        bag.unset(FooFlags::A);
        assert_eq!(bag.get(), 0b0000_0010);
    }

    #[cfg(feature = "std")]
    #[test]
    fn display() {
        let bitbag = FooFlags::A | FooFlags::B;
        assert_eq!("A | B", bitbag.to_string());
        let bitbag = BitBag::<FooFlags>::default();
        assert_eq!("<unset>", bitbag.to_string());
    }
}
