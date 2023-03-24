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
//! ```
//! # use bitbag::{BitBag, BitBaggable};
//! # #[derive(BitBaggable, Clone, Copy)]
//! # #[repr(u8)]
//! # enum Flags {
//! #     A = 0b0001,
//! #     B = 0b0010,
//! #     C = 0b0100,
//! # }
//! //                                         ⬇ this bit is not defined in Flags
//! let result = BitBag::<Flags>::new_strict(0b1000);
//! assert!(matches!(
//!     result,
//!     Err(e) if e.given == 0b1000
//! ));
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
mod bitwise;
mod iter;
pub use bitbag_derive::{BitBaggable, BitOr, BoolBag};
use itertools::Itertools as _;
use num::{PrimInt, Zero as _};
use std::{
    any::type_name,
    fmt::{self, Binary, Debug, Display},
    ops::{BitAnd as _, BitOr as _, BitXor as _, Not as _},
};

/// The trait that allows an enum to be placed inside a [`BitBag`].
///
/// The basic requirements are
/// - We must tell the type system the `primitive` in `#[repr(primitive)]`
/// - We must be able to convert (from any variant) into that primitive
/// - We must know all the variant names and values
///
/// You should derive this with the `BitBaggable` derive macro
pub trait BitBaggable: Sized + 'static {
    type Repr: PrimInt;
    fn into_repr(self) -> Self::Repr;
    /// names, values and discriminants
    const VARIANTS: &'static [(&'static str, Self, Self::Repr)];
}

/// Wraps a primitive, with helper methods for checking and setting flags.
#[derive(Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct BitBag<PossibleFlagsT: BitBaggable> {
    pub repr: PossibleFlagsT::Repr,
}

impl<PossibleFlagsT: BitBaggable> Clone for BitBag<PossibleFlagsT> {
    fn clone(&self) -> Self {
        Self { repr: self.repr }
    }
}

impl<PossibleFlagsT: BitBaggable> Copy for BitBag<PossibleFlagsT> {}

impl<PossibleFlagsT: BitBaggable> BitBag<PossibleFlagsT> {
    /// Get the inner primitive
    pub fn get(&self) -> PossibleFlagsT::Repr {
        self.repr
    }

    /// Create a new wrapper, permitting (and preserving) unrecognised bits
    pub fn new(prim: PossibleFlagsT::Repr) -> Self {
        Self { repr: prim }
    }

    /// Create a wrapper with no bits set
    pub fn empty() -> Self {
        Self {
            repr: PossibleFlagsT::Repr::zero(),
        }
    }
}

impl<PossibleFlagsT: BitBaggable> Default for BitBag<PossibleFlagsT> {
    fn default() -> Self {
        Self {
            repr: PossibleFlagsT::Repr::zero(),
        }
    }
}

impl<PossibleFlagsT: BitBaggable> BitBag<PossibleFlagsT> {
    pub fn is_set_raw(&self, raw: PossibleFlagsT::Repr) -> bool {
        self.repr.bitand(raw) == raw
    }
    pub fn is_set(&self, flag: PossibleFlagsT) -> bool {
        self.is_set_raw(flag.into_repr())
    }
}

impl<PossibleFlagsT: BitBaggable> BitBag<PossibleFlagsT> {
    pub fn set_raw(&mut self, raw: PossibleFlagsT::Repr) -> &mut Self {
        self.repr = self.repr.bitor(raw);
        self
    }
    pub fn set(&mut self, flag: PossibleFlagsT) -> &mut Self {
        self.set_raw(flag.into_repr())
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
}

impl<PossibleFlagsT: BitBaggable> BitBag<PossibleFlagsT> {
    pub fn unset_raw(&mut self, raw: PossibleFlagsT::Repr) -> &mut Self {
        self.repr = self.repr.bitand(raw.not());
        self
    }
    pub fn unset(&mut self, flag: PossibleFlagsT) -> &mut Self {
        self.unset_raw(flag.into_repr())
    }
}

impl<PossibleFlagsT: BitBaggable> BitBag<PossibleFlagsT> {
    /// Check the bits of `prim`, and return an [`NonFlagBits`] error if it has bits set which aren't defined in the enum.
    pub fn new_strict(prim: PossibleFlagsT::Repr) -> Result<Self, NonFlagBits<PossibleFlagsT>> {
        match mask::<PossibleFlagsT>().bitor(prim) == mask::<PossibleFlagsT>() {
            true => Ok(Self { repr: prim }),
            false => Err(NonFlagBits { given: prim }),
        }
    }
}

fn mask<PossibleFlagsT: BitBaggable>() -> PossibleFlagsT::Repr {
    PossibleFlagsT::VARIANTS
        .iter()
        .fold(PossibleFlagsT::Repr::zero(), |accumulator, (_, _, repr)| {
            accumulator.bitor(*repr)
        })
}

#[derive(Debug)]
pub struct OverlappingVariants<ReprT> {
    pair: OverlappingPair<ReprT>,
}

#[derive(Debug)]
struct OverlappingPair<ReprT> {
    left: (&'static str, ReprT),
    right: (&'static str, ReprT),
    position: u32,
}

impl<ReprT> Display for OverlappingPair<ReprT>
where
    ReprT: PrimInt + Binary,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            left: (left_name, left),
            right: (right_name, right),
            position,
        } = self;
        let width = ReprT::zero().count_zeros();
        macro_rules! print_wide_enough {
            ($width:ident, $($bits:expr),*) => {
                match $width {
                    $(
                        ..=$bits => {
                            f.write_fmt(format_args!(
                                concat!("0b{:0", stringify!($bits), "b} ({})\n"),
                                left,
                                left_name
                            ))?;
                            f.write_fmt(format_args!(
                                concat!("0b{:0", stringify!($bits), "b} ({})\n"),
                                right,
                                right_name
                            ))?;
                            let pointer = std::iter::repeat(' ')
                                .take(*position as usize + 1)
                                .chain(['^'])
                                .collect::<String>();
                            f.write_str(&pointer)?;
                        }
                    )*
                    _ => panic!("int is too wide"),
                }
            };
        }
        print_wide_enough!(width, 8, 16, 32, 64, 128);
        Ok(())
    }
}

impl<ReprT> Display for OverlappingVariants<ReprT>
where
    ReprT: PrimInt + Binary,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "The following pair of variants has overlapping bits:")?;
        writeln!(f, "{}", self.pair)?;
        Ok(())
    }
}

pub fn check_nonoverlapping<PossibleFlagsT: BitBaggable>(
) -> Result<(), OverlappingVariants<PossibleFlagsT::Repr>> {
    for permutation in PossibleFlagsT::VARIANTS.iter().permutations(2) {
        let (left_name, _, left_repr) = permutation[0];
        let (right_name, _, right_repr) = permutation[1];
        let anded = left_repr.bitand(*right_repr);
        if anded != PossibleFlagsT::Repr::zero() {
            return Err(OverlappingVariants {
                pair: OverlappingPair {
                    left: (*left_name, *left_repr),
                    right: (*right_name, *right_repr),
                    position: anded.leading_zeros(),
                },
            });
        }
    }

    Ok(())
}

impl<PossibleFlagsT: BitBaggable> fmt::Display for BitBag<PossibleFlagsT> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.repr.is_zero() {
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

        if Self::new_strict(self.repr).is_err() {
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
#[non_exhaustive]
pub struct NonFlagBits<PossibleFlagsT: BitBaggable> {
    /// The primitive which contained non-flag bits
    pub given: PossibleFlagsT::Repr,
}

impl<PossibleFlagsT: BitBaggable> std::error::Error for NonFlagBits<PossibleFlagsT>
where
    PossibleFlagsT::Repr: Binary + Debug,
    PossibleFlagsT: Debug,
{
}

impl<PossibleFlagsT: BitBaggable> Display for NonFlagBits<PossibleFlagsT>
where
    PossibleFlagsT::Repr: Binary,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let excess = self
            .given
            .bitor(mask::<PossibleFlagsT>())
            .bitxor(mask::<PossibleFlagsT>());
        write!(
            f,
            "The bits {:#b} are not accounted for in the flags {}",
            excess,
            type_name::<PossibleFlagsT>()
        )
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::collections::HashSet;

    use indoc::indoc;

    use super::*;
    use crate as bitbag;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, BitBaggable, BitOr, BoolBag)]
    #[repr(u8)]
    pub enum FooFlags {
        A = 0b0000_0001,
        B = 0b0000_0010,
        C = 0b0000_0100,
        D = 0b0000_1000,
    }

    #[test]
    fn new_single_flag() {
        let bag = BitBag::<FooFlags>::new_strict(0b0000_0001).unwrap();
        let mut flags = bag.into_iter().collect::<Vec<_>>();
        assert!(flags.len() == 1);
        assert!(matches!(flags.pop(), Some(FooFlags::A)));
    }

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

    #[derive(BitBaggable)]
    #[repr(u16)]
    pub enum BadFlags {
        A = 0b0000_0001,
        B = 0b0000_0010,
        C = 0b0000_0100,
        D = 0b0000_1100,
    }

    #[test]
    fn non_overlapping() {
        check_nonoverlapping::<FooFlags>().unwrap();
        let e = check_nonoverlapping::<BadFlags>().unwrap_err();
        assert_eq!(
            indoc!(
                "The following pair of variants has overlapping bits:
                0b0000000000000100 (C)
                0b0000000000001100 (D)
                              ^
                "
            ),
            e.to_string()
        );
    }
}
