//! This crate provides [`BitBag`], a type intended for tracking bitflags defined in a [field-less enum](https://doc.rust-lang.org/rust-by-example/custom_types/enum/c_like.html).
//! Get started like this:
//! ```
//! #[derive(bitbag::Flags)]
//! #[repr(u8)]
//! enum MyFlags {
//!     A = 0b0001,
//!     B = 0b0010,
//!     C = 0b0100,
//! }
//! ```
//! Basic functionality is provided by [`Flags`]
//! ```
//! # #[derive(bitbag::Flags)]
//! # #[repr(u8)]
//! # enum MyFlags {
//! #     A = 0b0001,
//! #     B = 0b0010,
//! #     C = 0b0100,
//! # }
//! let mut bag = bitbag::BitBag::<MyFlags>::new_unchecked(0b0011);
//! assert!(bag.is_set(MyFlags::A));
//! assert!(bag.is_set(MyFlags::B));
//! assert!(!bag.is_set(MyFlags::C));
//!
//! bag.set(MyFlags::C);
//! assert_eq!(bag.repr(), 0b0111);
//!
//! ```
//! Deriving [`BitOr`] will also give you very ergonomic constructors
//! ```
//! # stringify! {
//! #[derive(bitbag::BitOr)]
//! enum MyFlags { ... }
//! # };
//! # #[derive(bitbag::Flags, bitbag::BitOr)]
//! # #[repr(u8)]
//! # enum MyFlags {
//! #     A = 0b0001,
//! #     B = 0b0010,
//! #     C = 0b0100,
//! # }
//! use MyFlags::*;
//! let bag = A | B | C;
//! assert!(bag.is_set(MyFlags::A));
//! assert!(bag.is_set(MyFlags::B));
//! assert!(bag.is_set(MyFlags::C));
//! ```
//! You can also choose to reject unrecognised bits, and iterate over the set flags.
//! ```
//! # #[derive(bitbag::Flags, bitbag::BitOr, Debug, Clone)]
//! # #[repr(u8)]
//! # enum MyFlags {
//! #     A = 0b0001,
//! #     B = 0b0010,
//! #     C = 0b0100,
//! # }
//! let e = bitbag::BitBag::<MyFlags>::new_checked(0b1000).unwrap_err();
//! assert_eq!(e.to_string(), "The bits 0b1000 are not accounted for in MyFlags");
//!
//! let bag = bitbag::BitBag::<MyFlags>::new_checked(0b0110).unwrap();
//! for flag in bag {
//!     match flag {
//!         MyFlags::A => println!("Flag A was set"),
//!         MyFlags::B => println!("Flag B was set"),
//!         MyFlags::C => println!("Flag C was set"),
//!     }
//! };
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

mod bitwise;
mod impls;
mod iter;
pub use bitbag_derive::{check, BitOr, Flags};
use core::{
    fmt,
    ops::{BitAnd as _, BitOr as _, Not as _},
};

/// A type that can be used as an `enum`'s `#[repr(..)]`.
///
/// This trait is _sealed_, and may not be implemented for other types.
pub trait Repr: sealed::Sealed {}

mod sealed {
    use core::{
        fmt,
        hash::Hash,
        ops::{BitAnd, BitOr, BitOrAssign, BitXor, Not},
    };
    pub trait Sealed:
        BitAnd<Output = Self>
        + BitOr<Output = Self>
        + BitOrAssign
        + BitXor<Output = Self>
        + Not<Output = Self>
        + Sized
        + Copy
        + PartialEq
        + Hash
        + fmt::Debug
        + fmt::Binary
        + Default
    {
        const ZERO: Self;
    }
}
use sealed::Sealed as _;

macro_rules! impl_repr {
    ($($ty:ty),* $(,)?) => {
        $(
            impl Repr for $ty {}
            impl sealed::Sealed for $ty {
                const ZERO: Self = 0;
            }
        )*
    };
}

impl_repr! {
    u8, u16, u32, u64, u128,
    i8, i16, i32, i64, i128,
    isize, usize,
}

/// The trait that allows an enum to be placed inside a [`BitBag`].
///
/// You SHOULD derive this with the [`Flags`](bitbag_derive::Flags) derive macro.
pub trait Flags: Sized + 'static {
    /// The `<primitive>` in `#[repr(<primitive>)]`
    type Repr: Repr;
    /// Convert from a variant to its primitive.
    fn to_repr(&self) -> Self::Repr;
    /// Name of the enum.
    const NAME: &str;
    /// Names, values and discriminants.
    const VARIANTS: &'static [(&'static str, Self, Self::Repr)];
    /// All defined bits.
    const ALL: Self::Repr;
}

/// Wraps a primitive, with helper methods for checking and setting flags.
#[repr(transparent)]
pub struct BitBag<FlagsT: Flags>(pub FlagsT::Repr);

/// Constructors
impl<FlagsT: Flags> BitBag<FlagsT> {
    /// New bag, permitting (and preserving) unrecognised bits
    pub const fn new_unchecked(prim: FlagsT::Repr) -> Self {
        Self(prim)
    }

    /// New bag with no bits set
    pub const fn empty() -> Self {
        Self(FlagsT::Repr::ZERO)
    }

    /// New bag with all defined bits set
    pub const fn all() -> Self {
        Self(FlagsT::ALL)
    }

    /// Check the bits of `prim`, and return a [`NonFlagBits`] error if it has bits set which aren't defined in the enum.
    pub fn new_checked(prim: FlagsT::Repr) -> Result<Self, NonFlagBits<FlagsT::Repr>> {
        match unrecognised_bits::<FlagsT>(prim) {
            Some(unrecognised) => Err(NonFlagBits {
                unrecognised,
                ty_name: FlagsT::NAME,
            }),
            None => Ok(Self(prim)),
        }
    }
}

/// Properties
impl<FlagsT: Flags> BitBag<FlagsT> {
    pub fn is_empty(&self) -> bool {
        self.0 == FlagsT::Repr::ZERO
    }

    pub fn is_set_raw(&self, raw: FlagsT::Repr) -> bool {
        self.0 & raw == raw
    }

    pub fn is_set(&self, flag: FlagsT) -> bool {
        self.is_set_raw(flag.to_repr())
    }

    pub fn unrecognised_bits(&self) -> Option<FlagsT::Repr> {
        unrecognised_bits::<FlagsT>(self.0)
    }

    pub fn has_unrecognised_bits(&self) -> bool {
        self.unrecognised_bits().is_some()
    }

    pub const fn repr(&self) -> FlagsT::Repr {
        self.0
    }
}

/// Builder
impl<FlagsT: Flags> BitBag<FlagsT> {
    pub fn set_all(&mut self) -> &mut Self {
        self.0 = FlagsT::ALL;
        self
    }

    pub fn clear_all(&mut self) -> &mut Self {
        self.0 = FlagsT::Repr::ZERO;
        self
    }

    pub fn set(&mut self, flag: FlagsT) -> &mut Self {
        self.set_raw(flag.to_repr())
    }

    pub fn set_raw(&mut self, raw: FlagsT::Repr) -> &mut Self {
        self.0 |= raw;
        self
    }

    pub fn set_each(&mut self, flags: impl IntoIterator<Item = FlagsT>) -> &mut Self {
        for flag in flags {
            self.set(flag);
        }
        self
    }

    pub fn set_each_raw(&mut self, flags: impl IntoIterator<Item = FlagsT::Repr>) -> &mut Self {
        for flag in flags {
            self.set_raw(flag);
        }
        self
    }

    pub fn unset(&mut self, flag: FlagsT) -> &mut Self {
        self.unset_raw(flag.to_repr())
    }

    pub fn unset_raw(&mut self, raw: FlagsT::Repr) -> &mut Self {
        self.0 = self.0.bitand(raw.not());
        self
    }

    pub fn unset_each(&mut self, flags: impl IntoIterator<Item = FlagsT>) -> &mut Self {
        for flag in flags {
            self.unset(flag);
        }
        self
    }

    pub fn unset_each_raw(&mut self, flags: impl IntoIterator<Item = FlagsT::Repr>) -> &mut Self {
        for flag in flags {
            self.unset_raw(flag);
        }
        self
    }

    pub const fn build(&self) -> Self {
        *self
    }
}

/// Set operations
impl<FlagsT: Flags> BitBag<FlagsT> {
    /// A new bitbag with bits that are both in `self` and `other`
    pub fn union(&self, other: impl IntoIterator<Item = FlagsT>) -> Self {
        *self.clone().set_each(other)
    }

    /// A new bitbag with bits that are in `self` but not in `other`
    pub fn difference(&self, other: impl IntoIterator<Item = FlagsT>) -> Self {
        *self.clone().unset_each(other)
    }

    /// A new bitbag with bits that are in both `self` and `other`
    pub fn intersection(&self, other: impl IntoIterator<Item = FlagsT>) -> Self {
        let mut intersection = Self::empty();
        for flag in other {
            if self.is_set_raw(flag.to_repr()) {
                intersection.set(flag);
            }
        }
        intersection
    }

    /// A new bitbag with bits that in are `self` or `other`, but not both
    pub fn symmetric_difference(&self, other: impl IntoIterator<Item = FlagsT>) -> Self {
        let mut difference = Self::empty();
        let right = other.into_iter().collect::<Self>();
        let left = *self;
        for flag in left {
            if !right.is_set_raw(flag.to_repr()) {
                difference.set_raw(flag.to_repr());
            }
        }
        for flag in right {
            if !left.is_set_raw(flag.to_repr()) {
                difference.set_raw(flag.to_repr());
            }
        }
        difference
    }
}

/// The error returned when calling a [`BitBag`] from a primitive which contains bits set which aren't represented by flags
pub struct NonFlagBits<ReprT> {
    pub unrecognised: ReprT,
    ty_name: &'static str,
}

impl<ReprT> core::error::Error for NonFlagBits<ReprT> where ReprT: fmt::Binary {}

impl<ReprT> fmt::Display for NonFlagBits<ReprT>
where
    ReprT: fmt::Binary,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            unrecognised,
            ty_name,
        } = self;
        f.write_fmt(format_args!(
            "The bits {unrecognised:#b} are not accounted for in {ty_name}"
        ))
    }
}

impl<ReprT> fmt::Debug for NonFlagBits<ReprT>
where
    ReprT: fmt::Binary,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            unrecognised,
            ty_name,
        } = self;
        f.debug_struct("NonFlagBits")
            .field("unrecognised", &format_args!("{unrecognised:#b}"))
            .field("ty_name", ty_name)
            .finish()
    }
}

const fn mask<FlagsT: Flags>() -> FlagsT::Repr {
    FlagsT::ALL
}

fn unrecognised_bits<FlagsT: Flags>(repr: FlagsT::Repr) -> Option<FlagsT::Repr> {
    let mask = mask::<FlagsT>();
    match mask.bitor(repr) == mask {
        true => None,
        false => Some(repr & !mask),
    }
}

impl<FlagsT: Flags> fmt::Display for BitBag<FlagsT> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            return f.write_str("<unset>");
        }

        let mut first = true;

        for (name, _, repr) in FlagsT::VARIANTS {
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
                true => f.write_str("...")?,
                false => f.write_str(" | ...")?,
            }
        }

        Ok(())
    }
}

#[cfg(all(test, feature = "std"))]
pub(crate) mod tests {
    use super::*;

    use derive_quickcheck_arbitrary::Arbitrary;
    use quickcheck::quickcheck;
    use std::collections::{BTreeSet, HashSet};

    use crate as bitbag;

    #[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Flags, BitOr, Arbitrary, PartialOrd, Ord)]
    #[repr(u8)]
    pub enum FooFlags {
        A = 0b0000_0001,
        B = 0b0000_0010,
        C = 0b0000_0100,
        D = 0b0000_1000,
    }

    #[test]
    fn new_single_flag() {
        let bag = BitBag::<FooFlags>::new_checked(0b0000_0001).unwrap();
        let mut flags = bag.into_iter().collect::<Vec<_>>();
        assert!(flags.len() == 1);
        assert!(matches!(flags.pop(), Some(FooFlags::A)));
    }

    #[test]
    fn new_multiple_flags() {
        let bag = BitBag::<FooFlags>::new_checked(0b0000_1101).unwrap();
        let flags = bag.into_iter().collect::<HashSet<_>>();
        assert!(flags.len() == 3);
        assert!(flags.contains(&FooFlags::A));
        assert!(flags.contains(&FooFlags::C));
        assert!(flags.contains(&FooFlags::D));
    }

    #[test]
    fn fail_new_single_non_flag() {
        BitBag::<FooFlags>::new_checked(0b1000_0000).unwrap_err();
    }

    #[test]
    fn fail_new_mixed() {
        BitBag::<FooFlags>::new_checked(0b1000_0001).unwrap_err();
    }

    #[test]
    fn unchecked() {
        let bag = BitBag::<FooFlags>::new_unchecked(0b1000_0001);
        let flags = bag.into_iter().collect::<Vec<_>>();
        assert_eq!(flags, vec![&FooFlags::A]);
    }

    #[test]
    fn manually_set() {
        let mut bag = BitBag::<FooFlags>::default();
        bag.set(FooFlags::A).set(FooFlags::B);
        assert_eq!(bag.repr(), 0b0000_0011);
    }

    #[test]
    fn manually_unset() {
        let mut bag = BitBag::<FooFlags>::new_unchecked(0b0000_0011);
        bag.unset(FooFlags::A);
        assert_eq!(bag.repr(), 0b0000_0010);
    }

    #[test]
    fn display() {
        let bitbag = FooFlags::A | FooFlags::B;
        assert_eq!("A | B", bitbag.to_string());
        let bitbag = BitBag::<FooFlags>::default();
        assert_eq!("<unset>", bitbag.to_string());
    }

    #[derive(Debug, Clone, Copy, Arbitrary)]
    enum Op {
        Set(FooFlags),
        Unset(FooFlags),
        Test(FooFlags),
        Clear,
    }

    fn do_setlike(ops: Vec<Op>) {
        let mut ours_by_flag = BitBag::<FooFlags>::empty();
        let mut ours_by_repr = BitBag::<FooFlags>::empty();
        let mut theirs = BTreeSet::<FooFlags>::new();
        for op in ops {
            match op {
                Op::Set(it) => {
                    ours_by_flag.set(it);
                    ours_by_repr.set_raw(it.to_repr());
                    theirs.insert(it);
                }
                Op::Unset(it) => {
                    ours_by_flag.unset(it);
                    ours_by_repr.unset_raw(it.to_repr());
                    theirs.remove(&it);
                }
                Op::Test(it) => {
                    assert_eq!(ours_by_flag.is_set(it), theirs.contains(&it));
                    assert_eq!(
                        ours_by_flag.is_set(it),
                        ours_by_repr.is_set_raw(it.to_repr())
                    );
                }
                Op::Clear => {
                    ours_by_flag.clear_all();
                    ours_by_repr.clear_all();
                    theirs.clear();
                }
            }
            assert_eq!(
                ours_by_flag.into_iter().copied().collect::<BTreeSet<_>>(),
                theirs
            );
            assert_eq!(
                ours_by_repr.into_iter().copied().collect::<BTreeSet<_>>(),
                theirs
            );
        }
    }

    quickcheck! {
        fn setlike(ops: Vec<Op>) -> () {
            do_setlike(ops);
        }
    }
}
