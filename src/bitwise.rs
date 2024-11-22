use core::ops::{BitOr, BitOrAssign, Not};

use crate::{BitBag, Flags};

/// Toggle only the _known_ flags.
impl<FlagsT: Flags> Not for BitBag<FlagsT> {
    type Output = BitBag<FlagsT>;
    fn not(self) -> Self::Output {
        Self(!self.repr() & FlagsT::ALL)
    }
}
impl<FlagsT: Flags> Not for &BitBag<FlagsT> {
    type Output = BitBag<FlagsT>;
    fn not(self) -> Self::Output {
        BitBag(!self.repr() & FlagsT::ALL)
    }
}

mod rhs_is_flag {
    use super::*;

    impl<FlagsT: Flags> BitOr<FlagsT> for BitBag<FlagsT> {
        type Output = BitBag<FlagsT>;
        fn bitor(mut self, rhs: FlagsT) -> Self::Output {
            self.set(rhs);
            self
        }
    }
    impl<FlagsT: Flags> BitOrAssign<FlagsT> for BitBag<FlagsT> {
        fn bitor_assign(&mut self, rhs: FlagsT) {
            self.set(rhs);
        }
    }

    #[test]
    fn test() {
        use crate::tests::FooFlags::{self, *};
        let mut bag = BitBag::<FooFlags>::default();
        assert!(!bag.is_set(A));
        bag |= A;
        assert!(bag.is_set(A));
    }
}

mod rhs_is_bitbag {
    use super::*;

    /// Ignores unknown flags from the rhs
    impl<FlagsT: Flags> BitOr<BitBag<FlagsT>> for BitBag<FlagsT> {
        type Output = BitBag<FlagsT>;
        fn bitor(mut self, rhs: BitBag<FlagsT>) -> Self::Output {
            for flag in rhs {
                self.set_raw(flag.to_repr());
            }
            self
        }
    }

    /// Ignores unknown flags from the rhs
    impl<FlagsT: Flags> BitOrAssign<BitBag<FlagsT>> for BitBag<FlagsT> {
        fn bitor_assign(&mut self, rhs: BitBag<FlagsT>) {
            *self = *self | rhs;
        }
    }

    #[test]
    fn test() {
        use crate::tests::FooFlags::{self, *};
        let mut bag1 = BitBag::<FooFlags>::default();
        let bag2 = *BitBag::<FooFlags>::default().set(A);
        assert!(!bag1.is_set(A));
        bag1 |= bag2;
        assert!(bag1.is_set(A));
    }
}
#[cfg(test)]
mod tests {
    use crate::tests::FooFlags::*;

    #[test]
    fn test_or_two_flags() {
        let bag = A | B;
        assert!(bag.is_set(A));
        assert!(bag.is_set(B));
        assert!(!bag.is_set(C));
        assert!(!bag.is_set(D));
    }

    #[test]
    fn test_or_multiple_flags() {
        let bag = A | B | C;
        assert!(bag.is_set(A));
        assert!(bag.is_set(B));
        assert!(bag.is_set(C));
        assert!(!bag.is_set(D));
    }
}
