use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, Not};

use crate::{BitBag, BitBaggable};

// Unary
impl<PossibleFlagsT: BitBaggable> Not for BitBag<PossibleFlagsT> {
    type Output = BitBag<PossibleFlagsT>;

    fn not(self) -> Self::Output {
        Self { repr: !self.repr }
    }
}

mod rhs_is_flag {
    use super::*;

    impl<PossibleFlagsT: BitBaggable> BitAnd<PossibleFlagsT> for BitBag<PossibleFlagsT> {
        type Output = BitBag<PossibleFlagsT>;

        fn bitand(mut self, rhs: PossibleFlagsT) -> Self::Output {
            let rhs = rhs.into_repr();
            if self.is_set_raw(rhs) {
                self.set_raw(rhs);
            }
            self
        }
    }

    impl<PossibleFlagsT: BitBaggable> BitAndAssign<PossibleFlagsT> for BitBag<PossibleFlagsT> {
        fn bitand_assign(&mut self, rhs: PossibleFlagsT) {
            let rhs = rhs.into_repr();
            if self.is_set_raw(rhs) {
                self.set_raw(rhs);
            }
        }
    }

    impl<PossibleFlagsT: BitBaggable> BitOr<PossibleFlagsT> for BitBag<PossibleFlagsT> {
        type Output = BitBag<PossibleFlagsT>;

        fn bitor(mut self, rhs: PossibleFlagsT) -> Self::Output {
            self.set(rhs);
            self
        }
    }

    impl<PossibleFlagsT: BitBaggable> BitOrAssign<PossibleFlagsT> for BitBag<PossibleFlagsT> {
        fn bitor_assign(&mut self, rhs: PossibleFlagsT) {
            self.set(rhs);
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::tests::FooFlags::{self, *};

        #[test]
        fn test_or_assign() {
            let mut bag = BitBag::<FooFlags>::default();
            assert!(!bag.is_set(A));
            bag |= A;
            assert!(bag.is_set(A));
        }

        #[test]
        fn test_and_assign() {
            let mut bag = BitBag::<FooFlags>::default();
            assert!(!bag.is_set(A));
            bag &= A;
            assert!(!bag.is_set(A));
            bag.set(A);
            assert!(bag.is_set(A));
            bag &= A;
            assert!(bag.is_set(A));
        }
    }
}

mod rhs_is_bitbag {
    use super::*;

    impl<PossibleFlagsT: BitBaggable> BitAnd<BitBag<PossibleFlagsT>> for BitBag<PossibleFlagsT> {
        type Output = BitBag<PossibleFlagsT>;

        fn bitand(self, rhs: BitBag<PossibleFlagsT>) -> Self::Output {
            Self::new_unchecked(self.repr & rhs.repr)
        }
    }

    impl<PossibleFlagsT: BitBaggable> BitAndAssign<BitBag<PossibleFlagsT>> for BitBag<PossibleFlagsT> {
        fn bitand_assign(&mut self, rhs: BitBag<PossibleFlagsT>) {
            *self = self.bitand(rhs);
        }
    }

    impl<PossibleFlagsT: BitBaggable> BitOr<BitBag<PossibleFlagsT>> for BitBag<PossibleFlagsT> {
        type Output = BitBag<PossibleFlagsT>;

        fn bitor(self, rhs: BitBag<PossibleFlagsT>) -> Self::Output {
            Self::new_unchecked(self.repr | rhs.repr)
        }
    }

    impl<PossibleFlagsT: BitBaggable> BitOrAssign<BitBag<PossibleFlagsT>> for BitBag<PossibleFlagsT> {
        fn bitor_assign(&mut self, rhs: BitBag<PossibleFlagsT>) {
            *self = self.bitor(rhs);
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::tests::FooFlags::{self, *};

        #[test]
        fn test_or_assign() {
            let mut bag1 = BitBag::<FooFlags>::default();
            let bag2 = *BitBag::<FooFlags>::default().set(A);
            assert!(!bag1.is_set(A));
            bag1 |= bag2;
            assert!(bag1.is_set(A));
        }

        #[test]
        fn test_and_assign() {
            let mut bag1 = BitBag::<FooFlags>::default();
            let bag2 = *BitBag::<FooFlags>::default().set(A);
            assert!(!bag1.is_set(A));
            bag1 &= bag2;
            assert!(!bag1.is_set(A));
            bag1.set(A);
            assert!(bag1.is_set(A));
            bag1 &= bag2;
            assert!(bag1.is_set(A));
        }
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
