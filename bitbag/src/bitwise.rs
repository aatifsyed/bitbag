use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, Not};

use crate::{BitBag, BitBaggable};

// Unary
impl<Flag: BitBaggable> Not for BitBag<Flag>
where
    Flag::Repr: BitAndAssign<Flag::Repr> + BitOrAssign<Flag::Repr>,
{
    type Output = BitBag<Flag>;

    fn not(self) -> Self::Output {
        let repr = *self;
        let repr = !repr;
        Self::new_unchecked(repr)
    }
}

mod rhs_is_flag {
    use super::*;

    impl<Flag: BitBaggable> BitAnd<Flag> for BitBag<Flag>
    where
        Flag: Copy,
        Flag::Repr: BitAndAssign<Flag::Repr> + BitOrAssign<Flag::Repr>,
    {
        type Output = BitBag<Flag>;

        fn bitand(mut self, rhs: Flag) -> Self::Output {
            if self.is_set(rhs) {
                self.set(rhs);
            }
            self
        }
    }

    impl<Flag: BitBaggable> BitAndAssign<Flag> for BitBag<Flag>
    where
        Flag: Copy,
        Flag::Repr: BitAndAssign<Flag::Repr> + BitOrAssign<Flag::Repr>,
    {
        fn bitand_assign(&mut self, rhs: Flag) {
            if self.is_set(rhs) {
                self.set(rhs);
            }
        }
    }

    impl<Flag: BitBaggable> BitOr<Flag> for BitBag<Flag>
    where
        Flag::Repr: BitAndAssign<Flag::Repr> + BitOrAssign<Flag::Repr>,
    {
        type Output = BitBag<Flag>;

        fn bitor(mut self, rhs: Flag) -> Self::Output {
            self.set(rhs);
            self
        }
    }

    impl<Flag: BitBaggable> BitOrAssign<Flag> for BitBag<Flag>
    where
        Flag::Repr: BitAndAssign<Flag::Repr> + BitOrAssign<Flag::Repr>,
    {
        fn bitor_assign(&mut self, rhs: Flag) {
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

    impl<Flag: BitBaggable> BitAnd<BitBag<Flag>> for BitBag<Flag>
    where
        Flag::Repr: BitAndAssign<Flag::Repr> + BitOrAssign<Flag::Repr>,
    {
        type Output = BitBag<Flag>;

        fn bitand(self, rhs: BitBag<Flag>) -> Self::Output {
            Self::new_unchecked(*self & *rhs)
        }
    }

    impl<Flag: BitBaggable> BitAndAssign<BitBag<Flag>> for BitBag<Flag>
    where
        Flag: Copy,
        Flag::Repr: BitAndAssign<Flag::Repr> + BitOrAssign<Flag::Repr>,
    {
        fn bitand_assign(&mut self, rhs: BitBag<Flag>) {
            *self = self.bitand(rhs);
        }
    }

    impl<Flag: BitBaggable> BitOr<BitBag<Flag>> for BitBag<Flag>
    where
        Flag::Repr: BitAndAssign<Flag::Repr> + BitOrAssign<Flag::Repr>,
    {
        type Output = BitBag<Flag>;

        fn bitor(self, rhs: BitBag<Flag>) -> Self::Output {
            Self::new_unchecked(*self | *rhs)
        }
    }

    impl<Flag: BitBaggable> BitOrAssign<BitBag<Flag>> for BitBag<Flag>
    where
        Flag::Repr: BitAndAssign<Flag::Repr> + BitOrAssign<Flag::Repr>,
        Flag: Copy,
    {
        fn bitor_assign(&mut self, rhs: BitBag<Flag>) {
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
