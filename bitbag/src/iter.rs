use std::ops::{BitAndAssign, BitOrAssign};

use strum::IntoEnumIterator;

use crate::{BitBag, BitBaggable};

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
