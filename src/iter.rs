use std::iter::FromIterator;

use crate::{BitBag, BitBaggable};

impl<PossibleFlagsT: BitBaggable> FromIterator<PossibleFlagsT> for BitBag<PossibleFlagsT> {
    fn from_iter<T: IntoIterator<Item = PossibleFlagsT>>(iter: T) -> Self {
        BitBag::empty().set_each(iter).build()
    }
}

impl<PossibleFlagsT: BitBaggable> IntoIterator for BitBag<PossibleFlagsT>
where
    PossibleFlagsT: Clone,
{
    type Item = PossibleFlagsT;

    type IntoIter = BitBagIterator<PossibleFlagsT>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            bag: self,
            variant_iterator: PossibleFlagsT::VARIANTS.iter(),
        }
    }
}

pub struct BitBagIterator<PossibleFlagsT: BitBaggable> {
    bag: BitBag<PossibleFlagsT>,
    variant_iterator:
        std::slice::Iter<'static, (&'static str, PossibleFlagsT, PossibleFlagsT::ReprT)>,
}

impl<PossibleFlagsT: BitBaggable> Iterator for BitBagIterator<PossibleFlagsT>
where
    PossibleFlagsT: Clone,
{
    type Item = PossibleFlagsT;

    fn next(&mut self) -> Option<Self::Item> {
        for (_, value, _) in self.variant_iterator.by_ref() {
            if self.bag.is_set(value.clone()) {
                return Some(value.clone());
            }
        }
        None
    }
}
