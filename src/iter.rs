use crate::{BitBag, Flags};

impl<FlagsT: Flags> core::iter::FromIterator<FlagsT> for BitBag<FlagsT> {
    fn from_iter<T: IntoIterator<Item = FlagsT>>(iter: T) -> Self {
        BitBag::empty().set_each(iter).build()
    }
}

impl<FlagsT: Flags> IntoIterator for BitBag<FlagsT> {
    type Item = &'static FlagsT;
    type IntoIter = BitBagIterator<FlagsT>;
    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            bag: self,
            variant_iterator: FlagsT::VARIANTS.iter(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct BitBagIterator<FlagsT: Flags> {
    bag: BitBag<FlagsT>,
    variant_iterator: core::slice::Iter<'static, (&'static str, FlagsT, FlagsT::Repr)>,
}

impl<FlagsT: Flags> Iterator for BitBagIterator<FlagsT> {
    type Item = &'static FlagsT;
    fn next(&mut self) -> Option<Self::Item> {
        let Self {
            bag,
            variant_iterator,
        } = self;
        variant_iterator
            .by_ref()
            .map(|(_, value, _)| value)
            .find(|&value| bag.is_set_raw(value.to_repr()))
    }
}
