use crate::{BitBag, BitBaggable};

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
        std::slice::Iter<'static, (&'static str, PossibleFlagsT, PossibleFlagsT::Repr)>,
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

// use strum::IntoEnumIterator;

// use crate::{BitBag, BitBaggable};

// impl<Flag: BitBaggable> IntoIterator for BitBag<Flag>
// where
//     Flag: IntoEnumIterator + Copy,
//     Flag::Repr: BitAndAssign + BitOrAssign,
// {
//     type Item = Flag;

//     type IntoIter = BitBagIterator<Flag>;

//     fn into_iter(self) -> Self::IntoIter {
//         Self::IntoIter {
//             bag: self,
//             flags_iterator: Flag::iter(),
//         }
//     }
// }

// impl<Flag: BitBaggable> IntoIterator for &BitBag<Flag>
// where
//     Flag: IntoEnumIterator + Copy,
//     Flag::Repr: BitAndAssign + BitOrAssign,
//     BitBag<Flag>: Copy,
// {
//     type Item = Flag;

//     type IntoIter = BitBagIterator<Flag>;

//     fn into_iter(self) -> Self::IntoIter {
//         Self::IntoIter {
//             bag: *self,
//             flags_iterator: Flag::iter(),
//         }
//     }
// }

// pub struct BitBagIterator<Flag: BitBaggable>
// where
//     Flag: IntoEnumIterator,
// {
//     bag: BitBag<Flag>,
//     flags_iterator: <Flag as IntoEnumIterator>::Iterator,
// }

// impl<Flag: BitBaggable> Iterator for BitBagIterator<Flag>
// where
//     Flag: IntoEnumIterator,
//     Flag: Copy,
//     Flag::Repr: BitAndAssign + BitOrAssign,
// {
//     type Item = Flag;

//     fn next(&mut self) -> Option<Self::Item> {
//         for flag in self.flags_iterator.by_ref() {
//             if self.bag.is_set(flag) {
//                 return Some(flag);
//             }
//         }
//         None
//     }
// }
