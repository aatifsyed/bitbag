//! `#[derive(Trait)]` adds a `PossibleFlagsT: Trait` bound, which is not required.
//! So manually implement here.

use crate::{BitBag, BitBaggable};
use core::{
    fmt::{self, Debug},
    hash::Hash,
};
use num::Zero as _;

impl<PossibleFlagsT: BitBaggable> PartialEq for BitBag<PossibleFlagsT> {
    fn eq(&self, other: &Self) -> bool {
        self.repr == other.repr
    }
}

impl<PossibleFlagsT: BitBaggable> Eq for BitBag<PossibleFlagsT> {}

impl<PossibleFlagsT: BitBaggable> Hash for BitBag<PossibleFlagsT>
where
    PossibleFlagsT::ReprT: Hash,
{
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.repr.hash(state);
    }
}

impl<PossibleFlagsT: BitBaggable> Debug for BitBag<PossibleFlagsT>
where
    PossibleFlagsT::ReprT: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BitBag").field("repr", &self.repr).finish()
    }
}

impl<PossibleFlagsT: BitBaggable> Clone for BitBag<PossibleFlagsT> {
    fn clone(&self) -> Self {
        Self { repr: self.repr }
    }
}

impl<PossibleFlagsT: BitBaggable> Copy for BitBag<PossibleFlagsT> {}

impl<PossibleFlagsT: BitBaggable> Default for BitBag<PossibleFlagsT> {
    fn default() -> Self {
        Self {
            repr: PossibleFlagsT::ReprT::zero(),
        }
    }
}
