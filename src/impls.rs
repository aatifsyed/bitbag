//! `#[derive(Trait)]` adds a `PossibleFlagsT: Trait` bound, which is not required.
//! So manually implement here.

use crate::{BitBag, Flags};
use core::{
    fmt,
    hash::{Hash, Hasher},
};

/// Ignores unrecognised bits
impl<FlagsT: Flags> PartialEq for BitBag<FlagsT> {
    fn eq(&self, other: &Self) -> bool {
        self.repr() & FlagsT::ALL == other.repr() & FlagsT::ALL
    }
}

impl<FlagsT: Flags> Eq for BitBag<FlagsT> {}

/// Ignores unrecognised bits
impl<FlagsT: Flags> Hash for BitBag<FlagsT> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.repr() & FlagsT::ALL).hash(state);
    }
}

impl<FlagsT: Flags> fmt::Debug for BitBag<FlagsT> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        struct Set<T>(T);
        impl<T> fmt::Debug for Set<T>
        where
            T: Iterator + Clone,
            T::Item: fmt::Debug,
        {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_set().entries(self.0.clone()).finish()
            }
        }

        let names = FlagsT::VARIANTS
            .iter()
            .filter_map(|(name, _, repr)| self.is_set_raw(*repr).then_some(*name));

        f.debug_struct(FlagsT::NAME)
            .field("flags", &Set(names))
            .field("bits", &format_args!("{:#b}", self.0))
            .field(
                "unrecognized_bits",
                &format_args!("{:#b}", self.unrecognised_bits().unwrap_or_default()),
            )
            .finish()
    }
}

impl<FlagsT: Flags> Clone for BitBag<FlagsT> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<FlagsT: Flags> Copy for BitBag<FlagsT> {}

impl<FlagsT: Flags> Default for BitBag<FlagsT> {
    fn default() -> Self {
        Self::empty()
    }
}
