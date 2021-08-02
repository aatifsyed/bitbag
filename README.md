<div align="center">

[![crates-io](https://img.shields.io/crates/v/bitbag.svg)](https://crates.io/crates/bitbag)
[![docs-rs](https://docs.rs/bitbag/badge.svg)](https://docs.rs/bitbag)
[![github](https://img.shields.io/static/v1?label=&message=github&color=grey&logo=github)](https://github.com/aatifsyed/bitbag)

</div>

# bitbag

This crate provides [`BitBag`], a type intended for tracking bitflags defined in a [field-less enum](https://doc.rust-lang.org/rust-by-example/custom_types/enum/c_like.html).
Get started like this:
```rust
use bitbag::{BitBag, BitBaggable};
use strum::EnumIter;

#[derive(BitBaggable, EnumIter, Clone, Copy)]
#[repr(u8)]
enum Flags {
    A = 0b0001,
    B = 0b0010,
    C = 0b0100,
}
```
Basic functionality is provided by [`BitBag`]
```rust
let mut bag = BitBag::<Flags>::new_unchecked(0b0011);
assert!(bag.is_set(Flags::A));
assert!(bag.is_set(Flags::B));
assert!(!bag.is_set(Flags::C));

bag.set(Flags::C);
assert_eq!(*bag, 0b0111);

```
Additionally deriving [`EnumIter`], and [`Copy`] will allow fallible creation, and iteration over the set flags
```rust
let result = BitBag::<Flags>::new(0b1000);
assert!(matches!(
    result,
    Err(e) if e.given() == 0b1000
));

let bag = BitBag::<Flags>::new_unchecked(0b0110);
for flag in &bag {
    match flag {
        Flags::A => println!("Flag A was set"),
        Flags::B => println!("Flag B was set"),
        Flags::C => println!("Flag C was set"),
    }
};
```
