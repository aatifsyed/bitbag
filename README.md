<div align="center">

[![crates-io](https://img.shields.io/crates/v/bitbag.svg)](https://crates.io/crates/bitbag)
[![docs-rs](https://docs.rs/bitbag/badge.svg)](https://docs.rs/bitbag)
[![github](https://img.shields.io/static/v1?label=&message=github&color=grey&logo=github)](https://github.com/aatifsyed/bitbag)

</div>

<!-- cargo-rdme start -->

This crate provides [`BitBag`], a type intended for tracking bitflags defined in a [field-less enum](https://doc.rust-lang.org/rust-by-example/custom_types/enum/c_like.html).
Get started like this:
```rust
#[derive(bitbag::Flags)]
#[repr(u8)]
enum MyFlags {
    A = 0b0001,
    B = 0b0010,
    C = 0b0100,
}
```
Basic functionality is provided by [`Flags`]
```rust
let mut bag = bitbag::BitBag::<MyFlags>::new_unchecked(0b0011);
assert!(bag.is_set(MyFlags::A));
assert!(bag.is_set(MyFlags::B));
assert!(!bag.is_set(MyFlags::C));

bag.set(MyFlags::C);
assert_eq!(bag.repr(), 0b0111);

```
Deriving [`BitOr`] will also give you very ergonomic constructors
```rust
#[derive(bitbag::BitOr)]
enum MyFlags { ... }
use MyFlags::*;
let bag = A | B | C;
assert!(bag.is_set(MyFlags::A));
assert!(bag.is_set(MyFlags::B));
assert!(bag.is_set(MyFlags::C));
```
You can also choose to reject unrecognised bits, and iterate over the set flags.
```rust
let e = bitbag::BitBag::<MyFlags>::new_checked(0b1000).unwrap_err();
assert_eq!(e.to_string(), "The bits 0b1000 are not accounted for in MyFlags");

let bag = bitbag::BitBag::<MyFlags>::new_checked(0b0110).unwrap();
for flag in bag {
    match flag {
        MyFlags::A => println!("Flag A was set"),
        MyFlags::B => println!("Flag B was set"),
        MyFlags::C => println!("Flag C was set"),
    }
};
```

<!-- cargo-rdme end -->
