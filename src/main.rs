use bitbag::BitBag;

#[derive(BitBag)]
#[repr(u8)]
pub enum FooFlags {
    A = 1,
    B = 2,
}

fn main() {}
