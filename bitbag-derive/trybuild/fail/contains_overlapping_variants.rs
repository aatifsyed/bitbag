#[bitbag_derive::check]
#[repr(u8)]
enum BadFlags {
    A = 0b0001,
    B = 0b0110,
    C = 0b0100,
}

fn main() {}
