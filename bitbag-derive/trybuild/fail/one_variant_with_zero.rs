#[bitbag_derive::check]
#[repr(u8)]
enum BadFlags {
    A = 0b01,
    B = 0b10,
    Zero = 0b00,
}

fn main() {}
