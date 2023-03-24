mod sys {
    pub const FLAG_A: u32 = 0b01;
    pub const FLAG_B: u32 = 0b11;
}

#[bitbag_derive::check]
#[repr(u8)]
enum BadFlags {
    A = sys::FLAG_A as _,
    B = sys::FLAG_B as _,
}

fn main() {}
