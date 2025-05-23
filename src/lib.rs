pub mod addr;
pub mod addr_space;
pub mod cart;
mod crc32;
mod datatypes;
pub mod disasm;
pub mod instruction;
pub mod original_cart;
pub mod rewriter;
pub mod tvl;

pub(crate) use datatypes::vecmap::VecMap;

pub mod pf {
    pub const C: u8 = 1 << 0;
    pub const Z: u8 = 1 << 1;
    pub const I: u8 = 1 << 2;
    pub const D: u8 = 1 << 3;
    pub const X: u8 = 1 << 4;
    pub const M: u8 = 1 << 5;
    pub const V: u8 = 1 << 6;
    pub const N: u8 = 1 << 7;
}
