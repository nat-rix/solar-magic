use crate::cart::{Cart, Header};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Edition {
    International,
    Japanese,
    Arcade,
    EuropeRev0,
    EuropeRev1,
}

#[derive(Clone)]
pub struct OriginalCart {
    pub cart: Cart,
    pub header: Header,
    pub edition: Edition,
    pub crc32: u32,
}

impl OriginalCart {
    #[allow(clippy::result_large_err)]
    pub fn new(cart: Cart) -> Result<Self, Cart> {
        let header = cart.header();
        if !cart.is_checksum_matching(&header) {
            return Err(cart);
        }
        if cart.rom.data.len() != 0x8_0000 {
            return Err(cart);
        }
        let crc32 = crate::crc32::crc32(&cart.rom.data);
        let edition = match (crc32, header.checksum()) {
            (0xb19ed489, 0xa0da) => Edition::International,
            (0x0ec0ddac, 0x8c80) => Edition::Japanese,
            (0xeae45256, 0x4b30) => Edition::Arcade,
            (0x3c41070f, 0x09e9) => Edition::EuropeRev0,
            (0xb47f5f20, 0xc536) => Edition::EuropeRev1,
            _ => return Err(cart),
        };
        Ok(Self {
            cart,
            header,
            edition,
            crc32,
        })
    }
}
