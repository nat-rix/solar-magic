use bytemuck::*;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Zeroable)]
pub struct Addr {
    pub bank: u8,
    pub addr: u16,
}

impl Addr {
    pub const NULL: Self = Self::new(0, 0);
    pub const MAX: Self = Self::new(0xff, 0xffff);

    pub const fn new(bank: u8, addr: u16) -> Self {
        Self { bank, addr }
    }

    pub const fn from_bytes(bytes: [u8; 3]) -> Self {
        let [addr @ .., bank] = bytes;
        Self {
            bank,
            addr: u16::from_le_bytes(addr),
        }
    }

    pub const fn into_bytes(self) -> [u8; 3] {
        let [lo, hi] = self.addr.to_le_bytes();
        [lo, hi, self.bank]
    }

    pub const fn to_u32(&self) -> u32 {
        let [lo, hi, ba] = self.into_bytes();
        u32::from_le_bytes([lo, hi, ba, 0])
    }

    pub const fn from_u32(n: u32) -> Self {
        let [bytes @ .., _] = n.to_le_bytes();
        Self::from_bytes(bytes)
    }

    pub const fn add16(mut self, val: u16) -> Self {
        self.addr = self.addr.wrapping_add(val);
        self
    }

    pub const fn add16_repl(&mut self, val: u16) -> Self {
        let old = *self;
        *self = self.add16(val);
        old
    }

    pub const fn add24(self, val: u32) -> Self {
        Self::from_u32(self.to_u32().wrapping_add(val))
    }

    pub const fn sub24(self, val: u32) -> Self {
        Self::from_u32(self.to_u32().wrapping_sub(val))
    }

    pub fn range_around(self, radius: u16) -> core::ops::RangeInclusive<Self> {
        let lhs = Self::new(self.bank, self.addr.saturating_sub(radius));
        let rhs = Self::new(self.bank, self.addr.saturating_add(radius));
        lhs..=rhs
    }
}

impl core::fmt::Display for Addr {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "{:02x}:{:04x}", self.bank, self.addr)
    }
}

impl core::fmt::Debug for Addr {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "{:02x}:{:04x}", self.bank, self.addr)
    }
}
