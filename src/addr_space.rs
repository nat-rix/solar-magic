use crate::{addr::Addr, cart::Cart};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SystemMemoryLocation {
    /// 0x0000..=0x1fff
    Wram(u32),
    /// 0x2100..=0x21ff
    IoBbus(u8),
    /// 0x4000..=0x5fff
    Io(u16),
    /// 0x2000..=0x20ff or 0x2200..=3fff or 0x6000..=0x7fff
    Other(u16),
}

pub fn get_system_memory_location(addr: Addr) -> Option<SystemMemoryLocation> {
    let ptr = addr.to_u32();
    Some(if ptr & 0x40_8000 == 0 {
        // system area
        match addr.addr.to_le_bytes()[1] {
            0x00..=0x1f => SystemMemoryLocation::Wram(addr.addr as u32),
            0x21 => SystemMemoryLocation::IoBbus(addr.addr as u8),
            0x40..=0x5f => SystemMemoryLocation::Io(addr.addr),
            _ => SystemMemoryLocation::Other(addr.addr),
        }
    } else if addr.bank & 0xfe == 0x7e {
        // wram area
        SystemMemoryLocation::Wram(ptr & 0x1_ffff)
    } else {
        // cart area
        return None;
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CartMemoryLocation {
    Rom(u32),
    Sram(u32),
    Unmapped,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MemoryLocation {
    System(SystemMemoryLocation),
    Cart(CartMemoryLocation),
}
