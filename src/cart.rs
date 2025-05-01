use bytemuck::*;

use crate::{
    addr::Addr,
    addr_space::{CartMemoryLocation, MemoryLocation, SystemMemoryLocation},
    tvl::{TBool, TU24},
};

#[derive(Debug, Clone)]
pub struct Rom {
    pub data: Vec<u8>,
}

impl Rom {
    pub fn from_bytes(mut data: Vec<u8>) -> Self {
        let offset = data.len() & 0x3ff;
        if offset != 0 {
            data = data[offset..].to_vec();
        }
        // make mirrors until rom is a power of 2.
        while data.len().count_ones() > 1 {
            let index = data.len().trailing_zeros();
            data.extend_from_within(data.len() - (1 << index)..);
        }
        if data.is_empty() {
            data = vec![0xff];
        }
        Self { data }
    }

    pub fn read(&self, addr: u32) -> u8 {
        self.data[addr as usize & (self.data.len() - 1)]
    }

    pub fn read_header(&self, addr: u32) -> Header {
        let mut hdr = Header::zeroed();
        for i in 0..core::mem::size_of_val(&hdr) {
            bytes_of_mut(&mut hdr)[i] = self.read(addr + i as u32);
        }
        hdr
    }

    pub fn available_headers(&self) -> impl Iterator<Item = (Header, MappingType)> {
        [MappingType::LoRom, MappingType::HiRom, MappingType::ExHiRom]
            .into_iter()
            .map(|ty| (self.read_header(ty.get_rom_offset()), ty))
    }

    pub fn get_best_header(&self) -> (Header, MappingType) {
        let chksum = self.checksum();
        self.available_headers()
            .max_by_key(|(hdr, ty)| hdr.score(*ty, chksum))
            .unwrap()
    }

    pub fn checksum(&self) -> u16 {
        self.data.iter().fold(0, |a, b| a.wrapping_add(*b as u16))
    }

    pub const fn len(&self) -> u32 {
        self.data.len() as _
    }

    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum MappingType {
    LoRom,
    HiRom,
    ExHiRom,
}

impl MappingType {
    pub const fn get_rom_offset(&self) -> u32 {
        match self {
            Self::LoRom => 0x7fb0,
            Self::HiRom => 0xffb0,
            Self::ExHiRom => 0x40ffb0,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Zeroable, TransparentWrapper, Pod)]
#[repr(transparent)]
pub struct Title(pub [u8; 21]);

impl Title {
    pub fn unpadded_bytes(&self) -> &[u8] {
        let mut slice: &[u8] = &self.0;
        if slice[20] == 0 {
            slice = &slice[..20];
        }
        slice.trim_ascii_end()
    }

    pub const fn has_early_exthdr(&self) -> bool {
        self.0[20] == 0
    }
}

impl core::fmt::Display for Title {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        use core::fmt::Write;
        for c in self
            .unpadded_bytes()
            .iter()
            .take_while(|&&c| c != 0)
            .map(|c| match c {
                // these JIS X 0201 chars are different from ascii
                b'\\' => '¥',
                b'~' => '‾',
                // ascii and C0 codes
                0..=0xa0 => *c as char,
                // C1 codes
                0xa1..=0xdf => char::from_u32(u32::from(*c) + u32::from('｡')).unwrap(),
                // invalid JIS X 0201 characters
                0xe0..=0xff => char::REPLACEMENT_CHARACTER,
            })
        {
            f.write_char(c)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, Zeroable, TransparentWrapper, Pod)]
#[repr(transparent)]
pub struct BankedSize(pub u8);

impl BankedSize {
    pub fn bytes(&self) -> u32 {
        match self.0 {
            0 => 0,
            _ => 1024 << self.0.min(21),
        }
    }

    pub const fn is_empty(&self) -> bool {
        self.0 == 0
    }
}

impl core::fmt::Display for BankedSize {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self.0 {
            1..=9 => write!(f, "{}KiB", 1 << self.0),
            10..=19 => write!(f, "{}MiB", 1 << (self.0 - 10)),
            20..=21 => write!(f, "{}GiB", 1 << (self.0 - 20)),
            _ => write!(f, "0B"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CoprocessorType(pub u16);

impl CoprocessorType {
    pub const DSP: Self = Self(0);
    pub const GSU: Self = Self(1);
    pub const OBC1: Self = Self(2);
    pub const SA1: Self = Self(3);
    pub const DD1: Self = Self(4);
    pub const RTC: Self = Self(5);
    pub const OTHER: Self = Self(14);
    pub const SPC7110: Self = Self(15);
    pub const ST01X: Self = Self(16);
    pub const ST018: Self = Self(17);
    pub const CX4: Self = Self(31);
}

#[derive(Debug, Clone, Copy, Zeroable, Pod)]
#[repr(C)]
pub struct Header {
    pub maker_code: [u8; 2],
    pub game_code: [u8; 4],
    pub reserved: [u8; 6],
    pub expansion_flash_size: BankedSize,
    pub expansion_ram_size: BankedSize,
    pub special_version: u8,
    pub chipset_subtype: u8,
    pub title: Title,
    pub mode: u8,
    pub chipset: u8,
    pub rom_size: BankedSize,
    pub ram_size: BankedSize,
    pub country: u8,
    pub developer_id: u8,
    pub rom_version: u8,
    pub checksum_cpl: [u8; 2],
    pub checksum: [u8; 2],
}

impl Header {
    pub const fn has_early_exthdr(&self) -> bool {
        self.title.has_early_exthdr()
    }

    pub const fn has_later_exthdr(&self) -> bool {
        self.developer_id == 0x33
    }

    pub const fn has_exthdr(&self) -> bool {
        self.has_early_exthdr() || self.has_later_exthdr()
    }

    pub const fn coprocessor_type(&self) -> Option<CoprocessorType> {
        if self.mode < 3 {
            return None;
        }
        let mut ty = CoprocessorType((self.mode >> 4) as u16);
        if ty.0 == 15 && self.has_exthdr() {
            ty.0 |= (self.chipset_subtype as u16) << 4;
        }
        Some(ty)
    }

    pub const fn mapping_type(&self) -> MappingType {
        match self.mode & 15 {
            1 | 10 => MappingType::HiRom,
            5 => MappingType::ExHiRom,
            _ => MappingType::LoRom,
        }
    }

    pub const fn checksum(&self) -> u16 {
        u16::from_le_bytes(self.checksum)
    }

    pub const fn checksum_cpl(&self) -> u16 {
        u16::from_le_bytes(self.checksum_cpl)
    }

    pub fn score(&self, mapping: MappingType, checksum: u16) -> i32 {
        let mut score = 0;
        if self.mapping_type() == mapping {
            score += 30;
        }
        for chr in self.title.unpadded_bytes() {
            score += match chr {
                // normal ASCII printables, games are supposed to use these
                0x20..=0x7e => 3,
                // JIS X0201 characters make sense in a japanese title
                0xa1..=0xdf => 1,
                // these should not be in a title
                _ => -5,
            };
        }
        if self.has_exthdr() {
            score += 5;
        }
        if (6..=12).contains(&self.rom_size.0) {
            score += 15;
        }
        if (0..=6).contains(&self.ram_size.0) {
            score += 15;
        }
        if self.checksum() == !self.checksum_cpl() {
            score += 15;
        }
        if self.checksum() == checksum {
            score += 30;
        }
        score
    }
}

#[derive(Debug, Clone)]
pub struct CartConfig {
    pub mapping_type: MappingType,
    pub sram_size: BankedSize,
}

#[derive(Debug, Clone)]
struct Mapping {
    map: [CartMemoryLocation; 2048],
}

impl Mapping {
    pub fn get(&self, addr: Addr) -> &CartMemoryLocation {
        &self.map[((addr.bank as usize) << 3) | (addr.addr >> 13) as usize]
    }
}

impl Mapping {
    pub const fn new() -> Self {
        Self {
            map: [CartMemoryLocation::Unmapped; 2048],
        }
    }

    fn map_areas(
        &mut self,
        bank_range: core::ops::RangeInclusive<u8>,
        addr_range: core::ops::RangeInclusive<u16>,
        mut f: impl FnMut(u32) -> CartMemoryLocation,
    ) {
        let addr_range = (*addr_range.start() >> 13)..=(*addr_range.end() >> 13);
        let mut offset = 0;
        for bank in bank_range {
            for bits in addr_range.clone() {
                let idx = bits as usize | ((bank as usize) << 3);
                self.map[idx] = f(offset);
                offset += 0x2000;
            }
        }
    }

    pub fn map_lo(
        &mut self,
        bank_range: core::ops::RangeInclusive<u8>,
        f: impl FnMut(u32) -> CartMemoryLocation,
    ) {
        self.map_areas(bank_range, 0x0000..=0x7fff, f);
    }

    pub fn map_hi(
        &mut self,
        bank_range: core::ops::RangeInclusive<u8>,
        f: impl FnMut(u32) -> CartMemoryLocation,
    ) {
        self.map_areas(bank_range, 0x8000..=0xffff, f);
    }

    fn map(
        &mut self,
        bank_range: core::ops::RangeInclusive<u8>,
        mut f: impl FnMut(u32) -> CartMemoryLocation,
    ) {
        for (i, bank) in bank_range.enumerate() {
            for j in 0..2 {
                self.map[((bank as usize) << 1) | j as usize] = f(((i as u32) << 15) | j);
            }
        }
    }

    pub fn mirror(&mut self) {
        self.map.copy_within(..1024, 1024);
    }
}

#[derive(Debug, Clone)]
pub struct Cart {
    pub rom: Rom,
    pub cfg: CartConfig,
    mapping: Mapping,
}

impl Cart {
    pub fn from_bytes(bytes: Vec<u8>) -> Self {
        let rom = Rom::from_bytes(bytes);
        let (hdr, mapping_type) = rom.get_best_header();
        let cfg = CartConfig {
            mapping_type,
            sram_size: hdr.ram_size,
        };
        let mut mapping = Mapping::new();
        match mapping_type {
            MappingType::LoRom => {
                mapping.map_hi(0..=0x7f, CartMemoryLocation::Rom);
                if cfg.sram_size.is_empty() {
                    mapping.map_lo(0x40..=0x7f, CartMemoryLocation::Rom);
                } else {
                    // TODO: In most games it is a full mapping (?)
                    mapping.map_lo(0x70..=0x7f, CartMemoryLocation::Sram);
                }
                mapping.mirror();
            }
            MappingType::HiRom => {
                mapping.map(0x40..=0x7f, CartMemoryLocation::Rom);
                mapping.map_hi(0..=0x3f, CartMemoryLocation::Rom);
                if !cfg.sram_size.is_empty() {
                    mapping.map_areas(0x20..=0x3f, 0x6000..=0x7fff, CartMemoryLocation::Sram);
                }
                mapping.mirror();
            }
            MappingType::ExHiRom => {
                mapping.map_areas(0x80..=0xbf, 0x6000..=0x7fff, CartMemoryLocation::Sram);
                mapping.mirror();
                mapping.map(0xc0..=0xff, CartMemoryLocation::Rom);
                mapping.map(0x40..=0x7f, |off| CartMemoryLocation::Rom(0x40_0000 + off));
                mapping.map_hi(0x80..=0xbf, CartMemoryLocation::Rom);
                mapping.map_hi(0x00..=0x3f, |off| CartMemoryLocation::Rom(0x40_0000 + off));
            }
        }
        Self { rom, cfg, mapping }
    }

    pub fn header(&self) -> Header {
        self.rom.read_header(self.cfg.mapping_type.get_rom_offset())
    }

    pub fn is_checksum_matching(&self, hdr: &Header) -> bool {
        self.rom.checksum() == hdr.checksum()
    }

    pub fn map(&self, addr: Addr) -> CartMemoryLocation {
        match *self.mapping.get(addr) {
            CartMemoryLocation::Rom(off) => {
                CartMemoryLocation::Rom(off.wrapping_add(addr.addr as u32 & 0x1fff))
            }
            CartMemoryLocation::Sram(off) => {
                CartMemoryLocation::Sram(off.wrapping_add(addr.addr as u32 & 0x1fff))
            }
            CartMemoryLocation::Unmapped => CartMemoryLocation::Unmapped,
        }
    }

    pub fn map_rom(&self, addr: Addr) -> Option<u32> {
        match self.map_full(addr) {
            MemoryLocation::Cart(CartMemoryLocation::Rom(off)) => Some(off),
            _ => None,
        }
    }

    pub fn map_full(&self, addr: Addr) -> MemoryLocation {
        if let Some(loc) = crate::addr_space::get_system_memory_location(addr) {
            MemoryLocation::System(loc)
        } else {
            MemoryLocation::Cart(self.map(addr))
        }
    }

    pub fn map_full_unknown(&self, addr: TU24) -> Option<MemoryLocation> {
        let addr = if addr.addr().msb().is_known_false()
            && addr.bank().contains_any(0x40).is_known_false()
        {
            Addr::new(0, addr.addr().get()?)
        } else {
            addr.get()?
        };
        Some(self.map_full(addr))
    }

    pub fn reverse_map_rom(&self, rom_addr: u32) -> Option<Addr> {
        self.mapping
            .map
            .iter()
            .position(|item| item == &CartMemoryLocation::Rom(rom_addr & !0x1fff))
            .map(|i| Addr::from_u32((i << 13) as u32 | (rom_addr & 0x1fff)))
    }

    pub fn reverse_map_sram(&self, sram_addr: u32) -> Option<Addr> {
        self.mapping
            .map
            .iter()
            .position(|item| item == &CartMemoryLocation::Sram(sram_addr & !0x1fff))
            .map(|i| Addr::from_u32((i << 13) as u32 | (sram_addr & 0x1fff)))
    }

    pub fn reverse_map(&self, loc: MemoryLocation) -> Option<Addr> {
        Some(match loc {
            MemoryLocation::System(SystemMemoryLocation::Wram(off)) => {
                Addr::new(0x7e, 0).add24(off & 0x1ffff)
            }
            MemoryLocation::System(SystemMemoryLocation::IoBbus(off)) => {
                Addr::new(0, u16::from_le_bytes([off, 0x21]))
            }
            MemoryLocation::System(
                SystemMemoryLocation::Io(off) | SystemMemoryLocation::Other(off),
            ) => Addr::new(0, off),
            MemoryLocation::Cart(CartMemoryLocation::Rom(off)) => return self.reverse_map_rom(off),
            MemoryLocation::Cart(CartMemoryLocation::Sram(off)) => {
                return self.reverse_map_sram(off);
            }
            MemoryLocation::Cart(CartMemoryLocation::Unmapped) => return None,
        })
    }

    pub fn read_rom(&self, addr: Addr) -> Option<u8> {
        if let MemoryLocation::Cart(CartMemoryLocation::Rom(rom)) = self.map_full(addr) {
            Some(self.rom.read(rom))
        } else {
            None
        }
    }
}
