use crate::addr::Addr;

pub mod am {
    use crate::tvl::{TU16, TU24};

    use super::*;
    /// Absolute
    #[derive(Debug, Clone, Copy)]
    pub struct A(pub u16);
    /// Absolute Indexed, X
    #[derive(Debug, Clone, Copy)]
    pub struct Ax(pub u16);
    /// Absolute Indexed, Y
    #[derive(Debug, Clone, Copy)]
    pub struct Ay(pub u16);
    /// Absolute Long
    #[derive(Debug, Clone, Copy)]
    pub struct Al(pub Addr);
    /// Absolute Long Indexed, X
    #[derive(Debug, Clone, Copy)]
    pub struct Alx(pub Addr);
    /// Direct Page
    #[derive(Debug, Clone, Copy)]
    pub struct D(pub u8);
    /// Direct Indexed, X
    #[derive(Debug, Clone, Copy)]
    pub struct Dx(pub u8);
    /// Direct Indexed, Y
    #[derive(Debug, Clone, Copy)]
    pub struct Dy(pub u8);
    /// Direct Page Indexed Indirect, X
    #[derive(Debug, Clone, Copy)]
    pub struct Dxi(pub u8);
    /// Direct Page Indirect Indexed, Y
    #[derive(Debug, Clone, Copy)]
    pub struct Diy(pub u8);
    /// Direct Page Indirect Long Indexed, Y
    #[derive(Debug, Clone, Copy)]
    pub struct Dily(pub u8);
    /// Direct Page Indirect
    #[derive(Debug, Clone, Copy)]
    pub struct Di(pub u8);
    /// Direct Page Indirect Long
    #[derive(Debug, Clone, Copy)]
    pub struct Dil(pub u8);
    /// Stack Relative
    #[derive(Debug, Clone, Copy)]
    pub struct S(pub u8);
    /// Stack Relative Indirect Indexed, Y
    #[derive(Debug, Clone, Copy)]
    pub struct Siy(pub u8);
    /// Immediate
    #[derive(Debug, Clone, Copy)]
    pub enum I {
        U8(u8),
        U16(u16),
    }

    #[derive(Debug, Clone, Copy)]
    pub struct AddrModeRes {
        pub is24: bool,
        pub addr: TU24,
    }
    impl AddrModeRes {
        pub fn incr(&mut self) {
            if self.is24 {
                self.addr = self.addr.add24(1);
            } else {
                self.addr = self.addr.add16(1);
            }
        }

        pub fn offset16(mut self, off: impl Into<TU16>) -> Self {
            self.addr = self.addr.add16(off);
            self
        }

        pub fn offset24(mut self, off: impl Into<TU16>) -> Self {
            self.addr = self.addr.add24(off);
            self
        }
    }
    impl From<AddrModeRes> for TU24 {
        fn from(value: AddrModeRes) -> Self {
            value.addr
        }
    }
}
use am::*;

#[derive(Debug, Clone, Copy)]
pub struct FlagSet(pub u8);

impl FlagSet {
    pub const fn is_empty(&self) -> bool {
        self.0 == 0
    }
}

impl core::fmt::Display for FlagSet {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.is_empty() {
            return write!(f, "0");
        }
        let names = ["C", "Z", "I", "D", "X", "M", "V", "N"];
        let mut first = true;
        for flag in (0..8).filter(|i| (self.0 >> i) & 1 != 0) {
            if !first {
                write!(f, " | ")?;
            }
            first = false;
            f.write_str(names[flag])?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
pub struct NearLabel(pub u8);

#[derive(Debug, Clone, Copy)]
pub struct RelativeLabel(pub u16);

#[derive(Debug, Clone, Copy)]
pub struct AbsoluteLabel(pub u16);

#[derive(Debug, Clone, Copy)]
pub struct IndirectLabel(pub u16);

#[derive(Debug, Clone, Copy)]
pub struct IndirectIndexedLabel(pub u16);

#[derive(Debug, Clone, Copy)]
pub struct IndirectLongLabel(pub u16);

impl NearLabel {
    pub fn take(&self, pc: Addr) -> Addr {
        pc.add16((self.0 as i8 as i16 as u16).wrapping_add(2))
    }
}

impl RelativeLabel {
    pub fn take(&self, pc: Addr) -> Addr {
        pc.add16(self.0.wrapping_add(3))
    }
}

impl AbsoluteLabel {
    pub fn take(&self, pc: Addr) -> Addr {
        Addr::new(pc.bank, self.0)
    }
}

fn f16(f: &mut impl FnMut() -> Option<u8>) -> Option<u16> {
    Some(u16::from_le_bytes([f()?, f()?]))
}

fn f24(f: &mut impl FnMut() -> Option<u8>) -> Option<Addr> {
    Some(Addr::from_bytes([f()?, f()?, f()?]))
}

impl I {
    pub fn from_fetcher(f: &mut impl FnMut() -> Option<u8>, x: bool) -> Option<Self> {
        if x {
            f().map(Self::U8)
        } else {
            f16(f).map(Self::U16)
        }
    }

    pub const fn size(&self) -> u8 {
        match self {
            Self::U8(_) => 1,
            Self::U16(_) => 2,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum InstructionArgument {
    Signature(u8),
    A(A),
    Ax(Ax),
    Ay(Ay),
    Al(Al),
    Alx(Alx),
    D(D),
    Dx(Dx),
    Dy(Dy),
    Dxi(Dxi),
    Diy(Diy),
    Dily(Dily),
    Di(Di),
    Dil(Dil),
    S(S),
    Siy(Siy),
    I(I),
    NearLabel(NearLabel),
    RelativeLabel(RelativeLabel),
    AbsoluteLabel(AbsoluteLabel),
    LongLabel(Addr),
    IndirectLabel(IndirectLabel),
    IndirectIndexedLabel(IndirectIndexedLabel),
    IndirectLongLabel(IndirectLongLabel),
    Flags(FlagSet),
    Move(u8, u8),
}

impl InstructionArgument {
    pub const fn size(&self) -> u8 {
        match self {
            Self::Signature(_)
            | Self::D(_)
            | Self::Dx(_)
            | Self::Dy(_)
            | Self::Dxi(_)
            | Self::Diy(_)
            | Self::Dily(_)
            | Self::Di(_)
            | Self::Dil(_)
            | Self::S(_)
            | Self::Siy(_)
            | Self::NearLabel(_)
            | Self::Flags(_) => 1,
            Self::A(_)
            | Self::Ax(_)
            | Self::Ay(_)
            | Self::RelativeLabel(_)
            | Self::AbsoluteLabel(_)
            | Self::IndirectLabel(_)
            | Self::IndirectIndexedLabel(_)
            | Self::IndirectLongLabel(_)
            | Self::Move(_, _) => 2,
            Self::Al(_) | Self::Alx(_) | Self::LongLabel(_) => 3,
            Self::I(i) => i.size(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Instruction {
    Brk(u8),
    OraDxi(Dxi),
    Cop(u8),
    OraS(S),
    TsbD(D),
    OraD(D),
    AslD(D),
    OraDil(Dil),
    Php,
    OraI(I),
    AslAc,
    Phd,
    TsbA(A),
    OraA(A),
    AslA(A),
    OraAl(Al),
    Bpl(NearLabel),
    OraDiy(Diy),
    OraDi(Di),
    OraSiy(Siy),
    TrbD(D),
    OraDx(Dx),
    AslDx(Dx),
    OraDily(Dily),
    Clc,
    OraAy(Ay),
    IncAc,
    Tcs,
    TrbA(A),
    OraAx(Ax),
    AslAx(Ax),
    OraAlx(Alx),
    Jsr(AbsoluteLabel),
    AndDxi(Dxi),
    Jsl(Addr),
    AndS(S),
    BitD(D),
    AndD(D),
    RolD(D),
    AndDil(Dil),
    Plp,
    AndI(I),
    RolAc,
    Pld,
    BitA(A),
    AndA(A),
    RolA(A),
    AndAl(Al),
    Bmi(NearLabel),
    AndDiy(Diy),
    AndDi(Di),
    AndSiy(Siy),
    BitDx(Dx),
    AndDx(Dx),
    RolDx(Dx),
    AndDily(Dily),
    Sec,
    AndAy(Ay),
    DecAc,
    Tsc,
    BitAx(Ax),
    AndAx(Ax),
    RolAx(Ax),
    AndAlx(Alx),
    Rti,
    EorDxi(Dxi),
    Wdm(u8),
    EorS(S),
    /// dst bank, src bank
    Mvp(u8, u8),
    EorD(D),
    LsrD(D),
    EorDil(Dil),
    Pha,
    EorI(I),
    LsrAc,
    Phk,
    Jmp(AbsoluteLabel),
    EorA(A),
    LsrA(A),
    EorAl(Al),
    Bvc(NearLabel),
    EorDiy(Diy),
    EorDi(Di),
    EorSiy(Siy),
    /// dst bank, src bank
    Mvn(u8, u8),
    EorDx(Dx),
    LsrDx(Dx),
    EorDily(Dily),
    Cli,
    EorAy(Ay),
    Phy,
    Tcd,
    Jml(Addr),
    EorAx(Ax),
    LsrAx(Ax),
    EorAlx(Alx),
    Rts,
    AdcDxi(Dxi),
    Per(RelativeLabel),
    AdcS(S),
    StzD(D),
    AdcD(D),
    RorD(D),
    AdcDil(Dil),
    Pla,
    AdcI(I),
    RorAc,
    Rtl,
    Jmpi(IndirectLabel),
    AdcA(A),
    RorA(A),
    AdcAl(Al),
    Bvs(NearLabel),
    AdcDiy(Diy),
    AdcDi(Di),
    AdcSiy(Siy),
    StzDx(Dx),
    AdcDx(Dx),
    RorDx(Dx),
    AdcDily(Dily),
    Sei,
    AdcAy(Ay),
    Ply,
    Tdc,
    Jmpxi(IndirectIndexedLabel),
    AdcAx(Ax),
    RorAx(Ax),
    AdcAlx(Alx),
    Bra(NearLabel),
    StaDxi(Dxi),
    Brl(RelativeLabel),
    StaS(S),
    StyD(D),
    StaD(D),
    StxD(D),
    StaDil(Dil),
    Dey,
    BitI(I),
    Txa,
    Phb,
    StyA(A),
    StaA(A),
    StxA(A),
    StaAl(Al),
    Bcc(NearLabel),
    StaDiy(Diy),
    StaDi(Di),
    StaSiy(Siy),
    StyDx(Dx),
    StaDx(Dx),
    StxDy(Dy),
    StaDily(Dily),
    Tya,
    StaAy(Ay),
    Txs,
    Txy,
    StzA(A),
    StaAx(Ax),
    StzAx(Ax),
    StaAlx(Alx),
    LdyI(I),
    LdaDxi(Dxi),
    LdxI(I),
    LdaS(S),
    LdyD(D),
    LdaD(D),
    LdxD(D),
    LdaDil(Dil),
    Tay,
    LdaI(I),
    Tax,
    Plb,
    LdyA(A),
    LdaA(A),
    LdxA(A),
    LdaAl(Al),
    Bcs(NearLabel),
    LdaDiy(Diy),
    LdaDi(Di),
    LdaSiy(Siy),
    LdyDx(Dx),
    LdaDx(Dx),
    LdxDy(Dy),
    LdaDily(Dily),
    Clv,
    LdaAy(Ay),
    Tsx,
    Tyx,
    LdyAx(Ax),
    LdaAx(Ax),
    LdxAy(Ay),
    LdaAlx(Alx),
    CpyI(I),
    CmpDxi(Dxi),
    Rep(FlagSet),
    CmpS(S),
    CpyD(D),
    CmpD(D),
    DecD(D),
    CmpDil(Dil),
    Iny,
    CmpI(I),
    Dex,
    Wai,
    CpyA(A),
    CmpA(A),
    DecA(A),
    CmpAl(Al),
    Bne(NearLabel),
    CmpDiy(Diy),
    CmpDi(Di),
    CmpSiy(Siy),
    Pei(Di),
    CmpDx(Dx),
    DecDx(Dx),
    CmpDily(Dily),
    Cld,
    CmpAy(Ay),
    Phx,
    Stp,
    Jmli(IndirectLongLabel),
    CmpAx(Ax),
    DecAx(Ax),
    CmpAlx(Alx),
    CpxI(I),
    SbcDxi(Dxi),
    Sep(FlagSet),
    SbcS(S),
    CpxD(D),
    SbcD(D),
    IncD(D),
    SbcDil(Dil),
    Inx,
    SbcI(I),
    Nop,
    Xba,
    CpxA(A),
    SbcA(A),
    IncA(A),
    SbcAl(Al),
    Beq(NearLabel),
    SbcDiy(Diy),
    SbcDi(Di),
    SbcSiy(Siy),
    Pea(AbsoluteLabel),
    SbcDx(Dx),
    IncDx(Dx),
    SbcDily(Dily),
    Sed,
    SbcAy(Ay),
    Plx,
    Xce,
    Jsrxi(IndirectIndexedLabel),
    SbcAx(Ax),
    IncAx(Ax),
    SbcAlx(Alx),
}

impl Instruction {
    pub fn from_fetcher(
        mut f: impl FnMut() -> Option<u8>,
        m: Option<bool>,
        x: Option<bool>,
    ) -> Option<Self> {
        Some(match f()? {
            0x00 => Self::Brk(f()?),
            0x01 => Self::OraDxi(Dxi(f()?)),
            0x02 => Self::Cop(f()?),
            0x03 => Self::OraS(S(f()?)),
            0x04 => Self::TsbD(D(f()?)),
            0x05 => Self::OraD(D(f()?)),
            0x06 => Self::AslD(D(f()?)),
            0x07 => Self::OraDil(Dil(f()?)),
            0x08 => Self::Php,
            0x09 => Self::OraI(I::from_fetcher(&mut f, m?)?),
            0x0A => Self::AslAc,
            0x0B => Self::Phd,
            0x0C => Self::TsbA(A(f16(&mut f)?)),
            0x0D => Self::OraA(A(f16(&mut f)?)),
            0x0E => Self::AslA(A(f16(&mut f)?)),
            0x0F => Self::OraAl(Al(f24(&mut f)?)),
            0x10 => Self::Bpl(NearLabel(f()?)),
            0x11 => Self::OraDiy(Diy(f()?)),
            0x12 => Self::OraDi(Di(f()?)),
            0x13 => Self::OraSiy(Siy(f()?)),
            0x14 => Self::TrbD(D(f()?)),
            0x15 => Self::OraDx(Dx(f()?)),
            0x16 => Self::AslDx(Dx(f()?)),
            0x17 => Self::OraDily(Dily(f()?)),
            0x18 => Self::Clc,
            0x19 => Self::OraAy(Ay(f16(&mut f)?)),
            0x1A => Self::IncAc,
            0x1B => Self::Tcs,
            0x1C => Self::TrbA(A(f16(&mut f)?)),
            0x1D => Self::OraAx(Ax(f16(&mut f)?)),
            0x1E => Self::AslAx(Ax(f16(&mut f)?)),
            0x1F => Self::OraAlx(Alx(f24(&mut f)?)),
            0x20 => Self::Jsr(AbsoluteLabel(f16(&mut f)?)),
            0x21 => Self::AndDxi(Dxi(f()?)),
            0x22 => Self::Jsl(f24(&mut f)?),
            0x23 => Self::AndS(S(f()?)),
            0x24 => Self::BitD(D(f()?)),
            0x25 => Self::AndD(D(f()?)),
            0x26 => Self::RolD(D(f()?)),
            0x27 => Self::AndDil(Dil(f()?)),
            0x28 => Self::Plp,
            0x29 => Self::AndI(I::from_fetcher(&mut f, m?)?),
            0x2A => Self::RolAc,
            0x2B => Self::Pld,
            0x2C => Self::BitA(A(f16(&mut f)?)),
            0x2D => Self::AndA(A(f16(&mut f)?)),
            0x2E => Self::RolA(A(f16(&mut f)?)),
            0x2F => Self::AndAl(Al(f24(&mut f)?)),
            0x30 => Self::Bmi(NearLabel(f()?)),
            0x31 => Self::AndDiy(Diy(f()?)),
            0x32 => Self::AndDi(Di(f()?)),
            0x33 => Self::AndSiy(Siy(f()?)),
            0x34 => Self::BitDx(Dx(f()?)),
            0x35 => Self::AndDx(Dx(f()?)),
            0x36 => Self::RolDx(Dx(f()?)),
            0x37 => Self::AndDily(Dily(f()?)),
            0x38 => Self::Sec,
            0x39 => Self::AndAy(Ay(f16(&mut f)?)),
            0x3A => Self::DecAc,
            0x3B => Self::Tsc,
            0x3C => Self::BitAx(Ax(f16(&mut f)?)),
            0x3D => Self::AndAx(Ax(f16(&mut f)?)),
            0x3E => Self::RolAx(Ax(f16(&mut f)?)),
            0x3F => Self::AndAlx(Alx(f24(&mut f)?)),
            0x40 => Self::Rti,
            0x41 => Self::EorDxi(Dxi(f()?)),
            0x42 => Self::Wdm(f()?),
            0x43 => Self::EorS(S(f()?)),
            0x44 => Self::Mvp(f()?, f()?),
            0x45 => Self::EorD(D(f()?)),
            0x46 => Self::LsrD(D(f()?)),
            0x47 => Self::EorDil(Dil(f()?)),
            0x48 => Self::Pha,
            0x49 => Self::EorI(I::from_fetcher(&mut f, m?)?),
            0x4A => Self::LsrAc,
            0x4B => Self::Phk,
            0x4C => Self::Jmp(AbsoluteLabel(f16(&mut f)?)),
            0x4D => Self::EorA(A(f16(&mut f)?)),
            0x4E => Self::LsrA(A(f16(&mut f)?)),
            0x4F => Self::EorAl(Al(f24(&mut f)?)),
            0x50 => Self::Bvc(NearLabel(f()?)),
            0x51 => Self::EorDiy(Diy(f()?)),
            0x52 => Self::EorDi(Di(f()?)),
            0x53 => Self::EorSiy(Siy(f()?)),
            0x54 => Self::Mvn(f()?, f()?),
            0x55 => Self::EorDx(Dx(f()?)),
            0x56 => Self::LsrDx(Dx(f()?)),
            0x57 => Self::EorDily(Dily(f()?)),
            0x58 => Self::Cli,
            0x59 => Self::EorAy(Ay(f16(&mut f)?)),
            0x5A => Self::Phy,
            0x5B => Self::Tcd,
            0x5C => Self::Jml(f24(&mut f)?),
            0x5D => Self::EorAx(Ax(f16(&mut f)?)),
            0x5E => Self::LsrAx(Ax(f16(&mut f)?)),
            0x5F => Self::EorAlx(Alx(f24(&mut f)?)),
            0x60 => Self::Rts,
            0x61 => Self::AdcDxi(Dxi(f()?)),
            0x62 => Self::Per(RelativeLabel(f16(&mut f)?)),
            0x63 => Self::AdcS(S(f()?)),
            0x64 => Self::StzD(D(f()?)),
            0x65 => Self::AdcD(D(f()?)),
            0x66 => Self::RorD(D(f()?)),
            0x67 => Self::AdcDil(Dil(f()?)),
            0x68 => Self::Pla,
            0x69 => Self::AdcI(I::from_fetcher(&mut f, m?)?),
            0x6A => Self::RorAc,
            0x6B => Self::Rtl,
            0x6C => Self::Jmpi(IndirectLabel(f16(&mut f)?)),
            0x6D => Self::AdcA(A(f16(&mut f)?)),
            0x6E => Self::RorA(A(f16(&mut f)?)),
            0x6F => Self::AdcAl(Al(f24(&mut f)?)),
            0x70 => Self::Bvs(NearLabel(f()?)),
            0x71 => Self::AdcDiy(Diy(f()?)),
            0x72 => Self::AdcDi(Di(f()?)),
            0x73 => Self::AdcSiy(Siy(f()?)),
            0x74 => Self::StzDx(Dx(f()?)),
            0x75 => Self::AdcDx(Dx(f()?)),
            0x76 => Self::RorDx(Dx(f()?)),
            0x77 => Self::AdcDily(Dily(f()?)),
            0x78 => Self::Sei,
            0x79 => Self::AdcAy(Ay(f16(&mut f)?)),
            0x7A => Self::Ply,
            0x7B => Self::Tdc,
            0x7C => Self::Jmpxi(IndirectIndexedLabel(f16(&mut f)?)),
            0x7D => Self::AdcAx(Ax(f16(&mut f)?)),
            0x7E => Self::RorAx(Ax(f16(&mut f)?)),
            0x7F => Self::AdcAlx(Alx(f24(&mut f)?)),
            0x80 => Self::Bra(NearLabel(f()?)),
            0x81 => Self::StaDxi(Dxi(f()?)),
            0x82 => Self::Brl(RelativeLabel(f16(&mut f)?)),
            0x83 => Self::StaS(S(f()?)),
            0x84 => Self::StyD(D(f()?)),
            0x85 => Self::StaD(D(f()?)),
            0x86 => Self::StxD(D(f()?)),
            0x87 => Self::StaDil(Dil(f()?)),
            0x88 => Self::Dey,
            0x89 => Self::BitI(I::from_fetcher(&mut f, m?)?),
            0x8A => Self::Txa,
            0x8B => Self::Phb,
            0x8C => Self::StyA(A(f16(&mut f)?)),
            0x8D => Self::StaA(A(f16(&mut f)?)),
            0x8E => Self::StxA(A(f16(&mut f)?)),
            0x8F => Self::StaAl(Al(f24(&mut f)?)),
            0x90 => Self::Bcc(NearLabel(f()?)),
            0x91 => Self::StaDiy(Diy(f()?)),
            0x92 => Self::StaDi(Di(f()?)),
            0x93 => Self::StaSiy(Siy(f()?)),
            0x94 => Self::StyDx(Dx(f()?)),
            0x95 => Self::StaDx(Dx(f()?)),
            0x96 => Self::StxDy(Dy(f()?)),
            0x97 => Self::StaDily(Dily(f()?)),
            0x98 => Self::Tya,
            0x99 => Self::StaAy(Ay(f16(&mut f)?)),
            0x9A => Self::Txs,
            0x9B => Self::Txy,
            0x9C => Self::StzA(A(f16(&mut f)?)),
            0x9D => Self::StaAx(Ax(f16(&mut f)?)),
            0x9E => Self::StzAx(Ax(f16(&mut f)?)),
            0x9F => Self::StaAlx(Alx(f24(&mut f)?)),
            0xA0 => Self::LdyI(I::from_fetcher(&mut f, x?)?),
            0xA1 => Self::LdaDxi(Dxi(f()?)),
            0xA2 => Self::LdxI(I::from_fetcher(&mut f, x?)?),
            0xA3 => Self::LdaS(S(f()?)),
            0xA4 => Self::LdyD(D(f()?)),
            0xA5 => Self::LdaD(D(f()?)),
            0xA6 => Self::LdxD(D(f()?)),
            0xA7 => Self::LdaDil(Dil(f()?)),
            0xA8 => Self::Tay,
            0xA9 => Self::LdaI(I::from_fetcher(&mut f, m?)?),
            0xAA => Self::Tax,
            0xAB => Self::Plb,
            0xAC => Self::LdyA(A(f16(&mut f)?)),
            0xAD => Self::LdaA(A(f16(&mut f)?)),
            0xAE => Self::LdxA(A(f16(&mut f)?)),
            0xAF => Self::LdaAl(Al(f24(&mut f)?)),
            0xB0 => Self::Bcs(NearLabel(f()?)),
            0xB1 => Self::LdaDiy(Diy(f()?)),
            0xB2 => Self::LdaDi(Di(f()?)),
            0xB3 => Self::LdaSiy(Siy(f()?)),
            0xB4 => Self::LdyDx(Dx(f()?)),
            0xB5 => Self::LdaDx(Dx(f()?)),
            0xB6 => Self::LdxDy(Dy(f()?)),
            0xB7 => Self::LdaDily(Dily(f()?)),
            0xB8 => Self::Clv,
            0xB9 => Self::LdaAy(Ay(f16(&mut f)?)),
            0xBA => Self::Tsx,
            0xBB => Self::Tyx,
            0xBC => Self::LdyAx(Ax(f16(&mut f)?)),
            0xBD => Self::LdaAx(Ax(f16(&mut f)?)),
            0xBE => Self::LdxAy(Ay(f16(&mut f)?)),
            0xBF => Self::LdaAlx(Alx(f24(&mut f)?)),
            0xC0 => Self::CpyI(I::from_fetcher(&mut f, x?)?),
            0xC1 => Self::CmpDxi(Dxi(f()?)),
            0xC2 => Self::Rep(FlagSet(f()?)),
            0xC3 => Self::CmpS(S(f()?)),
            0xC4 => Self::CpyD(D(f()?)),
            0xC5 => Self::CmpD(D(f()?)),
            0xC6 => Self::DecD(D(f()?)),
            0xC7 => Self::CmpDil(Dil(f()?)),
            0xC8 => Self::Iny,
            0xC9 => Self::CmpI(I::from_fetcher(&mut f, m?)?),
            0xCA => Self::Dex,
            0xCB => Self::Wai,
            0xCC => Self::CpyA(A(f16(&mut f)?)),
            0xCD => Self::CmpA(A(f16(&mut f)?)),
            0xCE => Self::DecA(A(f16(&mut f)?)),
            0xCF => Self::CmpAl(Al(f24(&mut f)?)),
            0xD0 => Self::Bne(NearLabel(f()?)),
            0xD1 => Self::CmpDiy(Diy(f()?)),
            0xD2 => Self::CmpDi(Di(f()?)),
            0xD3 => Self::CmpSiy(Siy(f()?)),
            0xD4 => Self::Pei(Di(f()?)),
            0xD5 => Self::CmpDx(Dx(f()?)),
            0xD6 => Self::DecDx(Dx(f()?)),
            0xD7 => Self::CmpDily(Dily(f()?)),
            0xD8 => Self::Cld,
            0xD9 => Self::CmpAy(Ay(f16(&mut f)?)),
            0xDA => Self::Phx,
            0xDB => Self::Stp,
            0xDC => Self::Jmli(IndirectLongLabel(f16(&mut f)?)),
            0xDD => Self::CmpAx(Ax(f16(&mut f)?)),
            0xDE => Self::DecAx(Ax(f16(&mut f)?)),
            0xDF => Self::CmpAlx(Alx(f24(&mut f)?)),
            0xE0 => Self::CpxI(I::from_fetcher(&mut f, x?)?),
            0xE1 => Self::SbcDxi(Dxi(f()?)),
            0xE2 => Self::Sep(FlagSet(f()?)),
            0xE3 => Self::SbcS(S(f()?)),
            0xE4 => Self::CpxD(D(f()?)),
            0xE5 => Self::SbcD(D(f()?)),
            0xE6 => Self::IncD(D(f()?)),
            0xE7 => Self::SbcDil(Dil(f()?)),
            0xE8 => Self::Inx,
            0xE9 => Self::SbcI(I::from_fetcher(&mut f, m?)?),
            0xEA => Self::Nop,
            0xEB => Self::Xba,
            0xEC => Self::CpxA(A(f16(&mut f)?)),
            0xED => Self::SbcA(A(f16(&mut f)?)),
            0xEE => Self::IncA(A(f16(&mut f)?)),
            0xEF => Self::SbcAl(Al(f24(&mut f)?)),
            0xF0 => Self::Beq(NearLabel(f()?)),
            0xF1 => Self::SbcDiy(Diy(f()?)),
            0xF2 => Self::SbcDi(Di(f()?)),
            0xF3 => Self::SbcSiy(Siy(f()?)),
            0xF4 => Self::Pea(AbsoluteLabel(f16(&mut f)?)),
            0xF5 => Self::SbcDx(Dx(f()?)),
            0xF6 => Self::IncDx(Dx(f()?)),
            0xF7 => Self::SbcDily(Dily(f()?)),
            0xF8 => Self::Sed,
            0xF9 => Self::SbcAy(Ay(f16(&mut f)?)),
            0xFA => Self::Plx,
            0xFB => Self::Xce,
            0xFC => Self::Jsrxi(IndirectIndexedLabel(f16(&mut f)?)),
            0xFD => Self::SbcAx(Ax(f16(&mut f)?)),
            0xFE => Self::IncAx(Ax(f16(&mut f)?)),
            0xFF => Self::SbcAlx(Alx(f24(&mut f)?)),
        })
    }

    pub const fn opcode(&self) -> OpCode {
        let op = match self {
            Self::Brk(..) => 0x00,
            Self::OraDxi(..) => 0x01,
            Self::Cop(..) => 0x02,
            Self::OraS(..) => 0x03,
            Self::TsbD(..) => 0x04,
            Self::OraD(..) => 0x05,
            Self::AslD(..) => 0x06,
            Self::OraDil(..) => 0x07,
            Self::Php => 0x08,
            Self::OraI(..) => 0x09,
            Self::AslAc => 0x0A,
            Self::Phd => 0x0B,
            Self::TsbA(..) => 0x0C,
            Self::OraA(..) => 0x0D,
            Self::AslA(..) => 0x0E,
            Self::OraAl(..) => 0x0F,
            Self::Bpl(..) => 0x10,
            Self::OraDiy(..) => 0x11,
            Self::OraDi(..) => 0x12,
            Self::OraSiy(..) => 0x13,
            Self::TrbD(..) => 0x14,
            Self::OraDx(..) => 0x15,
            Self::AslDx(..) => 0x16,
            Self::OraDily(..) => 0x17,
            Self::Clc => 0x18,
            Self::OraAy(..) => 0x19,
            Self::IncAc => 0x1A,
            Self::Tcs => 0x1B,
            Self::TrbA(..) => 0x1C,
            Self::OraAx(..) => 0x1D,
            Self::AslAx(..) => 0x1E,
            Self::OraAlx(..) => 0x1F,
            Self::Jsr(..) => 0x20,
            Self::AndDxi(..) => 0x21,
            Self::Jsl(..) => 0x22,
            Self::AndS(..) => 0x23,
            Self::BitD(..) => 0x24,
            Self::AndD(..) => 0x25,
            Self::RolD(..) => 0x26,
            Self::AndDil(..) => 0x27,
            Self::Plp => 0x28,
            Self::AndI(..) => 0x29,
            Self::RolAc => 0x2A,
            Self::Pld => 0x2B,
            Self::BitA(..) => 0x2C,
            Self::AndA(..) => 0x2D,
            Self::RolA(..) => 0x2E,
            Self::AndAl(..) => 0x2F,
            Self::Bmi(..) => 0x30,
            Self::AndDiy(..) => 0x31,
            Self::AndDi(..) => 0x32,
            Self::AndSiy(..) => 0x33,
            Self::BitDx(..) => 0x34,
            Self::AndDx(..) => 0x35,
            Self::RolDx(..) => 0x36,
            Self::AndDily(..) => 0x37,
            Self::Sec => 0x38,
            Self::AndAy(..) => 0x39,
            Self::DecAc => 0x3A,
            Self::Tsc => 0x3B,
            Self::BitAx(..) => 0x3C,
            Self::AndAx(..) => 0x3D,
            Self::RolAx(..) => 0x3E,
            Self::AndAlx(..) => 0x3F,
            Self::Rti => 0x40,
            Self::EorDxi(..) => 0x41,
            Self::Wdm(..) => 0x42,
            Self::EorS(..) => 0x43,
            Self::Mvp(..) => 0x44,
            Self::EorD(..) => 0x45,
            Self::LsrD(..) => 0x46,
            Self::EorDil(..) => 0x47,
            Self::Pha => 0x48,
            Self::EorI(..) => 0x49,
            Self::LsrAc => 0x4A,
            Self::Phk => 0x4B,
            Self::Jmp(..) => 0x4C,
            Self::EorA(..) => 0x4D,
            Self::LsrA(..) => 0x4E,
            Self::EorAl(..) => 0x4F,
            Self::Bvc(..) => 0x50,
            Self::EorDiy(..) => 0x51,
            Self::EorDi(..) => 0x52,
            Self::EorSiy(..) => 0x53,
            Self::Mvn(..) => 0x54,
            Self::EorDx(..) => 0x55,
            Self::LsrDx(..) => 0x56,
            Self::EorDily(..) => 0x57,
            Self::Cli => 0x58,
            Self::EorAy(..) => 0x59,
            Self::Phy => 0x5A,
            Self::Tcd => 0x5B,
            Self::Jml(..) => 0x5C,
            Self::EorAx(..) => 0x5D,
            Self::LsrAx(..) => 0x5E,
            Self::EorAlx(..) => 0x5F,
            Self::Rts => 0x60,
            Self::AdcDxi(..) => 0x61,
            Self::Per(..) => 0x62,
            Self::AdcS(..) => 0x63,
            Self::StzD(..) => 0x64,
            Self::AdcD(..) => 0x65,
            Self::RorD(..) => 0x66,
            Self::AdcDil(..) => 0x67,
            Self::Pla => 0x68,
            Self::AdcI(..) => 0x69,
            Self::RorAc => 0x6A,
            Self::Rtl => 0x6B,
            Self::Jmpi(..) => 0x6C,
            Self::AdcA(..) => 0x6D,
            Self::RorA(..) => 0x6E,
            Self::AdcAl(..) => 0x6F,
            Self::Bvs(..) => 0x70,
            Self::AdcDiy(..) => 0x71,
            Self::AdcDi(..) => 0x72,
            Self::AdcSiy(..) => 0x73,
            Self::StzDx(..) => 0x74,
            Self::AdcDx(..) => 0x75,
            Self::RorDx(..) => 0x76,
            Self::AdcDily(..) => 0x77,
            Self::Sei => 0x78,
            Self::AdcAy(..) => 0x79,
            Self::Ply => 0x7A,
            Self::Tdc => 0x7B,
            Self::Jmpxi(..) => 0x7C,
            Self::AdcAx(..) => 0x7D,
            Self::RorAx(..) => 0x7E,
            Self::AdcAlx(..) => 0x7F,
            Self::Bra(..) => 0x80,
            Self::StaDxi(..) => 0x81,
            Self::Brl(..) => 0x82,
            Self::StaS(..) => 0x83,
            Self::StyD(..) => 0x84,
            Self::StaD(..) => 0x85,
            Self::StxD(..) => 0x86,
            Self::StaDil(..) => 0x87,
            Self::Dey => 0x88,
            Self::BitI(..) => 0x89,
            Self::Txa => 0x8A,
            Self::Phb => 0x8B,
            Self::StyA(..) => 0x8C,
            Self::StaA(..) => 0x8D,
            Self::StxA(..) => 0x8E,
            Self::StaAl(..) => 0x8F,
            Self::Bcc(..) => 0x90,
            Self::StaDiy(..) => 0x91,
            Self::StaDi(..) => 0x92,
            Self::StaSiy(..) => 0x93,
            Self::StyDx(..) => 0x94,
            Self::StaDx(..) => 0x95,
            Self::StxDy(..) => 0x96,
            Self::StaDily(..) => 0x97,
            Self::Tya => 0x98,
            Self::StaAy(..) => 0x99,
            Self::Txs => 0x9A,
            Self::Txy => 0x9B,
            Self::StzA(..) => 0x9C,
            Self::StaAx(..) => 0x9D,
            Self::StzAx(..) => 0x9E,
            Self::StaAlx(..) => 0x9F,
            Self::LdyI(..) => 0xA0,
            Self::LdaDxi(..) => 0xA1,
            Self::LdxI(..) => 0xA2,
            Self::LdaS(..) => 0xA3,
            Self::LdyD(..) => 0xA4,
            Self::LdaD(..) => 0xA5,
            Self::LdxD(..) => 0xA6,
            Self::LdaDil(..) => 0xA7,
            Self::Tay => 0xA8,
            Self::LdaI(..) => 0xA9,
            Self::Tax => 0xAA,
            Self::Plb => 0xAB,
            Self::LdyA(..) => 0xAC,
            Self::LdaA(..) => 0xAD,
            Self::LdxA(..) => 0xAE,
            Self::LdaAl(..) => 0xAF,
            Self::Bcs(..) => 0xB0,
            Self::LdaDiy(..) => 0xB1,
            Self::LdaDi(..) => 0xB2,
            Self::LdaSiy(..) => 0xB3,
            Self::LdyDx(..) => 0xB4,
            Self::LdaDx(..) => 0xB5,
            Self::LdxDy(..) => 0xB6,
            Self::LdaDily(..) => 0xB7,
            Self::Clv => 0xB8,
            Self::LdaAy(..) => 0xB9,
            Self::Tsx => 0xBA,
            Self::Tyx => 0xBB,
            Self::LdyAx(..) => 0xBC,
            Self::LdaAx(..) => 0xBD,
            Self::LdxAy(..) => 0xBE,
            Self::LdaAlx(..) => 0xBF,
            Self::CpyI(..) => 0xC0,
            Self::CmpDxi(..) => 0xC1,
            Self::Rep(..) => 0xC2,
            Self::CmpS(..) => 0xC3,
            Self::CpyD(..) => 0xC4,
            Self::CmpD(..) => 0xC5,
            Self::DecD(..) => 0xC6,
            Self::CmpDil(..) => 0xC7,
            Self::Iny => 0xC8,
            Self::CmpI(..) => 0xC9,
            Self::Dex => 0xCA,
            Self::Wai => 0xCB,
            Self::CpyA(..) => 0xCC,
            Self::CmpA(..) => 0xCD,
            Self::DecA(..) => 0xCE,
            Self::CmpAl(..) => 0xCF,
            Self::Bne(..) => 0xD0,
            Self::CmpDiy(..) => 0xD1,
            Self::CmpDi(..) => 0xD2,
            Self::CmpSiy(..) => 0xD3,
            Self::Pei(..) => 0xD4,
            Self::CmpDx(..) => 0xD5,
            Self::DecDx(..) => 0xD6,
            Self::CmpDily(..) => 0xD7,
            Self::Cld => 0xD8,
            Self::CmpAy(..) => 0xD9,
            Self::Phx => 0xDA,
            Self::Stp => 0xDB,
            Self::Jmli(..) => 0xDC,
            Self::CmpAx(..) => 0xDD,
            Self::DecAx(..) => 0xDE,
            Self::CmpAlx(..) => 0xDF,
            Self::CpxI(..) => 0xE0,
            Self::SbcDxi(..) => 0xE1,
            Self::Sep(..) => 0xE2,
            Self::SbcS(..) => 0xE3,
            Self::CpxD(..) => 0xE4,
            Self::SbcD(..) => 0xE5,
            Self::IncD(..) => 0xE6,
            Self::SbcDil(..) => 0xE7,
            Self::Inx => 0xE8,
            Self::SbcI(..) => 0xE9,
            Self::Nop => 0xEA,
            Self::Xba => 0xEB,
            Self::CpxA(..) => 0xEC,
            Self::SbcA(..) => 0xED,
            Self::IncA(..) => 0xEE,
            Self::SbcAl(..) => 0xEF,
            Self::Beq(..) => 0xF0,
            Self::SbcDiy(..) => 0xF1,
            Self::SbcDi(..) => 0xF2,
            Self::SbcSiy(..) => 0xF3,
            Self::Pea(..) => 0xF4,
            Self::SbcDx(..) => 0xF5,
            Self::IncDx(..) => 0xF6,
            Self::SbcDily(..) => 0xF7,
            Self::Sed => 0xF8,
            Self::SbcAy(..) => 0xF9,
            Self::Plx => 0xFA,
            Self::Xce => 0xFB,
            Self::Jsrxi(..) => 0xFC,
            Self::SbcAx(..) => 0xFD,
            Self::IncAx(..) => 0xFE,
            Self::SbcAlx(..) => 0xFF,
        };
        OpCode(op)
    }

    pub const fn arg(&self) -> Option<InstructionArgument> {
        use Instruction::*;
        use InstructionArgument as Ia;
        Some(match *self {
            Php | AslAc | Phd | Clc | IncAc | Tcs | Plp | RolAc | Pld | Sec | DecAc | Tsc | Rti
            | Pha | LsrAc | Phk | Cli | Phy | Tcd | Rts | Pla | RorAc | Rtl | Sei | Ply | Tdc
            | Dey | Txa | Phb | Tya | Txs | Txy | Tay | Tax | Plb | Clv | Tsx | Tyx | Iny | Dex
            | Wai | Cld | Phx | Stp | Inx | Nop | Xba | Sed | Plx | Xce => return None,
            Brk(s) | Cop(s) | Wdm(s) => Ia::Signature(s),
            OraDxi(a) | AndDxi(a) | EorDxi(a) | AdcDxi(a) | StaDxi(a) | LdaDxi(a) | CmpDxi(a)
            | SbcDxi(a) => Ia::Dxi(a),
            OraS(a) | AndS(a) | EorS(a) | AdcS(a) | StaS(a) | LdaS(a) | CmpS(a) | SbcS(a) => {
                Ia::S(a)
            }
            TsbD(a) | OraD(a) | AslD(a) | TrbD(a) | BitD(a) | AndD(a) | RolD(a) | EorD(a)
            | LsrD(a) | StzD(a) | AdcD(a) | RorD(a) | StyD(a) | StaD(a) | StxD(a) | LdyD(a)
            | LdaD(a) | LdxD(a) | CpyD(a) | CmpD(a) | DecD(a) | CpxD(a) | SbcD(a) | IncD(a) => {
                Ia::D(a)
            }
            OraDil(a) | AndDil(a) | EorDil(a) | AdcDil(a) | StaDil(a) | LdaDil(a) | CmpDil(a)
            | SbcDil(a) => Ia::Dil(a),
            OraI(a) | AndI(a) | EorI(a) | AdcI(a) | BitI(a) | LdyI(a) | LdxI(a) | LdaI(a)
            | CpyI(a) | CmpI(a) | CpxI(a) | SbcI(a) => Ia::I(a),
            TsbA(a) | OraA(a) | AslA(a) | TrbA(a) | BitA(a) | AndA(a) | RolA(a) | EorA(a)
            | LsrA(a) | AdcA(a) | RorA(a) | StyA(a) | StaA(a) | StxA(a) | StzA(a) | LdyA(a)
            | LdaA(a) | LdxA(a) | CpyA(a) | CmpA(a) | DecA(a) | CpxA(a) | SbcA(a) | IncA(a) => {
                Ia::A(a)
            }
            OraAl(a) | AndAl(a) | EorAl(a) | AdcAl(a) | StaAl(a) | LdaAl(a) | CmpAl(a)
            | SbcAl(a) => Ia::Al(a),
            Bpl(n) | Bmi(n) | Bvc(n) | Bvs(n) | Bra(n) | Bcc(n) | Bcs(n) | Bne(n) | Beq(n) => {
                Ia::NearLabel(n)
            }
            OraDiy(a) | AndDiy(a) | EorDiy(a) | AdcDiy(a) | StaDiy(a) | LdaDiy(a) | CmpDiy(a)
            | SbcDiy(a) => Ia::Diy(a),
            OraDi(a) | AndDi(a) | EorDi(a) | AdcDi(a) | StaDi(a) | LdaDi(a) | CmpDi(a)
            | SbcDi(a) | Pei(a) => Ia::Di(a),
            OraSiy(a) | AndSiy(a) | EorSiy(a) | AdcSiy(a) | StaSiy(a) | LdaSiy(a) | CmpSiy(a)
            | SbcSiy(a) => Ia::Siy(a),
            OraDx(a) | AslDx(a) | BitDx(a) | AndDx(a) | RolDx(a) | EorDx(a) | LsrDx(a)
            | StzDx(a) | AdcDx(a) | RorDx(a) | StyDx(a) | StaDx(a) | LdyDx(a) | LdaDx(a)
            | CmpDx(a) | DecDx(a) | SbcDx(a) | IncDx(a) => Ia::Dx(a),
            OraDily(a) | AndDily(a) | EorDily(a) | AdcDily(a) | StaDily(a) | LdaDily(a)
            | CmpDily(a) | SbcDily(a) => Ia::Dily(a),
            OraAy(a) | AndAy(a) | EorAy(a) | AdcAy(a) | StaAy(a) | LdaAy(a) | LdxAy(a)
            | CmpAy(a) | SbcAy(a) => Ia::Ay(a),
            OraAx(a) | AslAx(a) | BitAx(a) | AndAx(a) | RolAx(a) | EorAx(a) | LsrAx(a)
            | AdcAx(a) | RorAx(a) | StaAx(a) | StzAx(a) | LdyAx(a) | LdaAx(a) | CmpAx(a)
            | DecAx(a) | SbcAx(a) | IncAx(a) => Ia::Ax(a),
            OraAlx(a) | AndAlx(a) | EorAlx(a) | AdcAlx(a) | StaAlx(a) | LdaAlx(a) | CmpAlx(a)
            | SbcAlx(a) => Ia::Alx(a),
            Jsr(a) | Jmp(a) | Pea(a) => Ia::AbsoluteLabel(a),
            Jsl(a) | Jml(a) => Ia::LongLabel(a),
            Mvp(d, s) | Mvn(d, s) => Ia::Move(d, s),
            Per(r) | Brl(r) => Ia::RelativeLabel(r),
            Jmpi(i) => Ia::IndirectLabel(i),
            Jmpxi(i) | Jsrxi(i) => Ia::IndirectIndexedLabel(i),
            Jmli(i) => Ia::IndirectLongLabel(i),
            StxDy(a) | LdxDy(a) => Ia::Dy(a),
            Rep(f) | Sep(f) => Ia::Flags(f),
        })
    }

    pub fn size(&self) -> u8 {
        self.arg().map(|arg| arg.size() + 1).unwrap_or(1)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InstructionType {
    Brk,
    Ora,
    Cop,
    Tsb,
    Asl,
    Php,
    Phd,
    Bpl,
    Trb,
    Clc,
    Inc,
    Tcs,
    And,
    Js,
    Bit,
    Rol,
    Plp,
    Pld,
    Bmi,
    Sec,
    Dec,
    Tsc,
    Rti,
    Eor,
    Wdm,
    Mvp,
    Lsr,
    Pha,
    Phk,
    Jmp,
    Bvc,
    Mvn,
    Cli,
    Phy,
    Tcd,
    Rts,
    Adc,
    Per,
    Stz,
    Ror,
    Pla,
    Rtl,
    Bvs,
    Sei,
    Ply,
    Tdc,
    Bra,
    Sta,
    Sty,
    Stx,
    Dey,
    Txa,
    Phb,
    Bcc,
    Tya,
    Txs,
    Txy,
    Ldy,
    Lda,
    Ldx,
    Tay,
    Tax,
    Plb,
    Bcs,
    Clv,
    Tsx,
    Tyx,
    Cpy,
    Cmp,
    Rep,
    Iny,
    Dex,
    Wai,
    Bne,
    Pei,
    Cld,
    Phx,
    Stp,
    Cpx,
    Sbc,
    Sep,
    Inx,
    Nop,
    Xba,
    Beq,
    Pea,
    Sed,
    Plx,
    Xce,
}

impl InstructionType {
    pub fn name(&self) -> &'static str {
        use InstructionType::*;
        match self {
            Brk => "BRK",
            Ora => "ORA",
            Cop => "COP",
            Tsb => "TSB",
            Asl => "ASL",
            Php => "PHP",
            Phd => "PHD",
            Bpl => "BPL",
            Trb => "TRB",
            Clc => "CLC",
            Inc => "INC",
            Tcs => "TCS",
            And => "AND",
            Js => "JS",
            Bit => "BIT",
            Rol => "ROL",
            Plp => "PLP",
            Pld => "PLD",
            Bmi => "BMI",
            Sec => "SEC",
            Dec => "DEC",
            Tsc => "TSC",
            Rti => "RTI",
            Eor => "EOR",
            Wdm => "WDM",
            Mvp => "MVP",
            Lsr => "LSR",
            Pha => "PHA",
            Phk => "PHK",
            Jmp => "JMP",
            Bvc => "BVC",
            Mvn => "MVN",
            Cli => "CLI",
            Phy => "PHY",
            Tcd => "TCD",
            Rts => "RTS",
            Adc => "ADC",
            Per => "PER",
            Stz => "STZ",
            Ror => "ROR",
            Pla => "PLA",
            Rtl => "RTL",
            Bvs => "BVS",
            Sei => "SEI",
            Ply => "PLY",
            Tdc => "TDC",
            Bra => "BRA",
            Sta => "STA",
            Sty => "STY",
            Stx => "STX",
            Dey => "DEY",
            Txa => "TXA",
            Phb => "PHB",
            Bcc => "BCC",
            Tya => "TYA",
            Txs => "TXS",
            Txy => "TXY",
            Ldy => "LDY",
            Lda => "LDA",
            Ldx => "LDX",
            Tay => "TAY",
            Tax => "TAX",
            Plb => "PLB",
            Bcs => "BCS",
            Clv => "CLV",
            Tsx => "TSX",
            Tyx => "TYX",
            Cpy => "CPY",
            Cmp => "CMP",
            Rep => "REP",
            Iny => "INY",
            Dex => "DEX",
            Wai => "WAI",
            Bne => "BNE",
            Pei => "PEI",
            Cld => "CLD",
            Phx => "PHX",
            Stp => "STP",
            Cpx => "CPX",
            Sbc => "SBC",
            Sep => "SEP",
            Inx => "INX",
            Nop => "NOP",
            Xba => "XBA",
            Beq => "BEQ",
            Pea => "PEA",
            Sed => "SED",
            Plx => "PLX",
            Xce => "XCE",
        }
    }
}

pub enum InstructionFlagDependency {
    M,
    X,
}

impl InstructionType {
    pub const fn flag_dependency(&self) -> Option<InstructionFlagDependency> {
        use {InstructionFlagDependency::*, InstructionType::*};
        match self {
            Brk | Cop | Php | Phd | Bpl | Clc | Js | Plp | Pld | Bmi | Sec | Rti | Wdm | Phk
            | Jmp | Bvc | Cli | Tcd | Rts | Per | Rtl | Bvs | Sei | Tdc | Bra | Phb | Bcc | Txs
            | Plb | Bcs | Clv | Rep | Wai | Bne | Pei | Cld | Stp | Sep | Nop | Xba | Beq | Pea
            | Sed | Xce => None,
            Mvp | Mvn | Phy | Ply | Sty | Stx | Dey | Txy | Ldy | Ldx | Tay | Tax | Tsx | Tyx
            | Cpy | Iny | Dex | Phx | Cpx | Inx | Plx => Some(X),
            Ora | Tsb | Asl | Trb | Inc | Tcs | And | Bit | Rol | Dec | Tsc | Eor | Lsr | Pha
            | Adc | Stz | Ror | Pla | Sta | Txa | Tya | Lda | Cmp | Sbc => Some(M),
        }
    }
}

// TODO: Find better names for the naming conventions. Try to find their sources!
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InstructionNamingConvention {
    /// e.g. `INC A` instead of `INA`
    Regular,
    /// e.g. `INA` instead of `INC A`
    Descriptive,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct OpCode(pub u8);

impl OpCode {
    pub fn name(&self, convention: InstructionNamingConvention) -> &'static str {
        match self.0 {
            0x00 => "BRK",
            0x01 | 0x03 | 0x05 | 0x07 | 0x09 | 0x0d | 0x0f | 0x11 | 0x12 | 0x13 | 0x15 | 0x17
            | 0x19 | 0x1d | 0x1f => "ORA",
            0x02 => "COP",
            0x04 | 0x0c => "TSB",
            0x06 | 0x0a | 0x0e | 0x16 | 0x1e => "ASL",
            0x08 => "PHP",
            0x0b => "PHD",
            0x10 => "BPL",
            0x14 | 0x1c => "TRB",
            0x18 => "CLC",
            0x1a => match convention {
                InstructionNamingConvention::Regular => "INC",
                InstructionNamingConvention::Descriptive => "INA",
            },
            0x1b => "TCS",
            0x20 | 0xfc => "JSR",
            0x21 | 0x23 | 0x25 | 0x27 | 0x29 | 0x2d | 0x2f | 0x31 | 0x32 | 0x33 | 0x35 | 0x37
            | 0x39 | 0x3d | 0x3f => "AND",
            0x22 => match convention {
                InstructionNamingConvention::Regular => "JSR",
                InstructionNamingConvention::Descriptive => "JSL",
            },
            0x24 | 0x2c | 0x34 | 0x3c | 0x89 => "BIT",
            0x26 | 0x2a | 0x2e | 0x36 | 0x3e => "ROL",
            0x28 => "PLP",
            0x2b => "PLD",
            0x30 => "BMI",
            0x38 => "SEC",
            0x3a => match convention {
                InstructionNamingConvention::Regular => "DEC",
                InstructionNamingConvention::Descriptive => "DEA",
            },
            0x3b => "TSC",
            0x40 => "RTI",
            0x41 | 0x43 | 0x45 | 0x47 | 0x49 | 0x4d | 0x4f | 0x51 | 0x52 | 0x53 | 0x55 | 0x57
            | 0x59 | 0x5d | 0x5f => "EOR",
            0x42 => "WDM",
            0x44 => "MVP",
            0x46 | 0x4a | 0x4e | 0x56 | 0x5e => "LSR",
            0x48 => "PHA",
            0x4b => "PHK",
            0x4c | 0x6c | 0x7c => "JMP",
            0x50 => "BVC",
            0x54 => "MVN",
            0x58 => "CLI",
            0x5a => "PHY",
            0x5b => "TCD",
            0x5c | 0xdc => match convention {
                InstructionNamingConvention::Regular => "JMP",
                InstructionNamingConvention::Descriptive => "JML",
            },
            0x60 => "RTS",
            0x61 | 0x63 | 0x65 | 0x67 | 0x69 | 0x6d | 0x6f | 0x71 | 0x72 | 0x73 | 0x75 | 0x77
            | 0x79 | 0x7d | 0x7f => "ADC",
            0x62 => "PER",
            0x64 | 0x74 | 0x9c | 0x9e => "STZ",
            0x66 | 0x6a | 0x6e | 0x76 | 0x7e => "ROR",
            0x68 => "PLA",
            0x6b => "RTL",
            0x70 => "BVS",
            0x78 => "SEI",
            0x7a => "PLY",
            0x7b => "TDC",
            0x80 => "BRA",
            0x81 | 0x83 | 0x85 | 0x87 | 0x8d | 0x8f | 0x91 | 0x92 | 0x93 | 0x95 | 0x97 | 0x99
            | 0x9d | 0x9f => "STA",
            0x82 => "BRL",
            0x84 | 0x8c | 0x94 => "STY",
            0x86 | 0x8e | 0x96 => "STX",
            0x88 => "DEY",
            0x8a => "TXA",
            0x8b => "PHB",
            0x90 => match convention {
                InstructionNamingConvention::Regular => "BCC",
                InstructionNamingConvention::Descriptive => "BLT",
            },
            0x98 => "TYA",
            0x9a => "TXS",
            0x9b => "TXY",
            0xa0 | 0xa4 | 0xac | 0xb4 | 0xbc => "LDY",
            0xa1 | 0xa3 | 0xa5 | 0xa7 | 0xa9 | 0xad | 0xaf | 0xb1 | 0xb2 | 0xb3 | 0xb5 | 0xb7
            | 0xb9 | 0xbd | 0xbf => "LDA",
            0xa2 | 0xa6 | 0xae | 0xb6 | 0xbe => "LDX",
            0xa8 => "TAY",
            0xaa => "TAX",
            0xab => "PLB",
            0xb0 => match convention {
                InstructionNamingConvention::Regular => "BCS",
                InstructionNamingConvention::Descriptive => "BGE",
            },
            0xb8 => "CLV",
            0xba => "TSX",
            0xbb => "TYX",
            0xc0 | 0xc4 | 0xcc => "CPY",
            0xc1 | 0xc3 | 0xc5 | 0xc7 | 0xc9 | 0xcd | 0xcf | 0xd1 | 0xd2 | 0xd3 | 0xd5 | 0xd7
            | 0xd9 | 0xdd | 0xdf => "CMP",
            0xc2 => "REP",
            0xc6 | 0xce | 0xd6 | 0xde => "DEC",
            0xc8 => "INY",
            0xca => "DEX",
            0xcb => "WAI",
            0xd0 => "BNE",
            0xd4 => "PEI",
            0xd8 => "CLD",
            0xda => "PHX",
            0xdb => "STP",
            0xe0 | 0xe4 | 0xec => "CPX",
            0xe1 | 0xe3 | 0xe5 | 0xe7 | 0xe9 | 0xed | 0xef | 0xf1 | 0xf2 | 0xf3 | 0xf5 | 0xf7
            | 0xf9 | 0xfd | 0xff => "SBC",
            0xe2 => "SEP",
            0xe6 | 0xee | 0xf6 | 0xfe => "INC",
            0xe8 => "INX",
            0xea => "NOP",
            0xeb => "XBA",
            0xf0 => "BEQ",
            0xf4 => "PEA",
            0xf8 => "SED",
            0xfa => "PLX",
            0xfb => "XCE",
        }
    }

    pub const fn instr_ty(&self) -> InstructionType {
        use InstructionType::*;
        match self.0 {
            0x00 => Brk,
            0x01 | 0x03 | 0x05 | 0x07 | 0x09 | 0x0d | 0x0f | 0x11 | 0x12 | 0x13 | 0x15 | 0x17
            | 0x19 | 0x1d | 0x1f => Ora,
            0x02 => Cop,
            0x04 | 0x0c => Tsb,
            0x06 | 0x0a | 0x0e | 0x16 | 0x1e => Asl,
            0x08 => Php,
            0x0b => Phd,
            0x10 => Bpl,
            0x14 | 0x1c => Trb,
            0x18 => Clc,
            0x1a => Inc,
            0x1b => Tcs,
            0x20 | 0x22 | 0xfc => Js,
            0x21 | 0x23 | 0x25 | 0x27 | 0x29 | 0x2d | 0x2f | 0x31 | 0x32 | 0x33 | 0x35 | 0x37
            | 0x39 | 0x3d | 0x3f => And,
            0x24 | 0x2c | 0x34 | 0x3c | 0x89 => Bit,
            0x26 | 0x2a | 0x2e | 0x36 | 0x3e => Rol,
            0x28 => Plp,
            0x2b => Pld,
            0x30 => Bmi,
            0x38 => Sec,
            0x3b => Tsc,
            0x40 => Rti,
            0x41 | 0x43 | 0x45 | 0x47 | 0x49 | 0x4d | 0x4f | 0x51 | 0x52 | 0x53 | 0x55 | 0x57
            | 0x59 | 0x5d | 0x5f => Eor,
            0x42 => Wdm,
            0x44 => Mvp,
            0x46 | 0x4a | 0x4e | 0x56 | 0x5e => Lsr,
            0x48 => Pha,
            0x4b => Phk,
            0x4c | 0x5c | 0x6c | 0x7c | 0xdc => Jmp,
            0x50 => Bvc,
            0x54 => Mvn,
            0x58 => Cli,
            0x5a => Phy,
            0x5b => Tcd,
            0x60 => Rts,
            0x61 | 0x63 | 0x65 | 0x67 | 0x69 | 0x6d | 0x6f | 0x71 | 0x72 | 0x73 | 0x75 | 0x77
            | 0x79 | 0x7d | 0x7f => Adc,
            0x62 => Per,
            0x64 | 0x74 | 0x9c | 0x9e => Stz,
            0x66 | 0x6a | 0x6e | 0x76 | 0x7e => Ror,
            0x68 => Pla,
            0x6b => Rtl,
            0x70 => Bvs,
            0x78 => Sei,
            0x7a => Ply,
            0x7b => Tdc,
            0x80 | 0x82 => Bra,
            0x81 | 0x83 | 0x85 | 0x87 | 0x8d | 0x8f | 0x91 | 0x92 | 0x93 | 0x95 | 0x97 | 0x99
            | 0x9d | 0x9f => Sta,
            0x84 | 0x8c | 0x94 => Sty,
            0x86 | 0x8e | 0x96 => Stx,
            0x88 => Dey,
            0x8a => Txa,
            0x8b => Phb,
            0x90 => Bcc,
            0x98 => Tya,
            0x9a => Txs,
            0x9b => Txy,
            0xa0 | 0xa4 | 0xac | 0xb4 | 0xbc => Ldy,
            0xa1 | 0xa3 | 0xa5 | 0xa7 | 0xa9 | 0xad | 0xaf | 0xb1 | 0xb2 | 0xb3 | 0xb5 | 0xb7
            | 0xb9 | 0xbd | 0xbf => Lda,
            0xa2 | 0xa6 | 0xae | 0xb6 | 0xbe => Ldx,
            0xa8 => Tay,
            0xaa => Tax,
            0xab => Plb,
            0xb0 => Bcs,
            0xb8 => Clv,
            0xba => Tsx,
            0xbb => Tyx,
            0xc0 | 0xc4 | 0xcc => Cpy,
            0xc1 | 0xc3 | 0xc5 | 0xc7 | 0xc9 | 0xcd | 0xcf | 0xd1 | 0xd2 | 0xd3 | 0xd5 | 0xd7
            | 0xd9 | 0xdd | 0xdf => Cmp,
            0xc2 => Rep,
            0x3a | 0xc6 | 0xce | 0xd6 | 0xde => Dec,
            0xc8 => Iny,
            0xca => Dex,
            0xcb => Wai,
            0xd0 => Bne,
            0xd4 => Pei,
            0xd8 => Cld,
            0xda => Phx,
            0xdb => Stp,
            0xe0 | 0xe4 | 0xec => Cpx,
            0xe1 | 0xe3 | 0xe5 | 0xe7 | 0xe9 | 0xed | 0xef | 0xf1 | 0xf2 | 0xf3 | 0xf5 | 0xf7
            | 0xf9 | 0xfd | 0xff => Sbc,
            0xe2 => Sep,
            0xe6 | 0xee | 0xf6 | 0xfe => Inc,
            0xe8 => Inx,
            0xea => Nop,
            0xeb => Xba,
            0xf0 => Beq,
            0xf4 => Pea,
            0xf8 => Sed,
            0xfa => Plx,
            0xfb => Xce,
        }
    }
}
