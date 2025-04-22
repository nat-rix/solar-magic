//! Types using Kleene's Three-Valued logic K₃.

use crate::addr::Addr;

/// Three-Valued "bool". It can be either false, true or unknown.
#[derive(Default, Debug, Clone, Copy, PartialEq)]
pub enum TBool {
    False,
    True,
    #[default]
    Unknown,
}

impl TBool {
    pub fn adc(self, b: Self, c: Self) -> (Self, Self) {
        (self ^ b ^ c, (self & b) | (self & c) | (b & c))
    }

    pub const fn is_known(&self) -> bool {
        matches!(self, Self::False | Self::True)
    }

    pub const fn either(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Self::False, Self::False) => Self::False,
            (Self::True, Self::True) => Self::True,
            _ => Self::Unknown,
        }
    }

    pub const fn get(&self) -> Option<bool> {
        match self {
            Self::False => Some(false),
            Self::True => Some(true),
            Self::Unknown => None,
        }
    }

    pub const fn is_false_or_unknown(&self) -> bool {
        matches!(self, Self::False | Self::Unknown)
    }

    pub const fn is_true_or_unknown(&self) -> bool {
        matches!(self, Self::True | Self::Unknown)
    }
}

impl From<bool> for TBool {
    fn from(value: bool) -> Self {
        if value { Self::True } else { Self::False }
    }
}

impl TryFrom<TBool> for bool {
    type Error = ();
    fn try_from(value: TBool) -> Result<Self, Self::Error> {
        match value {
            TBool::False => Ok(false),
            TBool::True => Ok(true),
            TBool::Unknown => Err(()),
        }
    }
}

impl core::ops::Not for TBool {
    type Output = Self;
    fn not(self) -> Self::Output {
        match self {
            Self::False => Self::True,
            Self::True => Self::False,
            Self::Unknown => Self::Unknown,
        }
    }
}

impl<Rhs: Into<TBool>> core::ops::BitAnd<Rhs> for TBool {
    type Output = Self;
    fn bitand(self, rhs: Rhs) -> Self::Output {
        let rhs: Self = rhs.into();
        match (self, rhs) {
            (Self::False, _) | (_, Self::False) => Self::False,
            (Self::True, Self::True) => Self::True,
            _ => Self::Unknown,
        }
    }
}

impl<Rhs: Into<TBool>> core::ops::BitAndAssign<Rhs> for TBool {
    fn bitand_assign(&mut self, rhs: Rhs) {
        *self = *self & rhs;
    }
}

impl<Rhs: Into<TBool>> core::ops::BitOr<Rhs> for TBool {
    type Output = Self;
    fn bitor(self, rhs: Rhs) -> Self::Output {
        let rhs: Self = rhs.into();
        match (self, rhs) {
            (Self::True, _) | (_, Self::True) => Self::True,
            (Self::False, Self::False) => Self::False,
            _ => Self::Unknown,
        }
    }
}

impl<Rhs: Into<TBool>> core::ops::BitOrAssign<Rhs> for TBool {
    fn bitor_assign(&mut self, rhs: Rhs) {
        *self = *self | rhs;
    }
}

impl<Rhs: Into<TBool>> core::ops::BitXor<Rhs> for TBool {
    type Output = Self;
    fn bitxor(self, rhs: Rhs) -> Self::Output {
        let rhs: Self = rhs.into();
        match (self, rhs) {
            (Self::True, v) | (v, Self::True) => !v,
            (Self::False, v) | (v, Self::False) => v,
            (Self::Unknown, Self::Unknown) => Self::Unknown,
        }
    }
}

impl<Rhs: Into<TBool>> core::ops::BitXorAssign<Rhs> for TBool {
    fn bitxor_assign(&mut self, rhs: Rhs) {
        *self = *self ^ rhs;
    }
}

/// A vector of `TBool`s.
#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TInt<T> {
    mask: T,
    val: T,
}

macro_rules! impl_tint {
    ($($t:ty),*) => { $(
        impl TInt<$t> {
            pub const UNKNOWN: Self = Self { mask: 0, val: 0 };
            pub const fn is_fully_known(&self) -> bool {
                self.mask == <$t>::MAX
            }

            pub const fn is_fully_unknown(&self) -> bool {
                self.mask == 0
            }

            pub const fn new(val: $t) -> Self {
                Self { mask: <$t>::MAX, val }
            }

            pub const fn new_unknown_mask(val: $t) -> Self {
                Self { mask: !val, val: 0 }
            }

            pub const fn get(&self) -> Option<$t> {
                if self.is_fully_known() {
                    Some(self.mask & self.val)
                } else {
                    None
                }
            }

            pub const fn known_bits(&self) -> $t {
                self.mask
            }

            pub const fn known_ones(&self) -> $t {
                self.mask & self.val
            }

            pub const fn is_zero(&self) -> TBool {
                if self.mask & self.val != 0 {
                    TBool::False
                } else if self.mask != <$t>::MAX {
                    TBool::Unknown
                } else {
                    TBool::True
                }
            }

            pub fn contains_any(&self, val: $t) -> TBool {
                !(*self & val).is_zero()
            }

            pub const fn extract_bit(&self, i: u32) -> TBool {
                if (self.mask >> i) & 1 == 0 {
                    TBool::Unknown
                } else if (self.val >> i) & 1 == 0 {
                    TBool::False
                } else {
                    TBool::True
                }
            }

            pub const fn with_bits(mut self, mask: $t, val: TBool) -> Self {
                if matches!(val, TBool::Unknown) {
                    self.mask &= !mask;
                    self.val &= !mask;
                } else {
                    self.mask |= mask;
                    if let TBool::True = val {
                        self.val |= mask;
                    } else {
                        self.val &= !mask;
                    }
                }
                self
            }

            pub fn bitwise(mut self, rhs: impl Into<Self>, mut f: impl FnMut(TBool, TBool) -> TBool) -> Self {
                let rhs = rhs.into();
                for i in 0..<$t>::BITS {
                    let a = self.extract_bit(i);
                    let b = rhs.extract_bit(i);
                    self = self.with_bits(1 << i, f(a, b));
                }
                self
            }

            pub fn adc(self, rhs: impl Into<Self>, carry: impl Into<TBool>) -> (Self, TBool) {
                let mut carry = carry.into();
                let res = self.bitwise(rhs, |a, b| {
                    let (res, new_carry) = TBool::adc(a, b, carry);
                    carry = new_carry;
                    res
                });
                (res, carry)
            }

            pub const fn either(self, rhs: Self) -> Self {
                // mv | 10 | 00 | 11
                // 10 | 10 | 00 | 00
                // 00 | 00 | 00 | 00
                // 11 | 00 | 00 | 11
                let (m1, v1) = (self.mask, self.val);
                let (m2, v2) = (rhs.mask, rhs.val);
                let val = m1 & v1 & m2 & v2;
                let mask = (m1 & m2 & !v1 & !v2) | val;
                Self { mask, val }
            }

            pub const fn is_part_of(self, rhs: Self) -> bool {
                // mv | 10 | 00 | 11
                // 10 |  1 |  1 |  0
                // 00 |  0 |  1 |  0
                // 11 |  0 |  1 |  1
                (!rhs.mask & !rhs.val) | (self.mask & rhs.mask & !(self.val ^ rhs.val)) == <$t>::MAX
            }

            pub const fn msb(&self) -> TBool {
                self.extract_bit(<$t>::BITS - 1)
            }

            pub const fn rol(mut self, c: TBool) -> (Self, TBool) {
                let msb = self.msb();
                self.mask <<= 1;
                self.val <<= 1;
                self = self.with_bits(1, c);
                (self, msb)
            }

            pub const fn ror(mut self, c: TBool) -> (Self, TBool) {
                let lsb = self.extract_bit(0);
                self.mask >>= 1;
                self.val >>= 1;
                self = self.with_bits(1 << (<$t>::BITS - 1), c);
                (self, lsb)
            }

            pub fn set_nz(self, p: TU8) -> TU8 {
                p.with_bits(crate::pf::N, self.msb())
                 .with_bits(crate::pf::Z, self.is_zero())
            }
        }

        impl From<$t> for TInt<$t> {
            fn from(val: $t) -> Self {
                Self::new(val)
            }
        }

        impl TryFrom<TInt<$t>> for $t {
            type Error = ();
            fn try_from(value: TInt<$t>) -> Result<Self, Self::Error> {
                value.is_fully_known().then_some(value.val).ok_or(())
            }
        }

        impl core::ops::Not for TInt<$t> {
            type Output = Self;
            fn not(mut self) -> Self::Output {
                self.val ^= self.mask;
                self
            }
        }

        impl<Rhs: Into<TInt<$t>>> core::ops::BitAnd<Rhs> for TInt<$t> {
            type Output = Self;
            fn bitand(self, rhs: Rhs) -> Self::Output {
                // mv | 10 | 00 | 11
                // 10 | 10 | 10 | 10
                // 00 | 10 | 00 | 00
                // 11 | 10 | 00 | 11
                let rhs: Self = rhs.into();
                let (m1, v1) = (self.mask, self.val);
                let (m2, v2) = (rhs.mask, rhs.val);
                let val = m1 & v1 & m2 & v2;
                let mask = (m1 & !v1) | (m2 & !v2) | val;
                Self { mask, val }
            }
        }

        impl<Rhs: Into<TInt<$t>>> core::ops::BitAndAssign<Rhs> for TInt<$t> {
            fn bitand_assign(&mut self, rhs: Rhs) {
                *self = *self & rhs;
            }
        }

        impl<Rhs: Into<TInt<$t>>> core::ops::BitOr<Rhs> for TInt<$t> {
            type Output = Self;
            fn bitor(self, rhs: Rhs) -> Self::Output {
                // mv | 10 | 00 | 11
                // 10 | 10 | 00 | 11
                // 00 | 00 | 00 | 11
                // 11 | 11 | 11 | 11
                let rhs: Self = rhs.into();
                let (m1, v1) = (self.mask, self.val);
                let (m2, v2) = (rhs.mask, rhs.val);
                let val = (m1 & v1) | (m2 & v2);
                let mask = (m1 & m2 & !v1 & !v2) | val;
                Self { mask, val }
            }
        }

        impl<Rhs: Into<TInt<$t>>> core::ops::BitOrAssign<Rhs> for TInt<$t> {
            fn bitor_assign(&mut self, rhs: Rhs) {
                *self = *self | rhs;
            }
        }

        impl<Rhs: Into<TInt<$t>>> core::ops::BitXor<Rhs> for TInt<$t> {
            type Output = Self;
            fn bitxor(self, rhs: Rhs) -> Self::Output {
                // mv | 10 | 00 | 11
                // 10 | 10 | 00 | 11
                // 00 | 00 | 00 | 00
                // 11 | 11 | 00 | 10
                let rhs: Self = rhs.into();
                let (m1, v1) = (self.mask, self.val);
                let (m2, v2) = (rhs.mask, rhs.val);
                let mask = m1 & m2;
                let val = (v1 ^ v2) & mask;
                Self { mask, val }
            }
        }

        impl<Rhs: Into<TInt<$t>>> core::ops::BitXorAssign<Rhs> for TInt<$t> {
            fn bitxor_assign(&mut self, rhs: Rhs) {
                *self = *self ^ rhs;
            }
        }
    )*};
}

impl_tint!(u8, u16);

impl From<TInt<u8>> for TInt<u16> {
    fn from(value: TInt<u8>) -> Self {
        Self {
            mask: u16::from_le_bytes([value.mask, 0xff]),
            val: value.val.into(),
        }
    }
}

impl TInt<u16> {
    pub const fn into_byte(self) -> TInt<u8> {
        TInt {
            mask: self.mask as _,
            val: self.val as _,
        }
    }

    pub const fn high(&self) -> TU8 {
        self.to_bytes()[1]
    }

    pub const fn to_bytes(self) -> [TInt<u8>; 2] {
        let [m1, m2] = self.mask.to_le_bytes();
        let [v1, v2] = self.val.to_le_bytes();
        [TInt { mask: m1, val: v1 }, TInt { mask: m2, val: v2 }]
    }

    pub const fn from_bytes(bytes: [TInt<u8>; 2]) -> Self {
        Self {
            mask: u16::from_le_bytes([bytes[0].mask, bytes[1].mask]),
            val: u16::from_le_bytes([bytes[0].val, bytes[1].val]),
        }
    }

    pub const fn from_byte_unknown_high(byte: TInt<u8>) -> Self {
        Self::from_bytes([byte, TInt::<u8>::UNKNOWN])
    }

    pub const fn write_low(&mut self, byte: TInt<u8>) {
        let [_, hi] = self.to_bytes();
        *self = Self::from_bytes([byte, hi])
    }

    pub fn write_with_size(&mut self, rhs: TInt<u16>, is8: TBool) {
        match is8 {
            TBool::False => *self = rhs,
            TBool::True => self.write_low(rhs.into_byte()),
            TBool::Unknown => {
                let [_, hi0] = self.to_bytes();
                let [lo, hi1] = rhs.to_bytes();
                *self = Self::from_bytes([lo, hi0.either(hi1)])
            }
        }
    }

    pub fn write_sized(&mut self, rhs: TUnknown) {
        self.write_with_size(rhs.get16(), rhs.is8())
    }
}

impl TInt<Addr> {
    pub const UNKNOWN: Self = Self {
        mask: Addr::new(0, 0),
        val: Addr::new(0, 0),
    };

    pub fn new(bank: impl Into<TInt<u8>>, addr: impl Into<TInt<u16>>) -> Self {
        let (bank, addr) = (bank.into(), addr.into());
        Self {
            mask: Addr::new(bank.mask, addr.mask),
            val: Addr::new(bank.val, addr.val),
        }
    }

    pub fn bank(&self) -> TInt<u8> {
        TInt {
            mask: self.mask.bank,
            val: self.val.bank,
        }
    }

    pub fn addr(&self) -> TInt<u16> {
        TInt {
            mask: self.mask.addr,
            val: self.val.addr,
        }
    }

    pub fn adc(self, rhs: impl Into<TInt<u16>>, c: impl Into<TBool>) -> (Self, TBool) {
        let (addr, c) = self.addr().adc(rhs, c.into());
        let (bank, c) = self.bank().adc(0, c);
        (Self::new(bank, addr), c)
    }

    pub fn add16(self, rhs: impl Into<TInt<u16>>) -> Self {
        Self::new(self.bank(), self.addr().adc(rhs, false).0)
    }

    pub fn add24(self, rhs: impl Into<TInt<u16>>) -> Self {
        let (a, c) = self.addr().adc(rhs, false);
        Self::new(self.bank().adc(0, c).0, a)
    }

    pub const fn is_fully_known(&self) -> bool {
        matches!(self.mask, Addr::MAX)
    }

    pub fn get(&self) -> Option<Addr> {
        self.bank()
            .get()
            .zip(self.addr().get())
            .map(|(bank, addr)| Addr::new(bank, addr))
    }
}

impl From<TInt<u16>> for TInt<Addr> {
    fn from(value: TInt<u16>) -> Self {
        Self {
            mask: Addr::new(0xff, value.mask),
            val: Addr::new(0, value.val),
        }
    }
}

impl From<Addr> for TInt<Addr> {
    fn from(value: Addr) -> Self {
        Self::new(value.bank, value.addr)
    }
}

impl TryFrom<TInt<Addr>> for Addr {
    type Error = ();
    fn try_from(value: TInt<Addr>) -> Result<Self, Self::Error> {
        if value.is_fully_known() {
            Ok(value.val)
        } else {
            Err(())
        }
    }
}

pub type TU8 = TInt<u8>;
pub type TU16 = TInt<u16>;
pub type TU24 = TInt<Addr>;

#[derive(Debug, Clone, Copy)]
pub enum TUnknown {
    U8(TU8),
    U16(TU16),
    Unknown(TU16),
}

impl TUnknown {
    pub const UNKNOWN: Self = Self::Unknown(TU16::UNKNOWN);

    pub fn new(val: impl Into<TU16>, is8: TBool) -> Self {
        let val: TU16 = val.into();
        match is8 {
            TBool::True => Self::U8(val.into_byte()),
            TBool::False => Self::U16(val),
            TBool::Unknown => Self::Unknown(val),
        }
    }

    pub fn get8(self) -> TU8 {
        match self {
            Self::U8(val) => val,
            Self::U16(val) | Self::Unknown(val) => val.into_byte(),
        }
    }

    pub fn get16(self) -> TU16 {
        match self {
            Self::U8(val) => TU16::from_byte_unknown_high(val),
            Self::U16(val) | Self::Unknown(val) => val,
        }
    }

    pub const fn is8(&self) -> TBool {
        match self {
            Self::U8(_) => TBool::True,
            Self::U16(_) => TBool::False,
            Self::Unknown(_) => TBool::Unknown,
        }
    }

    pub fn map_generic<T8, T16, U>(
        self,
        f8: impl FnOnce(TU8) -> T8,
        f16: impl FnOnce(TU16) -> T16,
        t8: impl FnOnce(T8) -> U,
        t16: impl FnOnce(T16) -> U,
        unify: impl FnOnce(TU16, T8, T16) -> U,
    ) -> U {
        match self {
            Self::U8(val) => t8(f8(val)),
            Self::U16(val) => t16(f16(val)),
            Self::Unknown(val) => unify(val, f8(val.into_byte()), f16(val)),
        }
    }

    pub fn map_same<T>(
        self,
        f8: impl FnOnce(TU8) -> T,
        f16: impl FnOnce(TU16) -> T,
        unify: impl FnOnce(TU16, T, T) -> T,
    ) -> T {
        self.map_generic(f8, f16, |v| v, |v| v, unify)
    }

    pub fn map(self, f8: impl FnOnce(TU8) -> TU8, f16: impl FnOnce(TU16) -> TU16) -> Self {
        self.map_generic(f8, f16, Self::U8, Self::U16, |val, v8, v16| {
            TUnknown::Unknown(TU16::from_bytes([v8, val.high()]).either(v16))
        })
    }

    pub fn map8(self, f8: impl FnOnce(TU8) -> TU8, f16: impl FnOnce(TU16) -> TU8) -> TU8 {
        self.map_same(f8, f16, |_, a, b| a.either(b))
    }
}

impl core::ops::Not for TUnknown {
    type Output = Self;
    fn not(self) -> Self::Output {
        self.map(|v| !v, |v| !v)
    }
}

impl From<TU8> for TUnknown {
    fn from(value: TU8) -> Self {
        Self::U8(value)
    }
}

impl From<TU16> for TUnknown {
    fn from(value: TU16) -> Self {
        Self::U16(value)
    }
}

impl From<crate::instruction::am::I> for TUnknown {
    fn from(value: crate::instruction::am::I) -> Self {
        match value {
            crate::instruction::am::I::U8(val) => Self::U8(val.into()),
            crate::instruction::am::I::U16(val) => Self::U16(val.into()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn adc_u8_known_no_carry() {
        assert!(matches!(
            TInt::from(0x53u8).adc(0x9a, false),
            (
                TInt {
                    mask: 0xff,
                    val: 0xed
                },
                TBool::False
            )
        ));
    }

    #[test]
    fn adc_u8_known_carry() {
        assert!(matches!(
            TInt::from(0xc1u8).adc(0xb1, false),
            (
                TInt {
                    mask: 0xff,
                    val: 0x72
                },
                TBool::True
            )
        ));
    }

    #[test]
    fn adc_u8_unknown1() {
        let val: TInt<u8> = TInt { mask: 5, val: 1 };
        assert!(matches!(
            val.adc(val, false),
            (TInt { mask: 1, val: 0 }, TBool::Unknown)
        ));
    }

    #[test]
    fn adc_tbool() {
        assert_eq!(
            TBool::adc(TBool::True, TBool::True, TBool::True),
            (TBool::True, TBool::True)
        );
        assert_eq!(
            TBool::adc(TBool::True, TBool::True, TBool::False),
            (TBool::False, TBool::True)
        );
        assert_eq!(
            TBool::adc(TBool::True, TBool::Unknown, TBool::True),
            (TBool::Unknown, TBool::True)
        );
        assert_eq!(
            TBool::adc(TBool::True, TBool::Unknown, TBool::Unknown),
            (TBool::Unknown, TBool::Unknown)
        );
        assert_eq!(
            TBool::adc(TBool::False, TBool::False, TBool::Unknown),
            (TBool::Unknown, TBool::False)
        );
    }

    #[test]
    fn adc_u8_unknown2() {
        let a: TInt<u8> = TInt::from(0xff);
        let b: TInt<u8> = TInt { mask: 1, val: 1 };
        assert!(matches!(
            a.adc(b, false),
            (TInt { mask: 1, val: 0 }, TBool::True)
        ));
    }

    #[test]
    fn adc_u8_unknown3() {
        let a: TInt<u8> = TInt::from(0xff);
        let b: TInt<u8> = TInt { mask: 1, val: 1 };
        assert!(matches!(
            a.adc(b, TBool::Unknown),
            (TInt { mask: 0, val: 0 }, TBool::True)
        ));
    }

    #[test]
    fn adc_u8_unknown4() {
        let a = TInt::<u8>::from(0xff);
        let b = TInt::<u8>::UNKNOWN;
        assert!(matches!(
            a.adc(b, true),
            (TInt { mask: 0, val: 0 }, TBool::True)
        ));
    }

    #[test]
    fn adc_u8_unknown5() {
        let a = TInt::<u8>::from(0x58);
        let b = TInt { mask: 0xfa, val: 2 };
        assert!(matches!(
            a.adc(b, TBool::Unknown),
            (
                TInt {
                    mask: 0xc0,
                    val: 0x40
                },
                TBool::False
            )
        ));
    }

    #[test]
    fn is_part_of_8() {
        for i in 0..=0xff {
            assert!(TU8::new(i).is_part_of(TU8::new(i)));
            assert!(TU8::new(i).is_part_of(TU8::UNKNOWN));
        }
        assert!(TU8::UNKNOWN.is_part_of(TU8::UNKNOWN));
        assert!(!TU8::UNKNOWN.is_part_of(TU8::new(2) & TU8::UNKNOWN));
    }

    #[test]
    fn test_ror() {
        let mut v = TU8::UNKNOWN & !0x80;
        assert_eq!((v.mask, v.val), (0x80, 0));
        v = v.ror(false.into()).0;
        assert_eq!((v.mask, v.val), (0xc0, 0));
    }
}
