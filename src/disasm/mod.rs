use std::collections::{BTreeMap, HashMap};

use crate::{
    VecMap,
    addr::Addr,
    addr_space::{CartMemoryLocation, MemoryLocation, SystemMemoryLocation},
    cart::Cart,
    instruction::{
        IndirectLongLabel, Instruction, InstructionArgument,
        am::{self, AddrModeRes},
    },
    pf::*,
    tvl::{TBool, TU8, TU16, TU24, TUnknown},
};

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Stack {
    pub items: Vec<TU8>,
}

impl Stack {
    pub fn unify(&mut self, rhs: &Self) {
        for (i, j) in self.items.iter_mut().zip(&rhs.items) {
            *i = i.either(*j)
        }
        self.items.truncate(rhs.items.len());
    }

    pub fn push(&mut self, val: TU8) {
        self.items.push(val);
    }

    pub fn pop(&mut self) -> TU8 {
        self.items.pop().unwrap_or(TU8::UNKNOWN)
    }

    pub fn push16(&mut self, val: TU16) {
        let [lo, hi] = val.to_bytes();
        self.push(hi);
        self.push(lo);
    }

    pub fn pop16(&mut self) -> TU16 {
        let lo = self.pop();
        let hi = self.pop();
        TU16::from_bytes([lo, hi])
    }

    pub fn pop24(&mut self) -> TU24 {
        let addr = self.pop16();
        let bank = self.pop();
        TU24::new(bank, addr)
    }

    fn peek_at(&self, off: usize) -> Option<TU8> {
        self.items
            .get(self.items.len().checked_sub(off + 1)?)
            .copied()
    }

    pub fn peek24(&self, off: usize) -> TU24 {
        let [lo, hi, ba] = [0, 1, 2].map(|i| self.peek_at(off + i).unwrap_or(TU8::UNKNOWN));
        TU24::new(ba, TU16::from_bytes([lo, hi]))
    }

    pub fn push_unknown(&mut self, val: TUnknown) {
        match val {
            TUnknown::U8(val) => self.push(val),
            TUnknown::U16(val) => self.push16(val),
            TUnknown::Unknown(val) => {
                // Push of unknown size completely fucks up our stack.
                // The only thing we could do would be a unify between the two states.
                self.items.clear();
                self.push(val.into_byte());
            }
        }
    }

    pub fn pop_unknown(&mut self, is8: TBool) -> TUnknown {
        match is8 {
            TBool::True => self.pop().into(),
            TBool::False => self.pop16().into(),
            TBool::Unknown => {
                // Push of unknown size completely fucks up our stack.
                // The only thing we could do would be a unify between the two states.
                let lo = self.pop();
                self.items.clear();
                TUnknown::Unknown(TU16::from_byte_unknown_high(lo))
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Context {
    pub a: TU16,
    pub x: TU16,
    pub y: TU16,
    pub b: TU8,
    pub d: TU16,
    pub p: TU8,
    pub pc: Addr,
    pub map: VecMap<MemoryLocation, TU8>,
    pub stack: Stack,
}

impl Context {
    pub fn unknown(pc: Addr) -> Self {
        Self {
            a: TU16::UNKNOWN,
            x: TU16::UNKNOWN,
            y: TU16::UNKNOWN,
            b: TU8::UNKNOWN,
            d: TU16::UNKNOWN,
            p: TU8::UNKNOWN,
            pc,
            map: Default::default(),
            stack: Default::default(),
        }
    }

    pub fn read8(&self, cart: &Cart, addr: impl Into<TU24>) -> Option<TU8> {
        let addr = addr.into();
        let key = cart.map_full_unknown(addr)?;
        match &key {
            MemoryLocation::System(SystemMemoryLocation::Wram(_))
            | MemoryLocation::Cart(CartMemoryLocation::Sram(_)) => self.map.get(&key).copied(),
            MemoryLocation::Cart(CartMemoryLocation::Rom(off)) => Some(cart.rom.read(*off).into()),
            _ => None,
        }
    }

    pub fn write8(&mut self, cart: &Cart, addr: impl Into<TU24>, val: TU8) -> Option<()> {
        let addr = addr.into();
        let Some(key) = cart.map_full_unknown(addr) else {
            // a write to an unknown address could theoretically corrupt every
            // memory cell so we have to forget everything we have known
            self.map.clear();
            return None;
        };
        if val.is_fully_unknown() {
            self.map.remove(&key);
        } else {
            self.map.insert(key, val);
        }
        Some(())
    }

    pub fn read16(&self, cart: &Cart, mut addr: AddrModeRes) -> Option<TU16> {
        let lo = self.read8(cart, addr)?;
        addr.incr();
        let hi = self.read8(cart, addr)?;
        Some(TU16::from_bytes([lo, hi]))
    }

    pub fn write16(&mut self, cart: &Cart, mut addr: AddrModeRes, val: TU16) {
        let [lo, hi] = val.to_bytes();
        self.write8(cart, addr, lo);
        addr.incr();
        self.write8(cart, addr, hi);
    }

    pub fn read24(&self, cart: &Cart, mut addr: AddrModeRes) -> Option<TU24> {
        let lo = self.read8(cart, addr)?;
        addr.incr();
        let hi = self.read8(cart, addr)?;
        addr.incr();
        let ba = self.read8(cart, addr)?;
        Some(TU24::new(ba, TU16::from_bytes([lo, hi])))
    }

    pub fn write_sized(&mut self, cart: &Cart, mut addr: AddrModeRes, val: TUnknown) {
        match val {
            TUnknown::U8(val) => {
                self.write8(cart, addr, val);
            }
            TUnknown::U16(val) => {
                let [lo, hi] = val.to_bytes();
                self.write8(cart, addr, lo);
                addr.incr();
                self.write8(cart, addr, hi);
            }
            TUnknown::Unknown(val) => {
                let [lo, hi] = val.to_bytes();
                self.write8(cart, addr, lo);
                addr.incr();
                let val = self.read8(cart, addr).unwrap_or(TU8::UNKNOWN);
                self.write8(cart, addr, val.either(hi));
            }
        }
    }

    pub fn read_sized(&self, cart: &Cart, addr: AddrModeRes, is8: TBool) -> TUnknown {
        match is8 {
            TBool::True => self.read8(cart, addr.addr).unwrap_or(TU8::UNKNOWN).into(),
            TBool::False => self.read16(cart, addr).unwrap_or(TU16::UNKNOWN).into(),
            TBool::Unknown => TUnknown::Unknown(self.read16(cart, addr).unwrap_or(TU16::UNKNOWN)),
        }
    }

    pub fn read_sized_m(&self, cart: &Cart, addr: AddrModeRes) -> TUnknown {
        self.read_sized(cart, addr, self.mf())
    }

    pub fn read_sized_x(&self, cart: &Cart, addr: AddrModeRes) -> TUnknown {
        self.read_sized(cart, addr, self.xf())
    }

    pub fn resolve_a(&self, _cart: &Cart, a: &am::A) -> AddrModeRes {
        AddrModeRes {
            is24: true,
            addr: TU24::new(self.b, a.0),
        }
    }

    pub fn resolve_ax(&self, cart: &Cart, ax: &am::Ax) -> AddrModeRes {
        self.resolve_a(cart, &am::A(ax.0)).offset24(self.x)
    }

    pub fn resolve_ay(&self, cart: &Cart, ay: &am::Ay) -> AddrModeRes {
        self.resolve_a(cart, &am::A(ay.0)).offset24(self.y)
    }

    pub fn resolve_al(&self, _cart: &Cart, al: &am::Al) -> AddrModeRes {
        AddrModeRes {
            is24: true,
            addr: al.0.into(),
        }
    }

    pub fn resolve_alx(&self, cart: &Cart, alx: &am::Alx) -> AddrModeRes {
        self.resolve_al(cart, &am::Al(alx.0)).offset24(self.x)
    }

    pub fn resolve_d(&self, _cart: &Cart, d: &am::D) -> AddrModeRes {
        AddrModeRes {
            is24: false,
            addr: TU24::new(0, self.d.adc(u16::from(d.0), false).0),
        }
    }

    pub fn resolve_dx(&self, cart: &Cart, dx: &am::Dx) -> AddrModeRes {
        self.resolve_d(cart, &am::D(dx.0)).offset16(self.x)
    }

    pub fn resolve_dy(&self, cart: &Cart, dy: &am::Dy) -> AddrModeRes {
        self.resolve_d(cart, &am::D(dy.0)).offset16(self.y)
    }

    pub fn resolve_di(&self, cart: &Cart, di: &am::Di) -> AddrModeRes {
        let addr = self
            .read16(cart, self.resolve_d(cart, &am::D(di.0)))
            .unwrap_or(TU16::UNKNOWN);
        AddrModeRes {
            is24: true,
            addr: TU24::new(self.b, addr),
        }
    }

    pub fn resolve_diy(&self, cart: &Cart, diy: &am::Diy) -> AddrModeRes {
        self.resolve_di(cart, &am::Di(diy.0)).offset24(self.y)
    }

    pub fn resolve_dil(&self, cart: &Cart, dil: &am::Dil) -> AddrModeRes {
        let addr = self
            .read24(cart, self.resolve_d(cart, &am::D(dil.0)))
            .unwrap_or(TU24::UNKNOWN);
        AddrModeRes { is24: true, addr }
    }

    pub fn resolve_dily(&self, cart: &Cart, dily: &am::Dily) -> AddrModeRes {
        self.resolve_dil(cart, &am::Dil(dily.0)).offset24(self.y)
    }

    pub fn resolve_jmli(&self, cart: &Cart, jmli: &IndirectLongLabel) -> TU24 {
        self.read24(
            cart,
            AddrModeRes {
                is24: false,
                addr: TU24::new(0, jmli.0),
            },
        )
        .unwrap_or(TU24::UNKNOWN)
    }

    pub fn set_nz8(&mut self, val: impl Into<TU8>) {
        let val: TU8 = val.into();
        self.p = val.set_nz(self.p);
    }

    pub fn set_nz16(&mut self, val: impl Into<TU16>) {
        let val: TU16 = val.into();
        self.p = val.set_nz(self.p);
    }

    pub fn set_nzx(&mut self, val: impl Into<TUnknown>) {
        let val: TUnknown = val.into();
        self.p = val.map8(|v| v.set_nz(self.p), |v| v.set_nz(self.p));
    }

    pub fn mf(&self) -> TBool {
        self.p.contains_any(M)
    }

    pub fn xf(&self) -> TBool {
        self.p.contains_any(X)
    }

    pub fn a_sized(&self) -> TUnknown {
        TUnknown::new(self.a, self.mf())
    }

    pub fn x_sized(&self) -> TUnknown {
        TUnknown::new(self.x, self.xf())
    }

    pub fn y_sized(&self) -> TUnknown {
        TUnknown::new(self.y, self.xf())
    }

    pub fn is_part_of(&self, ctx: &Self) -> bool {
        self.a.is_part_of(ctx.a)
            && self.x.is_part_of(ctx.x)
            && self.y.is_part_of(ctx.y)
            && self.b.is_part_of(ctx.b)
            && self.d.is_part_of(ctx.d)
            && self.p.is_part_of(ctx.p)
            && ctx.map.iter().all(|(k, v)| {
                self.map
                    .get(k)
                    .copied()
                    .unwrap_or(TU8::UNKNOWN)
                    .is_part_of(*v)
            })
            && self.stack.items.len() <= ctx.stack.items.len()
            && ctx
                .stack
                .items
                .iter()
                .rev()
                .zip(self.stack.items.iter().rev())
                .all(|(a, b)| b.is_part_of(*a))
    }

    pub fn unify(&mut self, ctx: &Self) {
        self.a = self.a.either(ctx.a);
        self.x = self.x.either(ctx.x);
        self.y = self.y.either(ctx.y);
        self.b = self.b.either(ctx.b);
        self.d = self.d.either(ctx.d);
        self.p = self.p.either(ctx.p);
        self.map.retain(|k, v| {
            if let Some(v2) = ctx.map.get(k) {
                *v = v.either(*v2);
                true
            } else {
                false
            }
        });
        self.stack.unify(&ctx.stack);
    }

    pub fn call_subroutine(&mut self, cart: &Cart, new_pc: Addr) -> bool {
        if cart.read_rom(new_pc).is_none() {
            // in case of subroutines in ram... just ignore them
            // no ones gonna need them. We have to trust, that they
            // do a return instruction thou
            return false;
        }
        self.pc = new_pc;
        true
    }
}

#[derive(Debug, Clone)]
pub struct AnnotatedInstruction {
    pub instruction: Instruction,
    pub pre: Context,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CallStackRoot {
    Vector(u16),
    Table(Addr),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CallStackItem {
    pub addr: Addr,
    pub is_long: bool,
    pub stack_offset: u16,
}

impl CallStackItem {
    pub const fn new_short(addr: Addr, stack_offset: u16) -> Self {
        Self {
            is_long: false,
            stack_offset,
            addr,
        }
    }

    pub const fn new_long(addr: Addr, stack_offset: u16) -> Self {
        Self {
            is_long: true,
            stack_offset,
            addr,
        }
    }

    pub fn return_addr(&self) -> Addr {
        self.addr.add16(if self.is_long { 4 } else { 3 })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CallStack {
    root: CallStackRoot,
    items: Vec<CallStackItem>,
}

impl CallStack {
    pub const fn from_root(root: CallStackRoot) -> Self {
        Self {
            root,
            items: vec![],
        }
    }

    pub fn push(&mut self, item: CallStackItem) -> bool {
        if let Some(ix) = self.items.iter().position(|a| a.addr == item.addr) {
            // If the call stack already contais this address, we are trapped
            // in an infinity loop. We can break the cycle by reverting the call
            // stack to the original address.
            self.items.truncate(ix + 1);
            true
        } else {
            self.items.push(item);
            false
        }
    }

    pub fn push_short(&mut self, addr: Addr, stack_offset: u16) -> bool {
        self.push(CallStackItem::new_short(addr, stack_offset))
    }

    pub fn push_long(&mut self, addr: Addr, stack_offset: u16) -> bool {
        self.push(CallStackItem::new_long(addr, stack_offset))
    }

    pub fn pop(&mut self) -> Option<CallStackItem> {
        self.items.pop()
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn items(&self) -> &[CallStackItem] {
        &self.items
    }

    pub const fn root(&self) -> &CallStackRoot {
        &self.root
    }
}

impl core::fmt::Display for CallStack {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self.root {
            CallStackRoot::Vector(0xffe4) => write!(f, "COP")?,
            CallStackRoot::Vector(0xffe6) => write!(f, "BRK")?,
            CallStackRoot::Vector(0xffea) => write!(f, "NMI")?,
            CallStackRoot::Vector(0xffee) => write!(f, "IRQ")?,
            CallStackRoot::Vector(0xfff4) => write!(f, "COPe")?,
            CallStackRoot::Vector(0xfffa) => write!(f, "NMIe")?,
            CallStackRoot::Vector(0xfffc) => write!(f, "RESET")?,
            CallStackRoot::Vector(0xfffe) => write!(f, "IRQe")?,
            CallStackRoot::Vector(v) => write!(f, "vec{v:04X}")?,
            CallStackRoot::Table(addr) => write!(f, "{{{addr}}}")?,
        };
        for it in &self.items {
            write!(f, ",")?;
            if it.is_long {
                write!(f, "[{}]", it.addr)?;
            } else {
                write!(f, "({})", it.addr)?;
            }
        }
        Ok(())
    }
}

impl core::cmp::PartialOrd for CallStack {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl core::cmp::Ord for CallStack {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        fn score(v: &CallStack) -> impl core::cmp::Ord {
            (
                match &v.root {
                    CallStackRoot::Vector(0xfffc) => 0,
                    CallStackRoot::Vector(0xffea) => 1,
                    CallStackRoot::Vector(0xffee) => 2,
                    CallStackRoot::Vector(_) => 3,
                    CallStackRoot::Table(_) => 4,
                },
                v.len(),
                v.items.as_slice(),
            )
        }
        score(self).cmp(&score(other))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JumpTableType {
    Addr16,
    Addr24,
}

impl JumpTableType {
    pub const fn entry_size(&self) -> u8 {
        match self {
            Self::Addr16 => 2,
            Self::Addr24 => 3,
        }
    }
}

#[derive(Debug, Clone)]
pub struct JumpTable {
    pub known_entry_offsets: Vec<u16>,
    pub ty: JumpTableType,
}

impl JumpTable {
    pub fn offset_to_addr(&self, cart: &Cart, offset: u16, table_addr: Addr) -> Option<Addr> {
        let item_addr = table_addr.add16(offset);
        let lo = cart.read_rom(item_addr)?;
        let hi = cart.read_rom(item_addr.add16(1))?;
        let addr = u16::from_le_bytes([lo, hi]);
        let bank = match self.ty {
            JumpTableType::Addr16 => table_addr.bank,
            JumpTableType::Addr24 => cart.read_rom(item_addr.add16(2))?,
        };
        Some(Addr::new(bank, addr))
    }

    pub fn iter_addrs<'a>(
        &'a self,
        cart: &'a Cart,
        table_addr: Addr,
    ) -> impl Iterator<Item = Addr> + 'a {
        self.known_entry_offsets
            .iter()
            .filter_map(move |off| self.offset_to_addr(cart, *off, table_addr))
    }

    fn table_entry_is_null(&self, cart: &Cart, table_addr: Addr, off: u16) -> bool {
        self.offset_to_addr(cart, off, table_addr)
            .is_some_and(|val| match self.ty {
                JumpTableType::Addr16 => val.addr == 0,
                JumpTableType::Addr24 => val == Addr::NULL,
            })
    }

    pub fn first_free_offset(&self, cart: &Cart, table_addr: Addr) -> Option<u16> {
        let mut start = table_addr.addr;
        let entry_size: u16 = self.ty.entry_size() as _;
        loop {
            let off = start.wrapping_sub(table_addr.addr);
            if !self.known_entry_offsets.contains(&off)
                && !self.table_entry_is_null(cart, table_addr, off)
            {
                return Some(off);
            }
            let old_start = start;
            start = start.wrapping_add(entry_size);
            if start <= old_start {
                break;
            }
        }
        None
    }
}

#[derive(Debug, Clone)]
pub struct Head {
    pub ctx: Context,
    pub call_stack: CallStack,
}

#[derive(Clone)]
pub struct Disassembler {
    pub code_annotations: BTreeMap<Addr, VecMap<CallStack, AnnotatedInstruction>>,
    pub jump_tables: BTreeMap<Addr, JumpTable>,
    pub jump_table_items: HashMap<Addr, Addr>,
    pub vectors: Vec<(u16, u16)>,
    pub unified_code_annotations: BTreeMap<Addr, AnnotatedInstruction>,
    heads: Vec<Head>,
}

impl Disassembler {
    pub fn new() -> Self {
        Self {
            code_annotations: BTreeMap::new(),
            jump_tables: BTreeMap::new(),
            jump_table_items: HashMap::new(),
            unified_code_annotations: BTreeMap::new(),
            vectors: vec![],
            heads: vec![],
        }
    }

    pub fn get_annotation(
        &self,
        addr: Addr,
        call_stack: &CallStack,
    ) -> Option<&AnnotatedInstruction> {
        self.code_annotations.get(&addr)?.get(call_stack)
    }

    pub fn get_annotation_with_shortest_callstack(
        &self,
        addr: Addr,
    ) -> Option<(&CallStack, &AnnotatedInstruction)> {
        self.code_annotations.get(&addr)?.iter().next()
    }

    pub fn add_vector(&mut self, cart: &Cart, vec: u16) {
        let lo = cart.read_rom(Addr::new(0, vec));
        let hi = cart.read_rom(Addr::new(0, vec.wrapping_add(1)));
        let Some(addr) = lo.zip(hi).map(|(lo, hi)| u16::from_le_bytes([lo, hi])) else {
            return;
        };
        if !self.vectors.contains(&(vec, addr)) {
            self.vectors.push((vec, addr));
        }
        let ctx = Context {
            a: 0.into(),
            x: 0.into(),
            y: 0.into(),
            b: 0.into(),
            d: 0.into(),
            p: (M | X | I).into(),
            pc: Addr::new(0, addr),
            map: VecMap::new(),
            stack: Default::default(),
        };
        let head = Head {
            ctx,
            call_stack: CallStack::from_root(CallStackRoot::Vector(vec)),
        };
        self.heads.push(head);
    }

    pub fn add_vectors(&mut self, cart: &Cart) {
        for i in 0..16 {
            if (0xe4ac >> i) & 1 == 0 {
                continue;
            }
            let vec = 0xffe0 | (i << 1);
            self.add_vector(cart, vec);
        }
    }

    pub fn find_extendable_jump_table(
        &mut self,
        cart: &Cart,
    ) -> Option<(&mut JumpTable, Addr, u16)> {
        self.jump_tables
            .iter_mut()
            .filter_map(|(addr, table)| {
                let off = table.first_free_offset(cart, *addr)?;
                let dst = table.offset_to_addr(cart, off, *addr)?;
                // TODO: if we are desperate search even further.
                //       e.g. the table at 02:f825 has a null-pointer
                cart.read_rom(dst)?;
                Some((table, *addr, off, dst))
            })
            // table heuristics
            .filter_map(|(table, table_start, off, dst)| {
                let mut score: i64 = 0;

                score -= table.known_entry_offsets.len().min(200) as i64 >> 3;

                let mut pc = dst;
                for _ in 0..5 {
                    score += if let Some(instr) = Instruction::from_fetcher(
                        || cart.read_rom(pc.add16_repl(1)),
                        Some(true),
                        Some(true),
                    ) {
                        (match instr {
                            // wrong classified RTS & RTL isn't that problematic
                            Instruction::Rts | Instruction::Rtl => 100,
                            Instruction::Php => {
                                score += 20;
                                // PHP is good here but we need to look ahead,
                                // because PHP has opcode 0x08
                                continue;
                            }
                            Instruction::Phd => {
                                score += 5;
                                // PHD is good here but we need to look ahead,
                                // because PHD has opcode 0x0B
                                continue;
                            }
                            Instruction::Pha
                            | Instruction::Phx
                            | Instruction::Phy
                            | Instruction::Phb => 15,
                            Instruction::Cop(_)
                            | Instruction::Brk(_)
                            | Instruction::Stp
                            | Instruction::Wdm(_) => -1_000,
                            // these branch instructions are dependent of flags. It is rather
                            // unlikely that they are used as the first intruction
                            Instruction::Bpl(_)
                            | Instruction::Bmi(_)
                            | Instruction::Beq(_)
                            | Instruction::Bne(_)
                            | Instruction::Bvc(_)
                            | Instruction::Bvs(_)
                            | Instruction::Bcc(_)
                            | Instruction::Bcs(_) => -51,
                            Instruction::AslAc
                            | Instruction::IncAc
                            | Instruction::RolAc
                            | Instruction::DecAc
                            | Instruction::LsrAc
                            | Instruction::RorAc => -50,
                            // a rather uncommon instruction
                            Instruction::LdyDx(_) => -32,
                            Instruction::Rep(fl) | Instruction::Sep(fl) => {
                                if fl.0 == 0 {
                                    // basically a NOP, we don't need that
                                    -30
                                } else if fl.0 & (Z | I | V | D) != 0 {
                                    -5
                                } else {
                                    20
                                }
                            }
                            // why would you branch in the first instruction of a subroutine
                            Instruction::Bra(label) => {
                                score -= 5;
                                pc = label.take(pc);
                                continue;
                            }
                            Instruction::Jsr(label) => {
                                score += 10;
                                pc = label.take(pc);
                                continue;
                            }
                            Instruction::Jsl(label) => {
                                if label.bank & 0x7e == 0x7e {
                                    // jumps into wram are actually ok
                                    20
                                } else {
                                    score += 10;
                                    pc = label;
                                    continue;
                                }
                            }
                            Instruction::Nop => {
                                continue;
                            }
                            _ => 0,
                        }) + (match instr.arg() {
                            Some(InstructionArgument::A(_) | InstructionArgument::D(_)) => 5,
                            Some(InstructionArgument::S(_)) => -40,
                            Some(InstructionArgument::Siy(_)) => -60,
                            // these arguments are dependent of the A,X or Y register
                            // and thus it is unlikely that they are used as the
                            // first instruction
                            Some(
                                InstructionArgument::Ax(_)
                                | InstructionArgument::Ay(_)
                                | InstructionArgument::Alx(_),
                            ) => -10,
                            // direct address modes are even less likely
                            Some(
                                InstructionArgument::Dx(_)
                                | InstructionArgument::Dy(_)
                                | InstructionArgument::Dxi(_)
                                | InstructionArgument::Diy(_)
                                | InstructionArgument::Dily(_),
                            ) => -20,
                            _ => 0,
                        }) + (match instr
                            .opcode()
                            .name(crate::instruction::InstructionNamingConvention::Descriptive)
                        {
                            // these instructions are dependent of the A,X or Y register
                            // and thus it is unlikely that they are used as the
                            // first instruction
                            "ADC" | "SBC" | "TSB" | "TRB" | "STA" | "EOR" | "AND" | "ORA"
                            | "BIT" | "CMP" => -51,
                            "STX" | "STY" | "INX" | "INY" => -10,
                            // `LDA` is often used as the first instruction, because it
                            // was invalidated by the trampoline
                            "LDA" => 10,
                            _ => 0,
                        })
                    } else {
                        -1_000
                    };
                    break;
                }

                let is_samebank =
                    matches!(table.ty, JumpTableType::Addr24) && dst.bank == table_start.bank;
                if is_samebank {
                    score += 25;
                }

                // if there is no code in a range it is likely that this points to data
                if self
                    .code_annotations
                    .range(dst.range_around(0x80))
                    .next()
                    .is_none()
                {
                    score -= 10;
                }
                if self
                    .code_annotations
                    .range(dst.range_around(0x180))
                    .next()
                    .is_none()
                {
                    score -= 20;
                }
                if self
                    .code_annotations
                    .range(dst.range_around(0x600))
                    .next()
                    .is_none()
                {
                    score -= 20;
                }

                pc = table_start.add16(off);
                for _ in 0..5 {
                    if let Some(instr) = Instruction::from_fetcher(
                        || cart.read_rom(pc.add16_repl(1)),
                        Some(true),
                        Some(true),
                    ) {
                        match instr {
                            Instruction::Jsr(_) | Instruction::Jsl(_) => {
                                score -= 20;
                                continue;
                            }
                            Instruction::LdaA(_) => {
                                score -= 15;
                                continue;
                            }
                            Instruction::Rts => {
                                if is_samebank {
                                    score -= 20;
                                } else {
                                    score -= 100;
                                }
                            }
                            Instruction::Rtl => {
                                if is_samebank {
                                    score -= 5;
                                } else {
                                    score -= 20;
                                }
                            }
                            _ => (),
                        }
                    }
                    break;
                }

                // TODO: this check is temorary: bad looking table elements are skipped
                if score < -50 {
                    None
                } else {
                    Some((table, table_start, off, dst, score))
                }
            })
            .max_by_key(|(.., score)| *score)
            .map(|(table, table_start, off, ..)| (table, table_start, off))
    }

    pub fn disassemble(&mut self, cart: &Cart) {
        'disasm_loop: loop {
            while !self.is_done() {
                self.disassemble_step(cart);
            }
            for (dst, taddr) in self
                .jump_tables
                .iter()
                .flat_map(|(addr, table)| table.iter_addrs(cart, *addr).map(move |a| (a, addr)))
            {
                let call_stack = CallStack::from_root(CallStackRoot::Table(*taddr));
                let exists = self
                    .code_annotations
                    .get(&dst)
                    .is_some_and(|ann| ann.contains_key(&call_stack));
                if !exists {
                    self.heads.push(Head {
                        ctx: Context {
                            a: TU16::UNKNOWN,
                            x: TU16::UNKNOWN,
                            y: TU16::UNKNOWN,
                            b: TU8::UNKNOWN,
                            d: TU16::UNKNOWN,
                            p: TU8::UNKNOWN | M | X,
                            pc: dst,
                            map: Default::default(),
                            stack: Default::default(),
                        },
                        call_stack,
                    });
                    // TODO: there can be an infinite loop in case that `disassemble_step` fails
                    //       in the next iteration step
                    continue 'disasm_loop;
                }
            }
            if let Some((table, _taddr, off)) = self.find_extendable_jump_table(cart) {
                table.known_entry_offsets.push(off);
                continue 'disasm_loop;
            }
            break;
        }
        self.jump_table_items = self
            .jump_tables
            .iter()
            .flat_map(|(table_start, table)| {
                table
                    .known_entry_offsets
                    .iter()
                    .map(|off| (table_start.add16(*off), *table_start))
            })
            .collect();
        self.unified_code_annotations = self
            .code_annotations
            .iter()
            .filter_map(|(addr, map)| {
                let mut iter = map.iter();
                let (_, first) = iter.next()?;
                let mut first = first.clone();
                for (_cs, rhs) in iter {
                    first.pre.unify(&rhs.pre);
                }
                Some((*addr, first))
            })
            .collect();

        let mut off: u32 = 0;
        let mut first_area_ix: Option<u32> = None;
        let mut last_area_ix: Option<u32> = None;
        while off < cart.rom.data.len() as u32 {
            let Some(addr) = cart.reverse_map_rom(off) else {
                break;
            };
            off += if let Some((_call_stack, ann)) =
                self.get_annotation_with_shortest_callstack(addr)
            {
                u32::from(ann.instruction.size())
            } else if let Some(table_start) = self.jump_table_items.get(&addr) {
                let table = self.jump_tables.get(table_start).unwrap();
                u32::from(table.ty.entry_size())
            } else {
                if first_area_ix.is_none() {
                    first_area_ix = Some(off);
                }
                last_area_ix = Some(off);
                off += 1;
                continue;
            };
            if let (Some(start), Some(end)) = (first_area_ix, last_area_ix) {
                first_area_ix = None;
                let start_addr = cart.reverse_map_rom(start);
                let end_addr = cart.reverse_map_rom(end);
                if let (Some(start), Some(end)) = (start_addr, end_addr) {
                    println!("area: {start}..={end}");
                }
            }
        }
    }

    pub fn is_done(&self) -> bool {
        self.heads.is_empty()
    }

    pub fn disassemble_step(&mut self, cart: &Cart) {
        let Some(mut head) = self.heads.pop() else {
            return;
        };

        if let Some(location) = self.code_annotations.get(&head.ctx.pc) {
            if let Some(annotation) = location.get(&head.call_stack) {
                if head.ctx.is_part_of(&annotation.pre) {
                    return;
                }
                head.ctx.unify(&annotation.pre);
            }
        }

        let pc = head.ctx.pc;
        match self.disassemble_with_head(cart, head.clone()) {
            Some(instruction) => {
                let annotation = AnnotatedInstruction {
                    instruction,
                    pre: head.ctx,
                };
                self.code_annotations
                    .entry(pc)
                    .or_default()
                    .insert(head.call_stack, annotation);
            }
            None => {
                // TODO: rehandle
            }
        }
    }

    fn sync_callstack(&mut self, ctx: &Context, call_stack: &mut CallStack) {
        while call_stack
            .items
            .last()
            .is_some_and(|item| item.stack_offset as usize + 2 > ctx.stack.items.len())
        {
            call_stack.items.pop();
        }
    }

    fn instr_stz(&mut self, cart: &Cart, ctx: &mut Context, addr: AddrModeRes) {
        ctx.write_sized(cart, addr, TUnknown::new(0, ctx.mf()));
    }

    fn instr_sta(&mut self, cart: &Cart, ctx: &mut Context, addr: AddrModeRes) {
        ctx.write_sized(cart, addr, ctx.a_sized());
    }

    fn instr_stx(&mut self, cart: &Cart, ctx: &mut Context, addr: AddrModeRes) {
        ctx.write_sized(cart, addr, ctx.x_sized());
    }

    fn instr_sty(&mut self, cart: &Cart, ctx: &mut Context, addr: AddrModeRes) {
        ctx.write_sized(cart, addr, ctx.y_sized());
    }

    fn instr_adcimm(&mut self, ctx: &mut Context, mut val: TUnknown, is_sbc: bool) {
        let c = ctx.p.contains_any(C);
        if is_sbc {
            val = !val;
        }
        (ctx.a, ctx.p) = ctx.a_sized().map_same(
            |a| {
                let rhs = val.get8();
                let (new_a, c) = a.adc(rhs, c);
                let p = ctx
                    .p
                    .with_bits(V, !(a.msb() ^ rhs.msb()) & (a.msb() ^ new_a.msb()))
                    .with_bits(C, c);
                let p = new_a.set_nz(p);
                let new_a = TU16::from_bytes([new_a, ctx.a.high()]);
                (new_a, p)
            },
            |a| {
                let rhs = val.get16();
                let (new_a, c) = a.adc(rhs, c);
                let p = ctx
                    .p
                    .with_bits(V, !(a.msb() ^ rhs.msb()) & (a.msb() ^ new_a.msb()))
                    .with_bits(C, c);
                let p = new_a.set_nz(p);
                (new_a, p)
            },
            |_, (a1, p1), (a2, p2)| (a1.either(a2), p1.either(p2)),
        );
    }

    pub fn instr_adc(&mut self, cart: &Cart, ctx: &mut Context, addr: AddrModeRes, is_sbc: bool) {
        let rhs = ctx.read_sized_m(cart, addr);
        self.instr_adcimm(ctx, rhs, is_sbc);
    }

    fn instr_cmpimm(&mut self, ctx: &mut Context, a: TUnknown, b: TUnknown) {
        ctx.p = a.map8(
            |a| {
                let (r, c) = a.adc(!b.get8(), true);
                r.set_nz(ctx.p).with_bits(C, c)
            },
            |a| {
                let (r, c) = a.adc(!b.get16(), true);
                r.set_nz(ctx.p).with_bits(C, c)
            },
        );
    }

    fn instr_cmp(&mut self, cart: &Cart, ctx: &mut Context, addr: AddrModeRes) {
        let a = ctx.a_sized();
        let b = ctx.read_sized_m(cart, addr);
        self.instr_cmpimm(ctx, a, b);
    }

    fn instr_cpx(&mut self, cart: &Cart, ctx: &mut Context, addr: AddrModeRes) {
        let x = ctx.x_sized();
        let b = ctx.read_sized_x(cart, addr);
        self.instr_cmpimm(ctx, x, b);
    }

    fn instr_cpy(&mut self, cart: &Cart, ctx: &mut Context, addr: AddrModeRes) {
        let y = ctx.y_sized();
        let b = ctx.read_sized_x(cart, addr);
        self.instr_cmpimm(ctx, y, b);
    }

    fn modify(
        &mut self,
        ctx: &mut Context,
        f8: impl FnOnce(TU8, TU8) -> (TU8, TU8),
        f16: impl FnOnce(TU16, TU8) -> (TU16, TU8),
        val: TUnknown,
    ) -> TUnknown {
        let (new_val, new_p) = val.map_generic(
            |v| f8(v, ctx.p),
            |v| f16(v, ctx.p),
            |(v, p)| (TUnknown::U8(v), p),
            |(v, p)| (TUnknown::U16(v), p),
            |v, (v8, p8), (v16, p16)| {
                let v8 = TU16::from_bytes([v8, v.high()]);
                (TUnknown::Unknown(v8.either(v16)), p8.either(p16))
            },
        );
        ctx.p = new_p;
        new_val
    }

    fn instr_tsb(&mut self, ctx: &mut Context, cart: &Cart, addr: AddrModeRes, is_set: bool) {
        let val = ctx.read_sized_m(cart, addr);
        let a = ctx.a;
        let new_val = self.modify(
            ctx,
            |v, p| {
                (
                    if is_set {
                        v | a.into_byte()
                    } else {
                        v & !a.into_byte()
                    },
                    p.with_bits(Z, (v & a.into_byte()).is_zero()),
                )
            },
            |v, p| {
                (
                    if is_set { v | a } else { v & !a },
                    p.with_bits(Z, (v & a).is_zero()),
                )
            },
            val,
        );
        ctx.write_sized(cart, addr, new_val);
    }

    fn instr_incany(&mut self, ctx: &mut Context, val: TUnknown, is_inc: bool) -> TUnknown {
        self.modify(
            ctx,
            |v, p| {
                let v = v.adc(if is_inc { 1 } else { 0xff }, false).0;
                (v, v.set_nz(p))
            },
            |v, p| {
                let v = v.adc(if is_inc { 1 } else { 0xffff }, false).0;
                (v, v.set_nz(p))
            },
            val,
        )
    }

    fn instr_incimm(
        &mut self,
        ctx: &mut Context,
        mut reg: impl FnMut(&mut Context) -> &mut TU16,
        is8: TBool,
        is_inc: bool,
    ) {
        let old_a = *reg(ctx);
        let new_a = self.instr_incany(ctx, TUnknown::new(old_a, is8), is_inc);
        reg(ctx).write_sized(new_a);
    }

    fn instr_inc(&mut self, ctx: &mut Context, cart: &Cart, addr: AddrModeRes, is_inc: bool) {
        let old_val = ctx.read_sized_m(cart, addr);
        let new_val = self.instr_incany(ctx, old_val, is_inc);
        ctx.write_sized(cart, addr, new_val);
    }

    fn instr_lsrany(&mut self, ctx: &mut Context, val: TUnknown) -> TUnknown {
        self.modify(
            ctx,
            |v, p| {
                let (v, c) = v.ror(TBool::False);
                (v, v.set_nz(p).with_bits(C, c))
            },
            |v, p| {
                let (v, c) = v.ror(TBool::False);
                (v, v.set_nz(p).with_bits(C, c))
            },
            val,
        )
    }

    fn instr_lsrimm(&mut self, ctx: &mut Context) {
        let new = self.instr_lsrany(ctx, ctx.a_sized());
        ctx.a.write_sized(new);
    }

    fn instr_lsr(&mut self, cart: &Cart, ctx: &mut Context, addr: AddrModeRes) {
        let rhs = ctx.read_sized_m(cart, addr);
        let new = self.instr_lsrany(ctx, rhs);
        ctx.write_sized(cart, addr, new);
    }

    fn instr_aslany(&mut self, ctx: &mut Context, val: TUnknown) -> TUnknown {
        self.modify(
            ctx,
            |v, p| {
                let (v, c) = v.rol(TBool::False);
                (v, v.set_nz(p).with_bits(C, c))
            },
            |v, p| {
                let (v, c) = v.rol(TBool::False);
                (v, v.set_nz(p).with_bits(C, c))
            },
            val,
        )
    }

    fn instr_aslimm(&mut self, ctx: &mut Context) {
        let new = self.instr_aslany(ctx, ctx.a_sized());
        ctx.a.write_sized(new);
    }

    fn instr_asl(&mut self, cart: &Cart, ctx: &mut Context, addr: AddrModeRes) {
        let rhs = ctx.read_sized_m(cart, addr);
        let new = self.instr_aslany(ctx, rhs);
        ctx.write_sized(cart, addr, new);
    }

    fn instr_rolany(&mut self, ctx: &mut Context, val: TUnknown) -> TUnknown {
        self.modify(
            ctx,
            |v, p| {
                let (v, c) = v.rol(p.contains_any(C));
                (v, v.set_nz(p).with_bits(C, c))
            },
            |v, p| {
                let (v, c) = v.rol(p.contains_any(C));
                (v, v.set_nz(p).with_bits(C, c))
            },
            val,
        )
    }

    fn instr_rolimm(&mut self, ctx: &mut Context) {
        let new = self.instr_rolany(ctx, ctx.a_sized());
        ctx.a.write_sized(new);
    }

    fn instr_rol(&mut self, cart: &Cart, ctx: &mut Context, addr: AddrModeRes) {
        let rhs = ctx.read_sized_m(cart, addr);
        let new = self.instr_rolany(ctx, rhs);
        ctx.write_sized(cart, addr, new);
    }

    fn instr_rorany(&mut self, ctx: &mut Context, val: TUnknown) -> TUnknown {
        self.modify(
            ctx,
            |v, p| {
                let (v, c) = v.ror(p.contains_any(C));
                (v, v.set_nz(p).with_bits(C, c))
            },
            |v, p| {
                let (v, c) = v.ror(p.contains_any(C));
                (v, v.set_nz(p).with_bits(C, c))
            },
            val,
        )
    }

    fn instr_rorimm(&mut self, ctx: &mut Context) {
        let new = self.instr_rorany(ctx, ctx.a_sized());
        ctx.a.write_sized(new);
    }

    fn instr_ror(&mut self, cart: &Cart, ctx: &mut Context, addr: AddrModeRes) {
        let rhs = ctx.read_sized_m(cart, addr);
        let new = self.instr_rorany(ctx, rhs);
        ctx.write_sized(cart, addr, new);
    }

    fn instr_branch(&mut self, head: Head, p: u8, is_set: bool, label: Addr) {
        let cond = head.ctx.p.contains_any(p) ^ !is_set;
        if cond.is_true_or_unknown() {
            let mut new_ctx = head.ctx.clone();
            if is_set {
                new_ctx.p |= p;
            } else {
                new_ctx.p &= !p;
            }
            new_ctx.pc = label;
            self.heads.push(Head {
                call_stack: head.call_stack.clone(),
                ctx: new_ctx,
            });
        }
        if cond.is_false_or_unknown() {
            let mut new_ctx = head.ctx;
            if is_set {
                new_ctx.p &= !p;
            } else {
                new_ctx.p |= p;
            }
            self.heads.push(Head {
                call_stack: head.call_stack,
                ctx: new_ctx,
            });
        }
    }

    fn instr_lda(&mut self, cart: &Cart, ctx: &mut Context, addr: AddrModeRes) {
        let rhs = ctx.read_sized_m(cart, addr);
        ctx.a.write_sized(rhs);
        ctx.set_nzx(rhs);
    }

    fn instr_ldx(&mut self, cart: &Cart, ctx: &mut Context, addr: AddrModeRes) {
        let rhs = ctx.read_sized_x(cart, addr);
        ctx.x.write_sized(rhs);
        ctx.set_nzx(rhs);
    }

    fn instr_ldy(&mut self, cart: &Cart, ctx: &mut Context, addr: AddrModeRes) {
        let rhs = ctx.read_sized_x(cart, addr);
        ctx.y.write_sized(rhs);
        ctx.set_nzx(rhs);
    }

    fn instr_bit(&mut self, cart: &Cart, ctx: &mut Context, addr: AddrModeRes) {
        ctx.p = ctx.read_sized_m(cart, addr).map_same(
            |b| {
                ctx.p
                    .with_bits(Z, (ctx.a.into_byte() & b).is_zero())
                    .with_bits(N, b.msb())
                    .with_bits(V, b.extract_bit(6))
            },
            |b| {
                ctx.p
                    .with_bits(Z, (ctx.a & b).is_zero())
                    .with_bits(N, b.msb())
                    .with_bits(V, b.extract_bit(14))
            },
            |_, p1, p2| p1.either(p2),
        )
    }

    fn instr_andimm(&mut self, ctx: &mut Context, rhs: TUnknown) {
        let old_a = ctx.a;
        (ctx.a, ctx.p) = rhs.map_same(
            |b| {
                let r = ctx.a.into_byte() & b;
                (TU16::from_bytes([r, old_a.high()]), r.set_nz(ctx.p))
            },
            |b| {
                let r = ctx.a & b;
                (r, r.set_nz(ctx.p))
            },
            |_, (v8, p8), (v16, p16)| (v8.either(v16), p8.either(p16)),
        );
    }

    fn instr_and(&mut self, cart: &Cart, ctx: &mut Context, addr: AddrModeRes) {
        let rhs = ctx.read_sized_m(cart, addr);
        self.instr_andimm(ctx, rhs);
    }

    fn instr_oraimm(&mut self, ctx: &mut Context, rhs: TUnknown) {
        let old_a = ctx.a;
        (ctx.a, ctx.p) = rhs.map_same(
            |b| {
                let r = ctx.a.into_byte() | b;
                (TU16::from_bytes([r, old_a.high()]), r.set_nz(ctx.p))
            },
            |b| {
                let r = ctx.a | b;
                (r, r.set_nz(ctx.p))
            },
            |_, (v8, p8), (v16, p16)| (v8.either(v16), p8.either(p16)),
        );
    }

    fn instr_ora(&mut self, cart: &Cart, ctx: &mut Context, addr: AddrModeRes) {
        let rhs = ctx.read_sized_m(cart, addr);
        self.instr_oraimm(ctx, rhs);
    }

    fn instr_eorimm(&mut self, ctx: &mut Context, rhs: TUnknown) {
        let old_a = ctx.a;
        (ctx.a, ctx.p) = rhs.map_same(
            |b| {
                let r = ctx.a.into_byte() ^ b;
                (TU16::from_bytes([r, old_a.high()]), r.set_nz(ctx.p))
            },
            |b| {
                let r = ctx.a ^ b;
                (r, r.set_nz(ctx.p))
            },
            |_, (v8, p8), (v16, p16)| (v8.either(v16), p8.either(p16)),
        );
    }

    fn instr_eor(&mut self, cart: &Cart, ctx: &mut Context, addr: AddrModeRes) {
        let rhs = ctx.read_sized_m(cart, addr);
        self.instr_eorimm(ctx, rhs);
    }

    fn instr_blockmove(
        &mut self,
        cart: &Cart,
        ctx: &mut Context,
        dstbank: u8,
        srcbank: u8,
        is_neg: bool,
    ) {
        let delta = if is_neg { 1 } else { u8::MAX };
        loop {
            ctx.b = dstbank.into();
            let val = ctx
                .read8(cart, TU24::new(srcbank, ctx.x))
                .unwrap_or(TU8::UNKNOWN);
            ctx.write8(cart, TU24::new(dstbank, ctx.y), val);
            for reg in [&mut ctx.x, &mut ctx.y] {
                let val = reg.into_byte().adc(delta, false).0;
                reg.write_low(val);
            }
            let old_a = ctx.a;
            ctx.a = ctx.a.adc(u16::MAX, false).0;
            match old_a.is_zero() {
                TBool::False => continue,
                // in case of unknown just abort
                TBool::True | TBool::Unknown => break,
            }
        }
    }

    pub fn disassemble_with_head(&mut self, cart: &Cart, head: Head) -> Option<Instruction> {
        let Head {
            mut call_stack,
            mut ctx,
        } = head;
        let instr_pc = ctx.pc;
        let (mf, xf) = (ctx.mf(), ctx.xf());
        let instr = Instruction::from_fetcher(
            || {
                let addr = ctx.pc.add16_repl(1);
                ctx.read8(cart, addr).and_then(|e| e.get())
            },
            mf.get(),
            xf.get(),
        )?;

        match xf {
            TBool::True => {
                ctx.x &= 0xff;
                ctx.y &= 0xff;
            }
            TBool::False => (),
            TBool::Unknown => {
                ctx.x = ctx.x.either(ctx.x & 0xff);
                ctx.y = ctx.y.either(ctx.y & 0xff);
            }
        }

        // println!("{instr_pc} | {instr:x?}");

        #[allow(unused_variables)]
        match &instr {
            Instruction::Brk(_) => todo!(),
            Instruction::OraDxi(dxi) => todo!(),
            Instruction::Cop(_) => return Some(instr),
            Instruction::OraS(s) => todo!(),
            Instruction::TsbD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_tsb(&mut ctx, cart, addr, true);
            }
            Instruction::OraD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_ora(cart, &mut ctx, addr);
            }
            Instruction::AslD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_asl(cart, &mut ctx, addr);
            }
            Instruction::OraDil(dil) => {
                let addr = ctx.resolve_dil(cart, dil);
                self.instr_ora(cart, &mut ctx, addr);
            }
            Instruction::Php => ctx.stack.push(ctx.p),
            Instruction::OraI(i) => self.instr_oraimm(&mut ctx, (*i).into()),
            Instruction::AslAc => self.instr_aslimm(&mut ctx),
            Instruction::Phd => todo!(),
            Instruction::TsbA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_tsb(&mut ctx, cart, addr, true);
            }
            Instruction::OraA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_ora(cart, &mut ctx, addr);
            }
            Instruction::AslA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_asl(cart, &mut ctx, addr);
            }
            Instruction::OraAl(al) => {
                let addr = ctx.resolve_al(cart, al);
                self.instr_ora(cart, &mut ctx, addr);
            }
            Instruction::Bpl(label) => {
                self.instr_branch(Head { ctx, call_stack }, N, false, label.take(instr_pc));
                return Some(instr);
            }
            Instruction::OraDiy(diy) => {
                let addr = ctx.resolve_diy(cart, diy);
                self.instr_ora(cart, &mut ctx, addr);
            }
            Instruction::OraDi(di) => {
                let addr = ctx.resolve_di(cart, di);
                self.instr_ora(cart, &mut ctx, addr);
            }
            Instruction::OraSiy(siy) => todo!(),
            Instruction::TrbD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_tsb(&mut ctx, cart, addr, false);
            }
            Instruction::OraDx(dx) => {
                let addr = ctx.resolve_dx(cart, dx);
                self.instr_ora(cart, &mut ctx, addr);
            }
            Instruction::AslDx(dx) => {
                let addr = ctx.resolve_dx(cart, dx);
                self.instr_asl(cart, &mut ctx, addr);
            }
            Instruction::OraDily(dily) => {
                let addr = ctx.resolve_dily(cart, dily);
                self.instr_ora(cart, &mut ctx, addr);
            }
            Instruction::Clc => ctx.p &= !C,
            Instruction::OraAy(ay) => {
                let addr = ctx.resolve_ay(cart, ay);
                self.instr_ora(cart, &mut ctx, addr);
            }
            Instruction::IncAc => self.instr_incimm(&mut ctx, |c| &mut c.a, mf, true),
            Instruction::Tcs => (),
            Instruction::TrbA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_tsb(&mut ctx, cart, addr, false);
            }
            Instruction::OraAx(ax) => {
                let addr = ctx.resolve_ax(cart, ax);
                self.instr_ora(cart, &mut ctx, addr);
            }
            Instruction::AslAx(ax) => {
                let addr = ctx.resolve_ax(cart, ax);
                self.instr_asl(cart, &mut ctx, addr);
            }
            Instruction::OraAlx(alx) => {
                let addr = ctx.resolve_alx(cart, alx);
                self.instr_ora(cart, &mut ctx, addr);
            }
            Instruction::Jsr(dst) => {
                let old_pc = ctx.pc;
                if ctx.call_subroutine(cart, Addr::new(ctx.pc.bank, dst.0)) {
                    let offset = ctx.stack.items.len() as u16;
                    ctx.stack.push16(old_pc.addr.wrapping_sub(1).into());
                    if call_stack.push_short(instr_pc, offset) {
                        // recursion
                        return Some(instr);
                    }
                }
            }
            Instruction::AndDxi(dxi) => todo!(),
            Instruction::Jsl(dst) => {
                let old_pc = ctx.pc;
                if ctx.call_subroutine(cart, *dst) {
                    let offset = ctx.stack.items.len() as u16;
                    ctx.stack.push(old_pc.bank.into());
                    ctx.stack.push16(old_pc.addr.wrapping_sub(1).into());
                    if call_stack.push_long(instr_pc, offset) {
                        // recursion
                        return Some(instr);
                    }
                }
            }
            Instruction::AndS(s) => todo!(),
            Instruction::BitD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_bit(cart, &mut ctx, addr);
            }
            Instruction::AndD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_and(cart, &mut ctx, addr);
            }
            Instruction::RolD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_rol(cart, &mut ctx, addr);
            }
            Instruction::AndDil(dil) => {
                let addr = ctx.resolve_dil(cart, dil);
                self.instr_and(cart, &mut ctx, addr);
            }
            Instruction::Plp => ctx.p = ctx.stack.pop(),
            Instruction::AndI(i) => self.instr_andimm(&mut ctx, (*i).into()),
            Instruction::RolAc => self.instr_rolimm(&mut ctx),
            Instruction::Pld => todo!(),
            Instruction::BitA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_bit(cart, &mut ctx, addr);
            }
            Instruction::AndA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_and(cart, &mut ctx, addr);
            }
            Instruction::RolA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_rol(cart, &mut ctx, addr);
            }
            Instruction::AndAl(al) => {
                let addr = ctx.resolve_al(cart, al);
                self.instr_and(cart, &mut ctx, addr);
            }
            Instruction::Bmi(label) => {
                self.instr_branch(Head { ctx, call_stack }, N, true, label.take(instr_pc));
                return Some(instr);
            }
            Instruction::AndDiy(diy) => {
                let addr = ctx.resolve_diy(cart, diy);
                self.instr_and(cart, &mut ctx, addr);
            }
            Instruction::AndDi(di) => {
                let addr = ctx.resolve_di(cart, di);
                self.instr_and(cart, &mut ctx, addr);
            }
            Instruction::AndSiy(siy) => todo!(),
            Instruction::BitDx(dx) => {
                let addr = ctx.resolve_dx(cart, dx);
                self.instr_bit(cart, &mut ctx, addr);
            }
            Instruction::AndDx(dx) => {
                let addr = ctx.resolve_dx(cart, dx);
                self.instr_and(cart, &mut ctx, addr);
            }
            Instruction::RolDx(dx) => {
                let addr = ctx.resolve_dx(cart, dx);
                self.instr_rol(cart, &mut ctx, addr);
            }
            Instruction::AndDily(dily) => {
                let addr = ctx.resolve_dily(cart, dily);
                self.instr_and(cart, &mut ctx, addr);
            }
            Instruction::Sec => ctx.p |= C,
            Instruction::AndAy(ay) => {
                let addr = ctx.resolve_ay(cart, ay);
                self.instr_and(cart, &mut ctx, addr);
            }
            Instruction::DecAc => self.instr_incimm(&mut ctx, |c| &mut c.a, mf, false),
            Instruction::Tsc => todo!(),
            Instruction::BitAx(ax) => {
                let addr = ctx.resolve_ax(cart, ax);
                self.instr_bit(cart, &mut ctx, addr);
            }
            Instruction::AndAx(ax) => {
                let addr = ctx.resolve_ax(cart, ax);
                self.instr_and(cart, &mut ctx, addr);
            }
            Instruction::RolAx(ax) => {
                let addr = ctx.resolve_ax(cart, ax);
                self.instr_rol(cart, &mut ctx, addr);
            }
            Instruction::AndAlx(alx) => {
                let addr = ctx.resolve_alx(cart, alx);
                self.instr_and(cart, &mut ctx, addr);
            }
            Instruction::Rti => return Some(instr),
            Instruction::EorDxi(dxi) => todo!(),
            Instruction::Wdm(_) => todo!(),
            Instruction::EorS(s) => todo!(),
            Instruction::Mvp(dst, src) => self.instr_blockmove(cart, &mut ctx, *dst, *src, false),
            Instruction::EorD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_eor(cart, &mut ctx, addr);
            }
            Instruction::LsrD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_lsr(cart, &mut ctx, addr);
            }
            Instruction::EorDil(dil) => {
                let addr = ctx.resolve_dil(cart, dil);
                self.instr_eor(cart, &mut ctx, addr);
            }
            Instruction::Pha => ctx.stack.push_unknown(ctx.a_sized()),
            Instruction::EorI(i) => self.instr_eorimm(&mut ctx, TUnknown::from(*i)),
            Instruction::LsrAc => self.instr_lsrimm(&mut ctx),
            Instruction::Phk => ctx.stack.push(ctx.pc.bank.into()),
            Instruction::Jmp(dst) => ctx.pc.addr = dst.0,
            Instruction::EorA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_eor(cart, &mut ctx, addr);
            }
            Instruction::LsrA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_lsr(cart, &mut ctx, addr);
            }
            Instruction::EorAl(al) => {
                let addr = ctx.resolve_al(cart, al);
                self.instr_eor(cart, &mut ctx, addr);
            }
            Instruction::Bvc(label) => {
                self.instr_branch(Head { ctx, call_stack }, V, false, label.take(instr_pc));
                return Some(instr);
            }
            Instruction::EorDiy(diy) => {
                let addr = ctx.resolve_diy(cart, diy);
                self.instr_eor(cart, &mut ctx, addr);
            }
            Instruction::EorDi(di) => {
                let addr = ctx.resolve_di(cart, di);
                self.instr_eor(cart, &mut ctx, addr);
            }
            Instruction::EorSiy(siy) => todo!(),
            Instruction::Mvn(dst, src) => self.instr_blockmove(cart, &mut ctx, *dst, *src, true),
            Instruction::EorDx(dx) => {
                let addr = ctx.resolve_dx(cart, dx);
                self.instr_eor(cart, &mut ctx, addr);
            }
            Instruction::LsrDx(dx) => {
                let addr = ctx.resolve_dx(cart, dx);
                self.instr_lsr(cart, &mut ctx, addr);
            }
            Instruction::EorDily(dily) => {
                let addr = ctx.resolve_dily(cart, dily);
                self.instr_eor(cart, &mut ctx, addr);
            }
            Instruction::Cli => ctx.p &= !I,
            Instruction::EorAy(ay) => {
                let addr = ctx.resolve_ay(cart, ay);
                self.instr_eor(cart, &mut ctx, addr);
            }
            Instruction::Phy => ctx.stack.push_unknown(ctx.y_sized()),
            Instruction::Tcd => {
                ctx.d = ctx.a;
                ctx.set_nz16(ctx.a);
            }
            Instruction::Jml(addr) => ctx.pc = *addr,
            Instruction::EorAx(ax) => {
                let addr = ctx.resolve_ax(cart, ax);
                self.instr_eor(cart, &mut ctx, addr);
            }
            Instruction::LsrAx(ax) => {
                let addr = ctx.resolve_ax(cart, ax);
                self.instr_lsr(cart, &mut ctx, addr);
            }
            Instruction::EorAlx(alx) => {
                let addr = ctx.resolve_alx(cart, alx);
                self.instr_eor(cart, &mut ctx, addr);
            }
            Instruction::Rts => {
                self.sync_callstack(&ctx, &mut call_stack);
                if let Some(new_pc) = ctx.stack.pop16().get() {
                    ctx.pc.addr = new_pc.wrapping_add(1);
                    if call_stack
                        .pop()
                        .is_some_and(|item| item.return_addr() != ctx.pc)
                    {
                        // something is broken, better stop disassembling from here
                        return Some(instr);
                    }
                } else if let Some(item) = call_stack.pop() {
                    // fall back to our call stack implementation if the system stack got corrupted
                    ctx.pc = item.return_addr();
                } else {
                    return Some(instr);
                }
            }
            Instruction::AdcDxi(dxi) => todo!(),
            Instruction::Per(label) => {
                ctx.stack.push16(label.take(instr_pc).addr.into());
            }
            Instruction::AdcS(s) => todo!(),
            Instruction::StzD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_stz(cart, &mut ctx, addr);
            }
            Instruction::AdcD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_adc(cart, &mut ctx, addr, false);
            }
            Instruction::RorD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_ror(cart, &mut ctx, addr);
            }
            Instruction::AdcDil(dil) => {
                let addr = ctx.resolve_dil(cart, dil);
                self.instr_adc(cart, &mut ctx, addr, false);
            }
            Instruction::Pla => {
                ctx.a.write_sized(ctx.stack.pop_unknown(mf));
                ctx.set_nzx(ctx.a_sized());
            }
            Instruction::AdcI(i) => self.instr_adcimm(&mut ctx, (*i).into(), false),
            Instruction::RorAc => self.instr_rorimm(&mut ctx),
            Instruction::Rtl => {
                self.sync_callstack(&ctx, &mut call_stack);
                if let Some(new_pc) = ctx.stack.pop24().get() {
                    ctx.pc = new_pc.add16(1);
                    if call_stack
                        .pop()
                        .is_some_and(|item| item.return_addr() != ctx.pc)
                    {
                        // something is broken, better stop disassembling from here
                        return Some(instr);
                    }
                } else if let Some(item) = call_stack.pop() {
                    // fall back to our call stack implementation if the system stack got corrupted
                    ctx.pc = item.return_addr();
                } else {
                    return Some(instr);
                }
            }
            Instruction::Jmpi(_) => todo!(),
            Instruction::AdcA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_adc(cart, &mut ctx, addr, false);
            }
            Instruction::RorA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_ror(cart, &mut ctx, addr);
            }
            Instruction::AdcAl(al) => {
                let addr = ctx.resolve_al(cart, al);
                self.instr_adc(cart, &mut ctx, addr, false);
            }
            Instruction::Bvs(label) => {
                self.instr_branch(Head { ctx, call_stack }, V, true, label.take(instr_pc));
                return Some(instr);
            }
            Instruction::AdcDiy(diy) => {
                let addr = ctx.resolve_diy(cart, diy);
                self.instr_adc(cart, &mut ctx, addr, false);
            }
            Instruction::AdcDi(di) => {
                let addr = ctx.resolve_di(cart, di);
                self.instr_adc(cart, &mut ctx, addr, false);
            }
            Instruction::AdcSiy(siy) => todo!(),
            Instruction::StzDx(dx) => {
                let addr = ctx.resolve_dx(cart, dx);
                self.instr_stz(cart, &mut ctx, addr);
            }
            Instruction::AdcDx(dx) => {
                let addr = ctx.resolve_dx(cart, dx);
                self.instr_adc(cart, &mut ctx, addr, false);
            }
            Instruction::RorDx(dx) => {
                let addr = ctx.resolve_dx(cart, dx);
                self.instr_ror(cart, &mut ctx, addr);
            }
            Instruction::AdcDily(dily) => {
                let addr = ctx.resolve_dily(cart, dily);
                self.instr_adc(cart, &mut ctx, addr, false);
            }
            Instruction::Sei => ctx.p |= I,
            Instruction::AdcAy(ay) => {
                let addr = ctx.resolve_ay(cart, ay);
                self.instr_adc(cart, &mut ctx, addr, false);
            }
            Instruction::Ply => {
                ctx.y.write_sized(ctx.stack.pop_unknown(xf));
                ctx.set_nzx(ctx.y_sized());
            }
            Instruction::Tdc => {
                ctx.a = ctx.d;
                ctx.set_nz16(ctx.a);
            }
            Instruction::Jmpxi(_) => todo!(),
            Instruction::AdcAx(ax) => {
                let addr = ctx.resolve_ax(cart, ax);
                self.instr_adc(cart, &mut ctx, addr, false);
            }
            Instruction::RorAx(ax) => {
                let addr = ctx.resolve_ax(cart, ax);
                self.instr_ror(cart, &mut ctx, addr);
            }
            Instruction::AdcAlx(alx) => {
                let addr = ctx.resolve_alx(cart, alx);
                self.instr_adc(cart, &mut ctx, addr, false);
            }
            Instruction::Bra(label) => ctx.pc = label.take(instr_pc),
            Instruction::StaDxi(dxi) => todo!(),
            Instruction::Brl(label) => ctx.pc = label.take(instr_pc),
            Instruction::StaS(s) => todo!(),
            Instruction::StyD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_sty(cart, &mut ctx, addr);
            }
            Instruction::StaD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_sta(cart, &mut ctx, addr);
            }
            Instruction::StxD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_stx(cart, &mut ctx, addr);
            }
            Instruction::StaDil(dil) => {
                let addr = ctx.resolve_dil(cart, dil);
                self.instr_sta(cart, &mut ctx, addr);
            }
            Instruction::Dey => self.instr_incimm(&mut ctx, |c| &mut c.y, xf, false),
            Instruction::BitI(i) => {
                ctx.p = ctx.p.with_bits(
                    Z,
                    match i {
                        am::I::U8(v) => (ctx.a.into_byte() & *v).is_zero(),
                        am::I::U16(v) => (ctx.a & *v).is_zero(),
                    },
                )
            }
            Instruction::Txa => {
                ctx.a.write_with_size(ctx.x, mf);
                ctx.set_nzx(ctx.a_sized());
            }
            Instruction::Phb => ctx.stack.push(ctx.b),
            Instruction::StyA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_sty(cart, &mut ctx, addr)
            }
            Instruction::StaA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_sta(cart, &mut ctx, addr)
            }
            Instruction::StxA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_stx(cart, &mut ctx, addr)
            }
            Instruction::StaAl(al) => {
                let addr = ctx.resolve_al(cart, al);
                self.instr_sta(cart, &mut ctx, addr)
            }
            Instruction::Bcc(label) => {
                self.instr_branch(Head { ctx, call_stack }, C, false, label.take(instr_pc));
                return Some(instr);
            }
            Instruction::StaDiy(diy) => {
                let addr = ctx.resolve_diy(cart, diy);
                self.instr_sta(cart, &mut ctx, addr);
            }
            Instruction::StaDi(di) => {
                let addr = ctx.resolve_di(cart, di);
                self.instr_sta(cart, &mut ctx, addr);
            }
            Instruction::StaSiy(siy) => todo!(),
            Instruction::StyDx(dx) => {
                let addr = ctx.resolve_dx(cart, dx);
                self.instr_sty(cart, &mut ctx, addr);
            }
            Instruction::StaDx(dx) => {
                let addr = ctx.resolve_dx(cart, dx);
                self.instr_sta(cart, &mut ctx, addr);
            }
            Instruction::StxDy(dy) => {
                let addr = ctx.resolve_dy(cart, dy);
                self.instr_stx(cart, &mut ctx, addr);
            }
            Instruction::StaDily(dily) => {
                let addr = ctx.resolve_dily(cart, dily);
                self.instr_sta(cart, &mut ctx, addr);
            }
            Instruction::Tya => {
                ctx.a.write_with_size(ctx.y, mf);
                ctx.set_nzx(ctx.a_sized());
            }
            Instruction::StaAy(ay) => {
                let addr = ctx.resolve_ay(cart, ay);
                self.instr_sta(cart, &mut ctx, addr);
            }
            Instruction::Txs => todo!(),
            Instruction::Txy => {
                ctx.y.write_with_size(ctx.x, xf);
                ctx.set_nzx(ctx.y_sized());
            }
            Instruction::StzA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_stz(cart, &mut ctx, addr)
            }
            Instruction::StaAx(ax) => {
                let addr = ctx.resolve_ax(cart, ax);
                self.instr_sta(cart, &mut ctx, addr);
            }
            Instruction::StzAx(ax) => {
                let addr = ctx.resolve_ax(cart, ax);
                self.instr_stz(cart, &mut ctx, addr);
            }
            Instruction::StaAlx(alx) => {
                let addr = ctx.resolve_alx(cart, alx);
                self.instr_sta(cart, &mut ctx, addr)
            }
            Instruction::LdyI(i) => match *i {
                am::I::U8(val) => {
                    ctx.y.write_low(val.into());
                    ctx.set_nz8(val);
                }
                am::I::U16(val) => {
                    ctx.y = val.into();
                    ctx.set_nz16(val);
                }
            },
            Instruction::LdaDxi(dxi) => todo!(),
            Instruction::LdxI(i) => match *i {
                am::I::U8(val) => {
                    ctx.x.write_low(val.into());
                    ctx.set_nz8(val);
                }
                am::I::U16(val) => {
                    ctx.x = val.into();
                    ctx.set_nz16(val);
                }
            },
            Instruction::LdaS(s) => todo!(),
            Instruction::LdyD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_ldy(cart, &mut ctx, addr);
            }
            Instruction::LdaD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_lda(cart, &mut ctx, addr);
            }
            Instruction::LdxD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_ldx(cart, &mut ctx, addr);
            }
            Instruction::LdaDil(dil) => {
                let addr = ctx.resolve_dil(cart, dil);
                self.instr_lda(cart, &mut ctx, addr);
            }
            Instruction::Tay => {
                ctx.y.write_with_size(ctx.a, xf);
                ctx.set_nzx(ctx.y_sized());
            }
            Instruction::LdaI(i) => match *i {
                am::I::U8(val) => {
                    ctx.a.write_low(val.into());
                    ctx.set_nz8(val);
                }
                am::I::U16(val) => {
                    ctx.a = val.into();
                    ctx.set_nz16(val);
                }
            },
            Instruction::Tax => {
                ctx.x.write_with_size(ctx.a, xf);
                ctx.set_nzx(ctx.x_sized());
            }
            Instruction::Plb => {
                ctx.b = ctx.stack.pop();
                ctx.set_nz8(ctx.b);
            }
            Instruction::LdyA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_ldy(cart, &mut ctx, addr);
            }
            Instruction::LdaA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_lda(cart, &mut ctx, addr);
            }
            Instruction::LdxA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_ldx(cart, &mut ctx, addr);
            }
            Instruction::LdaAl(al) => {
                let addr = ctx.resolve_al(cart, al);
                self.instr_lda(cart, &mut ctx, addr);
            }
            Instruction::Bcs(label) => {
                self.instr_branch(Head { ctx, call_stack }, C, true, label.take(instr_pc));
                return Some(instr);
            }
            Instruction::LdaDiy(diy) => {
                let addr = ctx.resolve_diy(cart, diy);
                self.instr_lda(cart, &mut ctx, addr);
            }
            Instruction::LdaDi(di) => {
                let addr = ctx.resolve_di(cart, di);
                self.instr_lda(cart, &mut ctx, addr);
            }
            Instruction::LdaSiy(siy) => todo!(),
            Instruction::LdyDx(dx) => {
                let addr = ctx.resolve_dx(cart, dx);
                self.instr_ldy(cart, &mut ctx, addr);
            }
            Instruction::LdaDx(dx) => {
                let addr = ctx.resolve_dx(cart, dx);
                self.instr_lda(cart, &mut ctx, addr);
            }
            Instruction::LdxDy(dy) => {
                let addr = ctx.resolve_dy(cart, dy);
                self.instr_ldx(cart, &mut ctx, addr);
            }
            Instruction::LdaDily(dily) => {
                let addr = ctx.resolve_dily(cart, dily);
                self.instr_lda(cart, &mut ctx, addr);
            }
            Instruction::Clv => ctx.p &= !V,
            Instruction::LdaAy(ay) => {
                let addr = ctx.resolve_ay(cart, ay);
                self.instr_lda(cart, &mut ctx, addr);
            }
            Instruction::Tsx => todo!(),
            Instruction::Tyx => {
                ctx.x.write_with_size(ctx.y, xf);
                ctx.set_nzx(ctx.x_sized());
            }
            Instruction::LdyAx(ax) => {
                let addr = ctx.resolve_ax(cart, ax);
                self.instr_ldy(cart, &mut ctx, addr);
            }
            Instruction::LdaAx(ax) => {
                let addr = ctx.resolve_ax(cart, ax);
                self.instr_lda(cart, &mut ctx, addr);
            }
            Instruction::LdxAy(ay) => {
                let addr = ctx.resolve_ay(cart, ay);
                self.instr_ldx(cart, &mut ctx, addr);
            }
            Instruction::LdaAlx(alx) => {
                let addr = ctx.resolve_alx(cart, alx);
                self.instr_lda(cart, &mut ctx, addr);
            }
            Instruction::CpyI(i) => {
                let y = ctx.y_sized();
                self.instr_cmpimm(&mut ctx, y, (*i).into())
            }
            Instruction::CmpDxi(dxi) => todo!(),
            Instruction::Rep(p) => ctx.p &= !p.0,
            Instruction::CmpS(s) => todo!(),
            Instruction::CpyD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_cpy(cart, &mut ctx, addr);
            }
            Instruction::CmpD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_cmp(cart, &mut ctx, addr);
            }
            Instruction::DecD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_inc(&mut ctx, cart, addr, false);
            }
            Instruction::CmpDil(dil) => {
                let addr = ctx.resolve_dil(cart, dil);
                self.instr_cmp(cart, &mut ctx, addr);
            }
            Instruction::Iny => self.instr_incimm(&mut ctx, |c| &mut c.y, xf, true),
            Instruction::CmpI(i) => {
                let a = ctx.a_sized();
                self.instr_cmpimm(&mut ctx, a, (*i).into())
            }
            Instruction::Dex => self.instr_incimm(&mut ctx, |c| &mut c.x, xf, false),
            Instruction::Wai => todo!(),
            Instruction::CpyA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_cpy(cart, &mut ctx, addr);
            }
            Instruction::CmpA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_cmp(cart, &mut ctx, addr);
            }
            Instruction::DecA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_inc(&mut ctx, cart, addr, false);
            }
            Instruction::CmpAl(al) => {
                let addr = ctx.resolve_al(cart, al);
                self.instr_cmp(cart, &mut ctx, addr);
            }
            Instruction::Bne(label) => {
                self.instr_branch(Head { ctx, call_stack }, Z, false, label.take(instr_pc));
                return Some(instr);
            }
            Instruction::CmpDiy(diy) => {
                let addr = ctx.resolve_diy(cart, diy);
                self.instr_cmp(cart, &mut ctx, addr);
            }
            Instruction::CmpDi(di) => {
                let addr = ctx.resolve_di(cart, di);
                self.instr_cmp(cart, &mut ctx, addr);
            }
            Instruction::CmpSiy(siy) => todo!(),
            Instruction::Pei(_) => todo!(),
            Instruction::CmpDx(dx) => {
                let addr = ctx.resolve_dx(cart, dx);
                self.instr_cmp(cart, &mut ctx, addr);
            }
            Instruction::DecDx(dx) => {
                let addr = ctx.resolve_dx(cart, dx);
                self.instr_inc(&mut ctx, cart, addr, false);
            }
            Instruction::CmpDily(dily) => {
                let addr = ctx.resolve_dily(cart, dily);
                self.instr_cmp(cart, &mut ctx, addr);
            }
            Instruction::Cld => ctx.p &= !D,
            Instruction::CmpAy(ay) => {
                let addr = ctx.resolve_ay(cart, ay);
                self.instr_cmp(cart, &mut ctx, addr);
            }
            Instruction::Phx => ctx.stack.push_unknown(ctx.x_sized()),
            Instruction::Stp => todo!(),
            Instruction::Jmli(label) => {
                let dst = ctx.resolve_jmli(cart, label);
                // Assume that every `JML [$xyzw]` instruction is part
                // of a jump table trampoline.
                if let Some(byte) = cart.read_rom(instr_pc.add16(0xffff)) {
                    let is24 = byte == 5;
                    let trampoline_offset = if is24 { 0xffdf } else { 0xffe8 };
                    let ann = self
                        .get_annotation(instr_pc.add16(trampoline_offset), &call_stack)
                        .and_then(|ann| ann.pre.stack.peek24(0).get().map(|a| (ann, a.add16(1))));
                    if let Some((ann, table_start)) = ann {
                        let idx = ann.pre.a.into_byte().get().unwrap_or(0);
                        let off = u16::from(idx) * if is24 { 3 } else { 2 };
                        let table =
                            self.jump_tables
                                .entry(table_start)
                                .or_insert_with(|| JumpTable {
                                    known_entry_offsets: vec![],
                                    ty: if is24 {
                                        JumpTableType::Addr24
                                    } else {
                                        JumpTableType::Addr16
                                    },
                                });
                        if !table.known_entry_offsets.contains(&off) {
                            table.known_entry_offsets.push(off);
                        }
                    }
                }
                call_stack.pop();
                if let Some(item) = call_stack.items.last().copied() {
                    let mut call_stack = call_stack.clone();
                    let mut stack = ctx.stack.clone();
                    call_stack.pop();
                    if item.is_long {
                        stack.pop24();
                    } else {
                        stack.pop16();
                    };
                    let ret_addr = item.return_addr();
                    let mut ctx = Context::unknown(ret_addr);
                    // for now we assume all registers to be in 8-bit mode
                    ctx.p |= M | X;
                    ctx.stack = stack;
                    self.heads.push(Head { ctx, call_stack });
                }
                if let Some(dst) = dst.get() {
                    ctx.pc = dst;
                } else {
                    return Some(instr);
                }
            }
            Instruction::CmpAx(ax) => {
                let addr = ctx.resolve_ax(cart, ax);
                self.instr_cmp(cart, &mut ctx, addr);
            }
            Instruction::DecAx(ax) => {
                let addr = ctx.resolve_ax(cart, ax);
                self.instr_inc(&mut ctx, cart, addr, false);
            }
            Instruction::CmpAlx(alx) => {
                let addr = ctx.resolve_alx(cart, alx);
                self.instr_cmp(cart, &mut ctx, addr);
            }
            Instruction::CpxI(i) => {
                let x = ctx.x_sized();
                self.instr_cmpimm(&mut ctx, x, (*i).into())
            }
            Instruction::SbcDxi(dxi) => todo!(),
            Instruction::Sep(p) => ctx.p |= p.0,
            Instruction::SbcS(s) => todo!(),
            Instruction::CpxD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_cpx(cart, &mut ctx, addr);
            }
            Instruction::SbcD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_adc(cart, &mut ctx, addr, true);
            }
            Instruction::IncD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_inc(&mut ctx, cart, addr, true);
            }
            Instruction::SbcDil(dil) => {
                let addr = ctx.resolve_dil(cart, dil);
                self.instr_adc(cart, &mut ctx, addr, true);
            }
            Instruction::Inx => self.instr_incimm(&mut ctx, |c| &mut c.x, xf, true),
            Instruction::SbcI(i) => self.instr_adcimm(&mut ctx, (*i).into(), true),
            Instruction::Nop => (),
            Instruction::Xba => {
                let [lo, hi] = ctx.a.to_bytes();
                ctx.a = TU16::from_bytes([hi, lo]);
                ctx.set_nz8(hi);
            }
            Instruction::CpxA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_cpx(cart, &mut ctx, addr);
            }
            Instruction::SbcA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_adc(cart, &mut ctx, addr, true);
            }
            Instruction::IncA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_inc(&mut ctx, cart, addr, true);
            }
            Instruction::SbcAl(al) => {
                let addr = ctx.resolve_al(cart, al);
                self.instr_adc(cart, &mut ctx, addr, true);
            }
            Instruction::Beq(label) => {
                self.instr_branch(Head { ctx, call_stack }, Z, true, label.take(instr_pc));
                return Some(instr);
            }
            Instruction::SbcDiy(diy) => {
                let addr = ctx.resolve_diy(cart, diy);
                self.instr_adc(cart, &mut ctx, addr, true);
            }
            Instruction::SbcDi(di) => {
                let addr = ctx.resolve_di(cart, di);
                self.instr_adc(cart, &mut ctx, addr, true);
            }
            Instruction::SbcSiy(siy) => todo!(),
            Instruction::Pea(_) => todo!(),
            Instruction::SbcDx(dx) => {
                let addr = ctx.resolve_dx(cart, dx);
                self.instr_adc(cart, &mut ctx, addr, true);
            }
            Instruction::IncDx(dx) => {
                let addr = ctx.resolve_dx(cart, dx);
                self.instr_inc(&mut ctx, cart, addr, true);
            }
            Instruction::SbcDily(dily) => {
                let addr = ctx.resolve_dily(cart, dily);
                self.instr_adc(cart, &mut ctx, addr, true);
            }
            Instruction::Sed => ctx.p |= D,
            Instruction::SbcAy(ay) => {
                let addr = ctx.resolve_ay(cart, ay);
                self.instr_adc(cart, &mut ctx, addr, true);
            }
            Instruction::Plx => {
                ctx.x.write_sized(ctx.stack.pop_unknown(xf));
                ctx.set_nzx(ctx.x_sized());
            }
            // just ignore xce. We normally operate in native mode
            Instruction::Xce => (),
            Instruction::Jsrxi(_) => todo!(),
            Instruction::SbcAx(ax) => {
                let addr = ctx.resolve_ax(cart, ax);
                self.instr_adc(cart, &mut ctx, addr, true);
            }
            Instruction::IncAx(ax) => {
                let addr = ctx.resolve_ax(cart, ax);
                self.instr_inc(&mut ctx, cart, addr, true);
            }
            Instruction::SbcAlx(alx) => {
                let addr = ctx.resolve_alx(cart, alx);
                self.instr_adc(cart, &mut ctx, addr, true);
            }
        }
        self.heads.push(Head { ctx, call_stack });
        Some(instr)
    }
}

impl Default for Disassembler {
    fn default() -> Self {
        Self::new()
    }
}
