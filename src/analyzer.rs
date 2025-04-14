use std::collections::{BTreeMap, HashMap, HashSet};

use crate::{
    addr::Addr,
    addr_space::{CartMemoryLocation, MemoryLocation, SystemMemoryLocation},
    cart::Cart,
    instruction::{
        Instruction,
        am::{self, AddrModeRes},
    },
    pf::*,
    tvl::{TBool, TU8, TU16, TU24, TUnknown},
};

#[derive(Debug, Clone)]
pub struct Stack {
    pub items: Vec<TU8>,
}

impl Default for Stack {
    fn default() -> Self {
        Self { items: vec![] }
    }
}

impl Stack {
    pub fn unify(&mut self, rhs: &Self) {
        if self.items.len() <= rhs.items.len() {
            for (i, j) in self.items.iter_mut().zip(&rhs.items) {
                *i = i.either(*j)
            }
        } else {
            let mut newslf = rhs.clone();
            for (i, j) in newslf.items.iter_mut().zip(&self.items) {
                *i = i.either(*j)
            }
            *self = newslf
        }
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
    pub map: HashMap<MemoryLocation, TU8>,
    pub stack: Stack,
}

impl Context {
    pub fn read8(&self, cart: &Cart, addr: impl Into<TU24>) -> Option<TU8> {
        let addr = addr.into();
        let key = cart.map_full(addr.get()?);
        match &key {
            MemoryLocation::System(SystemMemoryLocation::Wram(_))
            | MemoryLocation::Cart(CartMemoryLocation::Sram(_)) => self.map.get(&key).copied(),
            MemoryLocation::Cart(CartMemoryLocation::Rom(off)) => Some(cart.rom.read(*off).into()),
            _ => None,
        }
    }

    pub fn write8(&mut self, cart: &Cart, addr: impl Into<TU24>, val: TU8) -> Option<()> {
        let addr = addr.into();
        let key = cart.map_full(addr.get()?);
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
        let a16 = self.read16(cart, addr)?;
        addr.incr();
        let bank = self.read8(cart, addr)?;
        Some(TU24::new(bank, a16))
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

    pub fn resolve_ax(&self, _cart: &Cart, ax: &am::Ax) -> AddrModeRes {
        AddrModeRes {
            is24: true,
            addr: TU24::new(self.b, ax.0).add24(self.x),
        }
    }

    pub fn resolve_ay(&self, _cart: &Cart, ay: &am::Ay) -> AddrModeRes {
        AddrModeRes {
            is24: true,
            addr: TU24::new(self.b, ay.0).add24(self.y),
        }
    }

    pub fn resolve_al(&self, _cart: &Cart, al: &am::Al) -> AddrModeRes {
        AddrModeRes {
            is24: true,
            addr: al.0.into(),
        }
    }

    pub fn resolve_alx(&self, _cart: &Cart, alx: &am::Alx) -> AddrModeRes {
        AddrModeRes {
            is24: true,
            addr: TU24::from(alx.0).add24(self.x),
        }
    }

    pub fn resolve_d(&self, _cart: &Cart, d: &am::D) -> AddrModeRes {
        AddrModeRes {
            is24: false,
            addr: TU24::new(0, self.d.adc(u16::from(d.0), false).0),
        }
    }

    pub fn resolve_dx(&self, _cart: &Cart, dx: &am::Dx) -> AddrModeRes {
        AddrModeRes {
            is24: false,
            addr: TU24::new(0, self.d.adc(u16::from(dx.0), false).0.adc(self.x, false).0),
        }
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

    pub fn resolve_dily(&self, cart: &Cart, dily: &am::Dily) -> AddrModeRes {
        let addr = self
            .read24(cart, self.resolve_d(cart, &am::D(dily.0)))
            .unwrap_or(TU24::UNKNOWN);
        AddrModeRes {
            is24: true,
            addr: addr.add24(self.y),
        }
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
}

#[derive(Debug, Clone)]
pub struct AnnotatedInstruction {
    pub instruction: Instruction,
    pub pre: Context,
    pub dst: Vec<Addr>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct CallStack {
    items: Vec<Addr>,
}

impl CallStack {
    pub fn push(&mut self, addr: Addr) {
        self.items.push(addr);
    }

    pub fn pop(&mut self) -> Option<Addr> {
        self.items.pop()
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }

    pub fn items(&self) -> &[Addr] {
        &self.items
    }
}

#[derive(Debug, Clone)]
pub struct Head {
    pub ctx: Context,
    pub call_stack: CallStack,
}

#[derive(Clone)]
pub struct Analyzer {
    pub code_annotations: BTreeMap<Addr, HashMap<CallStack, AnnotatedInstruction>>,
    pub shortest_callstacks: HashMap<Addr, CallStack>,
    heads: Vec<Head>,
}

impl Analyzer {
    pub fn new() -> Self {
        Self {
            code_annotations: BTreeMap::new(),
            shortest_callstacks: HashMap::new(),
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
        let call_stack = self.shortest_callstacks.get(&addr)?;
        self.get_annotation(addr, call_stack)
            .map(|a| (call_stack, a))
    }

    pub fn add_vector(&mut self, cart: &Cart, vec: u16) {
        let lo = cart.read_rom(Addr::new(0, vec));
        let hi = cart.read_rom(Addr::new(0, vec.wrapping_add(1)));
        let Some(addr) = lo.zip(hi).map(|(lo, hi)| u16::from_le_bytes([lo, hi])) else {
            return;
        };
        let ctx = Context {
            a: 0.into(),
            x: 0.into(),
            y: 0.into(),
            b: 0.into(),
            d: 0.into(),
            p: (M | X | I).into(),
            pc: Addr::new(0, addr),
            map: HashMap::new(),
            stack: Default::default(),
        };
        let head = Head {
            ctx,
            call_stack: Default::default(),
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

    pub fn analyze(&mut self, cart: &Cart) {
        while !self.is_done() {
            self.analyze_step(cart);
        }
        self.shortest_callstacks = self
            .code_annotations
            .iter()
            .filter_map(|(k, v)| v.keys().min_by_key(|v| v.len()).map(|v| (*k, v.clone())))
            .collect();
    }

    pub fn is_done(&self) -> bool {
        self.heads.is_empty()
    }

    pub fn analyze_step(&mut self, cart: &Cart) {
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
        let old_head_count = self.heads.len();
        match self.analyze_head(cart, head.clone()) {
            Ok(instruction) => {
                let dst = self.heads[old_head_count..]
                    .iter()
                    .map(|h| h.ctx.pc)
                    .collect();
                let annotation = AnnotatedInstruction {
                    instruction,
                    pre: head.ctx,
                    dst,
                };
                self.code_annotations
                    .entry(pc)
                    .or_default()
                    .insert(head.call_stack, annotation);
            }
            Err(_err) => {
                // TODO: rehandle
            }
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
                let (r, c) = a.adc(b.get8(), true);
                r.set_nz(ctx.p).with_bits(C, c)
            },
            |a| {
                let (r, c) = a.adc(b.get16(), true);
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
                let r = ctx.a.into_byte() & b;
                r.set_nz(ctx.p).with_bits(V, r.extract_bit(6))
            },
            |b| {
                let r = ctx.a & b;
                r.set_nz(ctx.p).with_bits(V, r.extract_bit(14))
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

    pub fn analyze_head(&mut self, cart: &Cart, head: Head) -> Result<Instruction, ()> {
        let Head {
            mut call_stack,
            mut ctx,
        } = head;
        let instr_pc = ctx.pc;
        let (mf, xf) = (ctx.mf(), ctx.xf());
        let Some(instr) = Instruction::from_fetcher(
            || {
                let addr = ctx.pc.add16_repl(1);
                ctx.read8(cart, addr).and_then(|e| e.get())
            },
            mf.get(),
            xf.get(),
        ) else {
            return Err(());
        };

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

        #[allow(unused_variables)]
        match &instr {
            Instruction::Brk(_) => todo!(),
            Instruction::OraDxi(dxi) => todo!(),
            Instruction::Cop(_) => todo!(),
            Instruction::OraS(s) => todo!(),
            Instruction::TsbD(d) => todo!(),
            Instruction::OraD(d) => todo!(),
            Instruction::AslD(d) => todo!(),
            Instruction::OraDil(dil) => todo!(),
            Instruction::Php => ctx.stack.push(ctx.p),
            Instruction::OraI(i) => self.instr_oraimm(&mut ctx, (*i).into()),
            Instruction::AslAc => self.instr_aslimm(&mut ctx),
            Instruction::Phd => todo!(),
            Instruction::TsbA(a) => todo!(),
            Instruction::OraA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_ora(cart, &mut ctx, addr);
            }
            Instruction::AslA(a) => todo!(),
            Instruction::OraAl(al) => todo!(),
            Instruction::Bpl(label) => {
                self.instr_branch(Head { ctx, call_stack }, N, false, label.take(instr_pc));
                return Ok(instr);
            }
            Instruction::OraDiy(diy) => todo!(),
            Instruction::OraDi(di) => todo!(),
            Instruction::OraSiy(siy) => todo!(),
            Instruction::TrbD(d) => todo!(),
            Instruction::OraDx(dx) => todo!(),
            Instruction::AslDx(dx) => todo!(),
            Instruction::OraDily(dily) => todo!(),
            Instruction::Clc => ctx.p &= !C,
            Instruction::OraAy(ay) => todo!(),
            Instruction::IncAc => self.instr_incimm(&mut ctx, |c| &mut c.a, mf, true),
            Instruction::Tcs => (),
            Instruction::TrbA(a) => todo!(),
            Instruction::OraAx(ax) => {
                let addr = ctx.resolve_ax(cart, ax);
                self.instr_ora(cart, &mut ctx, addr);
            }
            Instruction::AslAx(ax) => todo!(),
            Instruction::OraAlx(alx) => todo!(),
            Instruction::Jsr(dst) => {
                ctx.stack.push16(ctx.pc.addr.wrapping_sub(1).into());
                ctx.pc.addr = dst.0;
                call_stack.push(instr_pc);
            }
            Instruction::AndDxi(dxi) => todo!(),
            Instruction::Jsl(dst) => {
                ctx.stack.push(ctx.pc.bank.into());
                ctx.stack.push16(ctx.pc.addr.wrapping_sub(1).into());
                ctx.pc = *dst;
                call_stack.push(instr_pc);
            }
            Instruction::AndS(s) => todo!(),
            Instruction::BitD(d) => todo!(),
            Instruction::AndD(d) => todo!(),
            Instruction::RolD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_rol(cart, &mut ctx, addr);
            }
            Instruction::AndDil(dil) => todo!(),
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
            Instruction::RolA(a) => todo!(),
            Instruction::AndAl(al) => todo!(),
            Instruction::Bmi(label) => {
                self.instr_branch(Head { ctx, call_stack }, N, true, label.take(instr_pc));
                return Ok(instr);
            }
            Instruction::AndDiy(diy) => todo!(),
            Instruction::AndDi(di) => todo!(),
            Instruction::AndSiy(siy) => todo!(),
            Instruction::BitDx(dx) => todo!(),
            Instruction::AndDx(dx) => todo!(),
            Instruction::RolDx(dx) => todo!(),
            Instruction::AndDily(dily) => todo!(),
            Instruction::Sec => ctx.p |= C,
            Instruction::AndAy(ay) => todo!(),
            Instruction::DecAc => self.instr_incimm(&mut ctx, |c| &mut c.a, mf, false),
            Instruction::Tsc => todo!(),
            Instruction::BitAx(ax) => todo!(),
            Instruction::AndAx(ax) => todo!(),
            Instruction::RolAx(ax) => todo!(),
            Instruction::AndAlx(alx) => todo!(),
            Instruction::Rti => return Ok(instr),
            Instruction::EorDxi(dxi) => todo!(),
            Instruction::Wdm(_) => todo!(),
            Instruction::EorS(s) => todo!(),
            Instruction::Mvp(_, _) => todo!(),
            Instruction::EorD(d) => todo!(),
            Instruction::LsrD(d) => todo!(),
            Instruction::EorDil(dil) => todo!(),
            Instruction::Pha => ctx.stack.push_unknown(ctx.a_sized()),
            Instruction::EorI(i) => todo!(),
            Instruction::LsrAc => self.instr_lsrimm(&mut ctx),
            Instruction::Phk => ctx.stack.push(ctx.pc.bank.into()),
            Instruction::Jmp(dst) => ctx.pc.addr = dst.0,
            Instruction::EorA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_eor(cart, &mut ctx, addr);
            }
            Instruction::LsrA(a) => todo!(),
            Instruction::EorAl(al) => todo!(),
            Instruction::Bvc(label) => {
                self.instr_branch(Head { ctx, call_stack }, V, false, label.take(instr_pc));
                return Ok(instr);
            }
            Instruction::EorDiy(diy) => todo!(),
            Instruction::EorDi(di) => todo!(),
            Instruction::EorSiy(siy) => todo!(),
            Instruction::Mvn(_, _) => todo!(),
            Instruction::EorDx(dx) => todo!(),
            Instruction::LsrDx(dx) => todo!(),
            Instruction::EorDily(dily) => todo!(),
            Instruction::Cli => ctx.p &= !I,
            Instruction::EorAy(ay) => todo!(),
            Instruction::Phy => ctx.stack.push_unknown(ctx.y_sized()),
            Instruction::Tcd => {
                ctx.d = ctx.a;
                ctx.set_nz16(ctx.a);
            }
            Instruction::Jml(addr) => todo!(),
            Instruction::EorAx(ax) => todo!(),
            Instruction::LsrAx(ax) => todo!(),
            Instruction::EorAlx(alx) => todo!(),
            Instruction::Rts => {
                let cs_pc = call_stack.pop();
                if let Some(new_pc) = ctx.stack.pop16().get() {
                    ctx.pc.addr = new_pc.wrapping_add(1);
                } else if let Some(new_pc) = cs_pc {
                    // fall back to our call stack implementation if the system stack got corrupted
                    ctx.pc = new_pc;
                } else {
                    return Err(());
                }
            }
            Instruction::AdcDxi(dxi) => todo!(),
            Instruction::Per(_) => todo!(),
            Instruction::AdcS(s) => todo!(),
            Instruction::StzD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_stz(cart, &mut ctx, addr);
            }
            Instruction::AdcD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_adc(cart, &mut ctx, addr, false);
            }
            Instruction::RorD(d) => todo!(),
            Instruction::AdcDil(dil) => todo!(),
            Instruction::Pla => ctx.a.write_sized(ctx.stack.pop_unknown(mf)),
            Instruction::AdcI(i) => self.instr_adcimm(&mut ctx, i.clone().into(), false),
            Instruction::RorAc => self.instr_rorimm(&mut ctx),
            Instruction::Rtl => {
                let cs_pc = call_stack.pop();
                if let Some(new_pc) = ctx.stack.pop24().get() {
                    ctx.pc = new_pc;
                    ctx.pc.addr = ctx.pc.addr.wrapping_add(1);
                } else if let Some(new_pc) = cs_pc {
                    // fall back to our call stack implementation if the system stack got corrupted
                    ctx.pc = new_pc;
                } else {
                    return Err(());
                }
            }
            Instruction::Jmpi(_) => todo!(),
            Instruction::AdcA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_adc(cart, &mut ctx, addr, false);
            }
            Instruction::RorA(a) => todo!(),
            Instruction::AdcAl(al) => todo!(),
            Instruction::Bvs(label) => {
                self.instr_branch(Head { ctx, call_stack }, V, true, label.take(instr_pc));
                return Ok(instr);
            }
            Instruction::AdcDiy(diy) => todo!(),
            Instruction::AdcDi(di) => todo!(),
            Instruction::AdcSiy(siy) => todo!(),
            Instruction::StzDx(dx) => {
                let addr = ctx.resolve_dx(cart, dx);
                self.instr_stz(cart, &mut ctx, addr);
            }
            Instruction::AdcDx(dx) => todo!(),
            Instruction::RorDx(dx) => todo!(),
            Instruction::AdcDily(dily) => todo!(),
            Instruction::Sei => ctx.p |= I,
            Instruction::AdcAy(ay) => {
                let addr = ctx.resolve_ay(cart, ay);
                self.instr_adc(cart, &mut ctx, addr, false);
            }
            Instruction::Ply => ctx.y.write_sized(ctx.stack.pop_unknown(xf)),
            Instruction::Tdc => {
                ctx.a = ctx.d;
                ctx.set_nz16(ctx.a);
            }
            Instruction::Jmpxi(_) => todo!(),
            Instruction::AdcAx(ax) => todo!(),
            Instruction::RorAx(ax) => todo!(),
            Instruction::AdcAlx(alx) => todo!(),
            Instruction::Bra(label) => ctx.pc = label.take(instr_pc),
            Instruction::StaDxi(dxi) => todo!(),
            Instruction::Brl(near_label) => todo!(),
            Instruction::StaS(s) => todo!(),
            Instruction::StyD(d) => todo!(),
            Instruction::StaD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_sta(cart, &mut ctx, addr);
            }
            Instruction::StxD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_stx(cart, &mut ctx, addr);
            }
            Instruction::StaDil(dil) => todo!(),
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
            Instruction::Txa => todo!(),
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
                return Ok(instr);
            }
            Instruction::StaDiy(diy) => todo!(),
            Instruction::StaDi(di) => todo!(),
            Instruction::StaSiy(siy) => todo!(),
            Instruction::StyDx(dx) => todo!(),
            Instruction::StaDx(dx) => {
                let addr = ctx.resolve_dx(cart, dx);
                self.instr_sta(cart, &mut ctx, addr);
            }
            Instruction::StxDy(dy) => todo!(),
            Instruction::StaDily(dily) => todo!(),
            Instruction::Tya => {
                ctx.a.write_with_size(ctx.y, mf);
                ctx.set_nzx(ctx.a_sized());
            }
            Instruction::StaAy(ay) => {
                let addr = ctx.resolve_ay(cart, ay);
                self.instr_sta(cart, &mut ctx, addr);
            }
            Instruction::Txs => todo!(),
            Instruction::Txy => todo!(),
            Instruction::StzA(a) => {
                let addr = ctx.resolve_a(cart, a);
                self.instr_stz(cart, &mut ctx, addr)
            }
            Instruction::StaAx(ax) => {
                let addr = ctx.resolve_ax(cart, ax);
                self.instr_sta(cart, &mut ctx, addr);
            }
            Instruction::StzAx(ax) => todo!(),
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
            Instruction::LdaDil(dil) => todo!(),
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
            Instruction::Plb => ctx.b = ctx.stack.pop(),
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
            Instruction::LdaAl(al) => todo!(),
            Instruction::Bcs(label) => {
                self.instr_branch(Head { ctx, call_stack }, C, true, label.take(instr_pc));
                return Ok(instr);
            }
            Instruction::LdaDiy(diy) => todo!(),
            Instruction::LdaDi(di) => {
                let addr = ctx.resolve_di(cart, di);
                self.instr_lda(cart, &mut ctx, addr);
            }
            Instruction::LdaSiy(siy) => todo!(),
            Instruction::LdyDx(dx) => todo!(),
            Instruction::LdaDx(dx) => todo!(),
            Instruction::LdxDy(dy) => todo!(),
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
            Instruction::Tyx => todo!(),
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
            Instruction::CpyD(d) => todo!(),
            Instruction::CmpD(d) => todo!(),
            Instruction::DecD(d) => todo!(),
            Instruction::CmpDil(dil) => todo!(),
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
            Instruction::DecA(a) => todo!(),
            Instruction::CmpAl(al) => todo!(),
            Instruction::Bne(label) => {
                self.instr_branch(Head { ctx, call_stack }, Z, false, label.take(instr_pc));
                return Ok(instr);
            }
            Instruction::CmpDiy(diy) => todo!(),
            Instruction::CmpDi(di) => todo!(),
            Instruction::CmpSiy(siy) => todo!(),
            Instruction::Pei(_) => todo!(),
            Instruction::CmpDx(dx) => todo!(),
            Instruction::DecDx(dx) => todo!(),
            Instruction::CmpDily(dily) => todo!(),
            Instruction::Cld => ctx.p &= !D,
            Instruction::CmpAy(ay) => todo!(),
            Instruction::Phx => ctx.stack.push_unknown(ctx.x_sized()),
            Instruction::Stp => todo!(),
            Instruction::Jmli(_) => todo!(),
            Instruction::CmpAx(ax) => todo!(),
            Instruction::DecAx(ax) => todo!(),
            Instruction::CmpAlx(alx) => todo!(),
            Instruction::CpxI(i) => {
                let x = ctx.x_sized();
                self.instr_cmpimm(&mut ctx, x, (*i).into())
            }
            Instruction::SbcDxi(dxi) => todo!(),
            Instruction::Sep(p) => ctx.p |= p.0,
            Instruction::SbcS(s) => todo!(),
            Instruction::CpxD(d) => todo!(),
            Instruction::SbcD(d) => todo!(),
            Instruction::IncD(d) => {
                let addr = ctx.resolve_d(cart, d);
                self.instr_inc(&mut ctx, cart, addr, true);
            }
            Instruction::SbcDil(dil) => todo!(),
            Instruction::Inx => self.instr_incimm(&mut ctx, |c| &mut c.x, xf, true),
            Instruction::SbcI(i) => self.instr_adcimm(&mut ctx, i.clone().into(), true),
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
            Instruction::SbcA(a) => todo!(),
            Instruction::IncA(a) => todo!(),
            Instruction::SbcAl(al) => todo!(),
            Instruction::Beq(label) => {
                self.instr_branch(Head { ctx, call_stack }, Z, true, label.take(instr_pc));
                return Ok(instr);
            }
            Instruction::SbcDiy(diy) => todo!(),
            Instruction::SbcDi(di) => todo!(),
            Instruction::SbcSiy(siy) => todo!(),
            Instruction::Pea(_) => todo!(),
            Instruction::SbcDx(dx) => todo!(),
            Instruction::IncDx(dx) => todo!(),
            Instruction::SbcDily(dily) => todo!(),
            Instruction::Sed => ctx.p |= D,
            Instruction::SbcAy(ay) => todo!(),
            Instruction::Plx => ctx.x.write_sized(ctx.stack.pop_unknown(xf)),
            Instruction::Xce => (),
            Instruction::Jsrxi(_) => todo!(),
            Instruction::SbcAx(ax) => todo!(),
            Instruction::IncAx(ax) => todo!(),
            Instruction::SbcAlx(alx) => todo!(),
        }

        //println!("{ctx:x?}");
        self.heads.push(Head { ctx, call_stack });
        Ok(instr)
    }
}
