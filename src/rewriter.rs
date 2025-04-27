use std::collections::BTreeMap;

use crate::{
    addr::Addr,
    addr_space::MemoryLocation,
    cart::Cart,
    disasm::{AnnotatedInstruction, Context, Disassembler},
    instruction::{Instruction, NearLabel, am},
    pf,
    tvl::TBool,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockId {
    original_addr: Addr,
}

impl core::cmp::PartialOrd for BlockId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl core::cmp::Ord for BlockId {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.original_addr.cmp(&other.original_addr)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StoreableRegister {
    A,
    X,
    Y,
    Zero,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IndexRegister {
    X,
    Y,
}

#[derive(Debug, Clone)]
pub enum AbstractAddress {
    Location(MemoryLocation),
}

#[derive(Debug, Clone)]
pub struct AbstractAccess {
    pub addr: AbstractAddress,
    pub index: Option<IndexRegister>,
    pub is_long_wrapping: bool,
}

impl AbstractAccess {
    pub fn new_abs(cart: &Cart, ctx: &Context, abs: am::A) -> Self {
        let bank = if abs.0 < 0x8000
            && (ctx.b & 0x40)
                .is_zero()
                .get()
                .unwrap_or(ctx.pc.bank & 0x40 == 0)
        {
            0
        } else {
            ctx.b.get().unwrap_or(ctx.pc.bank)
        };
        Self::new_absl(cart, am::Al(Addr::new(bank, abs.0)))
    }

    pub fn new_absx(cart: &Cart, ctx: &Context, ax: am::Ax) -> Self {
        let mut slf = Self::new_abs(cart, ctx, am::A(ax.0));
        slf.index = Some(IndexRegister::X);
        slf
    }

    pub fn new_absy(cart: &Cart, ctx: &Context, ay: am::Ay) -> Self {
        let mut slf = Self::new_abs(cart, ctx, am::A(ay.0));
        slf.index = Some(IndexRegister::Y);
        slf
    }

    pub fn new_absl(cart: &Cart, al: am::Al) -> Self {
        Self {
            addr: AbstractAddress::Location(cart.map_full(al.0)),
            index: None,
            is_long_wrapping: true,
        }
    }

    pub fn new_abslx(cart: &Cart, alx: am::Alx) -> Self {
        let mut slf = Self::new_absl(cart, am::Al(alx.0));
        slf.index = Some(IndexRegister::X);
        slf
    }
}

#[derive(Debug, Clone)]
pub struct AbstractStoreInstruction {
    pub src: StoreableRegister,
    pub dst: AbstractAccess,
    pub is8: TBool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransferSrc8 {
    Imm(u8),
    A,
    X,
    Y,
}

impl TransferSrc8 {
    pub const fn to_instr(self, dst: TransferDst8) -> AbstractTransfer8 {
        AbstractTransfer8 { src: self, dst }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransferDst8 {
    A,
    X,
    Y,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransferSrc16 {
    Imm(u16),
    A,
    X,
    Y,
}

impl TransferSrc16 {
    pub const fn to_instr(self, dst: TransferDst16) -> AbstractTransfer16 {
        AbstractTransfer16 { src: self, dst }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransferDst16 {
    A,
    X,
    Y,
    D,
    S,
}

#[derive(Debug, Clone, Copy)]
pub struct AbstractTransfer8 {
    pub src: TransferSrc8,
    pub dst: TransferDst8,
}

#[derive(Debug, Clone, Copy)]
pub struct AbstractTransfer16 {
    pub src: TransferSrc16,
    pub dst: TransferDst16,
}

impl AbstractTransfer16 {
    pub const fn touches_flags(&self) -> bool {
        matches!(self.dst, TransferDst16::S)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModifyOperation {
    Inc,
    Dec,
    Asl,
    Lsr,
    Rol,
    Ror,
}

#[derive(Debug, Clone)]
pub enum ModifyLocation {
    A,
    X,
    Y,
    Access(AbstractAccess),
}

#[derive(Debug, Clone)]
pub struct AbstractModify {
    pub op: ModifyOperation,
    pub loc: ModifyLocation,
    pub is_long: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperateType {
    Adc,
    Sbc,
}

#[derive(Debug, Clone)]
pub enum OperateRhs8 {
    Imm(u8),
    Access(AbstractAccess),
}

#[derive(Debug, Clone)]
pub enum OperateRhs16 {
    Imm(u16),
    Access(AbstractAccess),
}

#[derive(Debug, Clone)]
pub enum OperateRhs {
    Op8(OperateRhs8),
    Op16(OperateRhs16),
}

impl From<am::I> for OperateRhs {
    fn from(value: am::I) -> Self {
        match value {
            am::I::U8(value) => Self::Op8(OperateRhs8::Imm(value)),
            am::I::U16(value) => Self::Op16(OperateRhs16::Imm(value)),
        }
    }
}

#[derive(Debug, Clone)]
pub struct AbstractOperate {
    pub op: OperateType,
    pub rhs: OperateRhs,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BranchCondition {
    Pl,
    Mi,
    Ne,
    Eq,
    Cc,
    Cs,
    Vc,
    Vs,
}

#[derive(Debug, Clone)]
pub struct AbstractBranch {
    pub cond: BranchCondition,
    pub label: BlockId,
}

#[derive(Debug, Clone)]
pub enum AbstractInstruction {
    SetFlags(u8),
    ClrFlags(u8),
    /// Store a value into address space.
    /// This does not affect flags.
    Store(AbstractStoreInstruction),
    Transfer8(AbstractTransfer8),
    Transfer16(AbstractTransfer16),
    Modify(AbstractModify),
    OperateA(AbstractOperate),
    Branch(AbstractBranch),
    Xce,
}

impl From<AbstractTransfer8> for AbstractInstruction {
    fn from(value: AbstractTransfer8) -> Self {
        Self::Transfer8(value)
    }
}

impl From<AbstractTransfer16> for AbstractInstruction {
    fn from(value: AbstractTransfer16) -> Self {
        Self::Transfer16(value)
    }
}

impl AbstractInstruction {
    pub fn new_stz(ctx: &Context, dst: AbstractAccess) -> Self {
        Self::Store(AbstractStoreInstruction {
            src: StoreableRegister::Zero,
            dst,
            is8: ctx.mf(),
        })
    }

    pub fn new_sta(ctx: &Context, dst: AbstractAccess) -> Self {
        Self::Store(AbstractStoreInstruction {
            src: StoreableRegister::A,
            dst,
            is8: ctx.mf(),
        })
    }

    pub fn new_ldimm(i: am::I, t8: TransferDst8, t16: TransferDst16) -> Self {
        match i {
            am::I::U8(v) => TransferSrc8::Imm(v).to_instr(t8).into(),
            am::I::U16(v) => TransferSrc16::Imm(v).to_instr(t16).into(),
        }
    }

    pub fn new_op(op: OperateType, rhs: impl Into<OperateRhs>) -> Self {
        Self::OperateA(AbstractOperate {
            op,
            rhs: rhs.into(),
        })
    }

    pub fn new_bra(ctx: &Context, cond: BranchCondition, label: NearLabel) -> Self {
        Self::Branch(AbstractBranch {
            cond,
            label: BlockId {
                original_addr: label.take(ctx.pc),
            },
        })
    }
}

#[derive(Debug, Clone)]
pub struct CodeBlock {
    instrs: Vec<AbstractInstruction>,
}

#[derive(Debug, Clone)]
pub enum BlockContent {
    Code(CodeBlock),
    Data,
}

#[derive(Debug, Clone)]
pub struct Block {
    pub content: BlockContent,
    pub start: u32,
    pub end: u32,
}

impl Block {
    pub const fn is_code(&self) -> bool {
        matches!(&self.content, BlockContent::Code(_))
    }
}

#[derive(Debug, Clone)]
pub struct Rewriter {
    // TODO: compare performance between `VecMap` and `BTreeMap`
    blocks: BTreeMap<BlockId, Block>,
    last_block_id: Option<BlockId>,
    cursor: u32,
}

impl Rewriter {
    pub fn new() -> Self {
        Self {
            blocks: Default::default(),
            last_block_id: None,
            cursor: 0,
        }
    }

    pub fn rewrite(&mut self, cart: &Cart, disasm: &Disassembler) {
        while self.cursor < cart.rom.len() {
            self.rewrite_step(cart, disasm);
        }
    }

    fn rewrite_step(&mut self, cart: &Cart, disasm: &Disassembler) {
        let Some(addr) = cart.reverse_map_rom(self.cursor) else {
            self.cursor = self.cursor.wrapping_add(1);
            return;
        };
        let block_id = self.last_block_id.as_ref().cloned().unwrap_or(BlockId {
            original_addr: addr,
        });
        if let Some(ann) = disasm.unified_code_annotations.get(&addr) {
            if self.rewrite_instr(cart, ann, block_id).is_none() {
                todo!()
            }
        }
    }

    fn rewrite_instr(
        &mut self,
        cart: &Cart,
        ann: &AnnotatedInstruction,
        block_id: BlockId,
    ) -> Option<()> {
        let block_entry = self.blocks.entry(block_id.clone());
        let block = match block_entry {
            std::collections::btree_map::Entry::Occupied(entry) if entry.get().is_code() => {
                entry.into_mut()
            }
            entry => {
                let block = Block {
                    content: BlockContent::Code(CodeBlock { instrs: vec![] }),
                    start: self.cursor,
                    end: self.cursor,
                };
                match entry {
                    std::collections::btree_map::Entry::Vacant(entry) => entry.insert(block),
                    std::collections::btree_map::Entry::Occupied(mut entry) => {
                        entry.insert(block);
                        entry.into_mut()
                    }
                }
            }
        };
        let Block {
            content: BlockContent::Code(block),
            ..
        } = block
        else {
            unreachable!()
        };
        let ctx = &ann.pre;
        let mut push = |v| block.instrs.push(v);
        match ann.instruction {
            Instruction::Brk(_) => todo!(),
            Instruction::OraDxi(_dxi) => todo!(),
            Instruction::Cop(_) => todo!(),
            Instruction::OraS(_s) => todo!(),
            Instruction::TsbD(_d) => todo!(),
            Instruction::OraD(_d) => todo!(),
            Instruction::AslD(_d) => todo!(),
            Instruction::OraDil(_dil) => todo!(),
            Instruction::Php => todo!(),
            Instruction::OraI(_i) => todo!(),
            Instruction::AslAc => todo!(),
            Instruction::Phd => todo!(),
            Instruction::TsbA(_a) => todo!(),
            Instruction::OraA(_a) => todo!(),
            Instruction::AslA(_a) => todo!(),
            Instruction::OraAl(_al) => todo!(),
            Instruction::Bpl(label) => push(AbstractInstruction::new_bra(
                ctx,
                BranchCondition::Pl,
                label,
            )),
            Instruction::OraDiy(_diy) => todo!(),
            Instruction::OraDi(_di) => todo!(),
            Instruction::OraSiy(_siy) => todo!(),
            Instruction::TrbD(_d) => todo!(),
            Instruction::OraDx(_dx) => todo!(),
            Instruction::AslDx(_dx) => todo!(),
            Instruction::OraDily(_dily) => todo!(),
            Instruction::Clc => {
                push(AbstractInstruction::ClrFlags(pf::C));
            }
            Instruction::OraAy(_ay) => todo!(),
            Instruction::IncAc => {
                push(AbstractInstruction::Modify(AbstractModify {
                    op: ModifyOperation::Inc,
                    loc: ModifyLocation::A,
                    is_long: !ctx.mf().get()?,
                }));
            }
            Instruction::Tcs => {
                push(AbstractInstruction::Transfer16(AbstractTransfer16 {
                    src: TransferSrc16::A,
                    dst: TransferDst16::S,
                }));
            }
            Instruction::TrbA(_a) => todo!(),
            Instruction::OraAx(_ax) => todo!(),
            Instruction::AslAx(_ax) => todo!(),
            Instruction::OraAlx(_alx) => todo!(),
            Instruction::Jsr(_absolute_label) => todo!(),
            Instruction::AndDxi(_dxi) => todo!(),
            Instruction::Jsl(_addr) => todo!(),
            Instruction::AndS(_s) => todo!(),
            Instruction::BitD(_d) => todo!(),
            Instruction::AndD(_d) => todo!(),
            Instruction::RolD(_d) => todo!(),
            Instruction::AndDil(_dil) => todo!(),
            Instruction::Plp => todo!(),
            Instruction::AndI(_i) => todo!(),
            Instruction::RolAc => todo!(),
            Instruction::Pld => todo!(),
            Instruction::BitA(_a) => todo!(),
            Instruction::AndA(_a) => todo!(),
            Instruction::RolA(_a) => todo!(),
            Instruction::AndAl(_al) => todo!(),
            Instruction::Bmi(label) => push(AbstractInstruction::new_bra(
                ctx,
                BranchCondition::Mi,
                label,
            )),
            Instruction::AndDiy(_diy) => todo!(),
            Instruction::AndDi(_di) => todo!(),
            Instruction::AndSiy(_siy) => todo!(),
            Instruction::BitDx(_dx) => todo!(),
            Instruction::AndDx(_dx) => todo!(),
            Instruction::RolDx(_dx) => todo!(),
            Instruction::AndDily(_dily) => todo!(),
            Instruction::Sec => {
                push(AbstractInstruction::SetFlags(pf::C));
            }
            Instruction::AndAy(_ay) => todo!(),
            Instruction::DecAc => {
                push(AbstractInstruction::Modify(AbstractModify {
                    op: ModifyOperation::Dec,
                    loc: ModifyLocation::A,
                    is_long: !ctx.mf().get()?,
                }));
            }
            Instruction::Tsc => todo!(),
            Instruction::BitAx(_ax) => todo!(),
            Instruction::AndAx(_ax) => todo!(),
            Instruction::RolAx(_ax) => todo!(),
            Instruction::AndAlx(_alx) => todo!(),
            Instruction::Rti => todo!(),
            Instruction::EorDxi(_dxi) => todo!(),
            Instruction::Wdm(_) => todo!(),
            Instruction::EorS(_s) => todo!(),
            Instruction::Mvp(_, _) => todo!(),
            Instruction::EorD(_d) => todo!(),
            Instruction::LsrD(_d) => todo!(),
            Instruction::EorDil(_dil) => todo!(),
            Instruction::Pha => todo!(),
            Instruction::EorI(_i) => todo!(),
            Instruction::LsrAc => todo!(),
            Instruction::Phk => todo!(),
            Instruction::Jmp(_absolute_label) => todo!(),
            Instruction::EorA(_a) => todo!(),
            Instruction::LsrA(_a) => todo!(),
            Instruction::EorAl(_al) => todo!(),
            Instruction::Bvc(label) => push(AbstractInstruction::new_bra(
                ctx,
                BranchCondition::Vc,
                label,
            )),
            Instruction::EorDiy(_diy) => todo!(),
            Instruction::EorDi(_di) => todo!(),
            Instruction::EorSiy(_siy) => todo!(),
            Instruction::Mvn(_, _) => todo!(),
            Instruction::EorDx(_dx) => todo!(),
            Instruction::LsrDx(_dx) => todo!(),
            Instruction::EorDily(_dily) => todo!(),
            Instruction::Cli => {
                push(AbstractInstruction::ClrFlags(pf::I));
            }
            Instruction::EorAy(_ay) => todo!(),
            Instruction::Phy => todo!(),
            Instruction::Tcd => {
                push(AbstractInstruction::Transfer16(AbstractTransfer16 {
                    src: TransferSrc16::A,
                    dst: TransferDst16::D,
                }));
            }
            Instruction::Jml(_addr) => todo!(),
            Instruction::EorAx(_ax) => todo!(),
            Instruction::LsrAx(_ax) => todo!(),
            Instruction::EorAlx(_alx) => todo!(),
            Instruction::Rts => todo!(),
            Instruction::AdcDxi(_dxi) => todo!(),
            Instruction::Per(_relative_label) => todo!(),
            Instruction::AdcS(_s) => todo!(),
            Instruction::StzD(_d) => todo!(),
            Instruction::AdcD(_d) => todo!(),
            Instruction::RorD(_d) => todo!(),
            Instruction::AdcDil(_dil) => todo!(),
            Instruction::Pla => todo!(),
            Instruction::AdcI(i) => {
                push(AbstractInstruction::new_op(OperateType::Adc, i));
            }
            Instruction::RorAc => todo!(),
            Instruction::Rtl => todo!(),
            Instruction::Jmpi(_indirect_label) => todo!(),
            Instruction::AdcA(_a) => todo!(),
            Instruction::RorA(_a) => todo!(),
            Instruction::AdcAl(_al) => todo!(),
            Instruction::Bvs(label) => push(AbstractInstruction::new_bra(
                ctx,
                BranchCondition::Vs,
                label,
            )),
            Instruction::AdcDiy(_diy) => todo!(),
            Instruction::AdcDi(_di) => todo!(),
            Instruction::AdcSiy(_siy) => todo!(),
            Instruction::StzDx(_dx) => todo!(),
            Instruction::AdcDx(_dx) => todo!(),
            Instruction::RorDx(_dx) => todo!(),
            Instruction::AdcDily(_dily) => todo!(),
            Instruction::Sei => {
                push(AbstractInstruction::SetFlags(pf::I));
            }
            Instruction::AdcAy(_ay) => todo!(),
            Instruction::Ply => todo!(),
            Instruction::Tdc => todo!(),
            Instruction::Jmpxi(_indirect_indexed_label) => todo!(),
            Instruction::AdcAx(_ax) => todo!(),
            Instruction::RorAx(_ax) => todo!(),
            Instruction::AdcAlx(_alx) => todo!(),
            Instruction::Bra(_near_label) => todo!(),
            Instruction::StaDxi(_dxi) => todo!(),
            Instruction::Brl(_relative_label) => todo!(),
            Instruction::StaS(_s) => todo!(),
            Instruction::StyD(_d) => todo!(),
            Instruction::StaD(_d) => todo!(),
            Instruction::StxD(_d) => todo!(),
            Instruction::StaDil(_dil) => todo!(),
            Instruction::Dey => {
                push(AbstractInstruction::Modify(AbstractModify {
                    op: ModifyOperation::Dec,
                    loc: ModifyLocation::Y,
                    is_long: !ctx.xf().get()?,
                }));
            }
            Instruction::BitI(_i) => todo!(),
            Instruction::Txa => {
                push(if ctx.mf().get()? {
                    TransferSrc8::Y.to_instr(TransferDst8::A).into()
                } else {
                    TransferSrc16::X.to_instr(TransferDst16::A).into()
                });
            }
            Instruction::Phb => todo!(),
            Instruction::StyA(_a) => todo!(),
            Instruction::StaA(a) => {
                let dst = AbstractAccess::new_abs(cart, ctx, a);
                push(AbstractInstruction::new_sta(ctx, dst));
            }
            Instruction::StxA(_a) => todo!(),
            Instruction::StaAl(al) => {
                let dst = AbstractAccess::new_absl(cart, al);
                push(AbstractInstruction::new_sta(ctx, dst));
            }
            Instruction::Bcc(label) => push(AbstractInstruction::new_bra(
                ctx,
                BranchCondition::Cc,
                label,
            )),
            Instruction::StaDiy(_diy) => todo!(),
            Instruction::StaDi(_di) => todo!(),
            Instruction::StaSiy(_siy) => todo!(),
            Instruction::StyDx(_dx) => todo!(),
            Instruction::StaDx(_dx) => todo!(),
            Instruction::StxDy(_dy) => todo!(),
            Instruction::StaDily(_dily) => todo!(),
            Instruction::Tya => {
                push(if ctx.mf().get()? {
                    TransferSrc8::Y.to_instr(TransferDst8::A).into()
                } else {
                    TransferSrc16::Y.to_instr(TransferDst16::A).into()
                });
            }
            Instruction::StaAy(ay) => {
                let dst = AbstractAccess::new_absy(cart, ctx, ay);
                push(AbstractInstruction::new_sta(ctx, dst));
            }
            Instruction::Txs => todo!(),
            Instruction::Txy => {
                push(if ctx.xf().get()? {
                    TransferSrc8::X.to_instr(TransferDst8::Y).into()
                } else {
                    TransferSrc16::X.to_instr(TransferDst16::Y).into()
                });
            }
            Instruction::StzA(a) => {
                let dst = AbstractAccess::new_abs(cart, ctx, a);
                push(AbstractInstruction::new_stz(ctx, dst));
            }
            Instruction::StaAx(ax) => {
                let dst = AbstractAccess::new_absx(cart, ctx, ax);
                push(AbstractInstruction::new_sta(ctx, dst));
            }
            Instruction::StzAx(ax) => {
                let dst = AbstractAccess::new_absx(cart, ctx, ax);
                push(AbstractInstruction::new_stz(ctx, dst));
            }
            Instruction::StaAlx(alx) => {
                let dst = AbstractAccess::new_abslx(cart, alx);
                push(AbstractInstruction::new_sta(ctx, dst));
            }
            Instruction::LdyI(i) => {
                push(AbstractInstruction::new_ldimm(
                    i,
                    TransferDst8::Y,
                    TransferDst16::Y,
                ));
            }
            Instruction::LdaDxi(_dxi) => todo!(),
            Instruction::LdxI(i) => {
                push(AbstractInstruction::new_ldimm(
                    i,
                    TransferDst8::X,
                    TransferDst16::X,
                ));
            }
            Instruction::LdaS(_s) => todo!(),
            Instruction::LdyD(_d) => todo!(),
            Instruction::LdaD(_d) => todo!(),
            Instruction::LdxD(_d) => todo!(),
            Instruction::LdaDil(_dil) => todo!(),
            Instruction::Tay => {
                push(if ctx.xf().get()? {
                    TransferSrc8::A.to_instr(TransferDst8::Y).into()
                } else {
                    TransferSrc16::A.to_instr(TransferDst16::Y).into()
                });
            }
            Instruction::LdaI(i) => {
                push(AbstractInstruction::new_ldimm(
                    i,
                    TransferDst8::A,
                    TransferDst16::A,
                ));
            }
            Instruction::Tax => {
                push(if ctx.xf().get()? {
                    TransferSrc8::A.to_instr(TransferDst8::X).into()
                } else {
                    TransferSrc16::A.to_instr(TransferDst16::X).into()
                });
            }
            Instruction::Plb => todo!(),
            Instruction::LdyA(_a) => todo!(),
            Instruction::LdaA(_a) => todo!(),
            Instruction::LdxA(_a) => todo!(),
            Instruction::LdaAl(_al) => todo!(),
            Instruction::Bcs(label) => push(AbstractInstruction::new_bra(
                ctx,
                BranchCondition::Cs,
                label,
            )),
            Instruction::LdaDiy(_diy) => todo!(),
            Instruction::LdaDi(_di) => todo!(),
            Instruction::LdaSiy(_siy) => todo!(),
            Instruction::LdyDx(_dx) => todo!(),
            Instruction::LdaDx(_dx) => todo!(),
            Instruction::LdxDy(_dy) => todo!(),
            Instruction::LdaDily(_dily) => todo!(),
            Instruction::Clv => {
                push(AbstractInstruction::ClrFlags(pf::V));
            }
            Instruction::LdaAy(_ay) => todo!(),
            Instruction::Tsx => todo!(),
            Instruction::Tyx => {
                push(if ctx.xf().get()? {
                    TransferSrc8::Y.to_instr(TransferDst8::X).into()
                } else {
                    TransferSrc16::Y.to_instr(TransferDst16::X).into()
                });
            }
            Instruction::LdyAx(_ax) => todo!(),
            Instruction::LdaAx(_ax) => todo!(),
            Instruction::LdxAy(_ay) => todo!(),
            Instruction::LdaAlx(_alx) => todo!(),
            Instruction::CpyI(_i) => todo!(),
            Instruction::CmpDxi(_dxi) => todo!(),
            Instruction::Rep(val) => {
                if !val.is_empty() {
                    push(AbstractInstruction::ClrFlags(val.0));
                }
            }
            Instruction::CmpS(_s) => todo!(),
            Instruction::CpyD(_d) => todo!(),
            Instruction::CmpD(_d) => todo!(),
            Instruction::DecD(_d) => todo!(),
            Instruction::CmpDil(_dil) => todo!(),
            Instruction::Iny => {
                push(AbstractInstruction::Modify(AbstractModify {
                    op: ModifyOperation::Inc,
                    loc: ModifyLocation::Y,
                    is_long: !ctx.xf().get()?,
                }));
            }
            Instruction::CmpI(_i) => todo!(),
            Instruction::Dex => {
                push(AbstractInstruction::Modify(AbstractModify {
                    op: ModifyOperation::Dec,
                    loc: ModifyLocation::X,
                    is_long: !ctx.xf().get()?,
                }));
            }
            Instruction::Wai => todo!(),
            Instruction::CpyA(_a) => todo!(),
            Instruction::CmpA(_a) => todo!(),
            Instruction::DecA(_a) => todo!(),
            Instruction::CmpAl(_al) => todo!(),
            Instruction::Bne(label) => push(AbstractInstruction::new_bra(
                ctx,
                BranchCondition::Ne,
                label,
            )),
            Instruction::CmpDiy(_diy) => todo!(),
            Instruction::CmpDi(_di) => todo!(),
            Instruction::CmpSiy(_siy) => todo!(),
            Instruction::Pei(_di) => todo!(),
            Instruction::CmpDx(_dx) => todo!(),
            Instruction::DecDx(_dx) => todo!(),
            Instruction::CmpDily(_dily) => todo!(),
            Instruction::Cld => {
                push(AbstractInstruction::ClrFlags(pf::D));
            }
            Instruction::CmpAy(_ay) => todo!(),
            Instruction::Phx => todo!(),
            Instruction::Stp => todo!(),
            Instruction::Jmli(_indirect_long_label) => todo!(),
            Instruction::CmpAx(_ax) => todo!(),
            Instruction::DecAx(_ax) => todo!(),
            Instruction::CmpAlx(_alx) => todo!(),
            Instruction::CpxI(_i) => todo!(),
            Instruction::SbcDxi(_dxi) => todo!(),
            Instruction::Sep(val) => {
                if !val.is_empty() {
                    push(AbstractInstruction::SetFlags(val.0));
                }
            }
            Instruction::SbcS(_s) => todo!(),
            Instruction::CpxD(_d) => todo!(),
            Instruction::SbcD(_d) => todo!(),
            Instruction::IncD(_d) => todo!(),
            Instruction::SbcDil(_dil) => todo!(),
            Instruction::Inx => {
                push(AbstractInstruction::Modify(AbstractModify {
                    op: ModifyOperation::Inc,
                    loc: ModifyLocation::X,
                    is_long: !ctx.xf().get()?,
                }));
            }
            Instruction::SbcI(i) => {
                push(AbstractInstruction::new_op(OperateType::Sbc, i));
            }
            Instruction::Nop => todo!(),
            Instruction::Xba => todo!(),
            Instruction::CpxA(_a) => todo!(),
            Instruction::SbcA(_a) => todo!(),
            Instruction::IncA(_a) => todo!(),
            Instruction::SbcAl(_al) => todo!(),
            Instruction::Beq(label) => push(AbstractInstruction::new_bra(
                ctx,
                BranchCondition::Eq,
                label,
            )),
            Instruction::SbcDiy(_diy) => todo!(),
            Instruction::SbcDi(_di) => todo!(),
            Instruction::SbcSiy(_siy) => todo!(),
            Instruction::Pea(_absolute_label) => todo!(),
            Instruction::SbcDx(_dx) => todo!(),
            Instruction::IncDx(_dx) => todo!(),
            Instruction::SbcDily(_dily) => todo!(),
            Instruction::Sed => {
                push(AbstractInstruction::SetFlags(pf::D));
            }
            Instruction::SbcAy(_ay) => todo!(),
            Instruction::Plx => todo!(),
            Instruction::Xce => push(AbstractInstruction::Xce),
            Instruction::Jsrxi(_indirect_indexed_label) => todo!(),
            Instruction::SbcAx(_ax) => todo!(),
            Instruction::IncAx(_ax) => todo!(),
            Instruction::SbcAlx(_alx) => todo!(),
        }
        println!("{:x?}", block.instrs.last());
        self.cursor = self.cursor.wrapping_add(u32::from(ann.instruction.size()));
        Some(())
    }
}

impl Default for Rewriter {
    fn default() -> Self {
        Self::new()
    }
}
