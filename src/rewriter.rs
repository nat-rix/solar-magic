use std::collections::{BTreeSet, HashMap};

use crate::{
    addr::Addr,
    addr_space::MemoryLocation,
    cart::Cart,
    disasm::{AnnotatedInstruction, Context, Disassembler},
    instruction::{Instruction, InstructionArgument, NearLabel, am},
    pf,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BlockId {
    start_rom_offset: u32,
}

impl BlockId {
    const fn from_off(start_rom_offset: u32) -> Self {
        Self { start_rom_offset }
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

#[derive(Debug, Clone, Copy)]
pub enum AccessType {
    Absolute(Option<IndexRegister>),
    Direct(Option<IndexRegister>),
    IndirectLongY,
}

#[derive(Debug, Clone)]
pub struct AbstractAccess {
    pub location: MemoryLocation,
    pub ty: AccessType,
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
        Self {
            ty: AccessType::Absolute(Some(IndexRegister::X)),
            ..Self::new_abs(cart, ctx, am::A(ax.0))
        }
    }

    pub fn new_absy(cart: &Cart, ctx: &Context, ay: am::Ay) -> Self {
        Self {
            ty: AccessType::Absolute(Some(IndexRegister::Y)),
            ..Self::new_abs(cart, ctx, am::A(ay.0))
        }
    }

    pub fn new_absl(cart: &Cart, al: am::Al) -> Self {
        Self {
            ty: AccessType::Absolute(None),
            location: cart.map_full(al.0),
        }
    }

    pub fn new_abslx(cart: &Cart, alx: am::Alx) -> Self {
        Self {
            ty: AccessType::Absolute(Some(IndexRegister::X)),
            ..Self::new_absl(cart, am::Al(alx.0))
        }
    }

    pub fn new_dir(cart: &Cart, ctx: &Context, d: am::D) -> Self {
        let addr = ctx.d.get().unwrap_or(0).wrapping_add(d.0 as _);
        Self {
            ty: AccessType::Direct(None),
            location: cart.map_full(Addr::new(0, addr)),
        }
    }

    pub fn new_indly(cart: &Cart, ctx: &Context, dily: am::Dily) -> Self {
        Self {
            ty: AccessType::IndirectLongY,
            ..Self::new_dir(cart, ctx, am::D(dily.0))
        }
    }
}

#[derive(Debug, Clone)]
pub struct AbstractStoreInstruction {
    pub src: StoreableRegister,
    pub dst: AbstractAccess,
    pub is8: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoadableRegister {
    A,
    X,
    Y,
}

#[derive(Debug, Clone)]
pub struct AbstractLoadInstruction {
    pub src: AbstractAccess,
    pub dst: LoadableRegister,
    pub is8: bool,
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

impl ModifyLocation {
    pub const fn is_index(&self) -> bool {
        matches!(self, Self::X | Self::Y)
    }
}

impl From<AbstractAccess> for ModifyLocation {
    fn from(value: AbstractAccess) -> Self {
        Self::Access(value)
    }
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
    Or,
    And,
    Eor,
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

impl OperateRhs {
    pub fn from_access(access: AbstractAccess, is_short: bool) -> Self {
        if is_short {
            Self::Op8(OperateRhs8::Access(access))
        } else {
            Self::Op16(OperateRhs16::Access(access))
        }
    }

    pub fn from_access_mf(ctx: &Context, access: AbstractAccess) -> Option<Self> {
        let is_short = ctx.mf().get()?;
        Some(Self::from_access(access, is_short))
    }
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

#[derive(Debug, Clone, Copy)]
pub enum CmpLhs {
    A,
    X,
    Y,
}

impl CmpLhs {
    pub const fn is_index(&self) -> bool {
        matches!(self, Self::X | Self::Y)
    }

    pub fn is_short(&self, ctx: &Context) -> Option<bool> {
        let flag = if self.is_index() { ctx.xf() } else { ctx.mf() };
        flag.get()
    }
}

#[derive(Debug, Clone)]
pub enum CompareType {
    Cmp(CmpLhs),
    Bit,
    Trb,
    Tsb,
}

impl CompareType {
    pub const fn lhs(&self) -> CmpLhs {
        match self {
            Self::Cmp(lhs) => *lhs,
            _ => CmpLhs::A,
        }
    }
}

#[derive(Debug, Clone)]
pub struct AbstractCompare {
    pub op: CompareType,
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
pub enum AbstractCodeLabel {
    Rom(BlockId),
    Addr(Addr),
}

impl AbstractCodeLabel {
    pub fn from_addr(cart: &Cart, addr: Addr) -> Self {
        cart.map_rom(addr)
            .map(BlockId::from_off)
            .map(Self::Rom)
            .unwrap_or(Self::Addr(addr))
    }
}

#[derive(Debug, Clone)]
pub struct AbstractBranch {
    pub cond: Option<BranchCondition>,
    pub label: AbstractCodeLabel,
}

#[derive(Debug, Clone)]
pub struct AbstractCall {
    pub is_long: bool,
    pub label: AbstractCodeLabel,
}

#[derive(Debug, Clone)]
pub enum AbstractPush {
    A { long: bool },
    X { long: bool },
    Y { long: bool },
    P,
    K,
    B,
}

#[derive(Debug, Clone)]
pub enum AbstractPop {
    A { long: bool },
    X { long: bool },
    Y { long: bool },
    P,
    B,
}

#[derive(Debug, Clone, Copy)]
pub struct AbstractReturn {
    pub is_long: bool,
}

#[derive(Debug, Clone)]
pub enum AbstractInstruction {
    SetFlags(u8),
    ClrFlags(u8),
    /// Store a value into address space.
    /// This does not affect flags.
    Store(AbstractStoreInstruction),
    Load(AbstractLoadInstruction),
    Transfer8(AbstractTransfer8),
    Transfer16(AbstractTransfer16),
    Modify(AbstractModify),
    OperateA(AbstractOperate),
    Compare(AbstractCompare),
    Branch(AbstractBranch),
    Call(AbstractCall),
    Push(AbstractPush),
    Pop(AbstractPop),
    Xce,
    Xba,
    Return(AbstractReturn),
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
    pub fn new_stz(ctx: &Context, dst: AbstractAccess) -> Option<Self> {
        Some(Self::Store(AbstractStoreInstruction {
            src: StoreableRegister::Zero,
            dst,
            is8: ctx.mf().get()?,
        }))
    }

    pub fn new_sta(ctx: &Context, dst: AbstractAccess) -> Option<Self> {
        Some(Self::Store(AbstractStoreInstruction {
            src: StoreableRegister::A,
            dst,
            is8: ctx.mf().get()?,
        }))
    }

    pub fn new_lda(ctx: &Context, src: AbstractAccess) -> Option<Self> {
        Some(Self::Load(AbstractLoadInstruction {
            src,
            dst: LoadableRegister::A,
            is8: ctx.mf().get()?,
        }))
    }

    pub fn new_ldy(ctx: &Context, src: AbstractAccess) -> Option<Self> {
        Some(Self::Load(AbstractLoadInstruction {
            src,
            dst: LoadableRegister::Y,
            is8: ctx.xf().get()?,
        }))
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

    pub fn new_op_mf(ctx: &Context, op: OperateType, rhs: AbstractAccess) -> Option<Self> {
        OperateRhs::from_access_mf(ctx, rhs).map(|rhs| Self::new_op(op, rhs))
    }

    pub fn new_mod(
        ctx: &Context,
        op: ModifyOperation,
        loc: impl Into<ModifyLocation>,
    ) -> Option<Self> {
        let loc = loc.into();
        let is_long = !(if loc.is_index() { ctx.xf() } else { ctx.mf() }).get()?;
        Some(Self::Modify(AbstractModify { op, loc, is_long }))
    }

    pub fn new_cmp(ctx: &Context, op: CompareType, rhs: AbstractAccess) -> Option<Self> {
        let is_short = op.lhs().is_short(ctx)?;
        Some(Self::Compare(AbstractCompare {
            op,
            rhs: OperateRhs::from_access(rhs, is_short),
        }))
    }

    pub fn new_bra(
        cart: &Cart,
        ctx: &Context,
        cond: Option<BranchCondition>,
        label: NearLabel,
    ) -> Self {
        let label = AbstractCodeLabel::from_addr(cart, label.take(ctx.pc));
        Self::Branch(AbstractBranch { cond, label })
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
    pub size: u32,
}

impl Block {
    pub const fn is_code(&self) -> bool {
        matches!(&self.content, BlockContent::Code(_))
    }
}

#[derive(Debug, Clone, Default)]
struct BlockMap {
    starts: BTreeSet<u32>,
}

impl BlockMap {
    pub fn get(&self, val: u32) -> Option<u32> {
        self.starts.range(..=val).last().copied()
    }
}

#[derive(Debug, Clone)]
pub struct Rewriter {
    blocks: HashMap<BlockId, Block>,
    block_starts: BlockMap,
}

impl Rewriter {
    pub fn new() -> Self {
        Self {
            blocks: Default::default(),
            block_starts: Default::default(),
        }
    }

    fn init_code_block_starts(&mut self, cart: &Cart, disasm: &Disassembler) {
        let iter0 = disasm.vectors.iter().map(|vec| Addr::new(0, *vec));
        let iter1 = disasm
            .unified_code_annotations
            .iter()
            .filter_map(|(addr, ann)| {
                Some(match &ann.instruction.arg() {
                    Some(InstructionArgument::NearLabel(label)) => label.take(*addr),
                    Some(InstructionArgument::RelativeLabel(label)) => label.take(*addr),
                    Some(InstructionArgument::AbsoluteLabel(label)) => label.take(*addr),
                    Some(InstructionArgument::LongLabel(label)) => *label,
                    _ => return None,
                })
            });
        let iter2 = disasm
            .jump_tables
            .iter()
            .flat_map(|(table_start, table)| {
                table
                    .known_entry_offsets
                    .iter()
                    .map(move |off| (table_start, table, *off))
            })
            .filter_map(|(table_start, table, table_off)| {
                table.offset_to_addr(cart, table_off, *table_start)
            });

        self.block_starts.starts = iter0
            .chain(iter1)
            .chain(iter2)
            .filter_map(|addr| cart.map_rom(addr))
            .collect();
    }

    pub fn rewrite(&mut self, cart: &Cart, disasm: &Disassembler) {
        self.init_code_block_starts(cart, disasm);
        for (addr, ann) in disasm.unified_code_annotations.iter() {
            let Some(off) = cart.map_rom(*addr) else {
                continue;
            };
            let Some(block_start) = self.block_starts.get(off) else {
                continue;
            };
            let block_id = BlockId {
                start_rom_offset: block_start,
            };
            let block = self.blocks.entry(block_id).or_insert_with(|| Block {
                content: BlockContent::Code(CodeBlock { instrs: vec![] }),
                size: 0,
            });
            if Self::rewrite_instr(cart, ann, block).is_none() {
                todo!()
            }
        }
    }

    fn rewrite_instr(cart: &Cart, ann: &AnnotatedInstruction, block: &mut Block) -> Option<()> {
        let ctx = &ann.pre;
        let Block {
            content: BlockContent::Code(block),
            size,
        } = block
        else {
            todo!()
        };
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
            Instruction::Php => push(AbstractInstruction::Push(AbstractPush::P)),
            Instruction::OraI(_i) => todo!(),
            Instruction::AslAc => todo!(),
            Instruction::Phd => todo!(),
            Instruction::TsbA(_a) => todo!(),
            Instruction::OraA(a) => push(AbstractInstruction::new_op_mf(
                ctx,
                OperateType::Or,
                AbstractAccess::new_abs(cart, ctx, a),
            )?),
            Instruction::AslA(_a) => todo!(),
            Instruction::OraAl(_al) => todo!(),
            Instruction::Bpl(label) => push(AbstractInstruction::new_bra(
                cart,
                ctx,
                Some(BranchCondition::Pl),
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
            Instruction::Jsr(label) => push(AbstractInstruction::Call(AbstractCall {
                is_long: false,
                label: AbstractCodeLabel::from_addr(cart, label.take(ctx.pc)),
            })),
            Instruction::AndDxi(_dxi) => todo!(),
            Instruction::Jsl(label) => push(AbstractInstruction::Call(AbstractCall {
                is_long: true,
                label: AbstractCodeLabel::from_addr(cart, label),
            })),
            Instruction::AndS(_s) => todo!(),
            Instruction::BitD(_d) => todo!(),
            Instruction::AndD(_d) => todo!(),
            Instruction::RolD(_d) => todo!(),
            Instruction::AndDil(_dil) => todo!(),
            Instruction::Plp => push(AbstractInstruction::Pop(AbstractPop::P)),
            Instruction::AndI(_i) => todo!(),
            Instruction::RolAc => push(AbstractInstruction::new_mod(
                ctx,
                ModifyOperation::Rol,
                ModifyLocation::A,
            )?),
            Instruction::Pld => todo!(),
            Instruction::BitA(_a) => todo!(),
            Instruction::AndA(_a) => todo!(),
            Instruction::RolA(_a) => todo!(),
            Instruction::AndAl(_al) => todo!(),
            Instruction::Bmi(label) => push(AbstractInstruction::new_bra(
                cart,
                ctx,
                Some(BranchCondition::Mi),
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
            Instruction::Pha => push(AbstractInstruction::Push(AbstractPush::A {
                long: !ctx.mf().get()?,
            })),
            Instruction::EorI(_i) => todo!(),
            Instruction::LsrAc => todo!(),
            Instruction::Phk => push(AbstractInstruction::Push(AbstractPush::K)),
            Instruction::Jmp(label) => push(AbstractInstruction::Branch(AbstractBranch {
                cond: None,
                label: AbstractCodeLabel::from_addr(cart, label.take(ctx.pc)),
            })),
            Instruction::EorA(_a) => todo!(),
            Instruction::LsrA(_a) => todo!(),
            Instruction::EorAl(_al) => todo!(),
            Instruction::Bvc(label) => push(AbstractInstruction::new_bra(
                cart,
                ctx,
                Some(BranchCondition::Vc),
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
            Instruction::Phy => push(AbstractInstruction::Push(AbstractPush::Y {
                long: !ctx.xf().get()?,
            })),
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
            Instruction::Rts => push(AbstractInstruction::Return(AbstractReturn {
                is_long: false,
            })),
            Instruction::AdcDxi(_dxi) => todo!(),
            Instruction::Per(_relative_label) => todo!(),
            Instruction::AdcS(_s) => todo!(),
            Instruction::StzD(d) => {
                let dst = AbstractAccess::new_dir(cart, ctx, d);
                push(AbstractInstruction::new_stz(ctx, dst)?);
            }
            Instruction::AdcD(_d) => todo!(),
            Instruction::RorD(_d) => todo!(),
            Instruction::AdcDil(_dil) => todo!(),
            Instruction::Pla => push(AbstractInstruction::Pop(AbstractPop::A {
                long: !ctx.mf().get()?,
            })),
            Instruction::AdcI(i) => {
                push(AbstractInstruction::new_op(OperateType::Adc, i));
            }
            Instruction::RorAc => push(AbstractInstruction::new_mod(
                ctx,
                ModifyOperation::Ror,
                ModifyLocation::A,
            )?),
            Instruction::Rtl => push(AbstractInstruction::Return(AbstractReturn {
                is_long: true,
            })),
            Instruction::Jmpi(_indirect_label) => todo!(),
            Instruction::AdcA(_a) => todo!(),
            Instruction::RorA(_a) => todo!(),
            Instruction::AdcAl(_al) => todo!(),
            Instruction::Bvs(label) => push(AbstractInstruction::new_bra(
                cart,
                ctx,
                Some(BranchCondition::Vs),
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
            Instruction::Bra(label) => push(AbstractInstruction::new_bra(cart, ctx, None, label)),
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
            Instruction::Phb => push(AbstractInstruction::Push(AbstractPush::B)),
            Instruction::StyA(_a) => todo!(),
            Instruction::StaA(a) => {
                let dst = AbstractAccess::new_abs(cart, ctx, a);
                push(AbstractInstruction::new_sta(ctx, dst)?);
            }
            Instruction::StxA(_a) => todo!(),
            Instruction::StaAl(al) => {
                let dst = AbstractAccess::new_absl(cart, al);
                push(AbstractInstruction::new_sta(ctx, dst)?);
            }
            Instruction::Bcc(label) => push(AbstractInstruction::new_bra(
                cart,
                ctx,
                Some(BranchCondition::Cc),
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
                push(AbstractInstruction::new_sta(ctx, dst)?);
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
                push(AbstractInstruction::new_stz(ctx, dst)?);
            }
            Instruction::StaAx(ax) => {
                let dst = AbstractAccess::new_absx(cart, ctx, ax);
                push(AbstractInstruction::new_sta(ctx, dst)?);
            }
            Instruction::StzAx(ax) => {
                let dst = AbstractAccess::new_absx(cart, ctx, ax);
                push(AbstractInstruction::new_stz(ctx, dst)?);
            }
            Instruction::StaAlx(alx) => {
                let dst = AbstractAccess::new_abslx(cart, alx);
                push(AbstractInstruction::new_sta(ctx, dst)?);
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
            Instruction::LdaD(d) => push(AbstractInstruction::new_lda(
                ctx,
                AbstractAccess::new_dir(cart, ctx, d),
            )?),
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
            Instruction::Plb => push(AbstractInstruction::Pop(AbstractPop::B)),
            Instruction::LdyA(a) => push(AbstractInstruction::new_ldy(
                ctx,
                AbstractAccess::new_abs(cart, ctx, a),
            )?),
            Instruction::LdaA(a) => push(AbstractInstruction::new_lda(
                ctx,
                AbstractAccess::new_abs(cart, ctx, a),
            )?),
            Instruction::LdxA(_a) => todo!(),
            Instruction::LdaAl(al) => push(AbstractInstruction::new_lda(
                ctx,
                AbstractAccess::new_absl(cart, al),
            )?),
            Instruction::Bcs(label) => push(AbstractInstruction::new_bra(
                cart,
                ctx,
                Some(BranchCondition::Cs),
                label,
            )),
            Instruction::LdaDiy(_diy) => todo!(),
            Instruction::LdaDi(_di) => todo!(),
            Instruction::LdaSiy(_siy) => todo!(),
            Instruction::LdyDx(_dx) => todo!(),
            Instruction::LdaDx(_dx) => todo!(),
            Instruction::LdxDy(_dy) => todo!(),
            Instruction::LdaDily(dily) => push(AbstractInstruction::new_lda(
                ctx,
                AbstractAccess::new_indly(cart, ctx, dily),
            )?),
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
            Instruction::CpyI(i) => push(AbstractInstruction::Compare(AbstractCompare {
                op: CompareType::Cmp(CmpLhs::Y),
                rhs: i.into(),
            })),
            Instruction::CmpDxi(_dxi) => todo!(),
            Instruction::Rep(val) => {
                if !val.is_empty() {
                    push(AbstractInstruction::ClrFlags(val.0));
                }
            }
            Instruction::CmpS(_s) => todo!(),
            Instruction::CpyD(_d) => todo!(),
            Instruction::CmpD(_d) => todo!(),
            Instruction::DecD(d) => {
                push(AbstractInstruction::new_mod(
                    ctx,
                    ModifyOperation::Dec,
                    AbstractAccess::new_dir(cart, ctx, d),
                )?);
            }
            Instruction::CmpDil(_dil) => todo!(),
            Instruction::Iny => {
                push(AbstractInstruction::Modify(AbstractModify {
                    op: ModifyOperation::Inc,
                    loc: ModifyLocation::Y,
                    is_long: !ctx.xf().get()?,
                }));
            }
            Instruction::CmpI(i) => push(AbstractInstruction::Compare(AbstractCompare {
                op: CompareType::Cmp(CmpLhs::X),
                rhs: i.into(),
            })),
            Instruction::Dex => {
                push(AbstractInstruction::Modify(AbstractModify {
                    op: ModifyOperation::Dec,
                    loc: ModifyLocation::X,
                    is_long: !ctx.xf().get()?,
                }));
            }
            Instruction::Wai => todo!(),
            Instruction::CpyA(a) => push(AbstractInstruction::new_cmp(
                ctx,
                CompareType::Cmp(CmpLhs::Y),
                AbstractAccess::new_abs(cart, ctx, a),
            )?),
            Instruction::CmpA(a) => push(AbstractInstruction::new_cmp(
                ctx,
                CompareType::Cmp(CmpLhs::A),
                AbstractAccess::new_abs(cart, ctx, a),
            )?),
            Instruction::DecA(_a) => todo!(),
            Instruction::CmpAl(_al) => todo!(),
            Instruction::Bne(label) => push(AbstractInstruction::new_bra(
                cart,
                ctx,
                Some(BranchCondition::Ne),
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
            Instruction::Phx => push(AbstractInstruction::Push(AbstractPush::X {
                long: !ctx.xf().get()?,
            })),
            Instruction::Stp => todo!(),
            Instruction::Jmli(_indirect_long_label) => todo!(),
            Instruction::CmpAx(_ax) => todo!(),
            Instruction::DecAx(_ax) => todo!(),
            Instruction::CmpAlx(_alx) => todo!(),
            Instruction::CpxI(i) => push(AbstractInstruction::Compare(AbstractCompare {
                op: CompareType::Cmp(CmpLhs::X),
                rhs: i.into(),
            })),
            Instruction::SbcDxi(_dxi) => todo!(),
            Instruction::Sep(val) => {
                if !val.is_empty() {
                    push(AbstractInstruction::SetFlags(val.0));
                }
            }
            Instruction::SbcS(_s) => todo!(),
            Instruction::CpxD(_d) => todo!(),
            Instruction::SbcD(_d) => todo!(),
            Instruction::IncD(d) => {
                push(AbstractInstruction::new_mod(
                    ctx,
                    ModifyOperation::Inc,
                    AbstractAccess::new_dir(cart, ctx, d),
                )?);
            }
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
            Instruction::Xba => push(AbstractInstruction::Xba),
            Instruction::CpxA(a) => push(AbstractInstruction::new_cmp(
                ctx,
                CompareType::Cmp(CmpLhs::X),
                AbstractAccess::new_abs(cart, ctx, a),
            )?),
            Instruction::SbcA(_a) => todo!(),
            Instruction::IncA(_a) => todo!(),
            Instruction::SbcAl(_al) => todo!(),
            Instruction::Beq(label) => push(AbstractInstruction::new_bra(
                cart,
                ctx,
                Some(BranchCondition::Eq),
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
        *size = size.wrapping_add(u32::from(ann.instruction.size()));
        Some(())
    }
}

impl Default for Rewriter {
    fn default() -> Self {
        Self::new()
    }
}
