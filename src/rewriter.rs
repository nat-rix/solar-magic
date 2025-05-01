use std::collections::{BTreeSet, HashMap};

use crate::{
    addr::Addr,
    addr_space::MemoryLocation,
    cart::Cart,
    disasm::{AnnotatedInstruction, Context, Disassembler},
    instruction::{
        FlagSet, Instruction, InstructionArgument, InstructionFlagDependency, InstructionType,
        NearLabel, am,
    },
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
    pub fn new_a(cart: &Cart, ctx: &Context, abs: am::A) -> Self {
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
        Self::new_al(cart, am::Al(Addr::new(bank, abs.0)))
    }

    pub fn new_ax(cart: &Cart, ctx: &Context, ax: am::Ax) -> Self {
        Self {
            ty: AccessType::Absolute(Some(IndexRegister::X)),
            ..Self::new_a(cart, ctx, am::A(ax.0))
        }
    }

    pub fn new_ay(cart: &Cart, ctx: &Context, ay: am::Ay) -> Self {
        Self {
            ty: AccessType::Absolute(Some(IndexRegister::Y)),
            ..Self::new_a(cart, ctx, am::A(ay.0))
        }
    }

    pub fn new_al(cart: &Cart, al: am::Al) -> Self {
        Self {
            ty: AccessType::Absolute(None),
            location: cart.map_full(al.0),
        }
    }

    pub fn new_alx(cart: &Cart, alx: am::Alx) -> Self {
        Self {
            ty: AccessType::Absolute(Some(IndexRegister::X)),
            ..Self::new_al(cart, am::Al(alx.0))
        }
    }

    pub fn new_d(cart: &Cart, ctx: &Context, d: am::D) -> Self {
        let addr = ctx.d.get().unwrap_or(0).wrapping_add(d.0 as _);
        Self {
            ty: AccessType::Direct(None),
            location: cart.map_full(Addr::new(0, addr)),
        }
    }

    pub fn new_dx(cart: &Cart, ctx: &Context, dx: am::Dx) -> Self {
        Self {
            ty: AccessType::Direct(Some(IndexRegister::X)),
            ..Self::new_d(cart, ctx, am::D(dx.0))
        }
    }

    pub fn new_dy(cart: &Cart, ctx: &Context, dy: am::Dy) -> Self {
        Self {
            ty: AccessType::Direct(Some(IndexRegister::Y)),
            ..Self::new_d(cart, ctx, am::D(dy.0))
        }
    }

    pub fn new_dily(cart: &Cart, ctx: &Context, dily: am::Dily) -> Self {
        Self {
            ty: AccessType::IndirectLongY,
            ..Self::new_d(cart, ctx, am::D(dily.0))
        }
    }
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
pub struct AbstractMove {
    pub src: MemoryLocation,
    pub dst: MemoryLocation,
    /// `0` means `0x10000` bytes
    pub count: u16,
    pub is_positive: bool,
}

#[derive(Debug, Clone)]
pub enum AbstractArgument {
    Access(AbstractAccess),
    Imm8(u8),
    Imm16(u16),
    CodeLabel(AbstractCodeLabel),
    Flags(FlagSet),
    Move(AbstractMove),
}

impl From<AbstractAccess> for AbstractArgument {
    fn from(value: AbstractAccess) -> Self {
        Self::Access(value)
    }
}

#[derive(Debug, Clone)]
pub struct AbstractInstruction {
    pub ty: InstructionType,
    pub arg: Option<AbstractArgument>,
    pub is_short: bool,
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
        let iter0 = disasm.vectors.iter().map(|(_, addr)| Addr::new(0, *addr));
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
        let opcode = ann.instruction.opcode();
        let opty = opcode.instr_ty();
        let orig_arg = ann.instruction.arg();
        // println!("pc: {}", ctx.pc);
        let is_short = match opty.flag_dependency() {
            None => false,
            Some(InstructionFlagDependency::M) => ctx.mf().get()?,
            Some(InstructionFlagDependency::X) => ctx.xf().get()?,
        };
        let arg = orig_arg.map(|orig_arg| {
            Some(match orig_arg {
                InstructionArgument::Signature(_) => todo!(),
                InstructionArgument::A(a) => AbstractAccess::new_a(cart, ctx, a).into(),
                InstructionArgument::Ax(ax) => AbstractAccess::new_ax(cart, ctx, ax).into(),
                InstructionArgument::Ay(ay) => AbstractAccess::new_ay(cart, ctx, ay).into(),
                InstructionArgument::Al(al) => AbstractAccess::new_al(cart, al).into(),
                InstructionArgument::Alx(alx) => AbstractAccess::new_alx(cart, alx).into(),
                InstructionArgument::D(d) => AbstractAccess::new_d(cart, ctx, d).into(),
                InstructionArgument::Dx(dx) => AbstractAccess::new_dx(cart, ctx, dx).into(),
                InstructionArgument::Dy(dy) => AbstractAccess::new_dy(cart, ctx, dy).into(),
                InstructionArgument::Dxi(_dxi) => todo!(),
                InstructionArgument::Diy(_diy) => todo!(),
                InstructionArgument::Dily(dily) => AbstractAccess::new_dily(cart, ctx, dily).into(),
                InstructionArgument::Di(_di) => todo!(),
                InstructionArgument::Dil(_dil) => todo!(),
                InstructionArgument::S(_s) => todo!(),
                InstructionArgument::Siy(_siy) => todo!(),
                InstructionArgument::I(i) => match i {
                    am::I::U8(i) => AbstractArgument::Imm8(i),
                    am::I::U16(i) => AbstractArgument::Imm16(i),
                },
                InstructionArgument::NearLabel(label) => AbstractArgument::CodeLabel(
                    AbstractCodeLabel::from_addr(cart, label.take(ctx.pc)),
                ),
                InstructionArgument::RelativeLabel(label) => AbstractArgument::CodeLabel(
                    AbstractCodeLabel::from_addr(cart, label.take(ctx.pc)),
                ),
                InstructionArgument::AbsoluteLabel(label) => AbstractArgument::CodeLabel(
                    AbstractCodeLabel::from_addr(cart, label.take(ctx.pc)),
                ),
                InstructionArgument::LongLabel(label) => {
                    AbstractArgument::CodeLabel(AbstractCodeLabel::from_addr(cart, label))
                }
                InstructionArgument::IndirectLabel(_label) => todo!(),
                InstructionArgument::IndirectIndexedLabel(_label) => todo!(),
                InstructionArgument::IndirectLongLabel(_label) => todo!(),
                InstructionArgument::Flags(flags) => AbstractArgument::Flags(flags),
                InstructionArgument::Move(dst_bank, src_bank) => {
                    let is_positive = matches!(opty, InstructionType::Mvp);
                    let count = ctx.a.get()?;
                    let src_addr = ctx.x.get()?;
                    let dst_addr = ctx.y.get()?;
                    let src = cart.map_full(Addr::new(src_bank, src_addr));
                    let dst = cart.map_full(Addr::new(dst_bank, dst_addr));
                    AbstractArgument::Move(AbstractMove {
                        src,
                        dst,
                        count,
                        is_positive,
                    })
                }
            })
        });
        let arg = match arg {
            Some(None) => return None,
            Some(Some(v)) => Some(v),
            None => None,
        };
        block.instrs.push(AbstractInstruction {
            ty: opty,
            arg,
            is_short,
        });
        // println!("{:x?}", block.instrs.last());
        *size = size.wrapping_add(u32::from(ann.instruction.size()));
        Some(())
    }
}

impl Default for Rewriter {
    fn default() -> Self {
        Self::new()
    }
}
