use std::collections::BTreeMap;

use crate::{
    addr::Addr,
    addr_space::MemoryLocation,
    cart::Cart,
    disasm::{AnnotatedInstruction, Context, Disassembler},
    instruction::{FlagSet, InstructionArgument, InstructionFlagDependency, InstructionType, am},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BlockId {
    start_rom_offset: u32,
}

impl BlockId {
    const fn from_off(start_rom_offset: u32) -> Self {
        Self { start_rom_offset }
    }

    pub const fn get_offset(&self) -> u32 {
        self.start_rom_offset
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IndexRegister {
    X,
    Y,
}

impl core::fmt::Display for IndexRegister {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::X => f.write_str("X"),
            Self::Y => f.write_str("Y"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum AccessType {
    Absolute(Option<IndexRegister>),
    Direct(Option<IndexRegister>),
    Indirect,
    IndirectY,
    IndirectLong,
    IndirectLongY,
}

impl AccessType {
    pub const fn index_register(&self) -> Option<IndexRegister> {
        match self {
            AccessType::Absolute(ix) | AccessType::Direct(ix) => *ix,
            AccessType::IndirectY | AccessType::IndirectLongY => Some(IndexRegister::Y),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub enum AbstractLabel {
    Block(BlockId),
    Location(MemoryLocation),
}

impl AbstractLabel {
    pub fn from_location(location: MemoryLocation) -> Self {
        if let Some(off) = location.rom_offset() {
            Self::Block(BlockId::from_off(off))
        } else {
            Self::Location(location)
        }
    }

    pub fn from_addr(cart: &Cart, addr: Addr) -> Self {
        Self::from_location(cart.map_full(addr))
    }

    pub const fn rom_offset(&self) -> Option<u32> {
        match self {
            Self::Block(id) => Some(id.start_rom_offset),
            Self::Location(loc) => loc.rom_offset(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct AbstractAccess {
    pub label: AbstractLabel,
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
            label: AbstractLabel::from_addr(cart, al.0),
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
            label: AbstractLabel::from_addr(cart, Addr::new(0, addr)),
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

    pub fn new_di(cart: &Cart, ctx: &Context, di: am::Di) -> Self {
        Self {
            ty: AccessType::Indirect,
            ..Self::new_d(cart, ctx, am::D(di.0))
        }
    }

    pub fn new_diy(cart: &Cart, ctx: &Context, diy: am::Diy) -> Self {
        Self {
            ty: AccessType::IndirectY,
            ..Self::new_d(cart, ctx, am::D(diy.0))
        }
    }

    pub fn new_dil(cart: &Cart, ctx: &Context, dil: am::Dil) -> Self {
        Self {
            ty: AccessType::IndirectLong,
            ..Self::new_d(cart, ctx, am::D(dil.0))
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
    Direct(AbstractLabel),
    IndirectLong(AbstractLabel),
}

impl AbstractCodeLabel {
    pub fn new_direct(cart: &Cart, addr: Addr) -> Self {
        Self::Direct(AbstractLabel::from_addr(cart, addr))
    }
}

#[derive(Debug, Clone)]
pub struct AbstractMove {
    pub src: Option<AbstractLabel>,
    pub dst: Option<AbstractLabel>,
    /// `0` means `0x10000` bytes
    pub count: Option<u16>,
    pub is_positive: bool,
}

#[derive(Debug, Clone)]
pub enum AbstractArgument {
    Signature(u8),
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
    pub is_short: Option<bool>,
    pub original_offset: Option<u32>,
}

#[derive(Debug, Clone)]
pub struct CodeBlock {
    instrs: Vec<AbstractInstruction>,
}

impl CodeBlock {
    pub fn instrs(&self) -> &[AbstractInstruction] {
        &self.instrs
    }

    pub const fn instrs_mut(&mut self) -> &mut Vec<AbstractInstruction> {
        &mut self.instrs
    }
}

#[derive(Debug, Clone)]
pub enum PointerType {
    Ptr16,
    Ptr24,
}

#[derive(Debug, Clone)]
pub enum PrimitiveDataType {
    U8,
    U16,
    Pointer(PointerType),
}

#[derive(Debug, Clone)]
pub enum DataType {
    Primitive(PrimitiveDataType),
    Array(PrimitiveDataType),
}

#[derive(Debug, Clone)]
pub struct DataBlock {
    pub data_type: DataType,
}

#[derive(Debug, Clone)]
pub enum BlockContent {
    Code(CodeBlock),
    Data(DataBlock),
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum PrimitiveSize {
    U8,
    U16,
    U24,
}

impl PrimitiveSize {
    pub const fn bits(&self) -> u8 {
        match self {
            Self::U8 => 8,
            Self::U16 => 16,
            Self::U24 => 24,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum AccessSize {
    Primitive(PrimitiveSize),
    Block(Option<u16>),
}

impl AccessSize {
    pub fn bits(&self) -> usize {
        match self {
            Self::Primitive(p) => p.bits().into(),
            Self::Block(bytes) => bytes.map(|val| val as usize * 8).unwrap_or(0),
        }
    }
}

#[derive(Debug, Clone)]
pub struct DirectDatarefAccess {
    pub indexed: Option<IndexRegister>,
    pub size: AccessSize,
}

#[derive(Debug, Clone)]
pub enum SimpleDatarefIndirection {
    Data(DirectDatarefAccess),
    Code,
}

#[derive(Debug, Clone)]
pub struct SimpleDataref {
    pub access: DirectDatarefAccess,
    pub indirect: Option<SimpleDatarefIndirection>,
    pub offset: u32,
}

pub struct DatatypeDescription<'a, F>(&'a DirectDatarefAccess, F);

impl<'a, F: Fn(&mut core::fmt::Formatter) -> core::fmt::Result> core::fmt::Display
    for DatatypeDescription<'a, F>
{
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        if let AccessSize::Block(size) = self.0.size {
            return if let Some(size) = size {
                write!(f, "Block of {size} bytes")
            } else {
                write!(f, "Block of an unknown amount of bytes")
            };
        }
        if self.0.indexed.is_some() {
            write!(f, "Array of ")?;
        }
        write!(f, "{}-bit ", self.0.size.bits())?;
        self.1(f)?;
        if self.0.indexed.is_some() {
            write!(f, "s")?;
        }
        Ok(())
    }
}

impl SimpleDataref {
    pub fn description(&self) -> impl core::fmt::Display {
        DatatypeDescription(&self.access, |f: &mut core::fmt::Formatter| {
            match &self.indirect {
                Some(SimpleDatarefIndirection::Data(data)) => write!(
                    f,
                    "{}",
                    DatatypeDescription(data, |f: &mut core::fmt::Formatter| write!(f, "integer"),)
                ),
                Some(SimpleDatarefIndirection::Code) => write!(f, "function pointer"),
                None => write!(f, "integer"),
            }
        })
    }
}

#[derive(Debug, Clone)]
pub struct Rewriter {
    pub blocks: BTreeMap<BlockId, Block>,
    pub simple_datarefs: BTreeMap<u32, Vec<SimpleDataref>>,
}

impl Rewriter {
    pub fn new() -> Self {
        Self {
            blocks: Default::default(),
            simple_datarefs: Default::default(),
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

        self.blocks = iter0
            .chain(iter1)
            .chain(iter2)
            .filter_map(|addr| cart.map_rom(addr))
            .map(|off| {
                (
                    BlockId::from_off(off),
                    Block {
                        content: BlockContent::Code(CodeBlock { instrs: vec![] }),
                        size: 0,
                    },
                )
            })
            .collect();
    }

    pub fn rewrite(&mut self, cart: &Cart, disasm: &Disassembler) {
        self.init_code_block_starts(cart, disasm);
        for (addr, ann) in disasm.unified_code_annotations.iter() {
            let Some(off) = cart.map_rom(*addr) else {
                continue;
            };
            let Some((_block_id, block)) = self.blocks.range_mut(..=BlockId::from_off(off)).last()
            else {
                continue;
            };
            if Self::rewrite_instr(cart, ann, block, off).is_none() {
                todo!()
            }
        }
        for (id, block) in self.blocks.iter() {
            let instr_offset = id.start_rom_offset;
            let BlockContent::Code(block) = &block.content else {
                continue;
            };
            for instr in &block.instrs {
                if let Some((dataref, data_offset)) =
                    self.extract_simple_dataref(instr, instr_offset)
                {
                    self.simple_datarefs
                        .entry(data_offset)
                        .or_default()
                        .push(dataref);
                }
            }
        }
        let mut contiguous: u32 = 0;
        for (data_offset, drefs) in self.simple_datarefs.iter().rev() {
            if self
                .simple_datarefs
                .contains_key(&data_offset.wrapping_sub(1))
            {
                contiguous = contiguous.wrapping_add(1);
                continue;
            }
            let ty = self.get_dref_data_type(drefs, contiguous);
            let block_id = self
                .blocks
                .range(BlockId::from_off(*data_offset)..)
                .next()
                .map(|(id, _)| *id);
            let end = if let Some(block_id) = block_id {
                block_id.start_rom_offset
            } else {
                cart.rom.len()
            };
            let size = end.wrapping_sub(*data_offset);
            self.blocks.insert(
                BlockId::from_off(*data_offset),
                Block {
                    content: BlockContent::Data(DataBlock { data_type: ty }),
                    size,
                },
            );
        }
    }

    fn get_dref_data_type(&self, drefs: &[SimpleDataref], contiguous: u32) -> DataType {
        let pointer = drefs.iter().find_map(|dref| {
            dref.indirect.as_ref().map(|_ind| match dref.access.size {
                AccessSize::Primitive(PrimitiveSize::U24) => PointerType::Ptr24,
                _ => PointerType::Ptr16,
            })
        });
        if let Some(pointer) = pointer {
            return DataType::Primitive(PrimitiveDataType::Pointer(pointer));
        }
        let ty = match contiguous {
            1 => PrimitiveDataType::U8,
            2 => PrimitiveDataType::U16,
            3 => PrimitiveDataType::Pointer(PointerType::Ptr24),
            _ => return DataType::Array(PrimitiveDataType::U8),
        };
        let indexed = drefs.iter().find_map(|dref| dref.access.indexed).is_some();
        if indexed {
            DataType::Array(ty)
        } else {
            DataType::Primitive(ty)
        }
    }

    fn extract_simple_dataref(
        &self,
        instr: &AbstractInstruction,
        offset: u32,
    ) -> Option<(SimpleDataref, u32)> {
        let size = AccessSize::Primitive(if instr.is_short.unwrap_or(false) {
            PrimitiveSize::U8
        } else {
            PrimitiveSize::U16
        });
        Some(match instr.arg.as_ref()? {
            AbstractArgument::Access(access) => {
                let data_offset = access.label.rom_offset()?;
                (
                    match access.ty {
                        AccessType::Absolute(indexed) | AccessType::Direct(indexed) => {
                            SimpleDataref {
                                access: DirectDatarefAccess { indexed, size },
                                indirect: None,
                                offset,
                            }
                        }
                        arg @ (AccessType::Indirect | AccessType::IndirectY) => SimpleDataref {
                            access: DirectDatarefAccess {
                                indexed: None,
                                size: AccessSize::Primitive(PrimitiveSize::U16),
                            },
                            indirect: Some(SimpleDatarefIndirection::Data(DirectDatarefAccess {
                                indexed: arg.index_register(),
                                size,
                            })),
                            offset,
                        },
                        arg @ (AccessType::IndirectLong | AccessType::IndirectLongY) => {
                            SimpleDataref {
                                access: DirectDatarefAccess {
                                    indexed: None,
                                    size: AccessSize::Primitive(PrimitiveSize::U24),
                                },
                                indirect: Some(SimpleDatarefIndirection::Data(
                                    DirectDatarefAccess {
                                        indexed: arg.index_register(),
                                        size,
                                    },
                                )),
                                offset,
                            }
                        }
                    },
                    data_offset,
                )
            }
            AbstractArgument::CodeLabel(AbstractCodeLabel::IndirectLong(loc)) => {
                let data_offset = loc.rom_offset()?;
                (
                    SimpleDataref {
                        access: DirectDatarefAccess {
                            indexed: None,
                            size: AccessSize::Primitive(PrimitiveSize::U24),
                        },
                        indirect: Some(SimpleDatarefIndirection::Code),
                        offset,
                    },
                    data_offset,
                )
            }
            AbstractArgument::Move(mv) => {
                let data_offset = mv.src.as_ref()?.rom_offset()?;
                (
                    SimpleDataref {
                        access: DirectDatarefAccess {
                            indexed: None,
                            size: AccessSize::Block(mv.count),
                        },
                        indirect: None,
                        offset,
                    },
                    data_offset,
                )
            }
            _ => return None,
        })
    }

    fn rewrite_instr(
        cart: &Cart,
        ann: &AnnotatedInstruction,
        block: &mut Block,
        original_offset: u32,
    ) -> Option<()> {
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
        let is_short = match opty.flag_dependency() {
            None => Some(false),
            Some(InstructionFlagDependency::M) => ctx.mf().get(),
            Some(InstructionFlagDependency::X) => ctx.xf().get(),
        };
        let arg = orig_arg.map(|orig_arg| {
            Some(match orig_arg {
                InstructionArgument::Signature(sig) => AbstractArgument::Signature(sig),
                InstructionArgument::A(a) => AbstractAccess::new_a(cart, ctx, a).into(),
                InstructionArgument::Ax(ax) => AbstractAccess::new_ax(cart, ctx, ax).into(),
                InstructionArgument::Ay(ay) => AbstractAccess::new_ay(cart, ctx, ay).into(),
                InstructionArgument::Al(al) => AbstractAccess::new_al(cart, al).into(),
                InstructionArgument::Alx(alx) => AbstractAccess::new_alx(cart, alx).into(),
                InstructionArgument::D(d) => AbstractAccess::new_d(cart, ctx, d).into(),
                InstructionArgument::Dx(dx) => AbstractAccess::new_dx(cart, ctx, dx).into(),
                InstructionArgument::Dy(dy) => AbstractAccess::new_dy(cart, ctx, dy).into(),
                InstructionArgument::Dxi(_dxi) => todo!(),
                InstructionArgument::Diy(diy) => AbstractAccess::new_diy(cart, ctx, diy).into(),
                InstructionArgument::Dily(dily) => AbstractAccess::new_dily(cart, ctx, dily).into(),
                InstructionArgument::Di(di) => AbstractAccess::new_di(cart, ctx, di).into(),
                InstructionArgument::Dil(dil) => AbstractAccess::new_dil(cart, ctx, dil).into(),
                InstructionArgument::S(_s) => todo!(),
                InstructionArgument::Siy(_siy) => todo!(),
                InstructionArgument::I(i) => match i {
                    am::I::U8(i) => AbstractArgument::Imm8(i),
                    am::I::U16(i) => AbstractArgument::Imm16(i),
                },
                InstructionArgument::NearLabel(label) => AbstractArgument::CodeLabel(
                    AbstractCodeLabel::new_direct(cart, label.take(ctx.pc)),
                ),
                InstructionArgument::RelativeLabel(label) => AbstractArgument::CodeLabel(
                    AbstractCodeLabel::new_direct(cart, label.take(ctx.pc)),
                ),
                InstructionArgument::AbsoluteLabel(label) => AbstractArgument::CodeLabel(
                    AbstractCodeLabel::new_direct(cart, label.take(ctx.pc)),
                ),
                InstructionArgument::LongLabel(label) => {
                    AbstractArgument::CodeLabel(AbstractCodeLabel::new_direct(cart, label))
                }
                InstructionArgument::IndirectLabel(_label) => todo!(),
                InstructionArgument::IndirectIndexedLabel(_label) => todo!(),
                InstructionArgument::IndirectLongLabel(label) => {
                    let label = AbstractLabel::from_addr(cart, Addr::new(0, label.0));
                    AbstractArgument::CodeLabel(AbstractCodeLabel::IndirectLong(label))
                }
                InstructionArgument::Flags(flags) => AbstractArgument::Flags(flags),
                InstructionArgument::Move(dst_bank, src_bank) => {
                    let is_positive = matches!(opty, InstructionType::Mvp);
                    let count = ctx.a.get();
                    let [src, dst] = [(src_bank, ctx.x), (dst_bank, ctx.y)].map(|(b, x)| {
                        x.get()
                            .map(|x| AbstractLabel::from_addr(cart, Addr::new(b, x)))
                    });
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
            original_offset: Some(original_offset),
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
