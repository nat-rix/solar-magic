use eframe::egui;
use solar_magic::{
    addr::Addr,
    analyzer::AnnotatedInstruction,
    instruction::{Instruction, InstructionArgument, InstructionNamingConvention, OpCode},
    tvl::TU24,
};

use crate::project::Project;

const SCROLL_SPEED_FACTOR: f32 = 0.1;

const DISASM_COLOR_INSTR: egui::Color32 = crate::theme::rgba(0x179299ff);
const DISASM_COLOR_ABSOLUTE: egui::Color32 = crate::theme::rgba(0xe64553ff);
const DISASM_COLOR_DIRECT: egui::Color32 = crate::theme::rgba(0x8839efff);
const DISASM_COLOR_INDEX: egui::Color32 = crate::theme::rgba(0xdf8e1dff);
const DISASM_COLOR_INDIRECT: egui::Color32 = crate::theme::rgba(0xfe640bff);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Lit {
    U8(u8),
    U16(u16),
    U24(Addr),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Idx {
    X,
    Y,
    S,
}

impl From<u8> for Lit {
    fn from(value: u8) -> Self {
        Self::U8(value)
    }
}

impl From<u16> for Lit {
    fn from(value: u16) -> Self {
        Self::U16(value)
    }
}

impl From<Addr> for Lit {
    fn from(value: Addr) -> Self {
        Self::U24(value)
    }
}

pub struct DisassemblyView {
    start_addr: Addr,
    scroll_offset: f32,
}

impl DisassemblyView {
    pub fn new() -> Self {
        Self {
            start_addr: Addr::new(0, 0x8000),
            scroll_offset: 0.0,
        }
    }

    fn show_grid(&mut self, project: &Project, ui: &mut egui::Ui) {
        if ui.ui_contains_pointer() {
            let scroll_speed = ui.ctx().options(|opt| opt.line_scroll_speed) * SCROLL_SPEED_FACTOR;
            let delta =
                ui.input_mut(|inp| core::mem::take(&mut inp.smooth_scroll_delta.y)) * scroll_speed;
            self.scroll_offset -= delta;
            if self.scroll_offset < -1.0 {
                let steps = -self.scroll_offset as u32;
                self.scroll_offset += steps as f32;
                self.start_addr = self.start_addr.sub24(steps);
            } else if self.scroll_offset > 1.0 {
                let steps = self.scroll_offset as u32;
                self.scroll_offset -= steps as f32;
                self.start_addr = self.start_addr.add24(steps);
            }
        }

        ui.with_layout(egui::Layout::top_down_justified(egui::Align::Min), |ui| {
            egui::Grid::new("disassembly-grid")
                .num_columns(4)
                .striped(true)
                .show(ui, |ui| {
                    self.show_grid_content(project, ui);
                });
        });
    }

    fn show_byte(project: &Project, addr: Addr, ui: &mut egui::Ui) {
        if let Some(byte) = project.smw.cart.read_rom(addr) {
            ui.monospace(format!("{byte:02x}"));
        } else {
            ui.monospace("??");
        }
    }

    fn show_bytes(project: &Project, iter: impl IntoIterator<Item = Addr>, ui: &mut egui::Ui) {
        ui.horizontal(|ui| {
            for i in iter {
                Self::show_byte(project, i, ui);
            }
        });
    }

    fn show_grid_content(&mut self, project: &Project, ui: &mut egui::Ui) {
        ui.expand_to_include_rect(ui.clip_rect());
        let mut addr = self.start_addr;
        loop {
            if !ui.is_rect_visible(ui.cursor()) {
                break;
            }

            ui.label(egui::RichText::new(addr.to_string()).monospace().weak());

            let opt_annotation = project
                .analyzer
                .code_annotations
                .get(&addr)
                .and_then(|v| v.iter().min_by_key(|(k, _)| k.len()));
            if let Some((_call_stack, instr)) = opt_annotation {
                let opcode = instr.instruction.opcode();
                let instr_size = instr.instruction.size();
                let arg = instr.instruction.arg();

                Self::show_bytes(project, (0..instr_size).map(|i| addr.add16(i.into())), ui);

                self.show_instr(arg, opcode, ui);

                self.show_helpers(project, instr, arg, addr, ui);

                addr = addr.add24(instr_size.into());
            } else {
                Self::show_bytes(project, [addr], ui);
                ui.label("<data byte>");
                addr = addr.add24(1);
            }
            ui.end_row();
        }
    }

    fn show_instr_lit_helper(lit: Lit, prefix: impl Into<String>, ui: &mut egui::Ui) {
        let (color, lit) = match lit {
            Lit::U8(lit) => (DISASM_COLOR_DIRECT, format!("{lit:02x}")),
            Lit::U16(lit) => (DISASM_COLOR_ABSOLUTE, format!("{lit:04x}")),
            Lit::U24(lit) => (DISASM_COLOR_ABSOLUTE, lit.to_string()),
        };
        ui.horizontal(|ui| {
            ui.monospace(prefix.into());
            ui.colored_label(color, egui::RichText::new(lit).monospace());
        });
    }

    fn show_instr_lit(lit: impl Into<Lit>, ui: &mut egui::Ui) {
        Self::show_instr_lit_helper(lit.into(), "$", ui);
    }

    fn show_instr_imm(lit: impl Into<Lit>, ui: &mut egui::Ui) {
        Self::show_instr_lit_helper(lit.into(), "#$", ui);
    }

    fn show_instr_mv(s: u8, d: u8, ui: &mut egui::Ui) {
        ui.horizontal(|ui| {
            Self::show_instr_lit(s, ui);
            ui.monospace("");
            Self::show_instr_lit(d, ui);
        });
    }

    fn show_instr_idx(idx: Idx, ui: &mut egui::Ui, f: impl FnOnce(&mut egui::Ui)) {
        let idx = match idx {
            Idx::X => ",x",
            Idx::Y => ",y",
            Idx::S => ",s",
        };
        ui.horizontal(|ui| {
            f(ui);
            ui.colored_label(DISASM_COLOR_INDEX, egui::RichText::new(idx).monospace());
        });
    }

    fn show_instr_ind(is_long: bool, ui: &mut egui::Ui, f: impl FnOnce(&mut egui::Ui)) {
        let (x, y) = if is_long { ("(", ")") } else { ("[", "]") };
        let [x, y] = [x, y].map(|i| egui::RichText::new(i).monospace());
        ui.horizontal(|ui| {
            ui.colored_label(DISASM_COLOR_INDIRECT, x);
            f(ui);
            ui.colored_label(DISASM_COLOR_INDIRECT, y);
        });
    }

    fn show_instr(&mut self, arg: Option<InstructionArgument>, opcode: OpCode, ui: &mut egui::Ui) {
        let name = opcode.name(InstructionNamingConvention::Descriptive);
        ui.horizontal(|ui| {
            ui.colored_label(DISASM_COLOR_INSTR, egui::RichText::new(name).monospace());
            ui.spacing_mut().item_spacing.x = 1.0;
            match arg {
                Some(InstructionArgument::Signature(a)) => Self::show_instr_imm(a, ui),
                Some(InstructionArgument::A(a)) => Self::show_instr_lit(a.0, ui),
                Some(InstructionArgument::Ax(a)) => {
                    Self::show_instr_idx(Idx::X, ui, |ui| Self::show_instr_lit(a.0, ui))
                }
                Some(InstructionArgument::Ay(a)) => {
                    Self::show_instr_idx(Idx::Y, ui, |ui| Self::show_instr_lit(a.0, ui))
                }
                Some(InstructionArgument::Al(a)) => Self::show_instr_lit(a.0, ui),
                Some(InstructionArgument::Alx(a)) => {
                    Self::show_instr_idx(Idx::X, ui, |ui| Self::show_instr_lit(a.0, ui))
                }
                Some(InstructionArgument::D(a)) => Self::show_instr_lit(a.0, ui),
                Some(InstructionArgument::Dx(a)) => {
                    Self::show_instr_idx(Idx::X, ui, |ui| Self::show_instr_lit(a.0, ui))
                }
                Some(InstructionArgument::Dy(a)) => {
                    Self::show_instr_idx(Idx::Y, ui, |ui| Self::show_instr_lit(a.0, ui))
                }
                Some(InstructionArgument::Dxi(a)) => Self::show_instr_ind(false, ui, |ui| {
                    Self::show_instr_idx(Idx::X, ui, |ui| Self::show_instr_lit(a.0, ui))
                }),
                Some(InstructionArgument::Diy(a)) => Self::show_instr_idx(Idx::Y, ui, |ui| {
                    Self::show_instr_ind(false, ui, |ui| Self::show_instr_lit(a.0, ui))
                }),
                Some(InstructionArgument::Dily(a)) => Self::show_instr_idx(Idx::Y, ui, |ui| {
                    Self::show_instr_ind(true, ui, |ui| Self::show_instr_lit(a.0, ui))
                }),
                Some(InstructionArgument::Di(a)) => {
                    Self::show_instr_ind(false, ui, |ui| Self::show_instr_lit(a.0, ui))
                }
                Some(InstructionArgument::Dil(a)) => {
                    Self::show_instr_ind(true, ui, |ui| Self::show_instr_lit(a.0, ui))
                }
                Some(InstructionArgument::S(a)) => {
                    Self::show_instr_idx(Idx::S, ui, |ui| Self::show_instr_lit(a.0, ui))
                }
                Some(InstructionArgument::Siy(a)) => Self::show_instr_idx(Idx::Y, ui, |ui| {
                    Self::show_instr_ind(false, ui, |ui| {
                        Self::show_instr_idx(Idx::S, ui, |ui| Self::show_instr_lit(a.0, ui))
                    })
                }),
                Some(InstructionArgument::I(a)) => Self::show_instr_imm(
                    match a {
                        solar_magic::instruction::am::I::U8(v) => Lit::U8(v),
                        solar_magic::instruction::am::I::U16(v) => Lit::U16(v),
                    },
                    ui,
                ),
                Some(InstructionArgument::NearLabel(a)) => Self::show_instr_lit(a.0, ui),
                Some(InstructionArgument::RelativeLabel(a)) => Self::show_instr_lit(a.0, ui),
                Some(InstructionArgument::AbsoluteLabel(a)) => Self::show_instr_lit(a.0, ui),
                Some(InstructionArgument::LongLabel(a)) => Self::show_instr_lit(a, ui),
                Some(InstructionArgument::IndirectLabel(a)) => {
                    Self::show_instr_ind(false, ui, |ui| Self::show_instr_lit(a.0, ui))
                }
                Some(InstructionArgument::IndirectIndexedLabel(a)) => {
                    Self::show_instr_ind(false, ui, |ui| {
                        Self::show_instr_idx(Idx::X, ui, |ui| Self::show_instr_lit(a.0, ui))
                    })
                }
                Some(InstructionArgument::IndirectLongLabel(a)) => {
                    Self::show_instr_ind(true, ui, |ui| Self::show_instr_lit(a.0, ui))
                }
                Some(InstructionArgument::Flags(a)) => Self::show_instr_imm(a.0, ui),
                Some(InstructionArgument::Move(s, d)) => Self::show_instr_mv(s, d, ui),
                None => (),
            }
        });
    }

    fn show_addr_helper(&mut self, project: &Project, addr: impl Into<TU24>, ui: &mut egui::Ui) {
        let Some(addr) = addr.into().get() else {
            return;
        };
        let btn = egui::Button::new(egui::RichText::new(format!(" {addr}")).monospace());
        if ui.add(btn).clicked() {
            self.start_addr = addr;
        }
    }

    fn show_flags_helper(&mut self, flags: u8, ui: &mut egui::Ui) {
        use solar_magic::pf::*;
        let names = ["C", "Z", "I", "D", "X", "M", "V", "N"];
        let text = (0..8)
            .filter(|i| (flags >> i) & 1 != 0)
            .map(|i| names[i])
            .collect::<Vec<_>>()
            .join(" | ");
        ui.monospace(text);
    }

    fn show_helpers(
        &mut self,
        project: &Project,
        instr: &AnnotatedInstruction,
        arg: Option<InstructionArgument>,
        addr: Addr,
        ui: &mut egui::Ui,
    ) {
        let Some(arg) = arg else {
            return;
        };
        let ctx = &instr.pre;
        let cart = &project.smw.cart;
        match arg {
            InstructionArgument::Signature(_) => (),
            InstructionArgument::A(a) => {
                self.show_addr_helper(project, ctx.resolve_a(cart, &a), ui)
            }
            InstructionArgument::Ax(a) => {
                self.show_addr_helper(project, ctx.resolve_ax(cart, &a), ui)
            }
            InstructionArgument::Ay(a) => {
                self.show_addr_helper(project, ctx.resolve_ay(cart, &a), ui)
            }
            InstructionArgument::Al(a) => {
                self.show_addr_helper(project, ctx.resolve_al(cart, &a), ui)
            }
            InstructionArgument::Alx(a) => {
                self.show_addr_helper(project, ctx.resolve_alx(cart, &a), ui)
            }
            InstructionArgument::D(a) => {
                self.show_addr_helper(project, ctx.resolve_d(cart, &a), ui)
            }
            InstructionArgument::Dx(a) => todo!(),
            InstructionArgument::Dy(a) => todo!(),
            InstructionArgument::Dxi(a) => todo!(),
            InstructionArgument::Diy(a) => todo!(),
            InstructionArgument::Dily(a) => {
                self.show_addr_helper(project, ctx.resolve_dily(cart, &a), ui)
            }
            InstructionArgument::Di(a) => {
                self.show_addr_helper(project, ctx.resolve_di(cart, &a), ui)
            }
            InstructionArgument::Dil(a) => todo!(),
            InstructionArgument::S(a) => todo!(),
            InstructionArgument::Siy(a) => todo!(),
            InstructionArgument::I(a) => (),
            InstructionArgument::NearLabel(a) => self.show_addr_helper(project, a.take(addr), ui),
            InstructionArgument::RelativeLabel(a) => {
                self.show_addr_helper(project, a.take(addr), ui)
            }
            InstructionArgument::AbsoluteLabel(a) => {
                self.show_addr_helper(project, a.take(addr), ui)
            }
            InstructionArgument::LongLabel(a) => self.show_addr_helper(project, a, ui),
            InstructionArgument::IndirectLabel(a) => todo!(),
            InstructionArgument::IndirectIndexedLabel(a) => todo!(),
            InstructionArgument::IndirectLongLabel(a) => todo!(),
            InstructionArgument::Flags(a) => self.show_flags_helper(a.0, ui),
            InstructionArgument::Move(_, _) => todo!(),
        }
    }

    fn show_sidepanel(&mut self, project: &Project, ui: &mut egui::Ui) {
        ui.collapsing("Position", |ui| {
            egui::Grid::new("disassembler-sidepanel-position-grid")
                .striped(true)
                .num_columns(2)
                .show(ui, |ui| {
                    ui.strong("Address:");
                    ui.add(crate::addr_widget::addr_drag(&mut self.start_addr));
                    ui.end_row();
                });
        });
        // TODO
    }
}

impl crate::app::App {
    pub fn show_disassembly(&mut self, ctx: &egui::Context) {
        egui::CentralPanel::default().show(ctx, |ui| {
            if let Some(project) = &self.project.project {
                self.disassembly_view.show_grid(project, ui);
            } else {
                ui.centered_and_justified(|ui| ui.strong("no cartridge loaded yet"));
            }
        });
        let Some(project) = &self.project.project else {
            return;
        };
        egui::SidePanel::right("disassembly-sidepanel")
            .resizable(true)
            .width_range(..)
            .max_width(f32::INFINITY)
            .show(ctx, |ui| {
                ui.with_layout(egui::Layout::top_down_justified(egui::Align::Min), |ui| {
                    egui::ScrollArea::vertical().show(ui, |ui| {
                        self.disassembly_view.show_sidepanel(project, ui);
                    });
                });
            });
    }
}
