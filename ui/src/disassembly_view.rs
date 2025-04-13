use eframe::egui;
use egui::ahash::{HashMap, HashMapExt};
use solar_magic::{
    addr::Addr,
    analyzer::AnnotatedInstruction,
    instruction::{InstructionArgument, InstructionNamingConvention, OpCode},
    tvl::TU24,
};

use crate::project::Project;

const SCROLL_SPEED_FACTOR: f32 = 0.1;
const GRID_ROW_HEIGHT: f32 = 20.0;
const GRID_JUMPARROW_INDENT: f32 = 20.0;
const GRID_JUMPARROW_INDENT_START: f32 = 20.0;
const GRID_JUMPARROW_WIDTH: f32 = 5.0;

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

fn calculate_visually_distinct_color(i: u32) -> egui::Color32 {
    // This will yield a sequence of following hues:
    // 1/2, 1/4, 3/4, 1/8, 5/8, 3/8, 7/8, 1/16, ...
    // yeah, i dunno why i ended up doing this subnormal float clusterfuck...
    const SEQF32: f32 = f32::from_bits(253 << 23);
    egui::epaint::Hsva {
        h: f32::from_bits(i.reverse_bits() >> 9) * SEQF32,
        s: 0.7,
        v: 0.6,
        a: 1.0,
    }
    .into()
}

#[derive(Debug, Clone, Default)]
pub struct JumpList {
    buffer: Vec<Addr>,
    len: usize,
}

impl JumpList {
    pub fn jump(&mut self, src: Addr, dst: Addr) {
        self.buffer.truncate(self.len);
        if !self.buffer.last().is_some_and(|v| v == &src) {
            self.buffer.push(src);
            self.len += 1;
        }
        if !self.buffer.last().is_some_and(|v| v == &dst) {
            self.buffer.push(dst);
            self.len += 1;
        }
    }

    pub fn can_undo(&self) -> bool {
        self.len > 0
    }

    pub fn undo(&mut self, cur: Addr) -> Option<Addr> {
        loop {
            self.len = self.len.checked_sub(1)?;
            let res = self.buffer.get(self.len).copied();
            if res.is_some_and(|res| res == cur) {
                continue;
            }
            break res;
        }
    }

    pub fn can_redo(&self) -> bool {
        self.len + 1 < self.buffer.len()
    }

    pub fn redo(&mut self) -> Option<Addr> {
        let old_len = self.len;
        self.len = (self.len + 1).min(self.buffer.len());
        (old_len != self.len)
            .then(|| self.buffer.get(self.len).copied())
            .flatten()
    }
}

pub struct DisassemblyView {
    start_addr: Addr,
    scroll_offset: f32,
    jump_list: JumpList,
}

impl DisassemblyView {
    pub fn new() -> Self {
        Self {
            start_addr: Addr::new(0, 0x8000),
            scroll_offset: 0.0,
            jump_list: Default::default(),
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
            ui.vertical(|ui| {
                ui.horizontal(|ui| {
                    let btn = egui::Button::new("");
                    if ui.add_enabled(self.jump_list.can_undo(), btn).clicked() {
                        if let Some(dst) = self.jump_list.undo(self.start_addr) {
                            self.start_addr = dst;
                        }
                    }
                    let btn = egui::Button::new("");
                    if ui.add_enabled(self.jump_list.can_redo(), btn).clicked() {
                        if let Some(dst) = self.jump_list.redo() {
                            self.start_addr = dst;
                        }
                    }
                    let old_start_addr = self.start_addr;
                    ui.add(
                        crate::addr_widget::addr_drag(&mut self.start_addr)
                            .update_while_editing(false),
                    );
                    if old_start_addr.to_u32().abs_diff(self.start_addr.to_u32()) > 0x100 {
                        self.jump_list.jump(old_start_addr, self.start_addr);
                    }
                });
                ui.separator();
                let mut grid_items = HashMap::new();
                let mut jumps = HashMap::new();
                let mut colx = None;
                let old_remains = ui.available_rect_before_wrap();
                egui_extras::TableBuilder::new(ui)
                    .columns(egui_extras::Column::auto(), 4)
                    // fill the remainder so we have stripes to the end of the panel
                    .column(egui_extras::Column::remainder())
                    .vscroll(false)
                    .striped(true)
                    .body(|mut body| {
                        self.show_grid_content(
                            project,
                            &mut body,
                            &mut grid_items,
                            &mut jumps,
                            &mut colx,
                        );
                    });
                if let Some(colx) = colx {
                    let rect = egui::Rect::everything_right_of(colx).intersect(old_remains);
                    ui.allocate_rect(rect, egui::Sense::empty());
                    let painter = ui.painter();
                    let x = rect.min.x;
                    let mut jump_ys: Vec<_> = jumps
                        .into_iter()
                        .filter_map(|(dst, srcs)| {
                            let dst = grid_items.get(&dst).copied()?;
                            let srcs: Vec<_> = srcs
                                .into_iter()
                                .filter_map(|src| grid_items.get(&src).copied())
                                .collect();
                            let srcmin = srcs.iter().copied().min_by(f32::total_cmp)?;
                            let srcmax = srcs.iter().copied().max_by(f32::total_cmp)?;
                            Some((srcs, dst, srcmin.min(dst), srcmax.max(dst)))
                        })
                        .collect();
                    jump_ys.sort_unstable_by(|(_, d1, a1, b1), (.., d2, a2, b2)| {
                        (b1 - a1).total_cmp(&(b2 - a2)).then(d1.total_cmp(d2))
                    });
                    let mut layers: Vec<usize> = vec![];
                    for (s, d, ymin1, ymax1) in &jump_ys {
                        let ly = jump_ys
                            .iter()
                            .zip(&layers)
                            .filter(|((.., ymin2, ymax2), _)| ymin1 <= ymax2 && ymax1 >= ymin2)
                            .map(|(_, ly)| *ly)
                            .max()
                            .map(|ly| ly + 1)
                            .unwrap_or(0);
                        layers.push(ly);
                        let x2 =
                            x + ly as f32 * GRID_JUMPARROW_INDENT + GRID_JUMPARROW_INDENT_START;
                        let color = calculate_visually_distinct_color(ly as _);

                        for y in s.iter().chain([d]).copied() {
                            if y == *ymin1 || y == *ymax1 {
                                continue;
                            }
                            painter.hline(x..=x2, y, (GRID_JUMPARROW_WIDTH, color));
                        }
                        painter.line(
                            vec![
                                egui::Pos2::new(x, *ymin1),
                                egui::Pos2::new(x2, *ymin1),
                                egui::Pos2::new(x2, *ymax1),
                                egui::Pos2::new(x, *ymax1),
                            ],
                            (GRID_JUMPARROW_WIDTH, color),
                        );
                        painter.add(egui::epaint::PathShape {
                            points: vec![
                                egui::Pos2::new(x - 6.0, *d),
                                egui::Pos2::new(x + 1.0, *d + 6.0),
                                egui::Pos2::new(x + 1.0, *d - 6.0),
                            ],
                            closed: true,
                            fill: color,
                            stroke: egui::epaint::PathStroke::NONE,
                        });
                    }
                }
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

    fn show_grid_content(
        &mut self,
        project: &Project,
        body: &mut egui_extras::TableBody,
        grid_items: &mut HashMap<Addr, f32>,
        jumps: &mut HashMap<Addr, Vec<Addr>>,
        colx: &mut Option<f32>,
    ) {
        let mut addr = self.start_addr;
        loop {
            let ui = body.ui_mut();
            if !ui.is_rect_visible(ui.cursor()) {
                break;
            }

            body.row(GRID_ROW_HEIGHT, |mut row| {
                let row_addr = addr;
                row.col(|ui| {
                    ui.label(egui::RichText::new(addr.to_string()).monospace().weak());
                });

                let opt_annotation = project
                    .analyzer
                    .code_annotations
                    .get(&addr)
                    .and_then(|v| v.iter().min_by_key(|(k, _)| k.len()));
                if let Some((_call_stack, instr)) = opt_annotation {
                    let opcode = instr.instruction.opcode();
                    let instr_size = instr.instruction.size();
                    let arg = instr.instruction.arg();

                    row.col(|ui| {
                        Self::show_bytes(
                            project,
                            (0..instr_size).map(|i| addr.add16(i.into())),
                            ui,
                        );
                    });

                    row.col(|ui| {
                        self.show_instr(arg, opcode, ui);
                    });

                    row.col(|ui| {
                        ui.with_layout(egui::Layout::left_to_right(egui::Align::Min), |ui| {
                            self.show_helpers(project, instr, arg, addr, jumps, ui);
                        });
                    });

                    addr = addr.add24(instr_size.into());
                } else {
                    row.col(|ui| {
                        Self::show_bytes(project, [addr], ui);
                    });
                    row.col(|ui| {
                        ui.label("<data byte>");
                    });
                    row.col(|ui| {
                        ui.horizontal(|ui| {
                            ui.add_space(ui.available_width());
                        });
                    });
                    addr = addr.add24(1);
                }
                row.col(|ui| {
                    let rect = ui.available_rect_before_wrap();
                    grid_items.insert(row_addr, rect.center().y);
                    let x = rect.min.x;
                    if let Some(colx) = colx {
                        *colx = colx.max(x)
                    } else {
                        *colx = Some(x)
                    }
                    ui.horizontal(|ui| {
                        ui.add_space(ui.available_width());
                    });
                });
            });
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

    fn show_addr_helper(
        &mut self,
        project: &Project,
        addr: impl Into<TU24>,
        isjmp: bool,
        ui: &mut egui::Ui,
    ) {
        let Some(addr) = addr.into().get() else {
            return;
        };
        let mut label = egui::RichText::new(format!(" {addr}")).monospace();
        if !isjmp {
            label = label.weak();
        }
        let btn = egui::Button::new(label);
        if ui.add(btn).clicked() {
            self.jump_list.jump(self.start_addr, addr);
            self.start_addr = addr;
        }
    }

    fn show_flags_helper(&mut self, flags: u8, ui: &mut egui::Ui) {
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
        jumps: &mut HashMap<Addr, Vec<Addr>>,
        ui: &mut egui::Ui,
    ) {
        let Some(arg) = arg else {
            return;
        };
        let mut add_jump = |s, d| jumps.entry(d).or_insert(vec![]).push(s);
        let ctx = &instr.pre;
        let cart = &project.smw.cart;
        match arg {
            InstructionArgument::Signature(_) => (),
            InstructionArgument::A(a) => {
                self.show_addr_helper(project, ctx.resolve_a(cart, &a), false, ui)
            }
            InstructionArgument::Ax(a) => {
                self.show_addr_helper(project, ctx.resolve_ax(cart, &a), false, ui)
            }
            InstructionArgument::Ay(a) => {
                self.show_addr_helper(project, ctx.resolve_ay(cart, &a), false, ui)
            }
            InstructionArgument::Al(a) => {
                self.show_addr_helper(project, ctx.resolve_al(cart, &a), false, ui)
            }
            InstructionArgument::Alx(a) => {
                self.show_addr_helper(project, ctx.resolve_alx(cart, &a), false, ui)
            }
            InstructionArgument::D(a) => {
                self.show_addr_helper(project, ctx.resolve_d(cart, &a), false, ui)
            }
            InstructionArgument::Dx(a) => todo!(),
            InstructionArgument::Dy(a) => todo!(),
            InstructionArgument::Dxi(a) => todo!(),
            InstructionArgument::Diy(a) => todo!(),
            InstructionArgument::Dily(a) => {
                self.show_addr_helper(project, ctx.resolve_dily(cart, &a), false, ui)
            }
            InstructionArgument::Di(a) => {
                self.show_addr_helper(project, ctx.resolve_di(cart, &a), false, ui)
            }
            InstructionArgument::Dil(a) => todo!(),
            InstructionArgument::S(a) => todo!(),
            InstructionArgument::Siy(a) => todo!(),
            InstructionArgument::I(a) => (),
            InstructionArgument::NearLabel(a) => {
                let dst = a.take(addr);
                add_jump(addr, dst);
                self.show_addr_helper(project, dst, true, ui)
            }
            InstructionArgument::RelativeLabel(a) => {
                let dst = a.take(addr);
                add_jump(addr, dst);
                self.show_addr_helper(project, dst, true, ui)
            }
            InstructionArgument::AbsoluteLabel(a) => {
                let dst = a.take(addr);
                add_jump(addr, dst);
                self.show_addr_helper(project, dst, true, ui)
            }
            InstructionArgument::LongLabel(a) => {
                add_jump(addr, a);
                self.show_addr_helper(project, a, true, ui)
            }
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
