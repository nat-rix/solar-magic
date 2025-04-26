use eframe::egui;
use egui::ahash::{HashMap, HashMapExt};
use solar_magic::{
    addr::Addr,
    analyzer::{Analyzer, AnnotatedInstruction, CallStack, CallStackRoot, JumpTableType},
    cart::Cart,
    instruction::{InstructionArgument, InstructionNamingConvention, OpCode},
    original_cart::OriginalCart,
    tvl::{TBool, TU8, TU16, TU24},
};

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

struct OptByte(Option<u8>);

impl core::fmt::Display for OptByte {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        if let Some(b) = self.0 {
            write!(f, "{b:02x}")
        } else {
            write!(f, "??")
        }
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
        if self.buffer.last().is_none_or(|v| v != &src) {
            self.buffer.push(src);
            self.len += 1;
        }
        if self.buffer.last().is_none_or(|v| v != &dst) {
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

fn call_stack_to_text(call_stack: &CallStack) -> String {
    let mut s = match call_stack.root() {
        CallStackRoot::Vector(0xffe4) => "COP".to_string(),
        CallStackRoot::Vector(0xffe6) => "BRK".to_string(),
        CallStackRoot::Vector(0xffea) => "NMI".to_string(),
        CallStackRoot::Vector(0xffee) => "IRQ".to_string(),
        CallStackRoot::Vector(0xfff4) => "COPe".to_string(),
        CallStackRoot::Vector(0xfffa) => "NMIe".to_string(),
        CallStackRoot::Vector(0xfffc) => "RESET".to_string(),
        CallStackRoot::Vector(0xfffe) => "IRQe".to_string(),
        CallStackRoot::Vector(v) => format!("vec{v:04X}"),
        CallStackRoot::Table(addr) => format!("<{addr}>"),
    };
    for it in call_stack.items() {
        s.push_str(" > ");
        if it.is_long {
            s.push_str(&format!("[{}]", it.addr));
        } else {
            s.push_str(&format!("({})", it.addr));
        }
    }
    s
}

pub struct DisassemblyView {
    start_addr: Addr,
    selected_addr: Option<Addr>,
    selected_callstack: Option<CallStack>,
    scroll_offset: f32,
    jump_list: JumpList,
}

impl DisassemblyView {
    pub fn new() -> Self {
        Self {
            start_addr: Addr::new(0, 0x8000),
            selected_addr: None,
            selected_callstack: None,
            scroll_offset: 0.0,
            jump_list: Default::default(),
        }
    }

    fn show_grid(&mut self, cart: &Cart, analyzer: Option<&Analyzer>, ui: &mut egui::Ui) {
        let rect = ui
            .with_layout(egui::Layout::top_down_justified(egui::Align::Min), |ui| {
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
                        .cell_layout(egui::Layout::centered_and_justified(
                            egui::Direction::LeftToRight,
                        ))
                        .columns(egui_extras::Column::auto(), 4)
                        // fill the remainder so we have stripes to the end of the panel
                        .column(egui_extras::Column::remainder())
                        .vscroll(false)
                        .striped(true)
                        .sense(egui::Sense::click())
                        .body(|mut body| {
                            self.show_grid_content(
                                cart,
                                analyzer,
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
            })
            .response
            .rect;

        if ui.rect_contains_pointer(rect) {
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
    }

    fn show_byte(cart: &Cart, addr: Addr, ui: &mut egui::Ui) {
        if let Some(byte) = cart.read_rom(addr) {
            ui.monospace(format!("{byte:02x}"));
        } else {
            ui.monospace("??");
        }
    }

    fn show_bytes(cart: &Cart, iter: impl IntoIterator<Item = Addr>, ui: &mut egui::Ui) {
        ui.horizontal(|ui| {
            for i in iter {
                Self::show_byte(cart, i, ui);
            }
        });
    }

    fn show_grid_content(
        &mut self,
        cart: &Cart,
        analyzer: Option<&Analyzer>,
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
                if self.selected_addr.is_some_and(|a| a == row_addr) {
                    row.set_selected(true);
                }

                row.col(|ui| {
                    ui.label(egui::RichText::new(addr.to_string()).monospace().weak());
                });

                let opt_annotation = analyzer
                    .and_then(|analyzer| analyzer.get_annotation_with_shortest_callstack(addr));

                if let Some((_call_stack, instr)) = opt_annotation {
                    let opcode = instr.instruction.opcode();
                    let instr_size = instr.instruction.size();
                    let arg = instr.instruction.arg();

                    row.col(|ui| {
                        Self::show_bytes(cart, (0..instr_size).map(|i| addr.add16(i.into())), ui);
                    });

                    row.col(|ui| {
                        self.show_instr(arg, opcode, ui);
                    });

                    row.col(|ui| {
                        ui.with_layout(egui::Layout::left_to_right(egui::Align::Min), |ui| {
                            self.show_helpers(cart, instr, arg, addr, jumps, ui);
                        });
                    });

                    addr = addr.add24(instr_size.into());
                } else if let Some((analyzer, table_start)) = analyzer.and_then(|analyzer| {
                    analyzer
                        .jump_table_items
                        .get(&addr)
                        .map(|table_start| (analyzer, table_start))
                }) {
                    let table = analyzer.jump_tables.get(table_start).unwrap();
                    let entry_size = table.ty.entry_size();

                    row.col(|ui| {
                        Self::show_bytes(cart, (0..entry_size).map(|i| addr.add16(i.into())), ui);
                    });

                    let lo = OptByte(cart.read_rom(addr));
                    let hi = OptByte(cart.read_rom(addr.add16(1)));
                    let ba = OptByte(if let JumpTableType::Addr24 = table.ty {
                        cart.read_rom(addr.add16(2))
                    } else {
                        None
                    });

                    row.col(|ui| {
                        ui.horizontal(|ui| {
                            ui.colored_label(
                                DISASM_COLOR_INSTR,
                                egui::RichText::new(".entry").monospace(),
                            );
                            ui.horizontal(|ui| {
                                ui.spacing_mut().item_spacing.x = 2.0;
                                ui.monospace("$");
                                if let JumpTableType::Addr24 = table.ty {
                                    ui.colored_label(
                                        DISASM_COLOR_ABSOLUTE,
                                        egui::RichText::new(format!("{ba}")).monospace(),
                                    );
                                    ui.monospace(":");
                                }
                                ui.colored_label(
                                    DISASM_COLOR_ABSOLUTE,
                                    egui::RichText::new(format!("{hi}{lo}")).monospace(),
                                );
                            });
                        });
                    });

                    row.col(|ui| {
                        ui.with_layout(egui::Layout::left_to_right(egui::Align::Min), |ui| {
                            let [OptByte(Some(lo)), OptByte(Some(hi))] = [lo, hi] else {
                                return;
                            };
                            let lohi = u16::from_le_bytes([lo, hi]);
                            let entry = if let JumpTableType::Addr24 = table.ty {
                                let OptByte(Some(ba)) = ba else {
                                    return;
                                };
                                Addr::new(ba, lohi)
                            } else {
                                Addr::new(table_start.bank, lohi)
                            };
                            jumps.entry(entry).or_default().push(addr);
                            self.show_addr_helper(entry, true, ui);
                        });
                    });

                    addr = addr.add24(entry_size.into());
                } else {
                    row.col(|ui| {
                        Self::show_bytes(cart, [addr], ui);
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
                if row.response().clicked() {
                    if self.selected_addr.is_some_and(|a| a == row_addr) {
                        self.selected_addr = None;
                    } else {
                        self.selected_callstack = None;
                        self.selected_addr = Some(row_addr);
                    }
                }
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

    fn show_instr_mv(d: u8, s: u8, ui: &mut egui::Ui) {
        ui.horizontal(|ui| {
            Self::show_instr_lit(d, ui);
            ui.monospace("←");
            Self::show_instr_lit(s, ui);
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
        let (x, y) = if is_long { ("[", "]") } else { ("(", ")") };
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
                Some(InstructionArgument::Move(d, s)) => Self::show_instr_mv(d, s, ui),
                None => (),
            }
        });
    }

    fn show_addr_helper(&mut self, addr: impl Into<TU24>, isjmp: bool, ui: &mut egui::Ui) {
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
        cart: &Cart,
        instr: &AnnotatedInstruction,
        arg: Option<InstructionArgument>,
        addr: Addr,
        jumps: &mut HashMap<Addr, Vec<Addr>>,
        ui: &mut egui::Ui,
    ) {
        let Some(arg) = arg else {
            return;
        };
        let mut add_jump = |s, d| jumps.entry(d).or_default().push(s);
        let ctx = &instr.pre;
        match arg {
            InstructionArgument::Signature(_) => (),
            InstructionArgument::A(a) => self.show_addr_helper(ctx.resolve_a(cart, &a), false, ui),
            InstructionArgument::Ax(a) => {
                self.show_addr_helper(ctx.resolve_ax(cart, &a), false, ui)
            }
            InstructionArgument::Ay(a) => {
                self.show_addr_helper(ctx.resolve_ay(cart, &a), false, ui)
            }
            InstructionArgument::Al(a) => {
                self.show_addr_helper(ctx.resolve_al(cart, &a), false, ui)
            }
            InstructionArgument::Alx(a) => {
                self.show_addr_helper(ctx.resolve_alx(cart, &a), false, ui)
            }
            InstructionArgument::D(a) => self.show_addr_helper(ctx.resolve_d(cart, &a), false, ui),
            InstructionArgument::Dx(a) => {
                self.show_addr_helper(ctx.resolve_dx(cart, &a), false, ui)
            }
            InstructionArgument::Dy(a) => {
                self.show_addr_helper(ctx.resolve_dy(cart, &a), false, ui)
            }
            InstructionArgument::Dxi(_a) => todo!(),
            InstructionArgument::Diy(a) => {
                self.show_addr_helper(ctx.resolve_diy(cart, &a), false, ui)
            }
            InstructionArgument::Dily(a) => {
                self.show_addr_helper(ctx.resolve_dily(cart, &a), false, ui)
            }
            InstructionArgument::Di(a) => {
                self.show_addr_helper(ctx.resolve_di(cart, &a), false, ui)
            }
            InstructionArgument::Dil(a) => {
                self.show_addr_helper(ctx.resolve_dil(cart, &a), false, ui)
            }
            InstructionArgument::S(_a) => todo!(),
            InstructionArgument::Siy(_a) => todo!(),
            InstructionArgument::I(_a) => (),
            InstructionArgument::NearLabel(a) => {
                let dst = a.take(addr);
                add_jump(addr, dst);
                self.show_addr_helper(dst, true, ui)
            }
            InstructionArgument::RelativeLabel(a) => {
                let dst = a.take(addr);
                add_jump(addr, dst);
                self.show_addr_helper(dst, true, ui)
            }
            InstructionArgument::AbsoluteLabel(a) => {
                let dst = a.take(addr);
                add_jump(addr, dst);
                self.show_addr_helper(dst, true, ui)
            }
            InstructionArgument::LongLabel(a) => {
                add_jump(addr, a);
                self.show_addr_helper(a, true, ui)
            }
            InstructionArgument::IndirectLabel(_a) => todo!(),
            InstructionArgument::IndirectIndexedLabel(_a) => todo!(),
            InstructionArgument::IndirectLongLabel(a) => {
                let dst = ctx.resolve_jmli(cart, &a);
                if let Some(dst) = dst.get() {
                    add_jump(addr, dst);
                }
                self.show_addr_helper(dst, true, ui)
            }
            InstructionArgument::Flags(a) => self.show_flags_helper(a.0, ui),
            // TODO: helpers for move instructions (are there actually any needed?)
            InstructionArgument::Move(_, _) => (),
        }
    }

    fn show_tu4_hex(&mut self, val: TU8, is_high: bool, ui: &mut egui::Ui) {
        let f = if is_high { |n| n >> 4 } else { |n| n & 15 };
        if f(val.known_bits()) == 15 {
            ui.monospace(format!("{:x}", f(val.known_ones())));
        } else {
            ui.monospace("?");
        }
    }

    fn show_tu8_hex(&mut self, val: TU8, ui: &mut egui::Ui) {
        ui.horizontal(|ui| {
            ui.spacing_mut().item_spacing.x = 0.0;
            self.show_tu4_hex(val, true, ui);
            self.show_tu4_hex(val, false, ui);
        });
    }

    fn show_tu4_bin(&mut self, val: TU8, is_high: bool, pmarkers: bool, ui: &mut egui::Ui) {
        let known = val.known_bits();
        let ones = val.known_ones();
        let shift = if is_high { 4 } else { 0 };
        ui.horizontal(|ui| {
            ui.spacing_mut().item_spacing.x = 0.0;
            for i in (shift..shift + 4).rev() {
                let label = match [known, ones].map(|v| (v >> i) & 1) {
                    [0, _] => egui::RichText::new("?").small().monospace().weak(),
                    [_, 0] => egui::RichText::new("0").small().monospace().weak(),
                    [_, _] => egui::RichText::new("1").small().monospace().weak(),
                };
                if pmarkers {
                    let marker = ["C", "Z", "I", "D", "X", "M", "V", "N"][i];
                    ui.label(egui::RichText::new(marker).small().monospace().weak());
                    ui.label(label);
                    if i != 0 {
                        ui.separator();
                    }
                } else {
                    ui.label(label);
                }
            }
        });
    }

    fn show_anyreg<U>(
        &mut self,
        name: &str,
        fx: impl FnOnce(&mut Self, &mut egui::Ui) -> U,
        fb: impl FnOnce(&mut Self, &mut egui::Ui) -> U,
        spacing: bool,
        ui: &mut egui::Ui,
    ) {
        ui.monospace(name);
        ui.with_layout(egui::Layout::left_to_right(egui::Align::Max), |ui| {
            ui.spacing_mut().item_spacing.x = 2.0;
            fx(self, ui);
        });
        ui.with_layout(egui::Layout::left_to_right(egui::Align::Max), |ui| {
            ui.spacing_mut().item_spacing.x = if spacing { 4.0 } else { 0.0 };
            fb(self, ui);
        });
    }

    fn show_reg8(&mut self, name: &str, val: TU8, pmarkers: bool, ui: &mut egui::Ui) {
        self.show_anyreg(
            name,
            |slf, ui| slf.show_tu8_hex(val, ui),
            |slf, ui| {
                slf.show_tu4_bin(val, true, pmarkers, ui);
                slf.show_tu4_bin(val, false, pmarkers, ui);
            },
            !pmarkers,
            ui,
        );
    }

    fn show_reg16(&mut self, name: &str, val: TU16, _is16: impl Into<TBool>, ui: &mut egui::Ui) {
        // TODO: faint the upper 8-bit of 16-bit if is16=false
        let [lo, hi] = val.to_bytes();
        self.show_anyreg(
            name,
            |slf, ui| {
                slf.show_tu8_hex(hi, ui);
                slf.show_tu8_hex(lo, ui);
            },
            |slf, ui| {
                slf.show_tu4_bin(hi, true, false, ui);
                slf.show_tu4_bin(hi, false, false, ui);
                slf.show_tu4_bin(lo, true, false, ui);
                slf.show_tu4_bin(lo, false, false, ui);
            },
            true,
            ui,
        );
    }

    fn show_sidepanel_call_stack<'a>(
        &mut self,
        analyzer: &'a Analyzer,
        ui: &mut egui::Ui,
    ) -> Option<(Addr, &'a AnnotatedInstruction)> {
        let addr = self.selected_addr?;
        if self.selected_callstack.is_none() {
            self.selected_callstack = Some(
                analyzer
                    .get_annotation_with_shortest_callstack(addr)?
                    .0
                    .clone(),
            );
        }
        let call_stack = self.selected_callstack.as_mut().unwrap();
        let mut selected = &*call_stack;
        ui.horizontal(|ui| {
            ui.heading(format!("{addr}"));
            if ui.button(" ").clicked() {
                self.start_addr = addr;
            }
        });
        ui.separator();
        egui::ComboBox::from_label("Call Stack")
            .selected_text(call_stack_to_text(selected))
            .show_ui(ui, |ui| {
                for item in analyzer
                    .code_annotations
                    .get(&addr)
                    .map(|a| a.keys())
                    .into_iter()
                    .flatten()
                {
                    ui.selectable_value(&mut selected, item, call_stack_to_text(item));
                }
            });
        if selected != call_stack {
            *call_stack = selected.clone();
        }
        analyzer.get_annotation(addr, call_stack).map(|a| (addr, a))
    }

    fn show_sidepanel(&mut self, cart: &OriginalCart, analyzer: &Analyzer, ui: &mut egui::Ui) {
        ui.vertical(|ui| {
            if let Some((_addr, annotation)) = self.show_sidepanel_call_stack(analyzer, ui) {
                ui.separator();
                let ctx = &annotation.pre;
                ui.group(|ui| {
                    ui.heading("Registers");
                    ui.separator();
                    egui::Grid::new("sidepanel-register-grid")
                        .num_columns(3)
                        .min_col_width(0.0)
                        .show(ui, |ui| {
                            self.show_reg16("A", ctx.a, ctx.mf(), ui);
                            ui.end_row();
                            self.show_reg16("D", ctx.d, false, ui);
                            ui.end_row();
                            self.show_reg16("X", ctx.x, ctx.xf(), ui);
                            ui.end_row();
                            self.show_reg16("Y", ctx.y, ctx.xf(), ui);
                            ui.end_row();
                            self.show_reg8("B", ctx.b, false, ui);
                            ui.end_row();
                            self.show_reg8("P", ctx.p, true, ui);
                            ui.end_row();
                        });
                });
                ui.separator();
                ui.group(|ui| {
                    ui.heading("Stack");
                    ui.separator();
                    egui::ScrollArea::vertical().show(ui, |ui| {
                        egui::Grid::new("sidepanel-stack-grid")
                            .num_columns(2)
                            .show(ui, |ui| {
                                for i in &ctx.stack.items {
                                    ui.horizontal(|ui| {
                                        self.show_tu8_hex(*i, ui);
                                        self.show_tu4_bin(*i, true, false, ui);
                                        self.show_tu4_bin(*i, false, false, ui);
                                    });
                                    ui.end_row();
                                }
                            });
                    });
                });
                ui.separator();
                ui.group(|ui| {
                    ui.heading("Memory");
                    ui.separator();
                    ui.with_layout(egui::Layout::top_down_justified(egui::Align::Min), |ui| {
                        egui::ScrollArea::vertical()
                            .id_salt("sidepanel-mem-scroll")
                            .show(ui, |ui| {
                                egui::Grid::new("sidepanel-mem-grid").num_columns(2).show(
                                    ui,
                                    |ui| {
                                        for (a, v) in ctx.map.iter() {
                                            let Some(addr) = cart.cart.reverse_map(*a) else {
                                                continue;
                                            };
                                            ui.label(
                                                egui::RichText::new(addr.to_string())
                                                    .monospace()
                                                    .weak(),
                                            );
                                            ui.horizontal(|ui| {
                                                self.show_tu8_hex(*v, ui);
                                                self.show_tu4_bin(*v, true, false, ui);
                                                self.show_tu4_bin(*v, false, false, ui);
                                                ui.add_space(ui.available_width());
                                            });
                                            ui.end_row();
                                        }
                                    },
                                );
                            });
                    });
                });
            }
        });
    }
}

impl crate::app::App {
    pub fn show_disassembly(&mut self, ctx: &egui::Context) {
        if let Some(desc) = self.project.get_description() {
            egui::TopBottomPanel::bottom("thread-info-panel")
                .resizable(false)
                .show(ctx, |ui| {
                    ui.horizontal(|ui| {
                        ui.spinner();
                        ui.small(desc);
                    });
                });
            ctx.output_mut(|out| out.cursor_icon = egui::CursorIcon::Progress);
        }
        if let (Some(cart), Some(analyzer)) = (&self.project.cart, &self.project.analyzer) {
            egui::SidePanel::right("disassembly-sidepanel")
                .resizable(true)
                .width_range(..)
                .max_width(f32::INFINITY)
                .show_animated(ctx, self.disassembly_view.selected_addr.is_some(), |ui| {
                    ui.with_layout(egui::Layout::top_down_justified(egui::Align::Min), |ui| {
                        egui::ScrollArea::vertical().show(ui, |ui| {
                            self.disassembly_view.show_sidepanel(cart, analyzer, ui);
                        });
                    });
                });
        }
        egui::CentralPanel::default().show(ctx, |ui| {
            if let Some(cart) = &self.project.cart {
                self.disassembly_view
                    .show_grid(&cart.cart, self.project.analyzer.as_ref(), ui);
            } else {
                ui.centered_and_justified(|ui| ui.strong("no cartridge loaded yet"));
            }
        });
    }
}
