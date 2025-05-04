use std::collections::HashMap;

use eframe::egui;
use solar_magic::{
    addr::Addr,
    addr_space::{CartMemoryLocation, MemoryLocation, SystemMemoryLocation},
    cart::Cart,
    rewriter::{
        AbstractArgument, AbstractCodeLabel, AbstractLabel, AccessType, Block, BlockContent,
        BlockId, CodeBlock, DataBlock, Rewriter,
    },
};

use crate::disassembly_view::{
    DISASM_COLOR_ABSOLUTE, DISASM_COLOR_IMMEDIATE, DISASM_COLOR_INDEX, DISASM_COLOR_INDIRECT,
    DISASM_COLOR_INSTR,
};

const CODE_COLOR: egui::Color32 = crate::theme::rgba(0xdf8e1dff);
const DATA_COLOR: egui::Color32 = crate::theme::rgba(0xe64553ff);

#[derive(Debug, Clone, Default)]
struct BlockNames {
    names: HashMap<BlockId, String>,
}

impl BlockNames {
    pub fn get(&mut self, cart: &Cart, block_id: BlockId, block: Option<&Block>) -> &String {
        self.names.entry(block_id).or_insert_with(|| {
            let prefix = match block.map(|block| &block.content) {
                Some(BlockContent::Code(_)) => "code",
                Some(BlockContent::Data(_)) => "data",
                None => "unknown",
            };
            let addr = cart
                .reverse_map_rom(block_id.get_offset())
                .unwrap_or(Addr::NULL);
            format!("{prefix}_{:02x}{:04x}", addr.bank, addr.addr)
        })
    }

    pub fn get_with_rewriter(
        &mut self,
        cart: &Cart,
        block_id: BlockId,
        rewriter: &Rewriter,
    ) -> &String {
        let block = rewriter.blocks.get(&block_id);
        self.get(cart, block_id, block)
    }
}

#[derive(Debug, Clone)]
struct SearchOptions {
    term: String,
    show_code: bool,
    show_data: bool,
    nucleo_cfg: nucleo_matcher::Config,
    norm: nucleo_matcher::pattern::Normalization,
    case: nucleo_matcher::pattern::CaseMatching,
    needs_reeval: bool,
}

impl Default for SearchOptions {
    fn default() -> Self {
        Self {
            term: String::new(),
            show_code: true,
            show_data: true,
            nucleo_cfg: nucleo_matcher::Config::DEFAULT,
            norm: nucleo_matcher::pattern::Normalization::Smart,
            case: nucleo_matcher::pattern::CaseMatching::Ignore,
            needs_reeval: true,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct DataBlockView {
    search_options: SearchOptions,
    block_names: BlockNames,
    search_results: Vec<(BlockId, u32)>,
    selected: Option<BlockId>,
}

impl crate::app::App {
    pub fn show_data_block_view(&mut self, ui: &mut egui::Ui) {
        if let (Some(rewriter), Some(cart)) = (
            self.project.rewriter.as_deref_mut(),
            self.project.cart.as_deref(),
        ) {
            self.data_block_view.show(ui, rewriter, &cart.cart);
        } else {
            egui::CentralPanel::default().show_inside(ui, |ui| {
                ui.centered_and_justified(|ui| {
                    ui.strong("Data is not yet available");
                });
            });
        }
    }
}

impl DataBlockView {
    pub fn show(&mut self, ui: &mut egui::Ui, rewriter: &mut Rewriter, cart: &Cart) {
        egui::SidePanel::left("data-block-view-search-panel").show_inside(ui, |ui| {
            self.show_search_panel(ui, rewriter, cart);
        });
        egui::CentralPanel::default().show_inside(ui, |ui| {
            self.show_central(ui, rewriter, cart);
        });
    }

    pub fn show_central(&mut self, ui: &mut egui::Ui, rewriter: &mut Rewriter, cart: &Cart) {
        let Some(block_id) = self.selected else {
            ui.centered_and_justified(|ui| {
                ui.set_max_size(egui::Vec2::new(190.0, 32.0));
                ui.heading("No block selected");
                ui.separator();
                ui.label("select a block on the left panel to view its contents");
            });
            return;
        };
        let Some(block) = rewriter.blocks.get(&block_id) else {
            ui.centered_and_justified(|ui| {
                ui.colored_label(ui.visuals().error_fg_color, "Selected block is missing!");
            });
            return;
        };
        match &block.content {
            BlockContent::Code(code) => self.show_central_code(ui, rewriter, code, cart),
            BlockContent::Data(data) => self.show_central_data(ui, data, cart),
        }
    }

    pub fn show_central_code(
        &mut self,
        ui: &mut egui::Ui,
        rewriter: &Rewriter,
        code: &CodeBlock,
        cart: &Cart,
    ) {
        ui.group(|ui| {
            egui::Grid::new("code-block-view-central-code")
                .striped(false)
                .num_columns(1)
                .show(ui, |ui| {
                    for instr in code.instrs() {
                        ui.horizontal(|ui| {
                            ui.colored_label(
                                DISASM_COLOR_INSTR,
                                egui::RichText::new(format!(
                                    "{}{}",
                                    instr.ty.name(),
                                    match instr
                                        .is_short
                                        .filter(|_| instr.ty.flag_dependency().is_some())
                                    {
                                        Some(false) => "W",
                                        Some(true) => "B",
                                        None => "",
                                    }
                                ))
                                .monospace(),
                            );
                            if let Some(arg) = &instr.arg {
                                match arg {
                                    AbstractArgument::Signature(val) => {
                                        ui.monospace(format!("${val:02x}"));
                                    }
                                    AbstractArgument::Imm8(val) => {
                                        ui.colored_label(
                                            DISASM_COLOR_IMMEDIATE,
                                            egui::RichText::new(format!("#${val:02x}")).monospace(),
                                        );
                                    }
                                    AbstractArgument::Imm16(val) => {
                                        ui.colored_label(
                                            DISASM_COLOR_IMMEDIATE,
                                            egui::RichText::new(format!("#${val:04x}")).monospace(),
                                        );
                                    }
                                    AbstractArgument::Access(acc) => {
                                        match &acc.ty {
                                            AccessType::Absolute(_) => {
                                                self.show_label(ui, &acc.label, rewriter, cart)
                                            }
                                            AccessType::Direct(_) => {
                                                self.show_label(ui, &acc.label, rewriter, cart)
                                            }
                                            AccessType::Indirect | AccessType::IndirectY => self
                                                .show_indirect_label(
                                                    ui, &acc.label, false, rewriter, cart,
                                                ),
                                            AccessType::IndirectLong
                                            | AccessType::IndirectLongY => self
                                                .show_indirect_label(
                                                    ui, &acc.label, true, rewriter, cart,
                                                ),
                                        }
                                        if let Some(ix) = acc.ty.index_register() {
                                            ui.colored_label(
                                                DISASM_COLOR_INDEX,
                                                egui::RichText::new(format!(", {ix}")).monospace(),
                                            );
                                        }
                                    }
                                    AbstractArgument::CodeLabel(label) => match label {
                                        AbstractCodeLabel::Direct(label) => {
                                            self.show_label(ui, label, rewriter, cart)
                                        }
                                        AbstractCodeLabel::IndirectLong(label) => self
                                            .show_indirect_label(ui, label, true, rewriter, cart),
                                    },
                                    AbstractArgument::Flags(flags) => {
                                        ui.monospace(flags.to_string());
                                    }
                                    AbstractArgument::Move(mv) => {
                                        self.show_move_label(ui, mv.dst.as_ref(), rewriter, cart);
                                        ui.monospace(" ← ");
                                        self.show_move_label(ui, mv.src.as_ref(), rewriter, cart);
                                    }
                                }
                            }
                        });
                        ui.end_row();
                    }
                });
        });
    }

    pub fn show_move_label(
        &mut self,
        ui: &mut egui::Ui,
        label: Option<&AbstractLabel>,
        rewriter: &Rewriter,
        cart: &Cart,
    ) {
        if let Some(label) = label {
            self.show_label(ui, label, rewriter, cart);
        } else {
            ui.monospace("?");
        }
    }

    pub fn show_indirect_label(
        &mut self,
        ui: &mut egui::Ui,
        label: &AbstractLabel,
        is_long: bool,
        rewriter: &Rewriter,
        cart: &Cart,
    ) {
        let parens = if is_long { ["[", "]"] } else { ["(", ")"] };
        for (i, p) in parens.into_iter().enumerate() {
            ui.colored_label(DISASM_COLOR_INDIRECT, egui::RichText::new(p).monospace());
            if i != 0 {
                return;
            }
            self.show_label(ui, label, rewriter, cart);
        }
    }

    pub fn show_label(
        &mut self,
        ui: &mut egui::Ui,
        label: &AbstractLabel,
        rewriter: &Rewriter,
        cart: &Cart,
    ) {
        match label {
            AbstractLabel::Block(block_id) => {
                let name = self
                    .block_names
                    .get_with_rewriter(cart, *block_id, rewriter);
                if ui.button(name).clicked() {
                    self.selected = Some(*block_id);
                }
            }
            AbstractLabel::Location(loc) => {
                let text = match loc {
                    MemoryLocation::System(SystemMemoryLocation::Wram(off)) => {
                        format!("wram+${off:x}")
                    }
                    MemoryLocation::System(SystemMemoryLocation::IoBbus(off)) => {
                        format!("bbus+${off:x}")
                    }
                    MemoryLocation::System(SystemMemoryLocation::Io(off)) => {
                        format!("io+${off:x}")
                    }
                    MemoryLocation::System(SystemMemoryLocation::Other(off)) => {
                        format!("$00:{off:x}")
                    }
                    MemoryLocation::Cart(CartMemoryLocation::Sram(off)) => {
                        format!("wram+${off:x}")
                    }
                    MemoryLocation::Cart(CartMemoryLocation::Rom(off)) => {
                        format!("rom+${off:x}")
                    }
                    MemoryLocation::Cart(CartMemoryLocation::Unmapped) => "unmapped".to_string(),
                };
                ui.colored_label(DISASM_COLOR_ABSOLUTE, egui::RichText::new(text));
            }
        }
    }

    pub fn show_central_data(&mut self, ui: &mut egui::Ui, data: &DataBlock, cart: &Cart) {
        ui.centered_and_justified(|ui| {
            ui.strong("TODO: data");
        });
    }

    pub fn show_search_panel(&mut self, ui: &mut egui::Ui, rewriter: &mut Rewriter, cart: &Cart) {
        ui.collapsing("Advanced search options", |ui| {
            if ui
                .checkbox(&mut self.search_options.show_code, "Show code blocks")
                .changed()
            {
                self.search_options.needs_reeval = true;
            }
            if ui
                .checkbox(&mut self.search_options.show_data, "Show data blocks")
                .changed()
            {
                self.search_options.needs_reeval = true;
            }
        });
        Self::show_search_bar(ui, &mut self.search_options);
        if self.search_options.needs_reeval {
            self.search_options.needs_reeval = false;
            let mut matcher = nucleo_matcher::Matcher::new(self.search_options.nucleo_cfg.clone());
            let pattern = nucleo_matcher::pattern::Pattern::parse(
                &self.search_options.term,
                self.search_options.case,
                self.search_options.norm,
            );
            let mut buffer = vec![];
            self.search_results = rewriter
                .blocks
                .iter()
                .filter_map(|(id, block)| {
                    if !self.search_options.show_code
                        && matches!(&block.content, BlockContent::Code(_))
                    {
                        return None;
                    }
                    if !self.search_options.show_data
                        && matches!(&block.content, BlockContent::Data(_))
                    {
                        return None;
                    }
                    let mut score = 0;
                    if !self.search_options.term.is_empty() {
                        let name = self.block_names.get(cart, *id, Some(block));
                        let name32 = nucleo_matcher::Utf32Str::new(name, &mut buffer);
                        score = pattern.score(name32, &mut matcher)?;
                    }
                    Some((*id, score))
                })
                .collect();
            if !self.search_options.term.is_empty() {
                self.search_results
                    .sort_by_key(|(id, score)| (core::cmp::Reverse(*score), *id));
            }
        }
        egui_extras::TableBuilder::new(ui)
            .striped(false)
            .vscroll(true)
            .drag_to_scroll(false)
            .column(egui_extras::Column::remainder())
            .body(|body| {
                body.rows(20.0, self.search_results.len(), |mut row| {
                    let (block_id, _score) = self.search_results[row.index()];
                    let Some(block) = rewriter.blocks.get(&block_id) else {
                        return;
                    };
                    row.set_selected(self.selected.is_some_and(|id| id == block_id));
                    row.col(|ui| {
                        let color = match &block.content {
                            BlockContent::Code(_) => CODE_COLOR,
                            BlockContent::Data(_) => DATA_COLOR,
                        };
                        let name = self.block_names.get(cart, block_id, Some(block));
                        let button =
                            egui::Button::new(egui::RichText::new(name).monospace()).fill(color);
                        if ui.add(button).clicked() {
                            if self.selected.is_some_and(|sel| sel == block_id) {
                                self.selected = None;
                            } else {
                                self.selected = Some(block_id);
                            }
                        }
                    });
                });
            });
    }

    fn show_search_bar(ui: &mut egui::Ui, options: &mut SearchOptions) {
        let search_icon_margin = 25;
        let search_icon_offset = search_icon_margin + 5;
        let delete_icon_margin = if options.term.is_empty() { 0 } else { 20 };
        let te_res = egui::TextEdit::singleline(&mut options.term)
            .hint_text("Search for blocks")
            .margin(egui::Margin {
                left: search_icon_offset,
                right: delete_icon_margin,
                ..egui::Margin::ZERO
            })
            .show(ui);
        if te_res.response.changed() {
            options.needs_reeval = true;
        }
        let mut search_icon_rect = te_res.response.rect;
        search_icon_rect.min.x -= search_icon_offset as f32;
        search_icon_rect.set_width(search_icon_margin as _);
        ui.painter_at(search_icon_rect).text(
            search_icon_rect.center(),
            egui::Align2::CENTER_CENTER,
            "",
            egui::FontId::monospace(search_icon_margin as f32 * 0.7),
            ui.style().interact(&te_res.response).text_color(),
        );
        if options.term.is_empty() {
            return;
        }
        let delete_icon_rect = egui::Rect::from_min_max(
            egui::Pos2::new(te_res.response.rect.max.x, te_res.response.rect.min.y),
            egui::Pos2::new(
                te_res.response.rect.max.x + delete_icon_margin as f32,
                te_res.response.rect.max.y,
            ),
        );
        let delete_resp = ui.allocate_rect(delete_icon_rect, egui::Sense::click());
        let delete_icon_painter = ui.painter_at(delete_icon_rect);
        let rect = delete_icon_rect.shrink2(delete_icon_rect.size() * 0.2);
        let delete_icon_style = ui.style().interact(&delete_resp);
        for corners in [
            [rect.left_top(), rect.right_bottom()],
            [rect.left_bottom(), rect.right_top()],
        ] {
            delete_icon_painter.line_segment(corners, delete_icon_style.fg_stroke);
        }
        if delete_resp.hovered() {
            ui.output_mut(|out| out.cursor_icon = egui::CursorIcon::PointingHand)
        }
        if delete_resp.clicked() {
            options.term.clear();
        }
    }
}
