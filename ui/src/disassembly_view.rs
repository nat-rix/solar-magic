use solar_magic::addr::Addr;

use crate::project::Project;

const SCROLL_SPEED_FACTOR: f32 = 0.1;

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

        egui::Grid::new("disassembly-grid")
            .num_columns(3)
            .show(ui, |ui| {
                self.show_grid_content(project, ui);
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
                let name =
                    opcode.name(solar_magic::instruction::InstructionNamingConvention::Descriptive);
                let instr_size = instr.instruction.size();

                Self::show_bytes(project, (0..instr_size).map(|i| addr.add16(i.into())), ui);

                ui.monospace(name);

                addr = addr.add24(instr_size.into());
            } else {
                Self::show_bytes(project, [addr], ui);
                ui.label("<data byte>");
                addr = addr.add24(1);
            }
            ui.end_row();
        }
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
    }
}
