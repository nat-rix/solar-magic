use eframe::egui;

use crate::app::PanelViewType;

impl crate::app::App {
    pub fn overlay(&mut self, ctx: &egui::Context) {
        self.about_window(ctx);
        self.show_cart_info(ctx);
        egui::TopBottomPanel::top("menu-panel").show(ctx, |ui| {
            self.menu(ui);
            ui.horizontal(|ui| {
                ui.spacing_mut().item_spacing.x = 1.0;
                for variant in PanelViewType::variants() {
                    let button =
                        egui::Button::new(variant.name()).selected(self.panel_view == variant);
                    if ui.add(button).clicked() {
                        self.panel_view = variant;
                    }
                }
            });
        });

        self.loader_panel(ctx);

        egui::CentralPanel::default()
            .frame(egui::Frame::central_panel(&ctx.style()).inner_margin(0))
            .show(ctx, |ui| match self.panel_view {
                PanelViewType::Disassembly => {
                    self.show_disassembly(ui);
                }
                PanelViewType::Graph => {
                    ui.label("TODO: graph");
                }
            });
    }

    pub fn loader_panel(&mut self, ctx: &egui::Context) {
        let desc = self.project.get_description();
        if desc.is_some() {
            ctx.output_mut(|out| out.cursor_icon = egui::CursorIcon::Progress);
        }
        egui::TopBottomPanel::bottom("thread-info-panel")
            .resizable(false)
            .show_animated(ctx, desc.is_some(), |ui| {
                if let Some(desc) = desc {
                    ui.horizontal(|ui| {
                        ui.spinner();
                        ui.small(desc);
                    });
                }
            });
    }

    pub fn about_window(&mut self, ctx: &egui::Context) {
        egui::Window::new(format!("About {}", crate::app::NAME))
            .id("about-window".into())
            .open(&mut self.about_window)
            .collapsible(false)
            .scroll(false)
            .resizable(false)
            .default_pos(ctx.screen_rect().center())
            .show(ctx, |ui| {
                ui.horizontal(|ui| {
                    ui.heading(crate::app::NAME);
                    ui.weak(format!("v{}", crate::app::VERSION))
                });
                ui.separator();
                ui.label(format!("{} {}", crate::app::NAME, crate::app::DESCRIPTION))
            });
    }

    pub fn menu(&mut self, ui: &mut egui::Ui) {
        egui::menu::bar(ui, |ui| {
            ui.menu_button("File", |ui| {
                let open_btn = egui::Button::new("Open")
                    .shortcut_text(ui.ctx().format_shortcut(&self.shortcuts.open));
                if ui.add(open_btn).clicked() {
                    self.project.start_file_picker();
                }
                if ui.button("Show Cartridge Info").clicked() {
                    self.cart_info_window ^= true;
                }
                ui.separator();
                if ui.button("Exit").clicked() {
                    ui.ctx().send_viewport_cmd(egui::ViewportCommand::Close);
                }
            });
            ui.menu_button("Help", |ui| {
                if ui.button(format!("About {}", crate::app::NAME)).clicked() {
                    self.about_window ^= true;
                }
            });
            #[cfg(debug_assertions)]
            {
                ui.with_layout(egui::Layout::right_to_left(egui::Align::Max), |ui| {
                    ui.horizontal_centered(|ui| {
                        ui.label(
                            egui::RichText::new("Debug build")
                                .small()
                                .strong()
                                .color(ui.visuals().warn_fg_color),
                        )
                        .on_hover_text("egui was compiled with debug assertions enabled.");
                    });
                    ui.menu_button("Debug", |ui| {
                        egui::ScrollArea::vertical()
                            .max_width(100.0)
                            .max_height(300.0)
                            .show(ui, |ui| {
                                ui.horizontal(|ui| {
                                    let mut doh = ui.ctx().debug_on_hover();
                                    ui.checkbox(&mut doh, "Debug on hover");
                                    if doh != ui.ctx().debug_on_hover() {
                                        ui.ctx().set_debug_on_hover(doh);
                                    }
                                    if ui.button("reset style").clicked() {
                                        crate::theme::set_style(ui.ctx());
                                    }
                                });
                                ui.ctx().clone().settings_ui(ui);
                            });
                    });
                    ui.add_space(ui.available_width());
                });
            }
            egui::warn_if_debug_build(ui);
        });
    }

    pub fn on_project_open(&mut self) {
        self.project.start_file_picker();
    }
}
