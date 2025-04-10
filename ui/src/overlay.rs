use eframe::egui;

impl crate::app::App {
    pub fn overlay(&mut self, ctx: &egui::Context) {
        self.about_window(ctx);
        egui::TopBottomPanel::top("menu-panel").show(ctx, |ui| {
            self.menu(ui);
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
                if ui.button("Exit").clicked() {
                    ui.ctx().send_viewport_cmd(egui::ViewportCommand::Close);
                }
            });
            ui.menu_button("Help", |ui| {
                if ui.button(format!("About {}", crate::app::NAME)).clicked() {
                    self.about_window ^= true;
                }
            });
        });
    }

    pub fn on_project_open(&mut self) {
        self.project.start_file_picker();
    }
}
