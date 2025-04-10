use eframe::egui;

pub struct Errors {
    errs: Vec<(usize, String)>,
    id: usize,
}

impl Errors {
    pub fn new() -> Self {
        Self {
            errs: vec![],
            id: 0,
        }
    }

    pub fn add(&mut self, err: String) {
        self.errs.push((self.id, err));
        self.id = self.id.wrapping_add(1);
    }

    pub fn show(&mut self, ctx: &egui::Context) {
        self.errs.retain_mut(|(id, err)| {
            let mut open = true;
            egui::Window::new("Error")
                .id(format!("error-window-id{id}").into())
                .open(&mut open)
                .collapsible(false)
                .show(ctx, |ui| {
                    ui.heading("An error occured!");
                    ui.separator();
                    ui.colored_label(ui.visuals().error_fg_color, err.clone());
                });
            open
        });
    }
}
