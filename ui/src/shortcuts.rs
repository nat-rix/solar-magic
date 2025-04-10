use eframe::egui::KeyboardShortcut;

#[derive(Debug, Clone)]
pub struct Shortcuts {
    pub open: KeyboardShortcut,
}

impl Default for Shortcuts {
    fn default() -> Self {
        use eframe::egui::{Key, Modifiers};
        Self {
            open: KeyboardShortcut::new(Modifiers::COMMAND, Key::O),
        }
    }
}
