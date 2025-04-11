use eframe::egui;

use crate::{
    disassembly_view::DisassemblyView, error::Errors, project::AppProject, shortcuts::Shortcuts,
};

pub const NAME: &str = "Solar Magic";
pub const DESCRIPTION: &str =
    "is an hack editor for the game Super Mario World for the Super Nintendo Entertainment System";
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

pub struct App {
    pub about_window: bool,
    pub cart_info_window: bool,
    pub project: AppProject,
    pub shortcuts: Shortcuts,
    pub errors: Errors,
    pub disassembly_view: DisassemblyView,
}

impl App {
    pub fn new(args: crate::Args, ctx: &eframe::CreationContext) -> Self {
        let mut slf = Self {
            about_window: false,
            cart_info_window: false,
            project: AppProject::new(),
            shortcuts: Default::default(),
            errors: Errors::new(),
            disassembly_view: DisassemblyView::new(),
        };
        if let Some(path) = args.rom_path {
            slf.project.load(&ctx.egui_ctx, path);
        }
        slf
    }

    pub fn run(args: crate::Args) -> Result<(), eframe::Error> {
        let options = eframe::NativeOptions::default();
        eframe::run_native(
            NAME,
            options,
            Box::new(|ctx| Ok(Box::new(Self::new(args, ctx)))),
        )
    }
}

impl eframe::App for App {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        if ctx.input_mut(|inp| inp.consume_shortcut(&self.shortcuts.open)) {
            self.on_project_open();
        }
        self.project.update(ctx, |err| {
            eprintln!("error: {err}");
            self.errors.add(err.to_string());
        });
        self.overlay(ctx);
        self.errors.show(ctx);
    }
}
