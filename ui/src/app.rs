use eframe::egui;

use crate::{
    disassembly_view::DisassemblyView, error::Errors, project::AppProject, shortcuts::Shortcuts,
};

pub const NAME: &str = "Solar Magic";
pub const DESCRIPTION: &str =
    "is a  Level Editor for the game Super Mario World on the Super Nintendo Entertainment System.";
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

macro_rules! define_panel_view_types {
    ($($var:ident),* $(,)?) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum PanelViewType {
            $($var),*
        }

        impl PanelViewType {
            pub const fn variants() -> [Self; {[$(Self::$var),*].len()}] {
                [$(Self::$var),*]
            }

            pub const fn name(&self) -> &'static str {
                match self {
                    $(Self::$var => stringify!($var)),*
                }
            }
        }
    };
}

define_panel_view_types! {
    Disassembly,
    Graph,
}

pub struct App {
    pub about_window: bool,
    pub cart_info_window: bool,
    pub project: AppProject,
    pub shortcuts: Shortcuts,
    pub errors: Errors,
    pub disassembly_view: DisassemblyView,
    pub panel_view: PanelViewType,
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
            panel_view: PanelViewType::Disassembly,
        };
        crate::theme::set_style(&ctx.egui_ctx);
        crate::fonts::set_fonts(&ctx.egui_ctx);
        if let Some(path) = args.rom_path {
            slf.project.load_cart(&ctx.egui_ctx, path);
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
