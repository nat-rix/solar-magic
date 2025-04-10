use eframe::egui;
use std::{
    path::{Path, PathBuf},
    thread::JoinHandle,
};

use solar_magic::{analyzer::Analyzer, cart::Cart, original_cart::OriginalCart};

pub struct AppProject {
    picker: Option<JoinHandle<Option<PathBuf>>>,
    loader: Option<JoinHandle<Result<Project, std::io::Error>>>,
    project: Option<Project>,
}

impl AppProject {
    pub fn new() -> Self {
        Self {
            picker: None,
            loader: None,
            project: None,
        }
    }

    pub fn load(&mut self, ctx: &egui::Context, path: PathBuf) {
        let ctx = ctx.clone();
        self.loader = Some(std::thread::spawn(move || {
            let res = Project::load(path);
            ctx.request_repaint();
            res
        }));
    }

    pub fn update(&mut self, ctx: &egui::Context, on_err: impl FnOnce(std::io::Error)) {
        if let Some(picker) = self.picker.take_if(|handle| handle.is_finished()) {
            if let Some(path) = picker.join().ok().flatten() {
                self.load(ctx, path);
            }
        }
        if let Some(loader) = self.loader.take_if(|handle| handle.is_finished()) {
            let failable_project = loader
                .join()
                .map_err(|_| std::io::Error::other("loader thread died"))
                .and_then(core::convert::identity);
            match failable_project {
                Ok(project) => self.project = Some(project),
                Err(err) => on_err(err),
            }
        }
    }

    pub fn start_file_picker(&mut self) {
        if self.picker.is_some() {
            return;
        }
        self.picker = Some(std::thread::spawn(|| rfd::FileDialog::new().pick_file()));
    }
}

#[derive(Clone)]
pub struct Project {
    smw: OriginalCart,
    analyzer: Analyzer,
}

impl Project {
    pub fn load(path: impl AsRef<Path>) -> Result<Self, std::io::Error> {
        let bytes = std::fs::read(path)?;
        let cart = Cart::from_bytes(bytes);
        let smw = OriginalCart::new(cart)
            .map_err(|_| std::io::Error::other("not an original Super Mario World cart"))?;

        let mut analyzer = solar_magic::analyzer::Analyzer::new();
        analyzer.add_vectors(&smw.cart);
        analyzer.analyze(&smw.cart);

        Ok(Self { smw, analyzer })
    }
}
