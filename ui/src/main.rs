mod addr_widget;
mod app;
mod cart_info;
mod data_block_view;
mod disassembly_view;
mod error;
mod fonts;
mod overlay;
mod project;
mod shortcuts;
mod theme;

use clap::Parser;
use std::path::PathBuf;

/// Solar Magic
#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Args {
    /// Path to the original SMW rom
    pub rom_path: Option<PathBuf>,
}

fn main_err() -> Result<(), String> {
    let args = Args::parse();

    app::App::run(args).map_err(|err| err.to_string())
}

fn main() {
    if let Err(err) = main_err() {
        eprintln!("\x1b[1;31merror:\x1b[m {err}");
    }
}
