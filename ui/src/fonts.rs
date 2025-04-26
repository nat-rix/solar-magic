use std::sync::Arc;

use eframe::egui;

pub const OPEN_SANS: &[u8] =
    include_bytes!("../../assets/OpenSans/OpenSans-VariableFont_wdth,wght.ttf");
pub const MARTIAN_MONO: &[u8] =
    include_bytes!("../../assets/MartianMono/MartianMonoNerdFont-Regular.ttf");

fn tweak(scale: f32) -> egui::FontTweak {
    egui::FontTweak {
        scale,
        ..Default::default()
    }
}

pub fn set_fonts(ctx: &egui::Context) {
    let [mono_tweak, sans_tweak] = [0.9, 1.05].map(tweak);
    let defs = egui::FontDefinitions {
        font_data: [
            (
                "Open Sans".to_string(),
                Arc::new(egui::FontData::from_static(OPEN_SANS).tweak(sans_tweak)),
            ),
            (
                "Martian Mono".to_string(),
                Arc::new(egui::FontData::from_static(MARTIAN_MONO).tweak(mono_tweak)),
            ),
        ]
        .into(),
        families: [
            (
                egui::FontFamily::Proportional,
                vec!["Open Sans".to_string(), "Martian Mono".to_string()],
            ),
            (
                egui::FontFamily::Monospace,
                vec!["Martian Mono".to_string(), "Open Sans".to_string()],
            ),
        ]
        .into(),
    };
    ctx.set_fonts(defs);
}
