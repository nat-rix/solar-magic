use eframe::egui;

impl crate::app::App {
    pub fn show_cart_info(&mut self, ctx: &egui::Context) {
        egui::Window::new("Cart Info")
            .id("cart-info-window".into())
            .open(&mut self.cart_info_window)
            .collapsible(false)
            .default_pos(ctx.screen_rect().center())
            .show(ctx, |ui| {
                if let Some(cart) = &self.project.cart {
                    let hdr = &cart.header;
                    egui::Grid::new("cart-info-grid")
                        .num_columns(2)
                        .striped(true)
                        .show(ui, |ui| {
                            ui.strong("Title");
                            ui.label(hdr.title.to_string());
                            ui.end_row();

                            ui.strong("Edition");
                            ui.label(match cart.edition {
                                solar_magic::original_cart::Edition::International => {
                                    "International"
                                }
                                solar_magic::original_cart::Edition::Japanese => "Japanese",
                                solar_magic::original_cart::Edition::Arcade => "Arcade",
                                solar_magic::original_cart::Edition::EuropeRev0 => {
                                    "European Old Revision"
                                }
                                solar_magic::original_cart::Edition::EuropeRev1 => {
                                    "European New Revision"
                                }
                            });
                            ui.end_row();

                            ui.strong("Mapping Type");
                            ui.label(match cart.cart.cfg.mapping_type {
                                solar_magic::cart::MappingType::LoRom => "LoRom",
                                solar_magic::cart::MappingType::HiRom => "HiRom",
                                solar_magic::cart::MappingType::ExHiRom => "ExHiRom",
                                _ => "Unknown",
                            });
                            ui.end_row();

                            ui.strong("ROM size");
                            ui.label(cart.header.rom_size.to_string());
                            ui.end_row();

                            ui.strong("SRAM size");
                            ui.label(cart.header.ram_size.to_string());
                            ui.end_row();
                        });
                } else {
                    ui.label("No cartridge loaded");
                }
            });
    }
}
