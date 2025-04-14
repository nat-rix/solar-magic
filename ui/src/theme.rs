use eframe::egui;

pub const fn rgba(v: u32) -> egui::Color32 {
    let [r, g, b, a] = v.to_be_bytes();
    egui::Color32::from_rgba_premultiplied(r, g, b, a)
}

pub fn set_style(ctx: &egui::Context) {
    let theme = ctx.theme();
    let style = match &theme {
        egui::Theme::Dark => default_themes::dark(),
        egui::Theme::Light => return,
    };
    ctx.set_style_of(theme, style);
}

mod default_themes {
    use super::rgba;
    use eframe::egui;
    use egui::{
        Align, CornerRadius,
        FontFamily::*,
        FontId, Margin, Shadow, Spacing, Stroke, Style, TextStyle, Vec2, Visuals,
        style::{
            HandleShape, Interaction, NumericColorSpace, ScrollAnimation, ScrollStyle,
            TextCursorStyle, WidgetVisuals,
        },
    };

    pub fn dark() -> Style {
        let shadow = Shadow {
            offset: [1, 2],
            blur: 4,
            spread: 1,
            color: rgba(0x00_00_00_90),
        };
        let bg = rgba(0x1D_19_16_FF);
        let bg_faint = rgba(0x2E_28_23_FF);
        let primary = rgba(0x4D_75_50_FF);
        let primary_font = primary.gamma_multiply(3.0);
        Style {
            override_text_style: None,
            override_font_id: None,
            override_text_valign: Some(Align::Center),
            text_styles: [
                (TextStyle::Small, FontId::new(11.0, Proportional)),
                (TextStyle::Body, FontId::new(14.0, Proportional)),
                (TextStyle::Monospace, FontId::new(14.0, Monospace)),
                (TextStyle::Button, FontId::new(13.0, Proportional)),
                (TextStyle::Heading, FontId::new(20.0, Proportional)),
            ]
            .into(),
            drag_value_text_style: TextStyle::Monospace,
            wrap_mode: None,
            spacing: Spacing {
                item_spacing: Vec2::new(10.0, 4.0),
                window_margin: Margin::same(8),
                button_padding: Vec2::new(6.0, 2.0),
                menu_margin: Margin::same(10),
                indent: 18.0,
                interact_size: Vec2::new(40.0, 18.0),
                slider_width: 100.0,
                slider_rail_height: 8.0,
                combo_width: 100.0,
                text_edit_width: 280.0,
                icon_width: 16.0,
                icon_width_inner: 12.0,
                icon_spacing: 7.0,
                default_area_size: Vec2::new(600.0, 400.0),
                tooltip_width: 500.0,
                menu_width: 600.0,
                menu_spacing: 5.0,
                indent_ends_with_horizontal_line: false,
                combo_height: 200.0,
                scroll: ScrollStyle {
                    floating: true,
                    bar_width: 9.0,
                    handle_min_length: 12.0,
                    bar_inner_margin: 4.0,
                    bar_outer_margin: 0.0,
                    floating_width: 4.0,
                    floating_allocated_width: 0.0,
                    foreground_color: true,
                    dormant_background_opacity: 0.0,
                    active_background_opacity: 0.4,
                    interact_background_opacity: 0.7,
                    dormant_handle_opacity: 0.2,
                    active_handle_opacity: 0.8,
                    interact_handle_opacity: 1.0,
                },
            },
            interaction: Interaction {
                interact_radius: 5.0,
                resize_grab_radius_side: 5.0,
                resize_grab_radius_corner: 10.0,
                show_tooltips_only_when_still: true,
                tooltip_delay: 0.5,
                tooltip_grace_time: 0.2,
                selectable_labels: true,
                multi_widget_text_select: true,
            },
            visuals: Visuals {
                dark_mode: true,
                override_text_color: None,
                widgets: egui::style::Widgets {
                    noninteractive: WidgetVisuals {
                        bg_fill: rgba(0x1B_1B_1B_FF),
                        weak_bg_fill: rgba(0x1B_1B_1B_FF),
                        bg_stroke: Stroke::new(1.0, rgba(0x3C_3C_3C_FF)),
                        corner_radius: CornerRadius::same(2),
                        fg_stroke: Stroke::new(1.0, primary_font),
                        expansion: 0.0,
                    },
                    inactive: WidgetVisuals {
                        bg_fill: primary,
                        weak_bg_fill: bg_faint,
                        bg_stroke: Stroke::new(0.0, rgba(0x00_00_00_00)),
                        corner_radius: CornerRadius::same(0),
                        fg_stroke: Stroke::new(2.0, rgba(0xE0_F0_D0_FF)),
                        expansion: 0.0,
                    },
                    hovered: WidgetVisuals {
                        bg_fill: rgba(0x46_46_46_FF),
                        weak_bg_fill: rgba(0x46_46_46_FF),
                        bg_stroke: Stroke::new(1.0, rgba(0x96_96_96_FF)),
                        corner_radius: CornerRadius::same(2),
                        fg_stroke: Stroke::new(1.5, rgba(0xF0_F0_F0_FF)),
                        expansion: 1.0,
                    },
                    active: WidgetVisuals {
                        bg_fill: rgba(0x37_37_37_FF),
                        weak_bg_fill: rgba(0x37_37_37_FF),
                        bg_stroke: Stroke::new(1.0, rgba(0xFF_FF_FF_FF)),
                        corner_radius: CornerRadius::same(2),
                        fg_stroke: Stroke::new(2.0, rgba(0xFF_FF_FF_FF)),
                        expansion: 1.0,
                    },
                    open: WidgetVisuals {
                        bg_fill: rgba(0x1B_1B_1B_FF),
                        weak_bg_fill: rgba(0x2D_2D_2D_FF),
                        bg_stroke: Stroke::new(1.0, rgba(0x3C_3C_3C_FF)),
                        corner_radius: CornerRadius::same(2),
                        fg_stroke: Stroke::new(1.0, rgba(0xD2_D2_D2_FF)),
                        expansion: 0.0,
                    },
                },
                selection: egui::style::Selection {
                    bg_fill: primary,
                    stroke: Stroke::new(1.0, rgba(0x00_00_00_FF)),
                },
                hyperlink_color: rgba(0x5A_AA_FF_FF),
                faint_bg_color: rgba(0x05_05_05_00),
                extreme_bg_color: rgba(0x0A_0A_0A_FF),
                code_bg_color: rgba(0x40_40_40_FF),
                warn_fg_color: rgba(0xFF_8F_00_FF),
                error_fg_color: rgba(0xFF_00_00_FF),
                window_corner_radius: CornerRadius::same(0),
                window_shadow: shadow,
                window_fill: bg,
                window_stroke: Stroke::new(1.0, rgba(0x3C_3C_3C_FF)),
                window_highlight_topmost: true,
                menu_corner_radius: CornerRadius::same(0),
                panel_fill: bg,
                popup_shadow: shadow,
                resize_corner_size: 15.0,
                text_cursor: TextCursorStyle {
                    stroke: Stroke::new(2.0, rgba(0xC0_DE_FF_FF)),
                    preview: false,
                    blink: true,
                    on_duration: 0.5,
                    off_duration: 0.5,
                },
                clip_rect_margin: 3.0,
                button_frame: true,
                collapsing_header_frame: true,
                indent_has_left_vline: false,
                striped: false,
                slider_trailing_fill: true,
                handle_shape: HandleShape::Circle,
                interact_cursor: None,
                image_loading_spinners: true,
                numeric_color_space: NumericColorSpace::GammaByte,
            },
            animation_time: 0.04,
            explanation_tooltips: true,
            url_in_tooltip: true,
            always_scroll_the_only_direction: false,
            scroll_animation: ScrollAnimation {
                points_per_second: 1000.0,
                duration: (0.1..=0.3).into(),
            },
            ..Default::default()
        }
    }
}
