use eframe::egui;
use solar_magic::addr::Addr;

fn to_f64(addr: Addr) -> f64 {
    addr.to_u32() as _
}

fn from_f64(num: f64) -> Addr {
    Addr::from_u32(num.clamp(0.0, Addr::MAX.to_u32() as _) as u32)
}

fn addr_formatter<Unused>(val: f64, _: Unused) -> String {
    from_f64(val).to_string()
}

fn addr_parser(text: &str) -> Option<f64> {
    fn trim(text: &str) -> &str {
        let val = text.trim().trim_start_matches("0x");
        if val.is_empty() {
            return "0";
        }
        val
    }
    let addr = if let Some((bank, addr)) = text.split_once(':') {
        let bank = u8::from_str_radix(trim(bank), 16).ok()?;
        let addr = u16::from_str_radix(trim(addr), 16).ok()?;
        Addr::new(bank, addr)
    } else {
        Addr::from_u32(u32::from_str_radix(text.trim().trim_start_matches("0x"), 16).ok()?)
    };
    Some(to_f64(addr))
}

pub fn addr_drag(addr: &mut Addr) -> egui::DragValue {
    egui::DragValue::from_get_set(|val| {
        if let Some(val) = val {
            *addr = from_f64(val)
        }
        to_f64(*addr)
    })
    .max_decimals(0)
    .range(to_f64(Addr::NULL)..=to_f64(Addr::MAX))
    .speed(10.0)
    .custom_formatter(addr_formatter)
    .custom_parser(addr_parser)
}
