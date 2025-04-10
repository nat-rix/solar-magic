const CRC_TABLE: [u32; 256] = gen_crc32_table();

const fn gen_crc32_table() -> [u32; 256] {
    let mut table = [0; 256];
    let mut x: u32 = 1;
    let mut i = 128;
    while i > 0 {
        x = (x >> 1) ^ ((x & 1) * 0xedb88320);
        let mut j = 0;
        while j < 256 {
            table[i + j] = x ^ table[j];
            j += i << 1;
        }
        i >>= 1;
    }
    table
}

pub fn crc32(bytes: &[u8]) -> u32 {
    bytes.iter().fold(u32::MAX, |mut x, b| {
        x ^= *b as u32;
        (x >> 8) ^ CRC_TABLE[x.to_le_bytes()[0] as usize]
    }) ^ u32::MAX
}
