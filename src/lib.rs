const INTERNAL_LABEL_START: u32 = 0xF000_000;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GeckoErr {
    InjectionAddressTooSmall(u32),
    InjectionAddressTooLarge(u32),
    InjectionAddressMisaligned(u32),
    BranchOffsetTooLarge(i32),
    LabelReused(u32),
    LabelNotFound(u32),
    InternalLabel(u32),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Cmp { Eq, NotEq, Less, LessOrEq, Greater, GreaterOrEq }

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Reg(pub u32);

impl Reg {
    pub fn fighter_data() -> Reg { Reg(30) }
    pub fn fighter_gobj() -> Reg { Reg(31) }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum DataSize { Byte, Half, Word }

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Asm {
    /// Please note that the labels >= 0xF000_0000 are reserved for internal use.
    Label(u32),
    Load { addr: Reg, offset: i16, to: Reg, size: DataSize },
    LoadImm { num: u32, to: Reg },
    Save { addr: Reg, offset: i16, from: Reg, size: DataSize },
    Copy { from: Reg, to: Reg },

    CmpJmp { label: u32, a: Reg, b: Reg, mode: Cmp },
    JmpAndLink { label: u32 },
    Jmp { label: u32 },

    /// Injects scratch data. Address will be put in addr register.
    Data { addr: Reg, words: u32 },

    Add { a: Reg, b: Reg, to: Reg },
    Sub { a: Reg, b: Reg, to: Reg },
    Mul { a: Reg, b: Reg, to: Reg },
    Div { a: Reg, b: Reg, to: Reg },
    AddImm { a: Reg, num: i16, to: Reg },
    MulImm { a: Reg, num: i16, to: Reg },
}

pub fn create_code(
    title: &str,
    description: &str,
    asm: &[Asm],
) -> Result<String, GeckoErr> {
    let assembled = assemble(0, asm)?; // todo insertion address
    Ok(gecko_string(title, description, &assembled))
}

// Panics if `asm.len() % 2 != 0`. This is required for gecko codes.
pub fn gecko_string(
    title: &str,
    description: &str,
    asm: &[u32],
) -> String {
    let mut gecko = String::with_capacity(title.len() + description.len() + asm.len()*9 + 16);

    gecko.push('$');
    for l in title.lines() { gecko.push_str(l); }
    gecko.push('\n');

    for l in description.lines() { 
        gecko.push('*');
        gecko.push_str(l);
        gecko.push('\n');
    }

    assert!(asm.len() % 2 == 0);
    for n in asm.chunks_exact(2) {
        use std::fmt::Write;
        write!(&mut gecko, "{:08X} {:08X}\n", n[0], n[1]).unwrap();
    }

    gecko
}

// ASM REFERENCE: https://math-atlas.sourceforge.net/devel/assembly/ppc_isa.pdf

fn at(num: u32, bit_end: u32) -> u32 { num << (32 - bit_end) }
fn op(op: u32) -> u32 { at(op, 6) }
fn imm(n: i16) -> u32 { 
    let mut b = [0u8; 4];
    b[2..4].copy_from_slice(&n.to_be_bytes());
    u32::from_be_bytes(b)
}
fn immu(n: u16) -> u32 { n as u32 }

fn mfspr(rt: Reg, spr: u32) -> u32 { op(31) | at(rt.0, 11) | at(spr, 21) | at(339, 30) }
fn mflr(r: Reg) -> u32 { mfspr(r, 8) }

fn lbz(rt: Reg, ra: Reg, d: i16) -> u32 { op(34) | at(rt.0, 11) | at(ra.0, 16) | imm(d) }
fn lhz(rt: Reg, ra: Reg, d: i16) -> u32 { op(40) | at(rt.0, 11) | at(ra.0, 16) | imm(d) }
fn lwz(rt: Reg, ra: Reg, d: i16) -> u32 { op(32) | at(rt.0, 11) | at(ra.0, 16) | imm(d) }

fn stb(rs: Reg, ra: Reg, d: i16) -> u32 { op(38) | at(rs.0, 11) | at(ra.0, 16) | imm(d) }
fn sth(rs: Reg, ra: Reg, d: i16) -> u32 { op(44) | at(rs.0, 11) | at(ra.0, 16) | imm(d) }
fn stw(rs: Reg, ra: Reg, d: i16) -> u32 { op(36) | at(rs.0, 11) | at(ra.0, 16) | imm(d) }

fn addi  (rt: Reg, ra: Reg, si: i16) -> u32 { op(14) | at(rt.0, 11) | at(ra.0, 16) | imm(si) }
fn addiu (rt: Reg, ra: Reg, si: u16) -> u32 { op(14) | at(rt.0, 11) | at(ra.0, 16) | immu(si) }
fn addisu(rt: Reg, ra: Reg, si: u16) -> u32 { op(15) | at(rt.0, 11) | at(ra.0, 16) | immu(si) }
fn mulli (rt: Reg, ra: Reg, si: i16) -> u32 { op( 7) | at(rt.0, 11) | at(ra.0, 16) | imm(si) }

fn add  (rt: Reg, ra: Reg, rb: Reg) -> u32 { op(31) | at(rt.0, 11) | at(ra.0, 16) | at(rb.0, 21) | at(266, 31) }
fn sub  (rt: Reg, ra: Reg, rb: Reg) -> u32 { op(31) | at(rt.0, 11) | at(ra.0, 16) | at(rb.0, 21) | at( 40, 31) }
fn mullw(rt: Reg, ra: Reg, rb: Reg) -> u32 { op(31) | at(rt.0, 11) | at(ra.0, 16) | at(rb.0, 21) | at(235, 31) }
fn divw (rt: Reg, ra: Reg, rb: Reg) -> u32 { op(31) | at(rt.0, 11) | at(ra.0, 16) | at(rb.0, 21) | at(491, 31) }

fn cmpw(a: Reg, b: Reg) -> u32 { op(31) | at(a.0, 16) | at(b.0, 21) }

fn b(word_offset: i32) -> Result<u32, GeckoErr> { 
    // Check that the offset will not overflow when converted to a 24 bit number
    if word_offset < -8_388_608 || word_offset > 8_388_607 { return Err(GeckoErr::BranchOffsetTooLarge(word_offset)); }

    let bytes = word_offset.to_be_bytes();
    Ok(op(18) | at(bytes[1] as u32, 14) | at(bytes[2] as u32, 22) | at(bytes[3] as u32, 30))
}

fn bl(word_offset: i32) -> Result<u32, GeckoErr> { b(word_offset).map(|n| n | 1) }

fn bc(bo: u32, bi: u32, word_offset: i32) -> Result<u32, GeckoErr> { 
    // Check that the offset will not overflow when converted to a 14 bit number
    if word_offset < -8192 || word_offset > 8191 { return Err(GeckoErr::BranchOffsetTooLarge(word_offset)); }

    let bytes = word_offset.to_be_bytes();
    Ok(
        op(16) | at(bo, 11) | at(bi, 16)
        | at(bytes[2] as u32 & 0b0011_111, 22) | at(bytes[3] as u32, 30)
    )
}

// https://math-atlas.sourceforge.net/devel/assembly/ppc_isa.pdf#page=160
fn beq(word_offset: i32) -> Result<u32, GeckoErr> { bc( 4, 0, word_offset) }
fn bne(word_offset: i32) -> Result<u32, GeckoErr> { bc(24, 0, word_offset) }
fn blt(word_offset: i32) -> Result<u32, GeckoErr> { bc(16, 0, word_offset) }
fn ble(word_offset: i32) -> Result<u32, GeckoErr> { bc(20, 0, word_offset) }
fn bgt(word_offset: i32) -> Result<u32, GeckoErr> { bc( 8, 0, word_offset) }
fn bge(word_offset: i32) -> Result<u32, GeckoErr> { bc(12, 0, word_offset) }

pub fn assemble(injection_address: u32, pseudo_asm: &[Asm]) -> Result<Vec<u32>, GeckoErr> {
    let mut asm = Vec::with_capacity(1024);
    let mut labels: Vec<(u32, u32)> = Vec::with_capacity(256); // (label, instr_idx)

    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    enum JmpMode {
        Unconditional,
        WithLink,
        Cmp(Cmp),
    }

    let mut jumps: Vec<(u32, u32, JmpMode)> = Vec::with_capacity(256); // (label, instr_idx, mode)
    let mut next_internal_label = INTERNAL_LABEL_START;

    // gecko injection header ----------------------------------
    
    if injection_address < 0x8000_0000  { return Err(GeckoErr::InjectionAddressTooSmall(injection_address)); }
    if injection_address >= 0x8180_0000 { return Err(GeckoErr::InjectionAddressTooLarge(injection_address)); }
    if injection_address % 4 != 0       { return Err(GeckoErr::InjectionAddressMisaligned(injection_address)); }
    asm.push(injection_address - 0x8000_0000 + 0xC200_0000);
    asm.push(0); // number of lines written later

    // write asm ------------------------------------------------

    for instr in pseudo_asm.iter().copied() {
        match instr {
            Asm::Label(new_l) => {
                if new_l >= INTERNAL_LABEL_START { return Err(GeckoErr::InternalLabel(new_l)); }
                if labels.iter().any(|(prev_l, _)| *prev_l == new_l) { return Err(GeckoErr::LabelReused(new_l)); }

                labels.push((new_l, asm.len() as u32));
            }

            Asm::Load { addr, offset, to, size } => {
                asm.push(match size {
                    DataSize::Byte => lbz(to, addr, offset),
                    DataSize::Half => lhz(to, addr, offset),
                    DataSize::Word => lwz(to, addr, offset),
                })
            }

            Asm::LoadImm { num, to } => {
                if num > 0xFFFF {
                    asm.push(addisu(to, Reg(0), (num >> 16) as u16));
                    asm.push(addiu(to, to, (num & 0xFFFF) as u16));
                } else {
                    asm.push(addiu(to, Reg(0), (num & 0xFFFF) as u16));
                }
            }

            Asm::Save { addr, offset, from, size } => {
                asm.push(match size {
                    DataSize::Byte => stb(from, addr, offset),
                    DataSize::Half => sth(from, addr, offset),
                    DataSize::Word => stw(from, addr, offset),
                })
            }

            Asm::Copy { from, to } => asm.push(addi(to, from, 0)),

            Asm::CmpJmp { label, a, b, mode } => {
                asm.push(cmpw(a, b));
                jumps.push((label, asm.len() as u32, JmpMode::Cmp(mode)));
                asm.push(0); // written later
            }

            Asm::JmpAndLink { label } => {
                jumps.push((label, asm.len() as u32, JmpMode::WithLink));
                asm.push(0); // written later
            }

            Asm::Jmp { label } => {
                jumps.push((label, asm.len() as u32, JmpMode::Unconditional));
                asm.push(0); // written later
            }

            Asm::Data { addr, words } => {
                jumps.push((next_internal_label, asm.len() as u32, JmpMode::WithLink));
                asm.push(0); // written later

                for _ in 0..words { asm.push(0) }

                labels.push((next_internal_label, asm.len() as u32));
                asm.push(mflr(addr));

                next_internal_label += 1;
            }

            Asm::Add { a, b, to } => asm.push(add(to, b, a)),
            Asm::Sub { a, b, to } => asm.push(sub(to, b, a)),
            Asm::Mul { a, b, to } => asm.push(mullw(to, b, a)),
            Asm::Div { a, b, to } => asm.push(divw(to, b, a)),
            Asm::AddImm { a, num, to } => asm.push(addi(to, a, num)),
            Asm::MulImm { a, num, to } => asm.push(mulli(to, a, num)),
        }
    }

    // resolve and write jumps ---------------------------------------------

    for (label, asm_idx, mode) in jumps.iter().copied() {
        let label_idx = match labels.iter().find(|(l, _)| *l == label) {
            Some((_, l)) => *l,
            None => return Err(GeckoErr::LabelNotFound(label)),
        };

        let word_offset = label_idx as i32 - asm_idx as i32;

        asm[asm_idx as usize] = match mode {
            JmpMode::Unconditional => b(word_offset)?,
            JmpMode::WithLink => bl(word_offset)?,
            JmpMode::Cmp(Cmp::Eq)          => beq(word_offset)?,
            JmpMode::Cmp(Cmp::NotEq)       => bne(word_offset)?,
            JmpMode::Cmp(Cmp::Less)        => blt(word_offset)?,
            JmpMode::Cmp(Cmp::LessOrEq)    => ble(word_offset)?,
            JmpMode::Cmp(Cmp::Greater)     => bgt(word_offset)?,
            JmpMode::Cmp(Cmp::GreaterOrEq) => bge(word_offset)?,
        }
    }

    // TODO add injection instruction + add nop if needed + write number of lines

    Ok(asm)
}
