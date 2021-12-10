use pairing_bn256::bn256::Fr;
pub fn add_mod(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
    let modulus: &[u64; 4] = &[
        0x43e1f593f0000001,
        0x2833e84879b97091,
        0xb85045b68181585d,
        0x30644e72e131a029,
    ];
    let mut r0: u64;
    let mut r1: u64;
    let mut r2: u64;
    let mut r3: u64;
    unsafe {
        asm!(
            // load a array to former register
            "mov r8, qword ptr [{a_ptr} + 0]",
            "mov r9, qword ptr [{a_ptr} + 8]",
            "mov r10, qword ptr [{a_ptr} + 16]",
            "mov r11, qword ptr [{a_ptr} + 24]",

            // add a array and b array with carry
            "add r8, qword ptr [{b_ptr} + 0]",
            "adc r9, qword ptr [{b_ptr} + 8]",
            "adc r10, qword ptr [{b_ptr} + 16]",
            "adc r11, qword ptr [{b_ptr} + 24]",

            // copy result array to latter register
            "mov r12, r8",
            "mov r13, r9",
            "mov r14, r10",
            "mov r15, r11",

            // mod reduction
            "sub r12, qword ptr [{m_ptr} + 0]",
            "sbb r13, qword ptr [{m_ptr} + 8]",
            "sbb r14, qword ptr [{m_ptr} + 16]",
            "sbb r15, qword ptr [{m_ptr} + 24]",

            // if sum >= mod return latter register
            // if sum <= mod return former register
            "cmovnc r8, r12",
            "cmovnc r9, r13",
            "cmovnc r10, r14",
            "cmovnc r11, r15",

            m_ptr = in(reg) modulus.as_ptr(),
            a_ptr = in(reg) a.as_ptr(),
            b_ptr = in(reg) b.as_ptr(),
            out("r8") _,
            out("r9") _,
            out("r10") _,
            out("r11") _,
            out("r12") r0,
            out("r13") r1,
            out("r14") r2,
            out("r15") r3,
            options(pure, readonly, nostack)
        );
    }

    [r0, r1, r2, r3]
}

#[cfg(test)]
mod asembly_tests {
    use super::*;

    #[test]
    fn add_mod_test() {
        let fa = Fr::from_raw([
            0x43e1f593f0000001,
            0x2833e84879b97091,
            0xb85045b68181585d,
            0x30644e72e131a029,
        ]);
        let fb = Fr::from_raw([
            0x0000000000000001,
            0x0000000000000000,
            0x0000000000000000,
            0x0000000000000000,
        ]);
        let fc = fa.add(&fb);
        let a: [u64; 4] = [
            0x43e1f593f0000001,
            0x2833e84879b97091,
            0xb85045b68181585d,
            0x30644e72e131a029,
        ];
        let b: [u64; 4] = [
            0x0000000000000001,
            0x0000000000000000,
            0x0000000000000000,
            0x0000000000000000,
        ];
        let c = Fr::from_raw(add_mod(&a, &b));
        assert_eq!(fc, c);
    }
}
