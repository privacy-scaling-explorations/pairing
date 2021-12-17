use pairing_bn256::bn256::Fr;

const MODULUS: &[u64; 4] = &[
    0x43e1f593f0000001,
    0x2833e84879b97091,
    0xb85045b68181585d,
    0x30644e72e131a029,
];

pub fn add(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
    let mut r0: u64;
    let mut r1: u64;
    let mut r2: u64;
    let mut r3: u64;
    unsafe {
        asm!(
            // load a array to former registers
            "mov r8, qword ptr [{a_ptr} + 0]",
            "mov r9, qword ptr [{a_ptr} + 8]",
            "mov r10, qword ptr [{a_ptr} + 16]",
            "mov r11, qword ptr [{a_ptr} + 24]",

            // add a array and b array with carry
            "add r8, qword ptr [{b_ptr} + 0]",
            "adc r9, qword ptr [{b_ptr} + 8]",
            "adc r10, qword ptr [{b_ptr} + 16]",
            "adc r11, qword ptr [{b_ptr} + 24]",

            // copy result array to latter registers
            "mov r12, r8",
            "mov r13, r9",
            "mov r14, r10",
            "mov r15, r11",

            // mod reduction
            "sub r12, qword ptr [{m_ptr} + 0]",
            "sbb r13, qword ptr [{m_ptr} + 8]",
            "sbb r14, qword ptr [{m_ptr} + 16]",
            "sbb r15, qword ptr [{m_ptr} + 24]",

            // if carry copy former registers to out areas
            "cmovc r12, r8",
            "cmovc r13, r9",
            "cmovc r14, r10",
            "cmovc r15, r11",

            m_ptr = in(reg) MODULUS.as_ptr(),
            a_ptr = in(reg) a.as_ptr(),
            b_ptr = in(reg) b.as_ptr(),
            out("r12") r0,
            out("r13") r1,
            out("r14") r2,
            out("r15") r3,
            options(pure, readonly, nostack)
        );
    }
    [r0, r1, r2, r3]
}

pub fn sub(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
    let mut r0: u64;
    let mut r1: u64;
    let mut r2: u64;
    let mut r3: u64;
    unsafe {
        asm!(
            // load a array to former registers
            "mov r8, qword ptr [{a_ptr} + 0]",
            "mov r9, qword ptr [{a_ptr} + 8]",
            "mov r10, qword ptr [{a_ptr} + 16]",
            "mov r11, qword ptr [{a_ptr} + 24]",

            // sub a array and b array with borrow
            "sub r8, qword ptr [{b_ptr} + 0]",
            "sbb r9, qword ptr [{b_ptr} + 8]",
            "sbb r10, qword ptr [{b_ptr} + 16]",
            "sbb r11, qword ptr [{b_ptr} + 24]",

            // copy result array to latter registers
            "mov r12, r8",
            "mov r13, r9",
            "mov r14, r10",
            "mov r15, r11",

            // mod addition
            "add r12, qword ptr [{m_ptr} + 0]",
            "adc r13, qword ptr [{m_ptr} + 8]",
            "adc r14, qword ptr [{m_ptr} + 16]",
            "adc r15, qword ptr [{m_ptr} + 24]",

            // if not carry copy former registers to out areas
            "cmovnc r12, r8",
            "cmovnc r13, r9",
            "cmovnc r14, r10",
            "cmovnc r15, r11",

            m_ptr = in(reg) MODULUS.as_ptr(),
            a_ptr = in(reg) a.as_ptr(),
            b_ptr = in(reg) b.as_ptr(),
            out("r12") r0,
            out("r13") r1,
            out("r14") r2,
            out("r15") r3,
            options(pure, readonly, nostack)
        );
    }
    [r0, r1, r2, r3]
}

pub fn double(a: &[u64; 4]) -> [u64; 4] {
    let mut r0: u64;
    let mut r1: u64;
    let mut r2: u64;
    let mut r3: u64;
    unsafe {
        asm!(
            // load a array to former registers
            "mov r8, qword ptr [{a_ptr} + 0]",
            "mov r9, qword ptr [{a_ptr} + 8]",
            "mov r10, qword ptr [{a_ptr} + 16]",
            "mov r11, qword ptr [{a_ptr} + 24]",

            // // add a array and b array with carry
            "add r8, r8",
            "adc r9, r9",
            "adc r10, r10",
            "adc r11, r11",

            // copy result array to latter registers
            "mov r12, r8",
            "mov r13, r9",
            "mov r14, r10",
            "mov r15, r11",

            // mod reduction
            "sub r12, qword ptr [{m_ptr} + 0]",
            "sbb r13, qword ptr [{m_ptr} + 8]",
            "sbb r14, qword ptr [{m_ptr} + 16]",
            "sbb r15, qword ptr [{m_ptr} + 24]",

            // if carry copy former registers to out areas
            "cmovc r12, r8",
            "cmovc r13, r9",
            "cmovc r14, r10",
            "cmovc r15, r11",

            m_ptr = in(reg) MODULUS.as_ptr(),
            a_ptr = in(reg) a.as_ptr(),
            out("r12") r0,
            out("r13") r1,
            out("r14") r2,
            out("r15") r3,
            options(pure, readonly, nostack)
        );
    }
    [r0, r1, r2, r3]
}

pub fn mul(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
    let mut r0: u64;
    let mut r1: u64;
    let mut r2: u64;
    let mut r3: u64;
    let mut r4: u64;
    let mut r5: u64;
    let mut r6: u64;
    unsafe {
        asm!(
            // load all array to register
            // "mov r12, qword ptr [{a_ptr} + 0]",
            // "mov r13, qword ptr [{a_ptr} + 8]",
            // "mov r14, qword ptr [{a_ptr} + 16]",
            // "mov r15, qword ptr [{a_ptr} + 24]",

            // schoolbook multiplication
            //    *    |   a0    |   a1    |   a2    |   a3
            //    b0   | b0 * a0 | b0 * a1 | b0 * a2 | b0 * a3
            //    b1   | b1 * a0 | b1 * a1 | b1 * a2 | b1 * a3
            //    b2   | b2 * a0 | b2 * a1 | b2 * a2 | b2 * a3
            //    b3   | b3 * a0 | b3 * a1 | b3 * a2 | b3 * a3

            //    r8   | a0 * b0 |         |         |
            //    r9   | a0 * b1 | a1 * b0 |         |
            //    r10  | a0 * b2 | a1 * b1 | a2 * b0 |
            //    r11  | a0 * b3 | a1 * b2 | a2 * b1 | a3 * b0 |
            //    r12  | a1 * b3 | a2 * b2 | a3 * b1 |
            //    r13  | a2 * b3 | a3 * b2 |         |
            //    r14  | a3 * b3 |         |         |

            //    r9   | 00  |     |     |
            //    r10  | 01  | 10  |     |
            //    r11  | 02  | 11  | 20  |
            //    r12  | 03  | 12  | 21  | 30
            //    r13  | 13  | 22  | 31  |
            //    r14  | 23  | 32  |     |
            //    r15  | 33  |     |     |

            // `a0`
            "mov rdx, qword ptr [{a_ptr} + 0]",

            // a0 * b0
            "mulx r9, r8, qword ptr [{b_ptr} + 0]",

            // a0 * b1
            "mulx r10, rbx, qword ptr [{b_ptr} + 8]",
            "add r9, rbx",

            // a0 * b2
            "mulx r11, rbx, qword ptr [{b_ptr} + 16]",
            "adcx r10, rbx",

            // a0 * b3
            "mulx r12, rbx, qword ptr [{b_ptr} + 24]",
            "adcx r11, rbx",
            "adc r12, 0",

            // `a1`
            "mov rdx, [{a_ptr} + 8]",

            // a1 * b0
            "mulx r15, rbx, qword ptr [{b_ptr} + 0]",
            "add r9, rbx",
            "adcx r10, r15",

            // a1 * b1
            "mulx r15, rbx, qword ptr [{b_ptr} + 8]",
            "adcx r10, rbx",
            "adcx r11, r15",

            // a1 * b2
            "mulx r15, rbx, qword ptr [{b_ptr} + 16]",
            "adcx r11, rbx",
            "adcx r12, r15",

            // a1 * b3
            "mulx r13, rbx, qword ptr [{b_ptr} + 24]",
            "adcx r12, rbx",

            // `a2`
            "mov rdx, [{a_ptr} + 16]",

            // a2 * b0
            "mulx r15, rbx, qword ptr [{b_ptr} + 0]",
            "add r10, rbx",
            "adcx r11, r15",

            // a2 * b1
            "mulx r15, rbx, qword ptr [{b_ptr} + 8]",
            "adcx r11, rbx",
            "adcx r12, r15",

            // a2 * b2
            "mulx r15, rbx, qword ptr [{b_ptr} + 16]",
            "adcx r12, rbx",
            "adcx r13, r15",

            // a2 * b3
            "mulx r14, rbx, qword ptr [{b_ptr} + 24]",
            "adcx r13, rbx",

            // `a3`
            "mov rdx, [{a_ptr} + 24]",

            // a3 * b0
            "mulx r15, rbx, qword ptr [{b_ptr} + 0]",
            "add r11, rbx",
            "adcx r12, r15",

            // a3 * b1
            "mulx r15, rbx, qword ptr [{b_ptr} + 8]",
            "adcx r12, rbx",
            "adcx r13, r15",

            // a3 * b2
            "mulx r15, rbx, qword ptr [{b_ptr} + 16]",
            "adcx r13, rbx",
            "adcx r14, r15",

            // a3 * b3
            "mulx r15, rbx, qword ptr [{b_ptr} + 24]",
            "adcx r14, rbx",
            "adc r15, 0",

            a_ptr = in(reg) a.as_ptr(),
            b_ptr = in(reg) b.as_ptr(),
            out("r8") r0,
            out("r9") r1,
            out("r10") r2,
            out("r11") r3,
            out("r12") r4,
            out("r13") r5,
            out("r14") r6,
            out("r15") r7,
        )
    }
}

#[cfg(test)]
mod asembly_tests {
    use super::*;

    #[test]
    fn test_add() {
        let a: [u64; 4] = [
            0x7e7140b5196b9e6f,
            0x9abac9e4157b6172,
            0xf04bc41062fd7322,
            0x1185fa9c9fef6326,
        ];
        let zero: [u64; 4] = [0; 4];
        assert_eq!(
            add(&a, &zero),
            [
                0x7e7140b5196b9e6f,
                0x9abac9e4157b6172,
                0xf04bc41062fd7322,
                0x1185fa9c9fef6326,
            ]
        );
        let prime: [u64; 4] = [
            0x43e1f593f0000001,
            0x2833e84879b97091,
            0xb85045b68181585d,
            0x30644e72e131a029,
        ];
        assert_eq!(
            add(&a, &prime),
            [
                0x7e7140b5196b9e6f,
                0x9abac9e4157b6172,
                0xf04bc41062fd7322,
                0x1185fa9c9fef6326,
            ]
        );
        let one: [u64; 4] = [
            0x0000000000000001,
            0x0000000000000000,
            0x0000000000000000,
            0x0000000000000000,
        ];
        assert_eq!(
            add(&a, &one),
            [
                0x7e7140b5196b9e70,
                0x9abac9e4157b6172,
                0xf04bc41062fd7322,
                0x1185fa9c9fef6326,
            ]
        );
    }

    #[test]
    fn test_sub() {
        let a: [u64; 4] = [
            0x7e7140b5196b9e6f,
            0x9abac9e4157b6172,
            0xf04bc41062fd7322,
            0x1185fa9c9fef6326,
        ];
        let zero: [u64; 4] = [0; 4];
        assert_eq!(
            sub(&a, &zero),
            [
                0x7e7140b5196b9e6f,
                0x9abac9e4157b6172,
                0xf04bc41062fd7322,
                0x1185fa9c9fef6326,
            ]
        );
        let prime: [u64; 4] = [
            0x43e1f593f0000001,
            0x2833e84879b97091,
            0xb85045b68181585d,
            0x30644e72e131a029,
        ];
        assert_eq!(
            sub(&a, &prime),
            [
                0x7e7140b5196b9e6f,
                0x9abac9e4157b6172,
                0xf04bc41062fd7322,
                0x1185fa9c9fef6326,
            ]
        );
        let one: [u64; 4] = [
            0x0000000000000001,
            0x0000000000000000,
            0x0000000000000000,
            0x0000000000000000,
        ];
        assert_eq!(
            sub(&a, &one),
            [
                0x7e7140b5196b9e6e,
                0x9abac9e4157b6172,
                0xf04bc41062fd7322,
                0x1185fa9c9fef6326,
            ]
        );
    }

    #[test]
    fn test_double() {
        let a: [u64; 4] = [
            0x7e7140b5196b9e6f,
            0x9abac9e4157b6172,
            0xf04bc41062fd7322,
            0x1185fa9c9fef6326,
        ];
        let b: [u64; 4] = [
            0x7e7140b5196b9e6f,
            0x9abac9e4157b6172,
            0xf04bc41062fd7322,
            0x1185fa9c9fef6326,
        ];
        assert_eq!(add(&a, &b), double(&a));
    }
}
