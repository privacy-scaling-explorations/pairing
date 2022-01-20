use super::LegendreSymbol;
use core::convert::TryInto;
use core::fmt;
use core::ops::{Add, Mul, Neg, Sub};
use rand::RngCore;
use std::io::{self, Read, Write};
use std::ops::AddAssign;
use std::ops::MulAssign;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

use crate::arithmetic::{adc, mac, sbb, BaseExt, FieldExt, Group};

#[derive(Clone, Copy, Eq, Hash)]
pub struct Fr(pub(crate) [u64; 4]);

/// Constant representing the modulus
/// q = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001
pub const MODULUS: Fr = Fr([
    0x43e1f593f0000001,
    0x2833e84879b97091,
    0xb85045b68181585d,
    0x30644e72e131a029,
]);

/// INV = -(q^{-1} mod 2^64) mod 2^64
const INV: u64 = 0xc2e1f593efffffff;

/// R = 2^256 mod q
/// 0xe0a77c19a07df2f666ea36f7879462e36fc76959f60cd29ac96341c4ffffffb
const R: Fr = Fr([
    0xac96341c4ffffffb,
    0x36fc76959f60cd29,
    0x666ea36f7879462e,
    0x0e0a77c19a07df2f,
]);

/// R^2 = 2^512 mod q
/// 0x216d0b17f4e44a58c49833d53bb808553fe3ab1e35c59e31bb8e645ae216da7
const R2: Fr = Fr([
    0x1bb8e645ae216da7,
    0x53fe3ab1e35c59e3,
    0x8c49833d53bb8085,
    0x0216d0b17f4e44a5,
]);

/// R^3 = 2^768 mod q
/// 0xcf8594b7fcc657c893cc664a19fcfed2a489cbe1cfbb6b85e94d8e1b4bf0040
const R3: Fr = Fr([
    0x5e94d8e1b4bf0040,
    0x2a489cbe1cfbb6b8,
    0x893cc664a19fcfed,
    0x0cf8594b7fcc657c,
]);

const GENERATOR: Fr = Fr::from_raw([0x07, 0x00, 0x00, 0x00]);

const S: u32 = 28;

const ROOT_OF_UNITY: Fr = Fr::from_raw([
    0xd34f1ed960c37c9c,
    0x3215cf6dd39329c8,
    0x98865ea93dd31f74,
    0x03ddb9f5166d18b7,
]);

impl Group for Fr {
    type Scalar = Fr;

    fn group_zero() -> Self {
        Self::zero()
    }
    fn group_add(&mut self, rhs: &Self) {
        *self += *rhs;
    }
    fn group_sub(&mut self, rhs: &Self) {
        *self -= *rhs;
    }
    fn group_scale(&mut self, by: &Self::Scalar) {
        *self *= *by;
    }
}

impl ::std::fmt::Display for Fr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let tmp = self.to_bytes();
        write!(f, "0x")?;
        for &b in tmp.iter().rev() {
            write!(f, "{:02x}", b)?;
        }
        Ok(())
    }
}

impl fmt::Debug for Fr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let tmp = self.to_bytes();
        write!(f, "0x")?;
        for &b in tmp.iter().rev() {
            write!(f, "{:02x}", b)?;
        }
        Ok(())
    }
}

impl Default for Fr {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

impl From<bool> for Fr {
    fn from(bit: bool) -> Fr {
        if bit {
            Fr::one()
        } else {
            Fr::zero()
        }
    }
}

impl From<u64> for Fr {
    fn from(val: u64) -> Fr {
        Fr([val, 0, 0, 0]) * R2
    }
}

impl ConstantTimeEq for Fr {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0[0].ct_eq(&other.0[0])
            & self.0[1].ct_eq(&other.0[1])
            & self.0[2].ct_eq(&other.0[2])
            & self.0[3].ct_eq(&other.0[3])
    }
}

impl PartialEq for Fr {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).unwrap_u8() == 1
    }
}

impl std::cmp::Ord for Fr {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let left = self.to_bytes();
        let right = other.to_bytes();
        left.iter()
            .zip(right.iter())
            .rev()
            .find_map(|(left_byte, right_byte)| match left_byte.cmp(right_byte) {
                std::cmp::Ordering::Equal => None,
                res => Some(res),
            })
            .unwrap_or(std::cmp::Ordering::Equal)
    }
}

impl std::cmp::PartialOrd for Fr {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl ConditionallySelectable for Fr {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Fr([
            u64::conditional_select(&a.0[0], &b.0[0], choice),
            u64::conditional_select(&a.0[1], &b.0[1], choice),
            u64::conditional_select(&a.0[2], &b.0[2], choice),
            u64::conditional_select(&a.0[3], &b.0[3], choice),
        ])
    }
}

impl Neg for Fr {
    type Output = Fr;

    #[inline]
    fn neg(self) -> Fr {
        -&self
    }
}

impl<'a> Neg for &'a Fr {
    type Output = Fr;

    #[inline]
    fn neg(self) -> Fr {
        self.neg()
    }
}

impl<'a, 'b> Sub<&'b Fr> for &'a Fr {
    type Output = Fr;

    #[inline]
    fn sub(self, rhs: &'b Fr) -> Fr {
        self.sub(rhs)
    }
}

impl<'a, 'b> Add<&'b Fr> for &'a Fr {
    type Output = Fr;

    #[inline]
    fn add(self, rhs: &'b Fr) -> Fr {
        self.add(rhs)
    }
}

impl<'a, 'b> Mul<&'b Fr> for &'a Fr {
    type Output = Fr;

    #[inline]
    fn mul(self, rhs: &'b Fr) -> Fr {
        self.mul(rhs)
    }
}

impl_binops_additive!(Fr, Fr);
impl_binops_multiplicative!(Fr, Fr);

impl Fr {
    pub fn legendre(&self) -> LegendreSymbol {
        unimplemented!()
    }

    /// Returns zero, the additive identity.
    #[inline]
    pub const fn zero() -> Self {
        Self([0, 0, 0, 0])
    }

    /// Returns one, the multiplicative identity.
    #[inline]
    pub const fn one() -> Self {
        R
    }

    /// Doubles this field element.
    #[inline]
    pub fn double(&self) -> Self {
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

                m_ptr = in(reg) MODULUS.0.as_ptr(),
                a_ptr = in(reg) self.0.as_ptr(),
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
        Self([r0, r1, r2, r3])
    }

    fn from_u512(limbs: [u64; 8]) -> Self {
        // We reduce an arbitrary 512-bit number by decomposing it into two 256-bit digits
        // with the higher bits multiplied by 2^256. Thus, we perform two reductions
        //
        // 1. the lower bits are multiplied by R^2, as normal
        // 2. the upper bits are multiplied by R^2 * 2^256 = R^3
        //
        // and computing their sum in the field. It remains to see that arbitrary 256-bit
        // numbers can be placed into Montgomery form safely using the reduction. The
        // reduction works so long as the product is less than R=2^256 multiplied by
        // the modulus. This holds because for any `c` smaller than the modulus, we have
        // that (2^256 - 1)*c is an acceptable product for the reduction. Therefore, the
        // reduction always works so long as `c` is in the field; in this case it is either the
        // constant `R2` or `R3`.
        let mut d0 = Fr([limbs[0], limbs[1], limbs[2], limbs[3]]);
        let mut d1 = Fr([limbs[4], limbs[5], limbs[6], limbs[7]]);
        // Convert to Montgomery form
        d0.mul_assign(R2);
        d1.mul_assign(R3);
        d0.add_assign(d1);
        d0
    }

    /// Converts from an integer represented in little endian
    /// into its (congruent) `Fr` representation.
    pub const fn from_raw(val: [u64; 4]) -> Self {
        let (r0, carry) = mac(0, val[0], R2.0[0], 0);
        let (r1, carry) = mac(0, val[0], R2.0[1], carry);
        let (r2, carry) = mac(0, val[0], R2.0[2], carry);
        let (r3, r4) = mac(0, val[0], R2.0[3], carry);

        let (r1, carry) = mac(r1, val[1], R2.0[0], 0);
        let (r2, carry) = mac(r2, val[1], R2.0[1], carry);
        let (r3, carry) = mac(r3, val[1], R2.0[2], carry);
        let (r4, r5) = mac(r4, val[1], R2.0[3], carry);

        let (r2, carry) = mac(r2, val[2], R2.0[0], 0);
        let (r3, carry) = mac(r3, val[2], R2.0[1], carry);
        let (r4, carry) = mac(r4, val[2], R2.0[2], carry);
        let (r5, r6) = mac(r5, val[2], R2.0[3], carry);

        let (r3, carry) = mac(r3, val[3], R2.0[0], 0);
        let (r4, carry) = mac(r4, val[3], R2.0[1], carry);
        let (r5, carry) = mac(r5, val[3], R2.0[2], carry);
        let (r6, r7) = mac(r6, val[3], R2.0[3], carry);

        let k = r0.wrapping_mul(INV);
        let (_, carry) = mac(r0, k, MODULUS.0[0], 0);
        let (r1, carry) = mac(r1, k, MODULUS.0[1], carry);
        let (r2, carry) = mac(r2, k, MODULUS.0[2], carry);
        let (r3, carry) = mac(r3, k, MODULUS.0[3], carry);
        let (r4, carry2) = adc(r4, 0, carry);

        let k = r1.wrapping_mul(INV);
        let (_, carry) = mac(r1, k, MODULUS.0[0], 0);
        let (r2, carry) = mac(r2, k, MODULUS.0[1], carry);
        let (r3, carry) = mac(r3, k, MODULUS.0[2], carry);
        let (r4, carry) = mac(r4, k, MODULUS.0[3], carry);
        let (r5, carry2) = adc(r5, carry2, carry);

        let k = r2.wrapping_mul(INV);
        let (_, carry) = mac(r2, k, MODULUS.0[0], 0);
        let (r3, carry) = mac(r3, k, MODULUS.0[1], carry);
        let (r4, carry) = mac(r4, k, MODULUS.0[2], carry);
        let (r5, carry) = mac(r5, k, MODULUS.0[3], carry);
        let (r6, carry2) = adc(r6, carry2, carry);

        let k = r3.wrapping_mul(INV);
        let (_, carry) = mac(r3, k, MODULUS.0[0], 0);
        let (r4, carry) = mac(r4, k, MODULUS.0[1], carry);
        let (r5, carry) = mac(r5, k, MODULUS.0[2], carry);
        let (r6, carry) = mac(r6, k, MODULUS.0[3], carry);
        let (r7, _) = adc(r7, carry2, carry);

        let (d0, borrow) = sbb(r4, MODULUS.0[0], 0);
        let (d1, borrow) = sbb(r5, MODULUS.0[1], borrow);
        let (d2, borrow) = sbb(r6, MODULUS.0[2], borrow);
        let (d3, borrow) = sbb(r7, MODULUS.0[3], borrow);

        // If underflow occurred on the final limb, borrow = 0xfff...fff, otherwise
        // borrow = 0x000...000. Thus, we use it as a mask to conditionally add the modulus.
        let (d0, carry) = adc(d0, MODULUS.0[0] & borrow, 0);
        let (d1, carry) = adc(d1, MODULUS.0[1] & borrow, carry);
        let (d2, carry) = adc(d2, MODULUS.0[2] & borrow, carry);
        let (d3, _) = adc(d3, MODULUS.0[3] & borrow, carry);

        Self([d0, d1, d2, d3])
    }

    /// Squares this element.
    #[inline]
    pub fn square(&self) -> Self {
        let mut r0: u64;
        let mut r1: u64;
        let mut r2: u64;
        let mut r3: u64;
        let mut r4: u64;
        let mut r5: u64;
        let mut r6: u64;
        let mut r7: u64;
        unsafe {
            asm!(
                // schoolbook multiplication
                //    *    |   a0    |   a1    |   a2    |   a3
                //    b0   | b0 * a0 | b0 * a1 | b0 * a2 | b0 * a3
                //    b1   | b1 * a0 | b1 * a1 | b1 * a2 | b1 * a3
                //    b2   | b2 * a0 | b2 * a1 | b2 * a2 | b2 * a3
                //    b3   | b3 * a0 | b3 * a1 | b3 * a2 | b3 * a3

                // init registers
                "xor r13, r13",
                "xor r14, r14",
                "xor r15, r15",

                // `a0`
                "mov rdx, qword ptr [{a_ptr} + 0]",

                // a0 * b0
                "mulx r9, r8, qword ptr [{a_ptr} + 0]",

                // a0 * b1
                "mulx r10, rax, qword ptr [{a_ptr} + 8]",
                "add r9, rax",

                // a0 * b2
                "mulx r11, rax, qword ptr [{a_ptr} + 16]",
                "adcx r10, rax",

                // a0 * b3
                "mulx r12, rax, qword ptr [{a_ptr} + 24]",
                "adcx r11, rax",
                "adc r12, 0",

                // `a1`
                "mov rdx, [{a_ptr} + 8]",

                // a1 * b0
                "mulx rcx, rax, qword ptr [{a_ptr} + 0]",
                "add r9, rax",
                "adcx r10, rcx",
                "adc r11, 0",

                // a1 * b1
                "mulx rcx, rax, qword ptr [{a_ptr} + 8]",
                "add r10, rax",
                "adcx r11, rcx",
                "adc r12, 0",

                // a1 * b2
                "mulx rcx, rax, qword ptr [{a_ptr} + 16]",
                "add r11, rax",
                "adcx r12, rcx",
                "adc r13, 0",

                // a1 * b3
                "mulx rcx, rax, qword ptr [{a_ptr} + 24]",
                "add r12, rax",
                "adcx r13, rcx",
                "adc r14, 0",

                // `a2`
                "mov rdx, [{a_ptr} + 16]",

                // a2 * b0
                "mulx rcx, rax, qword ptr [{a_ptr} + 0]",
                "add r10, rax",
                "adcx r11, rcx",
                "adc r12, 0",

                // a2 * b1
                "mulx rcx, rax, qword ptr [{a_ptr} + 8]",
                "add r11, rax",
                "adcx r12, rcx",
                "adc r13, 0",

                // a2 * b2
                "mulx rcx, rax, qword ptr [{a_ptr} + 16]",
                "add r12, rax",
                "adcx r13, rcx",
                "adc r14, 0",

                // a2 * b3
                "mulx rcx, rax, qword ptr [{a_ptr} + 24]",
                "adcx r13, rax",
                "adcx r14, rcx",
                "adc r15, 0",

                // `a3`
                "mov rdx, [{a_ptr} + 24]",

                // a3 * b0
                "mulx rcx, rax, qword ptr [{a_ptr} + 0]",
                "add r11, rax",
                "adcx r12, rcx",
                "adc r13, 0",

                // a3 * b1
                "mulx rcx, rax, qword ptr [{a_ptr} + 8]",
                "adcx r12, rax",
                "adcx r13, rcx",
                "adc r14, 0",

                // a3 * b2
                "mulx rcx, rax, qword ptr [{a_ptr} + 16]",
                "adcx r13, rax",
                "adcx r14, rcx",
                "adc r15, 0",

                // a3 * b3
                "mulx rcx, rax, qword ptr [{a_ptr} + 24]",
                "adcx r14, rax",
                "adc r15, rcx",

                a_ptr = in(reg) self.0.as_ptr(),
                out("rax") _,
                out("rcx") _,
                out("rdx") _,
                out("r8") r0,
                out("r9") r1,
                out("r10") r2,
                out("r11") r3,
                out("r12") r4,
                out("r13") r5,
                out("r14") r6,
                out("r15") r7,
                options(pure, readonly, nostack)
            )
        }

        Self::montgomery_reduce(&[r0, r1, r2, r3, r4, r5, r6, r7])
    }

    #[allow(clippy::too_many_arguments)]
    #[inline(always)]
    fn montgomery_reduce(a: &[u64; 8]) -> Self {
        let mut r0: u64;
        let mut r1: u64;
        let mut r2: u64;
        let mut r3: u64;

        unsafe {
            asm!(
                // The Montgomery reduction here is based on Algorithm 14.32 in
                // Handbook of Applied Cryptography
                // <https://cacr.uwaterloo.ca/hac/about/chap14.pdf>.

                "mov r8, qword ptr [{a_ptr} + 0]",
                "mov r9, qword ptr [{a_ptr} + 8]",
                "mov r10, qword ptr [{a_ptr} + 16]",
                "mov r11, qword ptr [{a_ptr} + 24]",
                "mov r12, qword ptr [{a_ptr} + 32]",
                "mov r13, qword ptr [{a_ptr} + 40]",
                "mov r14, qword ptr [{a_ptr} + 48]",
                "mov r15, qword ptr [{a_ptr} + 56]",

                // `r8` -> 0
                "mov rdx, qword ptr [{i_ptr}]",
                "mulx rax, rdx, r8",

                // r8' * m0
                "mulx rcx, rax, qword ptr [{m_ptr} + 0]",
                "add r8, rax",
                "adcx r9, rcx",
                "adc r10, 0",

                // r8' * m1
                "mulx rcx, rax, qword ptr [{m_ptr} + 8]",
                "adcx r9, rax",
                "adcx r10, rcx",
                "adc r11, 0",

                // // r8' * m2
                "mulx rcx, rax, qword ptr [{m_ptr} + 16]",
                "add r10, rax",
                "adcx r11, rcx",
                "adc r12, 0",

                // // r8' * m3
                "mulx rcx, rax, qword ptr [{m_ptr} + 24]",
                "add r11, rax",
                "adcx r12, rcx",
                "adc r13, 0",

                // `r9` -> 0
                "mov rdx, qword ptr [{i_ptr}]",
                "mulx rax, rdx, r9",

                // r9' * m0
                "mulx rax, rcx, qword ptr [{m_ptr} + 0]",
                "add r9, rcx",
                "adcx r10, rax",
                "adc r11, 0",

                // r9' * m1
                "mulx rax, rcx, qword ptr [{m_ptr} + 8]",
                "adcx r10, rcx",
                "adcx r11, rax",
                "adc r12, 0",

                // r9' * m2
                "mulx rax, rcx, qword ptr [{m_ptr} + 16]",
                "adcx r11, rcx",
                "adcx r12, rax",
                "adc r13, 0",

                // r9' * m3
                "mulx rax, rcx, qword ptr [{m_ptr} + 24]",
                "adcx r12, rcx",
                "adcx r13, rax",
                "adc r14, 0",

                // `r10` -> 0
                "mov rdx, qword ptr [{i_ptr}]",
                "mulx rax, rdx, r10",

                // r10' * m0
                "mulx rax, rcx, qword ptr [{m_ptr} + 0]",
                "add r10, rcx",
                "adcx r11, rax",
                "adc r12, 0",

                // r10' * m1
                "mulx rax, rcx, qword ptr [{m_ptr} + 8]",
                "add r11, rcx",
                "adcx r12, rax",
                "adc r13, 0",

                // r10' * m2
                "mulx rax, rcx, qword ptr [{m_ptr} + 16]",
                "add r12, rcx",
                "adcx r13, rax",
                "adc r14, 0",

                // r10' * m3
                "mulx rax, rcx, qword ptr [{m_ptr} + 24]",
                "add r13, rcx",
                "adcx r14, rax",
                "adc r15, 0",

                // `r11` -> 0
                "mov rdx, qword ptr [{i_ptr}]",
                "mulx rax, rdx, r11",

                // r11' * m0
                "mulx rax, rcx, qword ptr [{m_ptr} + 0]",
                "add r11, rcx",
                "adcx r12, rax",
                "adc r13, 0",

                // r11' * m1
                "mulx rax, rcx, qword ptr [{m_ptr} + 8]",
                "add r12, rcx",
                "adcx r13, rax",
                "adc r14, 0",

                // r11' * m2
                "mulx rax, rcx, qword ptr [{m_ptr} + 16]",
                "add r13, rcx",
                "adcx r14, rax",
                "adc r15, 0",

                // r11' * m3
                "mulx rax, rcx, qword ptr [{m_ptr} + 24]",
                "add r14, rcx",
                "adcx r15, rax",

                // reduction if limbs is greater then mod
                "mov r8, r12",
                "mov r9, r13",
                "mov r10, r14",
                "mov r11, r15",

                "sub r8, qword ptr [{m_ptr} + 0]",
                "sbb r9, qword ptr [{m_ptr} + 8]",
                "sbb r10, qword ptr [{m_ptr} + 16]",
                "sbb r11, qword ptr [{m_ptr} + 24]",

                "cmovc r8, r12",
                "cmovc r9, r13",
                "cmovc r10, r14",
                "cmovc r11, r15",

                i_ptr = in(reg) &INV,
                a_ptr = in(reg) a.as_ptr(),
                m_ptr = in(reg) MODULUS.0.as_ptr(),
                out("rax") _,
                out("rcx") _,
                out("rdx") _,
                out("r8") _,
                out("r9") _,
                out("r10") _,
                out("r11") _,
                out("r12") r0,
                out("r13") r1,
                out("r14") r2,
                out("r15") r3,
                options(pure, readonly, nostack)
            )
        }

        Self([r0, r1, r2, r3])
    }

    /// Multiplies `rhs` by `self`, returning the result.
    #[inline]
    pub fn mul(&self, rhs: &Self) -> Self {
        let mut r0: u64;
        let mut r1: u64;
        let mut r2: u64;
        let mut r3: u64;
        let mut r4: u64;
        let mut r5: u64;
        let mut r6: u64;
        let mut r7: u64;
        unsafe {
            asm!(
                // schoolbook multiplication
                //    *    |   a0    |   a1    |   a2    |   a3
                //    b0   | b0 * a0 | b0 * a1 | b0 * a2 | b0 * a3
                //    b1   | b1 * a0 | b1 * a1 | b1 * a2 | b1 * a3
                //    b2   | b2 * a0 | b2 * a1 | b2 * a2 | b2 * a3
                //    b3   | b3 * a0 | b3 * a1 | b3 * a2 | b3 * a3

                // init registers
                "xor r13, r13",
                "xor r14, r14",
                "xor r15, r15",

                // `a0`
                "mov rdx, qword ptr [{a_ptr} + 0]",

                // a0 * b0
                "mulx r9, r8, qword ptr [{b_ptr} + 0]",

                // a0 * b1
                "mulx r10, rax, qword ptr [{b_ptr} + 8]",
                "add r9, rax",

                // a0 * b2
                "mulx r11, rax, qword ptr [{b_ptr} + 16]",
                "adcx r10, rax",

                // a0 * b3
                "mulx r12, rax, qword ptr [{b_ptr} + 24]",
                "adcx r11, rax",
                "adc r12, 0",

                // `a1`
                "mov rdx, [{a_ptr} + 8]",

                // a1 * b0
                "mulx rcx, rax, qword ptr [{b_ptr} + 0]",
                "add r9, rax",
                "adcx r10, rcx",
                "adc r11, 0",

                // a1 * b1
                "mulx rcx, rax, qword ptr [{b_ptr} + 8]",
                "add r10, rax",
                "adcx r11, rcx",
                "adc r12, 0",

                // a1 * b2
                "mulx rcx, rax, qword ptr [{b_ptr} + 16]",
                "add r11, rax",
                "adcx r12, rcx",
                "adc r13, 0",

                // a1 * b3
                "mulx rcx, rax, qword ptr [{b_ptr} + 24]",
                "add r12, rax",
                "adcx r13, rcx",
                "adc r14, 0",

                // `a2`
                "mov rdx, [{a_ptr} + 16]",

                // a2 * b0
                "mulx rcx, rax, qword ptr [{b_ptr} + 0]",
                "add r10, rax",
                "adcx r11, rcx",
                "adc r12, 0",

                // a2 * b1
                "mulx rcx, rax, qword ptr [{b_ptr} + 8]",
                "add r11, rax",
                "adcx r12, rcx",
                "adc r13, 0",

                // a2 * b2
                "mulx rcx, rax, qword ptr [{b_ptr} + 16]",
                "add r12, rax",
                "adcx r13, rcx",
                "adc r14, 0",

                // a2 * b3
                "mulx rcx, rax, qword ptr [{b_ptr} + 24]",
                "adcx r13, rax",
                "adcx r14, rcx",
                "adc r15, 0",

                // `a3`
                "mov rdx, [{a_ptr} + 24]",

                // a3 * b0
                "mulx rcx, rax, qword ptr [{b_ptr} + 0]",
                "add r11, rax",
                "adcx r12, rcx",
                "adc r13, 0",

                // a3 * b1
                "mulx rcx, rax, qword ptr [{b_ptr} + 8]",
                "adcx r12, rax",
                "adcx r13, rcx",
                "adc r14, 0",

                // a3 * b2
                "mulx rcx, rax, qword ptr [{b_ptr} + 16]",
                "adcx r13, rax",
                "adcx r14, rcx",
                "adc r15, 0",

                // a3 * b3
                "mulx rcx, rax, qword ptr [{b_ptr} + 24]",
                "adcx r14, rax",
                "adc r15, rcx",

                a_ptr = in(reg) self.0.as_ptr(),
                b_ptr = in(reg) rhs.0.as_ptr(),
                out("rax") _,
                out("rcx") _,
                out("rdx") _,
                out("r8") r0,
                out("r9") r1,
                out("r10") r2,
                out("r11") r3,
                out("r12") r4,
                out("r13") r5,
                out("r14") r6,
                out("r15") r7,
                options(pure, readonly, nostack)
            )
        }

        Self::montgomery_reduce(&[r0, r1, r2, r3, r4, r5, r6, r7])
    }

    /// Subtracts `rhs` from `self`, returning the result.
    #[inline]
    pub fn sub(&self, rhs: &Self) -> Self {
        let mut r0: u64;
        let mut r1: u64;
        let mut r2: u64;
        let mut r3: u64;
        unsafe {
            asm!(
                // init modulus area
                "xor r12, r12",
                "xor r13, r13",
                "xor r14, r14",
                "xor r15, r15",

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

                // if carry copy modulus
                "cmovc r12, qword ptr [{m_ptr} + 0]",
                "cmovc r13, qword ptr [{m_ptr} + 8]",
                "cmovc r14, qword ptr [{m_ptr} + 16]",
                "cmovc r15, qword ptr [{m_ptr} + 24]",

                // mod addition
                "add  r12, r8",
                "adc  r13, r9",
                "adc  r14, r10",
                "adc  r15, r11",

                m_ptr = in(reg) MODULUS.0.as_ptr(),
                a_ptr = in(reg) self.0.as_ptr(),
                b_ptr = in(reg) rhs.0.as_ptr(),
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
        Self([r0, r1, r2, r3])
    }

    /// Adds `rhs` to `self`, returning the result.
    #[inline]
    pub fn add(&self, rhs: &Self) -> Self {
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

                m_ptr = in(reg) MODULUS.0.as_ptr(),
                a_ptr = in(reg) self.0.as_ptr(),
                b_ptr = in(reg) rhs.0.as_ptr(),
                out("r12") r0,
                out("r13") r1,
                out("r14") r2,
                out("r15") r3,
                options(pure, readonly, nostack)
            );
        }
        Self([r0, r1, r2, r3])
    }

    /// Negates `self`.
    #[inline]
    pub const fn neg(&self) -> Self {
        // Subtract `self` from `MODULUS` to negate. Ignore the final
        // borrow because it cannot underflow; self is guaranteed to
        // be in the field.
        let (d0, borrow) = sbb(MODULUS.0[0], self.0[0], 0);
        let (d1, borrow) = sbb(MODULUS.0[1], self.0[1], borrow);
        let (d2, borrow) = sbb(MODULUS.0[2], self.0[2], borrow);
        let (d3, _) = sbb(MODULUS.0[3], self.0[3], borrow);

        // `tmp` could be `MODULUS` if `self` was zero. Create a mask that is
        // zero if `self` was zero, and `u64::max_value()` if self was nonzero.
        let mask = (((self.0[0] | self.0[1] | self.0[2] | self.0[3]) == 0) as u64).wrapping_sub(1);

        Self([d0 & mask, d1 & mask, d2 & mask, d3 & mask])
    }
}

impl From<Fr> for [u8; 32] {
    fn from(value: Fr) -> [u8; 32] {
        value.to_bytes()
    }
}

impl<'a> From<&'a Fr> for [u8; 32] {
    fn from(value: &'a Fr) -> [u8; 32] {
        value.to_bytes()
    }
}

impl ff::Field for Fr {
    fn random(mut rng: impl RngCore) -> Self {
        Self::from_u512([
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
        ])
    }

    fn zero() -> Self {
        Self::zero()
    }

    fn one() -> Self {
        Self::one()
    }

    fn is_zero(&self) -> Choice {
        self.ct_is_zero()
    }

    fn double(&self) -> Self {
        self.double()
    }

    #[inline(always)]
    fn square(&self) -> Self {
        self.square()
    }

    /// Computes the square root of this element, if it exists.
    fn sqrt(&self) -> CtOption<Self> {
        unimplemented!()
    }

    /// Computes the multiplicative inverse of this element,
    /// failing if the element is zero.
    fn invert(&self) -> CtOption<Self> {
        let tmp = self.pow(&[
            0x43e1f593efffffff,
            0x2833e84879b97091,
            0xb85045b68181585d,
            0x30644e72e131a029,
        ]);

        CtOption::new(tmp, !self.ct_eq(&Self::zero()))
    }
}

impl ff::PrimeField for Fr {
    type Repr = [u8; 32];

    const NUM_BITS: u32 = 253;
    const CAPACITY: u32 = 252;
    const S: u32 = S;

    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        let mut tmp = Fr([0, 0, 0, 0]);

        tmp.0[0] = u64::from_le_bytes(repr[0..8].try_into().unwrap());
        tmp.0[1] = u64::from_le_bytes(repr[8..16].try_into().unwrap());
        tmp.0[2] = u64::from_le_bytes(repr[16..24].try_into().unwrap());
        tmp.0[3] = u64::from_le_bytes(repr[24..32].try_into().unwrap());

        // Try to subtract the modulus
        let (_, borrow) = sbb(tmp.0[0], MODULUS.0[0], 0);
        let (_, borrow) = sbb(tmp.0[1], MODULUS.0[1], borrow);
        let (_, borrow) = sbb(tmp.0[2], MODULUS.0[2], borrow);
        let (_, borrow) = sbb(tmp.0[3], MODULUS.0[3], borrow);

        // If the element is smaller than MODULUS then the
        // subtraction will underflow, producing a borrow value
        // of 0xffff...ffff. Otherwise, it'll be zero.
        let is_some = (borrow as u8) & 1;

        // Convert to Montgomery form by computing
        // (a.R^0 * R^2) / R = a.R
        tmp *= &R2;

        CtOption::new(tmp, Choice::from(is_some))
    }

    fn to_repr(&self) -> Self::Repr {
        // Turn into canonical form by computing
        // (a.R) / R = a
        let tmp = Fr::montgomery_reduce(&[self.0[0], self.0[1], self.0[2], self.0[3], 0, 0, 0, 0]);

        let mut res = [0; 32];
        res[0..8].copy_from_slice(&tmp.0[0].to_le_bytes());
        res[8..16].copy_from_slice(&tmp.0[1].to_le_bytes());
        res[16..24].copy_from_slice(&tmp.0[2].to_le_bytes());
        res[24..32].copy_from_slice(&tmp.0[3].to_le_bytes());

        res
    }

    fn is_odd(&self) -> Choice {
        Choice::from(self.to_repr()[0] & 1)
    }

    fn multiplicative_generator() -> Self {
        GENERATOR
    }

    fn root_of_unity() -> Self {
        ROOT_OF_UNITY
    }
}

impl BaseExt for Fr {
    const MODULUS: &'static str =
        "0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001";

    /// Converts a 512-bit little endian integer into
    /// a `Fr` by reducing by the modulus.
    fn from_bytes_wide(bytes: &[u8; 64]) -> Self {
        Self::from_u512([
            u64::from_le_bytes(bytes[0..8].try_into().unwrap()),
            u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
            u64::from_le_bytes(bytes[16..24].try_into().unwrap()),
            u64::from_le_bytes(bytes[24..32].try_into().unwrap()),
            u64::from_le_bytes(bytes[32..40].try_into().unwrap()),
            u64::from_le_bytes(bytes[40..48].try_into().unwrap()),
            u64::from_le_bytes(bytes[48..56].try_into().unwrap()),
            u64::from_le_bytes(bytes[56..64].try_into().unwrap()),
        ])
    }

    fn ct_is_zero(&self) -> Choice {
        self.ct_eq(&Self::zero())
    }

    /// Writes this element in its normalized, little endian form into a buffer.
    fn write<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        let compressed = self.to_bytes();
        writer.write_all(&compressed[..])
    }

    /// Reads a normalized, little endian represented field element from a
    /// buffer.
    fn read<R: Read>(reader: &mut R) -> io::Result<Self> {
        let mut compressed = [0u8; 32];
        reader.read_exact(&mut compressed[..])?;
        Option::from(Self::from_bytes(&compressed))
            .ok_or_else(|| io::Error::new(io::ErrorKind::Other, "invalid point encoding in proof"))
    }
}

impl FieldExt for Fr {
    // const ROOT_OF_UNITY: Self = ROOT_OF_UNITY;

    const TWO_INV: Self = Fr::from_raw([
        0xa1f0fac9f8000001,
        0x9419f4243cdcb848,
        0xdc2822db40c0ac2e,
        0x183227397098d014,
    ]);

    const ROOT_OF_UNITY_INV: Self = Self::from_raw([
        0x0ed3e50a414e6dba,
        0xb22625f59115aba7,
        0x1bbe587180f34361,
        0x048127174daabc26,
    ]);

    // 0x09226b6e22c6f0ca64ec26aad4c86e715b5f898e5e963f25870e56bbe533e9a2
    const DELTA: Self = Self::from_raw([
        0x870e56bbe533e9a2,
        0x5b5f898e5e963f25,
        0x64ec26aad4c86e71,
        0x09226b6e22c6f0ca,
    ]);

    const RESCUE_ALPHA: u64 = 5;

    const RESCUE_INVALPHA: [u64; 4] = [
        0xcfe7f7a98ccccccd,
        0x535cb9d394945a0d,
        0x93736af8679aad17,
        0x26b6a528b427b354,
    ];

    const T_MINUS1_OVER2: [u64; 4] = [
        0xcdcb848a1f0fac9f,
        0x0c0ac2e9419f4243,
        0x098d014dc2822db4,
        0x0000000183227397,
    ];

    const ZETA: Self = Self::from_raw([
        0xb8ca0b2d36636f23,
        0xcc37a73fec2bc5e9,
        0x048b6e193fd84104,
        0x30644e72e131a029,
    ]);

    fn from_u128(v: u128) -> Self {
        Fr::from_raw([v as u64, (v >> 64) as u64, 0, 0])
    }

    /// Attempts to convert a little-endian byte representation of
    /// a scalar into a `Fr`, failing if the input is not canonical.
    fn from_bytes(bytes: &[u8; 32]) -> CtOption<Fr> {
        <Self as ff::PrimeField>::from_repr(*bytes)
    }

    /// Converts an element of `Fr` into a byte representation in
    /// little-endian byte order.
    fn to_bytes(&self) -> [u8; 32] {
        <Self as ff::PrimeField>::to_repr(self)
    }

    /// Gets the lower 128 bits of this field element when expressed
    /// canonically.
    fn get_lower_128(&self) -> u128 {
        let tmp = Fr::montgomery_reduce(&[self.0[0], self.0[1], self.0[2], self.0[3], 0, 0, 0, 0]);

        u128::from(tmp.0[0]) | (u128::from(tmp.0[1]) << 64)
    }
}

#[cfg(test)]
mod fr_tests {
    use super::*;
    use ff::{Field, PrimeField};
    use std::ops::{AddAssign, MulAssign, SubAssign};
    #[test]
    fn test_zeta() {
        let a = Fr::ZETA;
        assert!(a != Fr::one());
        let b = a * a;
        assert!(b != Fr::one());
        let c = b * a;
        println!("{:?}", c);
        assert!(c == Fr::one());
    }

    #[test]
    fn test_root_of_unity() {
        assert_eq!(
            Fr::root_of_unity().pow_vartime(&[1 << Fr::S, 0, 0, 0]),
            Fr::one()
        );
    }

    #[test]
    fn test_inv_root_of_unity() {
        assert_eq!(Fr::ROOT_OF_UNITY_INV, Fr::root_of_unity().invert().unwrap());
    }

    #[test]
    fn test_inv() {
        // Compute -(r^{-1} mod 2^64) mod 2^64 by exponentiating
        // by totient(2**64) - 1

        let mut inv = 1u64;
        for _ in 0..63 {
            inv = inv.wrapping_mul(inv);
            inv = inv.wrapping_mul(MODULUS.0[0]);
        }
        inv = inv.wrapping_neg();

        assert_eq!(inv, INV);
    }

    #[test]
    fn test_inv_2() {
        assert_eq!(Fr::TWO_INV, Fr::from(2).invert().unwrap());
    }

    #[test]
    fn test_from_u512() {
        assert_eq!(
            Fr::from_raw([
                0x7e7140b5196b9e6f,
                0x9abac9e4157b6172,
                0xf04bc41062fd7322,
                0x1185fa9c9fef6326,
            ]),
            Fr::from_u512([
                0xaaaaaaaaaaaaaaaa,
                0xaaaaaaaaaaaaaaaa,
                0xaaaaaaaaaaaaaaaa,
                0xaaaaaaaaaaaaaaaa,
                0xaaaaaaaaaaaaaaaa,
                0xaaaaaaaaaaaaaaaa,
                0xaaaaaaaaaaaaaaaa,
                0xaaaaaaaaaaaaaaaa
            ])
        );
    }

    #[test]
    fn test_field() {
        crate::tests::field::random_field_tests::<Fr>();
    }

    #[test]
    fn test_add() {
        // Add zero equal itself
        let mut a = Fr::from_raw([
            0x7e7140b5196b9e6f,
            0x9abac9e4157b6172,
            0xf04bc41062fd7322,
            0x1185fa9c9fef6326,
        ]);
        a.add_assign(Fr::zero());
        assert_eq!(
            a,
            Fr::from_raw([
                0x7e7140b5196b9e6f,
                0x9abac9e4157b6172,
                0xf04bc41062fd7322,
                0x1185fa9c9fef6326,
            ])
        );

        // Add mod equal itself
        let b = Fr::from_raw([
            0x43e1f593f0000001,
            0x2833e84879b97091,
            0xb85045b68181585d,
            0x30644e72e131a029,
        ]);
        a.add_assign(b);
        assert_eq!(
            a,
            Fr::from_raw([
                0x7e7140b5196b9e6f,
                0x9abac9e4157b6172,
                0xf04bc41062fd7322,
                0x1185fa9c9fef6326,
            ])
        );

        // Add one equal incremented itself
        a.add_assign(Fr::one());
        assert_eq!(
            a,
            Fr::from_raw([
                0x7e7140b5196b9e70,
                0x9abac9e4157b6172,
                0xf04bc41062fd7322,
                0x1185fa9c9fef6326,
            ])
        );
    }

    #[test]
    fn test_sub() {
        // Sub zero equal itself
        let mut a = Fr::from_raw([
            0x7e7140b5196b9e6f,
            0x9abac9e4157b6172,
            0xf04bc41062fd7322,
            0x1185fa9c9fef6326,
        ]);
        a.sub_assign(Fr::zero());
        assert_eq!(
            a,
            Fr::from_raw([
                0x7e7140b5196b9e6f,
                0x9abac9e4157b6172,
                0xf04bc41062fd7322,
                0x1185fa9c9fef6326,
            ])
        );

        // Sub mod equal itself
        let b = Fr::from_raw([
            0x43e1f593f0000001,
            0x2833e84879b97091,
            0xb85045b68181585d,
            0x30644e72e131a029,
        ]);
        a.sub_assign(b);
        assert_eq!(
            a,
            Fr::from_raw([
                0x7e7140b5196b9e6f,
                0x9abac9e4157b6172,
                0xf04bc41062fd7322,
                0x1185fa9c9fef6326,
            ])
        );

        // Sub one equal decremented itself
        a.sub_assign(Fr::one());
        assert_eq!(
            a,
            Fr::from_raw([
                0x7e7140b5196b9e6e,
                0x9abac9e4157b6172,
                0xf04bc41062fd7322,
                0x1185fa9c9fef6326,
            ])
        );
    }

    #[test]
    fn test_mul() {
        // Mul random field
        let mut a = Fr::from_raw([
            0x6b7e9b8faeefc81a,
            0xe30a8463f348ba42,
            0xeff3cb67a8279c9c,
            0x3d303651bd7c774d,
        ]);
        a.mul_assign(Fr::from_raw([
            0x13ae28e3bc35ebeb,
            0xa10f4488075cae2c,
            0x8160e95a853c3b5d,
            0x5ae3f03b561a841d,
        ]));
        assert_eq!(
            a,
            Fr::from_raw([
                0x0417f80df17a3ebc,
                0xf7e6edaf7e953f87,
                0xe06b196270fbf5d4,
                0x119aceb10b6b0d46
            ])
        );

        // Mul a * b + a * c = a ( b + c )
        let mut b = Fr::from_raw([
            0x13ae28e3bc35ebeb,
            0xa10f4488075cae2c,
            0x8160e95a853c3b5d,
            0x5ae3f03b561a841d,
        ]);
        let mut c = Fr::from_raw([
            0xd0970e5ed6f72cb5,
            0xa6682093ccc81082,
            0x06673b0101343b00,
            0x0e7db4ea6533afa9,
        ]);
        let copy_a = a;
        let mut copy_b = b;
        let copy_c = c;
        b.mul_assign(a);
        c.mul_assign(a);
        copy_b.add_assign(copy_c);
        assert_eq!(b.add_assign(c), copy_b.mul_assign(copy_a));
    }

    #[test]
    fn test_double() {
        // Double random equal to adding itself
        let a = Fr::from_raw([
            0x6b7e9b8faeefc81a,
            0xe30a8463f348ba42,
            0xeff3cb67a8279c9c,
            0x3d303651bd7c774d,
        ]);
        let mut b = Fr::from_raw([
            0x6b7e9b8faeefc81a,
            0xe30a8463f348ba42,
            0xeff3cb67a8279c9c,
            0x3d303651bd7c774d,
        ]);
        b.add_assign(Fr::from_raw([
            0x6b7e9b8faeefc81a,
            0xe30a8463f348ba42,
            0xeff3cb67a8279c9c,
            0x3d303651bd7c774d,
        ]));
        assert_eq!(a.double(), b);
    }

    #[test]
    fn test_square() {
        // Square random
        let a = Fr::from_raw([
            0x6b7e9b8faeefc81a,
            0xe30a8463f348ba42,
            0xeff3cb67a8279c9c,
            0x3d303651bd7c774d,
        ]);
        let sq = a.square();
        assert_eq!(
            sq,
            Fr::from_raw([
                0xb3656703c1e79650,
                0xa293ae9f7da14011,
                0x569272907963b1f5,
                0x29e8fcd5ca4e3afe
            ])
        );
    }
}
