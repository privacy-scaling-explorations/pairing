use super::LegendreSymbol;
use crate::arithmetic::{adc, mac, sbb, BaseExt, FieldExt, Group};
use core::convert::TryInto;
use core::fmt;
use core::ops::{Add, Mul, Neg, Sub};
use rand::RngCore;
use std::io::{self, Read, Write};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

#[derive(Clone, Copy, Eq)]
pub struct Fq(pub(crate) [u64; 4]);

/// Constant representing the modulus
/// q = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47
pub const MODULUS: Fq = Fq([
    0x3c208c16d87cfd47,
    0x97816a916871ca8d,
    0xb85045b68181585d,
    0x30644e72e131a029,
]);

/// INV = -(q^{-1} mod 2^64) mod 2^64
const INV: u64 = 0x87d20782e4866389;

/// R = 2^256 mod q
const R: Fq = Fq([
    0xd35d438dc58f0d9d,
    0x0a78eb28f5c70b3d,
    0x666ea36f7879462c,
    0x0e0a77c19a07df2f,
]);

/// R^2 = 2^512 mod q
const R2: Fq = Fq([
    0xf32cfc5b538afa89,
    0xb5e71911d44501fb,
    0x47ab1eff0a417ff6,
    0x06d89f71cab8351f,
]);

/// R^3 = 2^768 mod q
const R3: Fq = Fq([
    0xb1cd6dafda1530df,
    0x62f210e6a7283db6,
    0xef7f0b0c0ada0afb,
    0x20fd6e902d592544,
]);

pub const NEGATIVE_ONE: Fq = Fq([
    0x68c3488912edefaa,
    0x8d087f6872aabf4f,
    0x51e1a24709081231,
    0x2259d6b14729c0fa,
]);

impl Group for Fq {
    type Scalar = Fq;

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

impl ::std::fmt::Display for Fq {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let tmp = self.to_bytes();
        write!(f, "0x")?;
        for &b in tmp.iter().rev() {
            write!(f, "{:02x}", b)?;
        }
        Ok(())
    }
}

impl fmt::Debug for Fq {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let tmp = self.to_bytes();
        write!(f, "0x")?;
        for &b in tmp.iter().rev() {
            write!(f, "{:02x}", b)?;
        }
        Ok(())
    }
}

impl Default for Fq {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

impl From<bool> for Fq {
    fn from(bit: bool) -> Fq {
        if bit {
            Fq::one()
        } else {
            Fq::zero()
        }
    }
}

impl From<u64> for Fq {
    fn from(val: u64) -> Fq {
        Fq([val, 0, 0, 0]) * R2
    }
}

impl ConstantTimeEq for Fq {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0[0].ct_eq(&other.0[0])
            & self.0[1].ct_eq(&other.0[1])
            & self.0[2].ct_eq(&other.0[2])
            & self.0[3].ct_eq(&other.0[3])
    }
}

impl PartialEq for Fq {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).unwrap_u8() == 1
    }
}

impl std::cmp::Ord for Fq {
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

impl std::cmp::PartialOrd for Fq {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl ConditionallySelectable for Fq {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Fq([
            u64::conditional_select(&a.0[0], &b.0[0], choice),
            u64::conditional_select(&a.0[1], &b.0[1], choice),
            u64::conditional_select(&a.0[2], &b.0[2], choice),
            u64::conditional_select(&a.0[3], &b.0[3], choice),
        ])
    }
}

impl Neg for Fq {
    type Output = Fq;

    #[inline]
    fn neg(self) -> Fq {
        -&self
    }
}

impl<'a> Neg for &'a Fq {
    type Output = Fq;

    #[inline]
    fn neg(self) -> Fq {
        self.neg()
    }
}

impl<'a, 'b> Sub<&'b Fq> for &'a Fq {
    type Output = Fq;

    #[inline]
    fn sub(self, rhs: &'b Fq) -> Fq {
        self.sub(rhs)
    }
}

impl<'a, 'b> Add<&'b Fq> for &'a Fq {
    type Output = Fq;

    #[inline]
    fn add(self, rhs: &'b Fq) -> Fq {
        self.add(rhs)
    }
}

impl<'a, 'b> Mul<&'b Fq> for &'a Fq {
    type Output = Fq;

    #[inline]
    fn mul(self, rhs: &'b Fq) -> Fq {
        self.mul(rhs)
    }
}

impl_binops_additive!(Fq, Fq);
impl_binops_multiplicative!(Fq, Fq);

impl Fq {
    pub const fn size() -> usize {
        32
    }
    /// Attempts to convert a little-endian byte representation of
    /// a scalar into a `Fq`, failing if the input is not canonical.
    pub fn from_bytes(bytes: &[u8; 32]) -> CtOption<Fq> {
        let mut tmp = Fq([0, 0, 0, 0]);

        tmp.0[0] = u64::from_le_bytes(bytes[0..8].try_into().unwrap());
        tmp.0[1] = u64::from_le_bytes(bytes[8..16].try_into().unwrap());
        tmp.0[2] = u64::from_le_bytes(bytes[16..24].try_into().unwrap());
        tmp.0[3] = u64::from_le_bytes(bytes[24..32].try_into().unwrap());

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

    /// Converts an element of `Fq` into a byte representation in
    /// little-endian byte order.
    pub fn to_bytes(&self) -> [u8; 32] {
        // Turn into canonical form by computing
        // (a.R) / R = a
        let tmp = Fq::montgomery_reduce(&[self.0[0], self.0[1], self.0[2], self.0[3], 0, 0, 0, 0]);

        let mut res = [0; 32];
        res[0..8].copy_from_slice(&tmp.0[0].to_le_bytes());
        res[8..16].copy_from_slice(&tmp.0[1].to_le_bytes());
        res[16..24].copy_from_slice(&tmp.0[2].to_le_bytes());
        res[24..32].copy_from_slice(&tmp.0[3].to_le_bytes());

        res
    }

    pub fn legendre(&self) -> LegendreSymbol {
        // s = self^((modulus - 1) // 2)
        // 0x183227397098d014dc2822db40c0ac2ecbc0b548b438e5469e10460b6c3e7ea3
        let s = &[
            0x9e10460b6c3e7ea3u64,
            0xcbc0b548b438e546u64,
            0xdc2822db40c0ac2eu64,
            0x183227397098d014u64,
        ];
        let s = self.pow(s);
        if s == Self::zero() {
            LegendreSymbol::Zero
        } else if s == Self::one() {
            LegendreSymbol::QuadraticResidue
        } else {
            LegendreSymbol::QuadraticNonResidue
        }
    }

    /// Returns zero, the additive identity.
    #[inline]
    pub const fn zero() -> Fq {
        Fq([0, 0, 0, 0])
    }

    /// Returns one, the multiplicative identity.
    #[inline]
    pub const fn one() -> Fq {
        R
    }

    /// Doubles this field element.
    #[inline]
    pub fn double(&self) -> Fq {
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
                "adcx r9, r9",
                "adcx r10, r10",
                "adcx r11, r11",

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

    fn from_u512(limbs: [u64; 8]) -> Fq {
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
        let d0 = Fq([limbs[0], limbs[1], limbs[2], limbs[3]]);
        let d1 = Fq([limbs[4], limbs[5], limbs[6], limbs[7]]);
        // Convert to Montgomery form
        d0 * R2 + d1 * R3
    }

    /// Converts from an integer represented in little endian
    /// into its (congruent) `Fq` representation.
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
    pub fn square(&self) -> Fq {
        let mut r0: u64;
        let mut r1: u64;
        let mut r2: u64;
        let mut r3: u64;
        unsafe {
            asm!(
                // schoolbook multiplication
                //    *    |   a0    |   a1    |   a2    |   a3
                //    b0   | b0 * a0 | b0 * a1 | b0 * a2 | b0 * a3
                //    b1   | b1 * a0 | b1 * a1 | b1 * a2 | b1 * a3
                //    b2   | b2 * a0 | b2 * a1 | b2 * a2 | b2 * a3
                //    b3   | b3 * a0 | b3 * a1 | b3 * a2 | b3 * a3

                // load value to registers
                "mov r13, qword ptr [{a_ptr} + 0]",
                "mov r14, qword ptr [{a_ptr} + 8]",
                "mov r15, qword ptr [{a_ptr} + 16]",

                // `a0`
                "mov rdx, r13",

                // a0 * b0
                "mulx r9, r8, r13",

                // a0 * b1
                "mulx r10, rax, r14",
                "add r9, rax",

                // a0 * b2
                "mulx r11, rax, r15",
                "adcx r10, rax",

                // a0 * b3
                "mulx r12, rax, qword ptr [{a_ptr} + 24]",
                "adcx r11, rax",
                "adc r12, 0",

                // `a1`
                "mov rdx, r14",

                // a1 * b0
                "mulx rcx, rax, r13",
                "add r9, rax",
                "adcx r10, rcx",
                "adc r11, 0",

                // a1 * b1
                "mulx rcx, rax, r14",
                "add r10, rax",
                "adcx r11, rcx",
                "adc r12, 0",
                "xor r13, r13",

                // a1 * b2
                "mulx rcx, rax, r15",
                "add r11, rax",
                "adcx r12, rcx",
                "adc r13, 0",
                "xor r14, r14",

                // a1 * b3
                "mulx rcx, rax, qword ptr [{a_ptr} + 24]",
                "add r12, rax",
                "adcx r13, rcx",
                "adc r14, 0",

                // `a2`
                "mov rdx, r15",

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
                "mulx rcx, rax, r15",
                "add r12, rax",
                "adcx r13, rcx",
                "adc r14, 0",
                "xor r15, r15",

                // a2 * b3
                "mulx rcx, rax, qword ptr [{a_ptr} + 24]",
                "add r13, rax",
                "adcx r14, rcx",
                "adc r15, 0",

                // `a3`
                "mov rdx, qword ptr [{a_ptr} + 24]",

                // a3 * b0
                "mulx rcx, rax, qword ptr [{a_ptr} + 0]",
                "add r11, rax",
                "adcx r12, rcx",
                "adc r13, 0",

                // a3 * b1
                "mulx rcx, rax, qword ptr [{a_ptr} + 8]",
                "add r12, rax",
                "adcx r13, rcx",
                "adc r14, 0",

                // a3 * b2
                "mulx rcx, rax, qword ptr [{a_ptr} + 16]",
                "add r13, rax",
                "adcx r14, rcx",
                "adc r15, 0",

                // a3 * b3
                "mulx rcx, rax, qword ptr [{a_ptr} + 24]",
                "add r14, rax",
                "adc r15, rcx",

                // montgomery reduction
                // r8 ~ r15

                // `r8` -> 0
                "mov rdx, 0x87d20782e4866389",
                "mulx rax, rdx, r8",

                // r8' * m0
                "mulx rcx, rax, qword ptr [{m_ptr} + 0]",
                "add r8, rax",
                "adcx r9, rcx",
                "adc r10, 0",

                // r8' * m1
                "mulx rcx, rax, qword ptr [{m_ptr} + 8]",
                "add r9, rax",
                "adcx r10, rcx",
                "adc r11, 0",

                // r8' * m2
                "mulx rcx, rax, qword ptr [{m_ptr} + 16]",
                "add r10, rax",
                "adcx r11, rcx",
                "adc r12, 0",

                // r8' * m3
                "mulx rcx, rax, qword ptr [{m_ptr} + 24]",
                "add r11, rax",
                "adcx r12, rcx",
                "adc r13, 0",

                // `r9` -> 0
                "mov rdx, 0x87d20782e4866389",
                "mulx rax, rdx, r9",

                // r9' * m0
                "mulx rax, rcx, qword ptr [{m_ptr} + 0]",
                "add r9, rcx",
                "adcx r10, rax",
                "adc r11, 0",

                // r9' * m1
                "mulx rax, rcx, qword ptr [{m_ptr} + 8]",
                "add r10, rcx",
                "adcx r11, rax",
                "adc r12, 0",

                // r9' * m2
                "mulx rax, rcx, qword ptr [{m_ptr} + 16]",
                "add r11, rcx",
                "adcx r12, rax",
                "adc r13, 0",

                // r9' * m3
                "mulx rax, rcx, qword ptr [{m_ptr} + 24]",
                "add r12, rcx",
                "adcx r13, rax",
                "adc r14, 0",

                // `r10` -> 0
                "mov rdx, 0x87d20782e4866389",
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
                "mov rdx, 0x87d20782e4866389",
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

                "mov r12, r8",
                "mov r13, r9",
                "mov r14, r10",
                "mov r15, r11",

                "sub r12, qword ptr [{m_ptr} + 0]",
                "sbb r13, qword ptr [{m_ptr} + 8]",
                "sbb r14, qword ptr [{m_ptr} + 16]",
                "sbb r15, qword ptr [{m_ptr} + 24]",

                "cmovc r12, r8",
                "cmovc r13, r9",
                "cmovc r14, r10",
                "cmovc r15, r11",

                a_ptr = in(reg) self.0.as_ptr(),
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
                "mov rdx, 0x87d20782e4866389",
                "mulx rax, rdx, r8",

                // r8' * m0
                "mulx rcx, rax, qword ptr [{m_ptr} + 0]",
                "add r8, rax",
                "adcx r9, rcx",
                "adc r10, 0",

                // r8' * m1
                "mulx rcx, rax, qword ptr [{m_ptr} + 8]",
                "add r9, rax",
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
                "mov rdx, 0x87d20782e4866389",
                "mulx rax, rdx, r9",

                // r9' * m0
                "mulx rax, rcx, qword ptr [{m_ptr} + 0]",
                "add r9, rcx",
                "adcx r10, rax",
                "adc r11, 0",

                // r9' * m1
                "mulx rax, rcx, qword ptr [{m_ptr} + 8]",
                "add r10, rcx",
                "adcx r11, rax",
                "adc r12, 0",

                // r9' * m2
                "mulx rax, rcx, qword ptr [{m_ptr} + 16]",
                "add r11, rcx",
                "adcx r12, rax",
                "adc r13, 0",

                // r9' * m3
                "mulx rax, rcx, qword ptr [{m_ptr} + 24]",
                "add r12, rcx",
                "adcx r13, rax",
                "adc r14, 0",

                // `r10` -> 0
                "mov rdx, 0x87d20782e4866389",
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
                "mov rdx, 0x87d20782e4866389",
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

                "mov r12, r8",
                "mov r13, r9",
                "mov r14, r10",
                "mov r15, r11",

                "sub r12, qword ptr [{m_ptr} + 0]",
                "sbb r13, qword ptr [{m_ptr} + 8]",
                "sbb r14, qword ptr [{m_ptr} + 16]",
                "sbb r15, qword ptr [{m_ptr} + 24]",

                "cmovc r12, r8",
                "cmovc r13, r9",
                "cmovc r14, r10",
                "cmovc r15, r11",

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
        unsafe {
            asm!(
                // schoolbook multiplication
                //    *    |   a0    |   a1    |   a2    |   a3
                //    b0   | b0 * a0 | b0 * a1 | b0 * a2 | b0 * a3
                //    b1   | b1 * a0 | b1 * a1 | b1 * a2 | b1 * a3
                //    b2   | b2 * a0 | b2 * a1 | b2 * a2 | b2 * a3
                //    b3   | b3 * a0 | b3 * a1 | b3 * a2 | b3 * a3

                // load value to registers
                "mov r13, qword ptr [{b_ptr} + 0]",
                "mov r14, qword ptr [{b_ptr} + 8]",
                "mov r15, qword ptr [{b_ptr} + 16]",

                // `a0`
                "mov rdx, qword ptr [{a_ptr} + 0]",

                // a0 * b0
                "mulx r9, r8, r13",

                // a0 * b1
                "mulx r10, rax, r14",
                "add r9, rax",

                // a0 * b2
                "mulx r11, rax, r15",
                "adcx r10, rax",

                // a0 * b3
                "mulx r12, rax, qword ptr [{b_ptr} + 24]",
                "adcx r11, rax",
                "adc r12, 0",

                // `a1`
                "mov rdx, [{a_ptr} + 8]",

                // a1 * b0
                "mulx rcx, rax, r13",
                "add r9, rax",
                "adcx r10, rcx",
                "adc r11, 0",

                // a1 * b1
                "mulx rcx, rax, r14",
                "add r10, rax",
                "adcx r11, rcx",
                "adc r12, 0",
                "xor r13, r13",

                // a1 * b2
                "mulx rcx, rax, r15",
                "add r11, rax",
                "adcx r12, rcx",
                "adc r13, 0",
                "xor r14, r14",

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
                "mulx rcx, rax, r15",
                "add r12, rax",
                "adcx r13, rcx",
                "adc r14, 0",
                "xor r15, r15",

                // a2 * b3
                "mulx rcx, rax, qword ptr [{b_ptr} + 24]",
                "add r13, rax",
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
                "add r12, rax",
                "adcx r13, rcx",
                "adc r14, 0",

                // a3 * b2
                "mulx rcx, rax, qword ptr [{b_ptr} + 16]",
                "add r13, rax",
                "adcx r14, rcx",
                "adc r15, 0",

                // a3 * b3
                "mulx rcx, rax, qword ptr [{b_ptr} + 24]",
                "add r14, rax",
                "adc r15, rcx",

                // montgomery reduction
                // r8 ~ r15

                // `r8` -> 0
                "mov rdx, 0x87d20782e4866389",
                "mulx rax, rdx, r8",

                // r8' * m0
                "mulx rcx, rax, qword ptr [{m_ptr} + 0]",
                "add r8, rax",
                "adcx r9, rcx",
                "adc r10, 0",

                // r8' * m1
                "mulx rcx, rax, qword ptr [{m_ptr} + 8]",
                "add r9, rax",
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
                "mov rdx, 0x87d20782e4866389",
                "mulx rax, rdx, r9",

                // r9' * m0
                "mulx rax, rcx, qword ptr [{m_ptr} + 0]",
                "add r9, rcx",
                "adcx r10, rax",
                "adc r11, 0",

                // r9' * m1
                "mulx rax, rcx, qword ptr [{m_ptr} + 8]",
                "add r10, rcx",
                "adcx r11, rax",
                "adc r12, 0",

                // r9' * m2
                "mulx rax, rcx, qword ptr [{m_ptr} + 16]",
                "add r11, rcx",
                "adcx r12, rax",
                "adc r13, 0",

                // r9' * m3
                "mulx rax, rcx, qword ptr [{m_ptr} + 24]",
                "add r12, rcx",
                "adcx r13, rax",
                "adc r14, 0",

                // `r10` -> 0
                "mov rdx, 0x87d20782e4866389",
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
                "mov rdx, 0x87d20782e4866389",
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

                "mov r12, r8",
                "mov r13, r9",
                "mov r14, r10",
                "mov r15, r11",

                "sub r12, qword ptr [{m_ptr} + 0]",
                "sbb r13, qword ptr [{m_ptr} + 8]",
                "sbb r14, qword ptr [{m_ptr} + 16]",
                "sbb r15, qword ptr [{m_ptr} + 24]",

                "cmovc r12, r8",
                "cmovc r13, r9",
                "cmovc r14, r10",
                "cmovc r15, r11",

                m_ptr = in(reg) MODULUS.0.as_ptr(),
                a_ptr = in(reg) self.0.as_ptr(),
                b_ptr = in(reg) rhs.0.as_ptr(),
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
                "adcx  r13, r9",
                "adcx  r14, r10",
                "adcx  r15, r11",

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
                "adcx r9, qword ptr [{b_ptr} + 8]",
                "adcx r10, qword ptr [{b_ptr} + 16]",
                "adcx r11, qword ptr [{b_ptr} + 24]",

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

    /// Negates `self`.
    #[inline]
    pub fn neg(&self) -> Self {
        let mut r0: u64;
        let mut r1: u64;
        let mut r2: u64;
        let mut r3: u64;
        unsafe {
            asm!(
                // load a array to former registers
                "mov r8, 0x3c208c16d87cfd47",
                "mov r9, 0x97816a916871ca8d",
                "mov r10, 0xb85045b68181585d",
                "mov r11, 0x30644e72e131a029",

                "sub r8, qword ptr [{a_ptr} + 0]",
                "sbb r9, qword ptr [{a_ptr} + 8]",
                "sbb r10, qword ptr [{a_ptr} + 16]",
                "sbb r11, qword ptr [{a_ptr} + 24]",

                "mov r12, qword ptr [{a_ptr} + 0]",
                "mov r13, qword ptr [{a_ptr} + 8]",
                "mov r14, qword ptr [{a_ptr} + 16]",
                "mov r15, qword ptr [{a_ptr} + 24]",

                "or r12, r13",
                "or r14, r15",
                "or r12, r14",

                "mov r13, 0xffffffffffffffff",
                "cmp r12, 0x0000000000000000",
                "cmove r13, r12",

                "and r8, r13",
                "and r9, r13",
                "and r10, r13",
                "and r11, r13",

                a_ptr = in(reg) self.0.as_ptr(),
                out("r8") r0,
                out("r9") r1,
                out("r10") r2,
                out("r11") r3,
                out("r12") _,
                out("r13") _,
                out("r14") _,
                out("r15") _,
                options(pure, readonly, nostack)
            )
        }
        Self([r0, r1, r2, r3])
    }
}

impl From<Fq> for [u8; 32] {
    fn from(value: Fq) -> [u8; 32] {
        value.to_bytes()
    }
}

impl<'a> From<&'a Fq> for [u8; 32] {
    fn from(value: &'a Fq) -> [u8; 32] {
        value.to_bytes()
    }
}

impl ff::Field for Fq {
    fn random(mut rng: impl RngCore) -> Self {
        let mut random_bytes = [0; 64];
        rng.fill_bytes(&mut random_bytes[..]);

        Self::from_bytes_wide(&random_bytes)
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
        let tmp = self.pow(&[
            0x4f082305b61f3f52,
            0x65e05aa45a1c72a3,
            0x6e14116da0605617,
            0x0c19139cb84c680a,
        ]);

        CtOption::new(tmp, tmp.square().ct_eq(self))
    }

    /// Computes the multiplicative inverse of this element,
    /// failing if the element is zero.
    fn invert(&self) -> CtOption<Self> {
        let tmp = self.pow(&[
            0x3c208c16d87cfd45,
            0x97816a916871ca8d,
            0xb85045b68181585d,
            0x30644e72e131a029,
        ]);

        CtOption::new(tmp, !self.ct_eq(&Self::zero()))
    }
}

impl ff::PrimeField for Fq {
    type Repr = [u8; 32];

    const NUM_BITS: u32 = 254;
    const CAPACITY: u32 = 253;

    const S: u32 = 0;

    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        let mut tmp = Fq([0, 0, 0, 0]);

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
        let tmp =
            Self::montgomery_reduce(&[self.0[0], self.0[1], self.0[2], self.0[3], 0, 0, 0, 0]);

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
        unimplemented!()
    }

    fn root_of_unity() -> Self {
        unimplemented!()
    }
}

impl BaseExt for Fq {
    const MODULUS: &'static str =
        "0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47";

    /// Converts a 512-bit little endian integer into
    /// a `Fq` by reducing by the modulus.
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

impl FieldExt for Fq {
    const TWO_INV: Self = Self::from_raw([0, 0, 0, 0]);
    const ROOT_OF_UNITY_INV: Self = Self::from_raw([0, 0, 0, 0]);
    const DELTA: Self = Self::from_raw([0, 0, 0, 0]);
    const RESCUE_ALPHA: u64 = 0;
    const RESCUE_INVALPHA: [u64; 4] = [0, 0, 0, 0];
    const T_MINUS1_OVER2: [u64; 4] = [0, 0, 0, 0];
    const ZETA: Self = Self::from_raw([0, 0, 0, 0]);

    fn from_u128(v: u128) -> Self {
        Fq::from_raw([v as u64, (v >> 64) as u64, 0, 0])
    }

    /// Attempts to convert a little-endian byte representation of
    /// a scalar into a `Fr`, failing if the input is not canonical.
    fn from_bytes(bytes: &[u8; 32]) -> CtOption<Fq> {
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
        let tmp = Fq::montgomery_reduce(&[self.0[0], self.0[1], self.0[2], self.0[3], 0, 0, 0, 0]);

        u128::from(tmp.0[0]) | (u128::from(tmp.0[1]) << 64)
    }
}

#[cfg(test)]
use ff::Field;
#[cfg(test)]
use rand::SeedableRng;
#[cfg(test)]
use rand_xorshift::XorShiftRng;

#[test]
fn test_ser() {
    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    let a0 = Fq::random(&mut rng);
    let a_bytes = a0.to_bytes();
    let a1 = Fq::from_bytes(&a_bytes).unwrap();
    assert_eq!(a0, a1);
}

#[test]
fn test_inv() {
    let mut inv = 1u64;
    for _ in 0..63 {
        inv = inv.wrapping_mul(inv);
        inv = inv.wrapping_mul(MODULUS.0[0]);
    }
    inv = inv.wrapping_neg();

    assert_eq!(inv, INV);
}

#[test]
pub fn test_sqrt() {
    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);
    for _ in 0..10000 {
        let a = Fq::random(&mut rng);
        let mut b = a;
        b = b.square();
        assert_eq!(b.legendre(), LegendreSymbol::QuadraticResidue);

        let b = b.sqrt().unwrap();
        let mut negb = b;
        negb = negb.neg();

        assert!(a == b || a == negb);
    }

    let mut c = Fq::one();
    for _ in 0..10000 {
        let mut b = c;
        b = b.square();
        assert_eq!(b.legendre(), LegendreSymbol::QuadraticResidue);

        b = b.sqrt().unwrap();

        if b != c {
            b = b.neg();
        }

        assert_eq!(b, c);

        c += &Fq::one();
    }
}

#[test]
fn test_from_u512() {
    assert_eq!(
        Fq::from_raw([
            0x1f8905a172affa8a,
            0xde45ad177dcf3306,
            0xaaa7987907d73ae2,
            0x24d349431d468e30,
        ]),
        Fq::from_u512([
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
    crate::tests::field::random_field_tests::<Fq>();
}
