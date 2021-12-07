// const INV: u64 = 0xc2e1f593efffffff;

use quote::quote;

pub fn add_mod_impl() -> proc_macro2::TokenStream {
    let mut gen = proc_macro2::TokenStream::new();
    let modulus: [u64; 4] = [
        0x43e1f593f0000001,
        0x2833e84879b97091,
        0xb85045b68181585d,
        0x30644e72e131a029,
    ];

    let m0: syn::Ident = syn::Ident::new(
        &format!("{}{}", modulus[0], 0),
        proc_macro2::Span::call_site(),
    );
    let m1: syn::Ident = syn::Ident::new(
        &format!("{}{}", modulus[1], 1),
        proc_macro2::Span::call_site(),
    );
    let m2: syn::Ident = syn::Ident::new(
        &format!("{}{}", modulus[2], 2),
        proc_macro2::Span::call_site(),
    );
    let m3: syn::Ident = syn::Ident::new(
        &format!("{}{}", modulus[3], 3),
        proc_macro2::Span::call_site(),
    );

    gen.extend(quote! {
        #[inline(always)]
        #[cfg(all(target_arch = "x86_64"))]
        pub fn asm_add_mod(a: &[u64; 4], b: &[u64; 4]) -> [u64; 4] {
            let mut r0: u64;
            let mut r1: u64;
            let mut r2: u64;
            let mut r3: u64;

            unsafe {
                asm!(
                    // we sum (a+b) using addition chain with OF
                    // and sum (a+b) - p using addition chain with CF
                    // if (a+b) does not overflow the modulus
                    // then sum (a+b) will produce CF
                    "xor r12d, r12d",
                    "mov r12, qword ptr [{a_ptr} + 0]",
                    "mov r13, qword ptr [{a_ptr} + 8]",
                    "mov r14, qword ptr [{a_ptr} + 16]",
                    "mov r15, qword ptr [{a_ptr} + 24]",
                    "adox r12, qword ptr [{b_ptr} + 0]",
                    "mov r8, r12",
                    "adcx r8, qword ptr [rip + {q0_ptr}]",
                    "adox r13, qword ptr [{b_ptr} + 8]",
                    "mov r9, r13",
                    "adcx r9, qword ptr [rip + {q1_ptr}]",
                    "adox r14, qword ptr [{b_ptr} + 16]",
                    "mov r10, r14",
                    "adcx r10, qword ptr [rip + {q2_ptr}]",
                    "adox r15, qword ptr [{b_ptr} + 24]",
                    "mov r11, r15",
                    "adcx r11, qword ptr [rip + {q3_ptr}]",

                    // if CF = 0 then take value (a+b) from [r12, .., r15]
                    // otherwise take (a+b) - p

                    "cmovc r12, r8",
                    "cmovc r13, r9",
                    "cmovc r14, r10",
                    "cmovc r15, r11",

                    q0_ptr = sym #m0,
                    q1_ptr = sym #m1,
                    q2_ptr = sym #m2,
                    q3_ptr = sym #m3,
                    // end of reduction
                    a_ptr = in(reg) a.as_ptr(),
                    b_ptr = in(reg) b.as_ptr(),
                    out("r8") _,
                    out("r9") _,
                    out("r10") _,
                    out("r11") _,
                    out("r12") r0
                    out("r13") r1
                    out("r14") r2
                    out("r15") r3,
                    options(pure, readonly, nostack)
                );
            }
            [r0, r1, r2, r3]
        }
    });
    gen
}
