#![feature(asm)]
mod arithmetic;

use arithmetic::add_mod_impl;
use proc_macro::{self, TokenStream};
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

mod tests;

#[proc_macro_derive(AsmArith, attributes(PrimeFieldModulus, PrimeFieldGenerator, UseADX))]
pub fn asm_arith(input: TokenStream) -> TokenStream {
    let DeriveInput { ident, .. } = parse_macro_input!(input);
    let mut gen = add_mod_impl();
    let output = quote! {
        impl #ident {
            fn asm_add(self, b: #ident) -> #ident {
                self
            }
        }
    };
    gen.extend(output);

    gen.into()
}
