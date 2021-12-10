#![allow(dead_code)]
#![feature(asm)]
mod arithmetic;

use proc_macro::{self, TokenStream};
use quote::quote;
use syn::{parse_macro_input, ItemStruct};

#[proc_macro_derive(AsmArith)]
pub fn derive_self_name(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let item = parse_macro_input!(input as ItemStruct);
    let struct_name = item.ident;
    let output = quote! {
        impl #struct_name {
            #[inline(always)]
            #[cfg(all(target_arch = "x86_64"))]
            pub fn asm_add_mod(&self, other: &#struct_name) -> Self {
                #struct_name([0,0,0,0])
            }
        }
    };
    output.into()
}
