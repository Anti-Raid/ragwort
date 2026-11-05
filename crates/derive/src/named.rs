use std::collections::HashSet;

use proc_macro2::TokenStream;
use quote::quote;
use syn::{Error, Expr, ExprLit, Fields, ItemEnum, Lit, LitStr};

pub(crate) fn expand(input: TokenStream) -> Result<TokenStream, Error> {
    let mut item: ItemEnum = syn::parse2(input)?;
    if !item.generics.params.is_empty() {
        return Err(Error::new_spanned(&item.generics, "a named enum can't be generic"));
    }
    let mut seen = HashSet::new();
    let mut variants = Vec::new();
    for variant in &mut item.variants {
        let name = match variant.discriminant.take() {
            Some((_, Expr::Lit(ExprLit { lit: Lit::Str(name), .. }))) => name,
            _ => return Err(Error::new_spanned(&variant.ident, "write each variant as `Variant = \"name\"`, after any fields")),
        };
        if !seen.insert(name.value()) {
            return Err(Error::new_spanned(&name, "two variants have this name"));
        }
        let ident = &variant.ident;
        let pattern = match variant.fields {
            Fields::Unit => quote!(Self::#ident),
            Fields::Named(_) => quote!(Self::#ident { .. }),
            Fields::Unnamed(_) => quote!(Self::#ident(..)),
        };
        variants.push((ident.clone(), pattern, name));
    }
    let name = &item.ident;
    let patterns = variants.iter().map(|(_, pattern, _)| pattern);
    let names: Vec<&LitStr> = variants.iter().map(|(_, _, name)| name).collect();
    let named = quote! {
        #item

        impl #name {
            /// What it's called.
            pub fn name(&self) -> &'static str {
                match self {
                    #(#patterns => #names,)*
                }
            }
        }
    };
    if !item.variants.iter().all(|v| matches!(v.fields, Fields::Unit)) {
        return Ok(named);
    }
    let idents: Vec<_> = variants.iter().map(|(ident, _, _)| ident).collect();
    Ok(quote! {
        #named

        impl #name {
            /// Every one, in order.
            pub const ALL: &'static [#name] = &[#(#name::#idents),*];
        }

        impl ::core::str::FromStr for #name {
            type Err = ::ragwort_types::UnknownName;

            fn from_str(name: &str) -> ::core::result::Result<Self, Self::Err> {
                match name {
                    #(#names => ::core::result::Result::Ok(#name::#idents),)*
                    _ => ::core::result::Result::Err(::ragwort_types::UnknownName),
                }
            }
        }
    })
}
