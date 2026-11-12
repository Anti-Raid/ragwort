use std::collections::HashSet;

use proc_macro2::TokenStream;
use quote::quote;
use syn::{Error, Expr, ExprLit, Fields, ItemEnum, Lit, LitStr, Type};

pub(crate) fn expand(input: TokenStream) -> Result<TokenStream, Error> {
    let mut item: ItemEnum = syn::parse2(input)?;
    if !item.generics.params.is_empty() {
        return Err(Error::new_spanned(&item.generics, "a named enum can't be generic"));
    }
    // `#[data(Type)]` on the enum: each variant is written with a value of the type too.
    let mut data_type = None;
    if let Some(at) = item.attrs.iter().position(|attr| attr.path().is_ident("data")) {
        data_type = Some(item.attrs.remove(at).parse_args::<Type>()?);
    }
    let mut seen = HashSet::new();
    let mut variants = Vec::new();
    let mut data = Vec::new();
    for variant in &mut item.variants {
        let written = variant.discriminant.take().map(|(_, written)| written);
        let name = match (written, &data_type) {
            (Some(Expr::Lit(ExprLit { lit: Lit::Str(name), .. })), None) => name,
            (Some(Expr::Tuple(both)), Some(_)) if both.elems.len() == 2 => {
                let Expr::Lit(ExprLit { lit: Lit::Str(name), .. }) = &both.elems[0] else {
                    return Err(Error::new_spanned(&both.elems[0], "the name comes first, as a string"));
                };
                data.push(both.elems[1].clone());
                name.clone()
            }
            (_, None) => return Err(Error::new_spanned(&variant.ident, "write each variant as `Variant = \"name\"`, after any fields")),
            (_, Some(_)) => return Err(Error::new_spanned(&variant.ident, "write each variant as `Variant = (\"name\", data)`")),
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
        if let Some(data_type) = data_type {
            return Err(Error::new_spanned(data_type, "only an enum whose variants have no fields has data"));
        }
        return Ok(named);
    }
    let idents: Vec<_> = variants.iter().map(|(ident, _, _)| ident).collect();
    let with_data = data_type.map(|data_type| {
        quote! {
            impl #name {
                /// What it's written with, after its name.
                const fn data(&self) -> #data_type {
                    match self {
                        #(Self::#idents => #data,)*
                    }
                }
            }
        }
    });
    Ok(quote! {
        #named
        #with_data

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
