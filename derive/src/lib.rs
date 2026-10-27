//! Derives for `ragwort::gc::Trace` and `ragwort::gc::Plain`, so arena types need no unsafe.

use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{Data, DeriveInput, Fields, Type, parse_macro_input, parse_quote};

/// Traces every field. With `#[gc(items = Type)]` the type becomes an inline head, followed in
/// its allocation by items of `Type`, which the collector traces.
#[proc_macro_derive(Trace, attributes(gc))]
pub fn derive_trace(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    trace(input).unwrap_or_else(syn::Error::into_compile_error).into()
}

/// Checks at compile time that every field is `Plain` and that the type has no padding.
#[proc_macro_derive(Plain)]
pub fn derive_plain(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    plain(input).unwrap_or_else(syn::Error::into_compile_error).into()
}

fn items_attr(input: &DeriveInput) -> syn::Result<Option<Type>> {
    let mut items = None;
    for attr in input.attrs.iter().filter(|a| a.path().is_ident("gc")) {
        attr.parse_nested_meta(|meta| {
            if meta.path.is_ident("items") {
                items = Some(meta.value()?.parse::<Type>()?);
                Ok(())
            } else {
                Err(meta.error("expected `items = Type`"))
            }
        })?;
    }
    Ok(items)
}

/// Field types, and the code that traces them given `t: &mut Tracer`.
fn trace_body(data: &Data) -> (Vec<Type>, TokenStream) {
    fn bind(fields: &Fields) -> (Vec<Type>, TokenStream, Vec<proc_macro2::Ident>) {
        let names: Vec<_> = (0..fields.len()).map(|i| format_ident!("__f{i}")).collect();
        let types = fields.iter().map(|f| f.ty.clone()).collect();
        let pattern = match fields {
            Fields::Named(named) => {
                let members = named.named.iter().map(|f| f.ident.as_ref().unwrap());
                quote!({ #(#members: #names),* })
            }
            Fields::Unnamed(_) => quote!((#(#names),*)),
            Fields::Unit => quote!(),
        };
        (types, pattern, names)
    }
    match data {
        Data::Struct(s) => {
            let (types, pattern, names) = bind(&s.fields);
            (types, quote!(let Self #pattern = self; #(::ragwort::gc::Trace::trace(#names, t);)*))
        }
        Data::Enum(e) => {
            let mut all = Vec::new();
            let arms = e.variants.iter().map(|v| {
                let (types, pattern, names) = bind(&v.fields);
                all.extend(types);
                let ident = &v.ident;
                quote!(Self::#ident #pattern => { #(::ragwort::gc::Trace::trace(#names, t);)* })
            });
            let arms: Vec<_> = arms.collect();
            (all, quote!(match self { #(#arms)* }))
        }
        Data::Union(_) => (Vec::new(), quote!(compile_error!("unions can't derive Trace");)),
    }
}

fn trace(input: DeriveInput) -> syn::Result<TokenStream> {
    let name = &input.ident;
    let items = items_attr(&input)?;
    let (types, body) = trace_body(&input.data);
    let mut generics = input.generics.clone();
    // Concrete field types are checked by the body itself; generic ones need bounds.
    if generics.type_params().next().is_some() {
        let clause = generics.make_where_clause();
        for ty in types.iter().chain(&items) {
            clause.predicates.push(parse_quote!(#ty: ::ragwort::gc::Trace));
        }
    }
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let inline = items.as_ref().map(|items| {
        quote! {
            unsafe impl #impl_generics ::ragwort::gc::Inline for #name #ty_generics #where_clause {
                type Item = #items;
            }
        }
    });
    let inline_const = items.is_some().then(|| quote!(const INLINE: bool = true;));
    Ok(quote! {
        unsafe impl #impl_generics ::ragwort::gc::Trace for #name #ty_generics #where_clause {
            const NEEDS_TRACE: bool = false #(|| <#types as ::ragwort::gc::Trace>::NEEDS_TRACE)*;
            #inline_const

            #[inline]
            #[allow(unused_variables)]
            fn trace(&mut self, t: &mut ::ragwort::gc::Tracer<'_>) {
                #body
            }
        }
        #inline
    })
}

fn plain(input: DeriveInput) -> syn::Result<TokenStream> {
    let name = &input.ident;
    let Data::Struct(data) = &input.data else {
        return Err(syn::Error::new_spanned(name, "only structs can be Plain: an enum has invalid bit patterns"));
    };
    let types: Vec<Type> = data.fields.iter().map(|f| f.ty.clone()).collect();
    let items = items_attr(&input)?;
    // The type's one lifetime is its arena brand. Every field and the inline items must carry
    // that same brand, so the type can't be read with references from another arena.
    let lifetimes: Vec<_> = input.generics.lifetimes().map(|l| l.lifetime.clone()).collect();
    if lifetimes.len() > 1 {
        return Err(syn::Error::new_spanned(&input.generics, "a Plain type can have at most one lifetime, its arena brand"));
    }
    let (ty_generics, brand) = (input.generics.split_for_impl().1, lifetimes.first().cloned());
    let mut generics = input.generics.clone();
    let brand = brand.unwrap_or_else(|| {
        let brand: syn::Lifetime = parse_quote!('__gc);
        generics.params.insert(0, parse_quote!(#brand));
        brand
    });
    let clause = generics.make_where_clause();
    for ty in types.iter().chain(&items) {
        clause.predicates.push(parse_quote!(#ty: ::ragwort::gc::Plain<#brand>));
    }
    let (impl_generics, _, where_clause) = generics.split_for_impl();
    let message = format!("`{name}` has padding bytes; add explicit fields to fill them");
    // Without type parameters the layout is fixed, so check it where the type is defined.
    // Lifetimes don't change layout, so `'static` stands in for the brand.
    let eager = (input.generics.type_params().next().is_none() && input.generics.const_params().next().is_none())
        .then(|| {
            let args = (!lifetimes.is_empty()).then(|| quote!(<'static>));
            quote! { const _: () = <#name #args as ::ragwort::gc::Plain<'static>>::CHECK; }
        });
    let items_iter = items.iter();
    Ok(quote! {
        #eager
        unsafe impl #impl_generics ::ragwort::gc::Plain<#brand> for #name #ty_generics #where_clause {
            #[doc(hidden)]
            const CHECK: () = {
                #(let () = <#types as ::ragwort::gc::Plain<#brand>>::CHECK;)*
                #(let () = <#items_iter as ::ragwort::gc::Plain<#brand>>::CHECK;)*
                assert!(::core::mem::size_of::<Self>() == 0 #(+ ::core::mem::size_of::<#types>())*, #message);
            };
        }
    })
}
