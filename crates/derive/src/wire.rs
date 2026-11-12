use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{Data, DeriveInput, Error, Fields, Index};

/// The code that writes `fields`, bound as `names`, and the code that reads them into what
/// `make` makes of them.
fn parts(fields: &Fields, make: TokenStream) -> (TokenStream, TokenStream, TokenStream) {
    let w = quote!(::ragwort_types::wire);
    match fields {
        Fields::Unit => (quote!(), quote!(), quote!(#make)),
        Fields::Named(named) => {
            let names: Vec<_> = named.named.iter().map(|field| field.ident.clone()).collect();
            let pattern = quote!({ #(#names),* });
            let write = quote!(#(#w::Wire::write(#names, out);)*);
            let read = quote!(#make { #(#names: #w::Wire::read(input)?),* });
            (pattern, write, read)
        }
        Fields::Unnamed(unnamed) => {
            let names: Vec<_> = (0..unnamed.unnamed.len()).map(|i| format_ident!("field{i}")).collect();
            let pattern = quote!((#(#names),*));
            let write = quote!(#(#w::Wire::write(#names, out);)*);
            let reads = names.iter().map(|_| quote!(#w::Wire::read(input)?));
            let read = quote!(#make(#(#reads),*));
            (pattern, write, read)
        }
    }
}

/// The names and types of `fields`, as text, for the shape.
fn text(fields: &Fields) -> String {
    let mut text = String::new();
    for field in fields {
        let (name, ty) = (field.ident.as_ref().map_or(String::new(), |name| name.to_string()), &field.ty);
        text.push_str(&format!("{name}:{};", quote!(#ty)));
    }
    text
}

pub(crate) fn expand(input: TokenStream) -> Result<TokenStream, Error> {
    let item: DeriveInput = syn::parse2(input)?;
    if !item.generics.params.is_empty() {
        return Err(Error::new_spanned(&item.generics, "a type with parameters has no one binary form"));
    }
    let w = quote!(::ragwort_types::wire);
    let name = &item.ident;
    let mut shape = name.to_string();
    let (write, read) = match &item.data {
        Data::Struct(data) => {
            shape.push_str(&text(&data.fields));
            let (pattern, write, read) = parts(&data.fields, quote!(Self));
            (quote!(let Self #pattern = self; #write), quote!(Ok(#read)))
        }
        Data::Enum(data) => {
            if data.variants.len() > usize::from(u16::MAX) {
                return Err(Error::new_spanned(&data.variants, "more variants than a `u16` counts"));
            }
            let (mut writes, mut reads) = (Vec::new(), Vec::new());
            for (place, variant) in data.variants.iter().enumerate() {
                shape.push_str(&format!("|{}{}", variant.ident, text(&variant.fields)));
                let ident = &variant.ident;
                let place = Index::from(place);
                let (pattern, write, read) = parts(&variant.fields, quote!(Self::#ident));
                writes.push(quote!(Self::#ident #pattern => { out.u16(#place); #write }));
                reads.push(quote!(#place => Ok(#read)));
            }
            (quote!(match self { #(#writes)* }), quote!(match input.u16()? { #(#reads,)* _ => Err(#w::Malformed) }))
        }
        Data::Union(data) => return Err(Error::new_spanned(data.union_token, "a union has no binary form")),
    };
    Ok(quote! {
        impl #w::Wire for #name {
            const SHAPE: u64 = #w::shape_of(#shape);

            fn write(&self, out: &mut #w::Writer) {
                #write
            }

            fn read(input: &mut #w::Reader<'_>) -> ::core::result::Result<Self, #w::Malformed> {
                #read
            }
        }
    })
}
