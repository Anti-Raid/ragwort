use proc_macro2::{Literal, TokenStream};
use quote::{format_ident, quote};
use syn::ext::IdentExt;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::{Attribute, Error, GenericArgument, Ident, LitInt, Path, PathArguments, Token, Type, TypePath, Visibility, braced};

/// Names a field can't take: methods of `Gc` that would hide its accessors, and the
/// constructor's parameters.
const RESERVED: [&str; 10] = ["get", "set", "len", "is_empty", "entry", "set_entry", "items", "mc", "fill", "entries"];

fn krate() -> TokenStream {
    quote!(::ragwort_gc_words)
}

struct Group {
    attrs: Vec<Attribute>,
    vis: Visibility,
    name: Ident,
    base: TokenStream,
    objects: Vec<Object>,
}

struct Object {
    attrs: Vec<Attribute>,
    vis: Visibility,
    name: Ident,
    fields: Vec<Field>,
    items: Option<Slot>,
}

struct Field {
    docs: Vec<Attribute>,
    name: Ident,
    slot: Slot,
}

#[derive(Clone, Copy, PartialEq)]
enum Class {
    Word,
    Value,
    Reference,
    Ephemeron,
}

struct Slot {
    /// The marker type in `ragwort_gc_words::slot`.
    path: TokenStream,
    /// What a read gives and what a write takes.
    out: TokenStream,
    input: TokenStream,
    class: Class,
}

impl Slot {
    fn width(&self) -> usize {
        if self.class == Class::Ephemeron { 2 } else { 1 }
    }
}

fn keyword(input: ParseStream, word: &str) -> bool {
    input.fork().parse::<Ident>().is_ok_and(|i| i == word)
}

impl Parse for Group {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let vis = input.parse()?;
        if !keyword(input, "kind") {
            return Err(input.error("expected `kind Name;`, naming the group's enum"));
        }
        input.parse::<Ident>()?;
        let name = input.parse()?;
        let w = krate();
        let base = if input.peek(Token![;]) {
            quote!(#w::FIRST_TYPE)
        } else if keyword(input, "after") {
            input.parse::<Ident>()?;
            let group: Path = input.parse()?;
            quote!(#group::END)
        } else if keyword(input, "at") {
            input.parse::<Ident>()?;
            let number: LitInt = input.parse()?;
            number.base10_parse::<u16>()?;
            quote!(#number)
        } else {
            return Err(input.error("expected `;`, `after Group;` or `at N;`"));
        };
        input.parse::<Token![;]>()?;
        let mut objects = Vec::new();
        while !input.is_empty() {
            objects.push(input.parse()?);
        }
        if objects.is_empty() {
            return Err(input.error("expected at least one struct"));
        }
        Ok(Self { attrs, vis, name, base, objects })
    }
}

impl Parse for Object {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let vis = input.parse()?;
        input.parse::<Token![struct]>()?;
        let name = input.parse()?;
        let content;
        braced!(content in input);
        let fields = Punctuated::<Field, Token![,]>::parse_terminated(&content)?.into_iter().collect();
        let items = if keyword(input, "items") {
            let word: Ident = input.parse()?;
            let slot = slot(&input.parse()?)?;
            if slot.class == Class::Reference {
                return Err(Error::new(word.span(), "items can be Value, Ephemeron or a word type"));
            }
            Some(slot)
        } else {
            None
        };
        if input.peek(Token![;]) {
            input.parse::<Token![;]>()?;
        }
        Ok(Self { attrs, vis, name, fields, items })
    }
}

impl Parse for Field {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let docs = input.call(Attribute::parse_outer)?;
        if let Some(attr) = docs.iter().find(|a| !a.path().is_ident("doc")) {
            return Err(Error::new_spanned(attr, "only doc comments go on fields"));
        }
        if input.peek(Token![pub]) {
            return Err(input.error("fields take their object's visibility"));
        }
        let name: Ident = input.parse()?;
        if RESERVED.contains(&name.unraw().to_string().as_str()) {
            return Err(Error::new(name.span(), "reserved: a method of `Gc` or a constructor parameter"));
        }
        input.parse::<Token![:]>()?;
        Ok(Self { docs, name, slot: slot(&input.parse()?)? })
    }
}

fn slot(ty: &Type) -> syn::Result<Slot> {
    let w = krate();
    let err = || Error::new_spanned(ty, "expected Value, Member<T>, Weak<T>, Host<T>, Ephemeron, u64, i64, u32, f64 or bool");
    let Type::Path(TypePath { qself: None, path }) = ty else { return Err(err()) };
    let [segment] = &path.segments.iter().collect::<Vec<_>>()[..] else { return Err(err()) };
    if path.leading_colon.is_some() {
        return Err(err());
    }
    let arg = match &segment.arguments {
        PathArguments::None => None,
        PathArguments::AngleBracketed(a) => match &a.args.iter().collect::<Vec<_>>()[..] {
            [GenericArgument::Type(t)] => Some(t),
            _ => return Err(err()),
        },
        PathArguments::Parenthesized(_) => return Err(err()),
    };
    let ident = &segment.ident;
    let value = quote!(#w::Value<'gc>);
    let slot = |path, out: TokenStream, input, class| Slot { path, out, input, class };
    Ok(match (ident.to_string().as_str(), arg) {
        ("Value", None) => slot(quote!(#w::slot::Value), value.clone(), value, Class::Value),
        ("u64" | "i64" | "u32" | "f64" | "bool", None) => {
            slot(quote!(#w::slot::#ident), quote!(::core::primitive::#ident), quote!(::core::primitive::#ident), Class::Word)
        }
        ("Member" | "Weak", Some(t)) => {
            let out = quote!(::core::option::Option<#w::Gc<'gc, #t>>);
            slot(quote!(#w::slot::#ident<#t>), out.clone(), out, Class::Reference)
        }
        ("Host", Some(t)) => {
            let out = quote!(::core::option::Option<#w::HostRef<'gc, #t>>);
            slot(quote!(#w::slot::Host<#t>), out.clone(), out, Class::Reference)
        }
        ("Ephemeron", None) => slot(
            quote!(#w::slot::Ephemeron),
            quote!(::core::option::Option<(#value, #value)>),
            quote!((#value, #value)),
            Class::Ephemeron,
        ),
        _ => return Err(err()),
    })
}

pub(crate) fn expand(input: TokenStream) -> syn::Result<TokenStream> {
    let group: Group = syn::parse2(input)?;
    let w = krate();
    let Group { attrs, vis, name: kind, base, objects } = &group;
    let count = u16::try_from(objects.len()).map_err(|_| Error::new(kind.span(), "too many types"))?;
    let names: Vec<&Ident> = objects.iter().map(|o| &o.name).collect();
    let numbers: Vec<Literal> = (0..count).map(Literal::u16_unsuffixed).collect();
    let count = Literal::u16_unsuffixed(count);
    let mut out = quote! {
        #(#attrs)*
        #[derive(Clone, Copy, PartialEq, Debug)]
        #[allow(dead_code)]
        #vis enum #kind<'gc> {
            #(#names(#w::Gc<'gc, #names>),)*
        }

        #[allow(dead_code)]
        impl #kind<'_> {
            /// The type number of the group's first type.
            pub const BASE: u16 = #base;
            /// One past the group's last type number, where a group declared `after` it starts.
            pub const END: u16 = Self::BASE + #count;
        }

        #[allow(dead_code)]
        impl<'gc> #kind<'gc> {
            /// Which of the group's types `value` refers to, from the type number it carries, or
            /// `None` for any other value.
            #[inline]
            pub fn of(value: #w::Value<'gc>) -> ::core::option::Option<Self> {
                let (ty, index) = value.object_parts()?;
                match ty.wrapping_sub(Self::BASE) {
                    #(#numbers => ::core::option::Option::Some(Self::#names(#w::Gc::forge(index))),)*
                    _ => ::core::option::Option::None,
                }
            }

            #[inline]
            pub fn value(self, mc: &#w::Mutation<'gc>) -> #w::Value<'gc> {
                match self {
                    #(Self::#names(gc) => #w::Value::object(mc, gc),)*
                }
            }
        }
    };
    for (object, number) in objects.iter().zip(&numbers) {
        out.extend(expand_object(object, kind, number)?);
    }
    Ok(out)
}

fn expand_object(object: &Object, kind: &Ident, number: &Literal) -> syn::Result<TokenStream> {
    let w = krate();
    let Object { attrs, vis, name, fields, items } = object;
    let mut seen = std::collections::HashSet::new();
    for field in fields {
        let base = field.name.unraw().to_string();
        for method in [base.clone(), format!("set_{base}")] {
            if !seen.insert(method.clone()) {
                return Err(Error::new(field.name.span(), format!("`{method}` would be generated twice")));
            }
        }
    }

    let mut at = 0;
    let mut starts = Vec::new();
    for field in fields {
        starts.push(at);
        at += field.slot.width();
    }
    let words = Literal::usize_unsuffixed(at);
    let roles = fields.iter().map(|f| {
        let path = &f.slot.path;
        quote!(<#path as #w::slot::Slot>::ROLE)
    });
    let items_kind = match items {
        None => quote!(#w::Items::None),
        Some(Slot { class: Class::Ephemeron, .. }) => quote!(#w::Items::Ephemerons),
        Some(Slot { path, .. }) => quote!(<#path as #w::slot::Item>::ITEMS),
    };

    let field_names: Vec<&Ident> = fields.iter().map(|f| &f.name).collect();
    let consts: Vec<Ident> = fields.iter().map(|f| format_ident!("{}", f.name.unraw().to_string().to_uppercase(), span = f.name.span())).collect();
    let setters: Vec<Ident> = fields.iter().map(|f| format_ident!("set_{}", f.name.unraw(), span = f.name.span())).collect();
    let paths: Vec<&TokenStream> = fields.iter().map(|f| &f.slot.path).collect();
    let outs: Vec<&TokenStream> = fields.iter().map(|f| &f.slot.out).collect();
    let inputs: Vec<&TokenStream> = fields.iter().map(|f| &f.slot.input).collect();
    let docs: Vec<&Vec<Attribute>> = fields.iter().map(|f| &f.docs).collect();
    let indices: Vec<Literal> = starts.iter().map(|&s| Literal::usize_unsuffixed(s)).collect();
    let ends: Vec<Literal> = fields.iter().zip(&starts).map(|(f, &s)| Literal::usize_unsuffixed(s + f.slot.width())).collect();

    // Without items it's `alloc_fixed`, which is small enough to inline everywhere and has to
    // be: LLVM stops inlining it into large functions otherwise.
    let inline = if items.is_none() { quote!(#[inline(always)]) } else { quote!(#[inline]) };
    let (params, alloc, items_sig, items_impl) = match items {
        None => (quote!(), quote!(mc.alloc::<#name, #words>(__words)), quote!(), quote!()),
        Some(Slot { class: Class::Ephemeron, .. }) => (
            quote!(entries: usize),
            quote!(mc.alloc_items::<#name, #words>(__words, entries.saturating_mul(2), #w::Value::BROKEN)),
            quote!(),
            quote!(),
        ),
        Some(Slot { path, input, .. }) => (
            quote!(len: usize, fill: #input),
            quote!(mc.alloc_items::<#name, #words>(__words, len, #w::Value::from_bits(<#path as #w::slot::Item>::store(fill)))),
            quote!(fn items(self, mc: &#w::Mutation<'gc>) -> #w::Slots<'gc, #path>;),
            quote! {
                #[inline]
                fn items(self, mc: &#w::Mutation<'gc>) -> #w::Slots<'gc, #path> {
                    #w::raw::Raw::item_slots(self, mc)
                }
            },
        ),
    };
    let fields_trait = format_ident!("{}Fields", name);
    let doc = format!("Field accessors for `Gc<{name}>`.");

    Ok(quote! {
        #(#attrs)*
        #[allow(dead_code)]
        #vis struct #name;

        impl #w::Object for #name {
            const DESC: #w::Desc =
                #w::Desc::layout::<#name>(&[#(#roles),*], #items_kind).numbered(#kind::BASE + #number);
        }

        #[allow(dead_code)]
        impl #name {
            #(#(#docs)* #vis const #consts: #w::Field<#name, #paths> = #w::Field::new(#indices);)*

            #inline
            #[allow(clippy::new_ret_no_self, clippy::too_many_arguments)]
            #vis fn new<'gc>(
                mc: &#w::Mutation<'gc>,
                #(#field_names: #inputs,)*
                #params
            ) -> ::core::result::Result<#w::Gc<'gc, #name>, #w::OutOfMemory> {
                #[allow(unused_mut)]
                let mut __words = [0u64; #words];
                #(<#paths as #w::slot::Slot>::init(#field_names, &mut __words[#indices..#ends]);)*
                #alloc
            }
        }

        #[doc = #doc]
        #[allow(dead_code)]
        #vis trait #fields_trait<'gc> {
            #(
                #(#docs)*
                fn #field_names(self, mc: &#w::Mutation<'gc>) -> #outs;
                fn #setters(self, mc: &#w::Mutation<'gc>, value: #inputs);
            )*
            #items_sig
        }

        impl<'gc> #fields_trait<'gc> for #w::Gc<'gc, #name> {
            #(
                #[inline]
                fn #field_names(self, mc: &#w::Mutation<'gc>) -> #outs {
                    self.get(mc, #name::#consts)
                }

                #[inline]
                fn #setters(self, mc: &#w::Mutation<'gc>, value: #inputs) {
                    self.set(mc, #name::#consts, value);
                }
            )*
            #items_impl
        }
    })
}
