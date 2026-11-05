//! `objects!`, which declares `ragwort_types::gc` types, and `named!`, which declares enums of
//! named built-ins. What they write is safe code.

mod named;
mod objects;

/// Declares a group of `ragwort_types::gc` object types, with typed fields and an enum over the
/// group. See that crate's docs for the syntax and what's generated.
#[proc_macro]
pub fn objects(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    objects::expand(input.into()).unwrap_or_else(syn::Error::into_compile_error).into()
}

/// Declares an enum whose variants are each named, written `Variant = "name"` after any fields,
/// with `name` each one's name. If none has fields, it also has `ALL`, its variants in order, and
/// `FromStr` back from a name, failing with `ragwort_types::UnknownName`. Names must differ.
#[proc_macro]
pub fn named(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    named::expand(input.into()).unwrap_or_else(syn::Error::into_compile_error).into()
}
