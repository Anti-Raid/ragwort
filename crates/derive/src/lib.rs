//! `objects!`, which declares `ragwort_types::gc` types. What it writes is safe code.

mod objects;

/// Declares a group of `ragwort_types::gc` object types, with typed fields and an enum over the
/// group. See that crate's docs for the syntax and what's generated.
#[proc_macro]
pub fn objects(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    objects::expand(input.into()).unwrap_or_else(syn::Error::into_compile_error).into()
}
