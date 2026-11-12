//! `objects!`, which declares `ragwort_types::gc` types, and `named!`, which declares enums of
//! named built-ins. What they write is safe code.

mod named;
mod objects;
mod wire;

/// Declares a group of `ragwort_types::gc` object types, with typed fields and an enum over the
/// group. See that crate's docs for the syntax and what's generated.
#[proc_macro]
pub fn objects(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    objects::expand(input.into()).unwrap_or_else(syn::Error::into_compile_error).into()
}

/// Declares an enum whose variants are each named, written `Variant = "name"` after any fields,
/// with `name` each one's name. If none has fields, it also has `ALL`, its variants in order, and
/// `FromStr` back from a name, failing with `ragwort_types::UnknownName`. Names must differ.
///
/// # Data
///
/// With `#[data(Type)]` on an enum whose variants have no fields, each variant is written
/// `Variant = ("name", value)`, and the enum has a private `const fn data(&self) -> Type` that
/// gives its value. What's true of each variant is then written once, where it's declared:
///
/// ```text
/// named! {
///     #[data(u8)]
///     pub enum Shape {
///         /// Three sides.
///         Triangle = ("triangle", 3),
///         Square = ("square", 4),
///     }
/// }
/// ```
#[proc_macro]
pub fn named(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    named::expand(input.into()).unwrap_or_else(syn::Error::into_compile_error).into()
}

/// Writes `ragwort_types::wire::Wire` for a struct or an enum whose fields all have it: the
/// fields in order, after the variant's place for an enum. Its `SHAPE` is made of the names
/// and types of its fields and variants, so it changes when they do.
#[proc_macro_derive(Wire)]
pub fn wire(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    wire::expand(input.into()).unwrap_or_else(syn::Error::into_compile_error).into()
}
