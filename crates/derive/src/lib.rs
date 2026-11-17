//! Procedural macros for `ragwort_types`: `objects!`, which declares `ragwort_types::gc` object
//! types, `named!`, which declares enums of named built-ins, and `#[derive(Wire)]`. The code they
//! generate is safe Rust.

mod named;
mod objects;
mod wire;

/// Declares a group of `ragwort_types::gc` object types, with typed fields and an enum over the
/// group. See the docs of that module for the syntax and the generated code.
#[proc_macro]
pub fn objects(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    objects::expand(input.into()).unwrap_or_else(syn::Error::into_compile_error).into()
}

/// Declares an enum in which each variant has a name. A variant is written `Variant = "name"`,
/// after any fields. The generated `name` method returns the name of a variant. If no variant has
/// fields, the enum also gets `ALL`, a slice of its variants in order, and a `FromStr`
/// implementation, which maps a name back to its variant and fails with
/// `ragwort_types::UnknownName`. The names must be distinct.
///
/// # Data
///
/// With `#[data(Type)]` on an enum whose variants have no fields, each variant is written
/// `Variant = ("name", value)`. The enum then gets a private `const fn data(&self) -> Type`, which
/// returns the value of a variant. The properties of each variant are then written once, on the
/// line that declares it:
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

/// Implements `ragwort_types::wire::Wire` for a struct or an enum whose fields all implement it.
/// The fields are written in order. For an enum, the index of the variant is written first.
/// `SHAPE` is computed from the names and types of the fields and variants, so it changes when
/// they change.
#[proc_macro_derive(Wire)]
pub fn wire(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    wire::expand(input.into()).unwrap_or_else(syn::Error::into_compile_error).into()
}
