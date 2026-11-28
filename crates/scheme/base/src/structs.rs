//! The `struct` form.
//!
//! ```text
//! (struct name (field ...) option ...)
//! (struct name super (field ...) option ...)
//! ```
//!
//! The second form makes a subtype of the struct `super`. Its instances have `super`'s fields
//! followed by its own.
//!
//! A field is written as its name, or as `(name #:mutable)` for one that can be set.
//!
//! The form only goes at a module's top level, as `require` and `provide` do. So every struct
//! type exists before any code runs, and the compiler knows each one where it's used.
//!
//! # What it defines
//!
//! For `(struct point (x (y #:mutable)))`:
//!
//! - `struct:point`: the struct type.
//! - `point`: the constructor. It takes a value for every field, the supertype's fields first.
//! - `point?`: the predicate. It is true for a `point` and for an instance of any subtype.
//! - `point-x`, `point-y`: an accessor for each field the form declares.
//! - `set-point-y!`: a mutator for each mutable field.
//!
//! # Options
//!
//! - `#:mutable`: every field the form declares is mutable.
//! - `#:identity-eq?`: an instance is `equal?` only to itself. Without it, two instances of the
//!   same type are `equal?` when their fields are. Subtypes inherit this option.
//! - `#:constructor-name id` and `#:extra-constructor-name id`: also define `id` as a
//!   constructor. The struct's own name stays a constructor either way.
//! - `#:sealed`: the struct cannot be the supertype of another.
//! - `#:transparent`: accepted and ignored, since every struct is already printed with its
//!   fields.
//!
//! # Where a struct's name is used
//!
//! The name works in the module that defines the struct and in any module that requires it:
//!
//! - As the supertype in another `struct` form.
//! - In a `match` pattern such as `(point px py)`, with one sub-pattern per field, the
//!   supertype's fields first. It matches an instance of the struct or of a subtype. One
//!   sub-pattern can be followed by `...` to stand for the fields the others leave:
//!   `(point px _ ...)` looks at `x` alone.
//! - In `(struct-copy point p (y 5))`, which makes a new `point` with the fields of `p` except
//!   the ones given.
//!
//! # Providing a struct
//!
//! `(provide (struct-out point))` exports everything the form defines.
//!
//! `(provide (struct-out point #:omit-constructor))` exports everything but the constructors.
//! A module that requires it can still test, read and match a `point`, but can't make one
//! except through what else the module provides:
//!
//! ```text
//! (provide (struct-out user #:omit-constructor) make-user)
//! (struct user (name age))
//! (define (make-user name age)
//!   (unless (string? name) (raise 'bad-name))
//!   (user name age))
//! ```
//!
//! In a module that requires this one:
//!
//! - `(match u [(user name age) ...])` works, as do `user?` and `user-name`.
//! - `(user "ann" 3)`, `user` as a value and `(struct-copy user u ...)` are errors, since each
//!   would make a `user` that `make-user` hasn't checked.
//! - `user` can't be a supertype, since a subtype's constructor would do the same.
//!
//! # Procedures that work on any struct
//!
//! These look at a struct as a whole and never change one:
//!
//! - `(struct? v)`: whether `v` is an instance of any struct type.
//! - `(struct-type? v)`: whether `v` is a struct type, such as `struct:point`.
//! - `(struct-derived-from? v type)`: whether `v` is an instance of `type` or of a subtype.
//! - `(struct-type s)`: the type `s` was made as.
//! - `(struct-fields type)`: the list of `type`'s field names, the supertype's first.
//! - `(struct->list s)`: a new list of the values of the fields of `s`, in the order
//!   `(struct-fields (struct-type s))` names them.
//! - `(struct-field-mutable? type k)`: whether the field at position `k` of
//!   `(struct-fields type)` is mutable.
//!
//! Together they describe any struct without knowing its type:
//!
//! ```text
//! (define (struct->alist s)
//!   (map cons (struct-fields (struct-type s)) (struct->list s)))
//!
//! (struct->alist (point 1 2))   ; ((x . 1) (y . 2))
//! ```
//!
//! Nothing else makes a struct, reads one field or sets one: only the constructor, accessors
//! and mutators the form defines do. Code that needs to build or update structs of a type it
//! is handed takes the constructor or a mutator as an argument, as in `(apply point fields)`.
//!
//! A struct has no guard or contract of its own. To check the values a struct is made with,
//! write a procedure that checks them and then calls the constructor, and provide that with
//! the struct's constructor left out, as above.
//!
//! # How it is built
//!
//! The struct types are in [`ragwort_vm::structs`]. The code a form defines is built by
//! [`ragwort_compiler::structs`], which native ragwort's `%struct` uses too. The form's type is
//! created once, when its module is expanded.

use ragwort_compiler::module::{Field, ModuleError, StructDef};
use ragwort_compiler::structs::{self, Declaration, Declared, Named, Supertype};
use ragwort_compiler::Core;
use ragwort_types::gc::{OutOfMemory, Value};
use ragwort_types::string::chars;
use ragwort_types::syntax::SyntaxSpan;
use ragwort_vm::structs::TypeFlags;

use crate::expand::{Binding, Expander};
use crate::tree::{Stx, View};
use crate::{ExpandError, ExpandErrorKind};

/// A field declaration of a `struct` form.
struct FieldSpec {
    id: Stx,
    mutable: bool,
}

/// The parsed parts of a `struct` form. `constructors` holds the names of the extra constructors, and
/// `flags` holds the flags that the options set.
struct Form {
    name: Stx,
    parent: Option<Stx>,
    fields: Vec<FieldSpec>,
    constructors: Vec<Stx>,
    flags: TypeFlags,
}

/// A struct type, as known through the name of its constructor. `fields` holds all fields, with the
/// supertype's fields first.
#[derive(Clone, Debug)]
pub(crate) struct Info<'gc> {
    pub(crate) kind: Value<'gc>,
    pub(crate) fields: Vec<Field>,
    sealed: bool,
    /// Whether the struct's module provides it without its constructor. The name is then valid only in a `match` pattern.
    match_only: bool,
}

impl<'a, 'gc> Expander<'a, 'gc> {
    /// Returns the name of `stx` if it is a keyword. The name does not include the `#:` prefix.
    pub(crate) fn keyword_name(&self, stx: Stx) -> Option<String> {
        let keyword = self.engine.tree.keyword(stx)?;
        Some(chars(&self.engine.strings, keyword.symbol(self.engine.mc).name(self.engine.mc)).collect())
    }

    /// Creates an identifier named `name` with the scopes and the span of `from`. A form that binds
    /// `from` uses it for a derived name that the form also binds, such as `point?` for `point`.
    fn named_after(&mut self, from: Stx, name: &str) -> Result<Stx, ExpandError> {
        let (symbol, scopes) = (self.symbol(name)?, self.engine.tree.scopes_of(from)?);
        Ok(self.engine.tree.id(symbol, scopes, self.engine.tree.span(from))?)
    }

    /// Parses `form`, a `struct` form.
    fn struct_form(&mut self, form: Stx) -> Result<Form, ExpandError> {
        let bad = ExpandErrorKind::BadSyntax;
        let items = self.proper(form)?;
        let mut rest = items[1..].iter().copied();
        let Some(name) = rest.next().filter(|&name| self.is_id(name)) else { return Err(self.error(bad, form)) };
        let Some(mut next) = rest.next() else { return Err(self.error(bad, form)) };
        let mut parent = None;
        if self.is_id(next) {
            parent = Some(next);
            next = rest.next().ok_or_else(|| self.error(bad, form))?;
        }
        let specs = match self.engine.tree.view(next)? {
            View::List(specs, None) => specs,
            View::Datum(Value::NULL) => Vec::new(),
            _ => return Err(self.error(bad, next)),
        };
        let mut fields = Vec::with_capacity(specs.len());
        for spec in specs {
            if self.is_id(spec) {
                fields.push(FieldSpec { id: spec, mutable: false });
                continue;
            }
            let parts = self.proper(spec)?;
            let mut options = parts.iter().copied();
            let Some(id) = options.next().filter(|&id| self.is_id(id)) else { return Err(self.error(bad, spec)) };
            let mut field = FieldSpec { id, mutable: false };
            for option in options {
                match self.keyword_name(option).as_deref() {
                    Some("mutable") => field.mutable = true,
                    _ => return Err(self.error(bad, spec)),
                }
            }
            fields.push(field);
        }
        self.distinct(&fields.iter().map(|field| field.id).collect::<Vec<_>>())?;
        let (mut constructors, mut flags) = (Vec::new(), TypeFlags::empty());
        while let Some(option) = rest.next() {
            match self.keyword_name(option).as_deref() {
                Some("mutable") => fields.iter_mut().for_each(|field| field.mutable = true),
                Some("identity-eq?") => flags |= TypeFlags::IDENTITY,
                Some("sealed") => flags |= TypeFlags::SEALED,
                Some("transparent") => {}
                Some("constructor-name" | "extra-constructor-name") => {
                    let Some(id) = rest.next().filter(|&id| self.is_id(id)) else { return Err(self.error(bad, option)) };
                    constructors.push(id);
                }
                _ => return Err(self.error(bad, option)),
            }
        }
        Ok(Form { name, parent, fields, constructors, flags })
    }

    /// Returns the struct type that `id` names, if `id` is an identifier bound to the constructor of a struct.
    pub(crate) fn struct_info(&mut self, id: Stx) -> Result<Option<Info<'gc>>, ExpandError> {
        if !self.is_id(id) {
            return Ok(None);
        }
        fn info<'gc>(def: &StructDef, kind: Value<'gc>) -> Info<'gc> {
            Info { kind, fields: def.fields.to_vec(), sealed: def.sealed, match_only: def.match_only }
        }
        Ok(match self.resolve(id)? {
            Binding::Slot(slot) => self.engine.module.struct_def(slot).map(|(def, kind)| info(def, kind)),
            Binding::Import(import) => import.struct_def(self.engine.mc).map(|(def, kind)| info(def, kind)),
            _ => None,
        })
    }

    /// Converts the parsed `form` into the compiler's struct declaration. `whole` is the syntax of the entire form. Names become symbols with their spans.
    fn struct_item(&self, form: &Form, whole: Stx) -> structs::Form<'gc> {
        structs::Form {
            name: self.symbol_and_span(form.name),
            span: self.engine.tree.span(whole),
            parent: form.parent.map(|parent| self.symbol_and_span(parent)),
            fields: form.fields.iter().map(|field| Declaration { name: self.symbol_and_span(field.id).0, mutable: field.mutable }).collect(),
            flags: form.flags,
            constructors: form.constructors.iter().map(|&id| self.symbol_and_span(id)).collect(),
        }
    }

    /// Returns the symbol of the identifier `id` and its span.
    fn symbol_and_span(&self, id: Stx) -> (Value<'gc>, SyntaxSpan<'gc>) {
        (self.engine.tree.symbol(id).expect("an identifier").value(self.engine.mc), self.engine.tree.span(id))
    }

    /// Declares the bindings of `form`, a `struct` form that is the module's top-level form `index`.
    /// Also creates the struct type, which the module's code refers to as a constant.
    ///
    /// The compiler plans the declaration: it creates the type and lists the bindings. This method does the two steps that depend on scopes:
    /// - It resolves the supertype's identifier.
    /// - It defines each binding as an identifier with the scopes of the struct's name. A `struct` form written by a macro therefore keeps its bindings private to that macro.
    pub(crate) fn declare_struct(&mut self, form: Stx, index: u32) -> Result<Declared, ExpandError> {
        let parts = self.struct_form(form)?;
        let parent = match parts.parent {
            None => None,
            Some(id) => match self.struct_info(id)? {
                Some(info) => Some(Supertype { kind: info.kind, fields: info.fields, sealed: info.sealed }),
                None => return Err(self.error(ExpandErrorKind::BadSyntax, id)),
            },
        };
        let planned = self.struct_item(&parts, form).plan(self.engine.mc, parent).map_err(|error| match (error, parts.parent) {
            (ModuleError::Supertype, Some(id)) => self.error(ExpandErrorKind::BadSyntax, id),
            _ => self.module_error(error, form),
        })?;
        let mut slots = Vec::with_capacity(planned.members.len());
        for (named, _) in &planned.members {
            let id = match named {
                Named::Own => parts.name,
                Named::Constructor(i) => parts.constructors[*i],
                Named::Derived(name) => self.named_after(parts.name, name)?,
            };
            slots.push(self.define_top(id, index)?);
        }
        Ok(planned.declare(&mut self.engine.module, slots))
    }

    /// Returns the code of a declared `struct` form. The code defines each of the form's variables.
    pub(crate) fn lower_struct(&mut self, declared: Declared) -> Core<'gc> {
        let (_, kind) = self.engine.module.struct_def(declared.constructor()).expect("a declared struct");
        declared.define(kind, self.engine.module.locals())
    }

    /// Returns an expression for the struct type of `info`, with the span of `at`.
    pub(crate) fn struct_type(&mut self, info: &Info<'gc>, at: Stx) -> Result<Stx, ExpandError> {
        let kind = self.value(info.kind, at)?;
        self.quoted(kind, at)
    }

    /// Expands `(struct-copy name expr [field value] ...)` to `(let ((t expr)) (let ((v value)) ... (name field
    /// ...)))`. The body calls the struct's constructor. Each argument is the `v` given for the field, or a read of that field
    /// from `t`. A field read checks that `t` is an instance of the type.
    pub(crate) fn struct_copy(&mut self, stx: Stx, name: Stx, expr: Stx, updates: &[Stx]) -> Result<Stx, ExpandError> {
        let bad = ExpandErrorKind::BadSyntax;
        let Some(info) = self.struct_info(name)? else { return Err(self.error(bad, name)) };
        if info.match_only {
            return Err(self.error(ExpandErrorKind::NoConstructor, name));
        }
        let (is, get) = ("struct-derived-from?", self.internal("struct-ref", stx)?);
        let kind = self.struct_type(&info, stx)?;
        let source = self.introduce("t", stx)?;
        let mut given: Vec<Option<Stx>> = vec![None; info.fields.len()];
        let mut binds = Vec::with_capacity(updates.len());
        for (i, &update) in updates.iter().enumerate() {
            let &[field, value] = self.proper(update)?.as_slice() else { return Err(self.error(bad, update)) };
            let named = if self.is_id(field) { self.text(field) } else { None };
            // If several types in the supertype chain have a field of this name, the name refers to the field of the most derived type.
            let Some(index) = named.and_then(|named| info.fields.iter().rposition(|candidate| *candidate.name == *named)) else { return Err(self.error(bad, field)) };
            if given[index].is_some() {
                return Err(self.error(ExpandErrorKind::Duplicate, field));
            }
            let temp = self.introduce(&format!("v{i}"), stx)?;
            given[index] = Some(temp);
            binds.push((temp, value));
        }
        let all_given = given.iter().all(Option::is_some);
        let mut fields = Vec::with_capacity(given.len());
        for (index, given) in given.into_iter().enumerate() {
            fields.push(match given {
                Some(temp) => temp,
                None => {
                    let index = self.value(Value::fixnum(index as i64).ok_or_else(|| self.error(OutOfMemory, stx))?, stx)?;
                    self.list(&[get, source, kind, index], stx)?
                }
            });
        }
        let mut body = self.list(&[&[name], fields.as_slice()].concat(), stx)?;
        // Every field is given, so no field read has checked the type of the source. Test it here. If the test fails, read field 0, which raises the type error.
        if all_given {
            let zero = self.value(Value::fixnum(0).expect("zero is a fixnum"), stx)?;
            let (test, not_one) = (self.build(stx, is, &[&[source, kind]])?, self.list(&[get, source, kind, zero], stx)?);
            body = self.build(stx, "if", &[&[test, body, not_one]])?;
        }
        for (temp, value) in binds.into_iter().rev() {
            body = self.with_temp(stx, temp, value, body)?;
        }
        self.with_temp(stx, source, expr, body)
    }
}
