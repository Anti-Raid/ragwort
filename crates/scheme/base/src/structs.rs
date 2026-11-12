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

use ragwort_compiler::module::{Field, StructDef};
use ragwort_compiler::structs::{self, Declaration, Declared, Member};
use ragwort_compiler::Core;
use ragwort_types::gc::{OutOfMemory, Value};
use ragwort_types::string::chars;
use ragwort_vm::Fault;
use ragwort_vm::structs::TypeFlags;

use crate::expand::{Binding, Expander};
use crate::tree::{Stx, View};
use crate::{ExpandError, ExpandErrorKind};

/// A field as a struct form writes it.
struct FieldSpec {
    id: Stx,
    mutable: bool,
}

/// A struct form's parts: its fields, the names of its constructors besides its own, and the
/// flags its options set.
struct Form {
    name: Stx,
    parent: Option<Stx>,
    fields: Vec<FieldSpec>,
    constructors: Vec<Stx>,
    flags: TypeFlags,
}

/// What a struct form says of its type.
struct Parts<'gc> {
    parent: Option<Info<'gc>>,
    /// All the type's fields, its supertype's first.
    fields: Vec<Field>,
    /// What the form defines, each with its identifier: the type, then the constructor that has
    /// the struct's name, then the rest.
    members: Vec<(Stx, Member)>,
}

/// A struct type, as the name of its constructor stands for it: its fields are all of them, its
/// supertype's first.
#[derive(Clone, Debug)]
pub(crate) struct Info<'gc> {
    pub(crate) kind: Value<'gc>,
    pub(crate) fields: Vec<Field>,
    sealed: bool,
    /// Whether its module provides it without its constructor, so the name is only for `match`.
    match_only: bool,
}

impl<'a, 'gc> Expander<'a, 'gc> {
    /// The name of the keyword `stx` is, if it's one.
    pub(crate) fn keyword_name(&self, stx: Stx) -> Option<String> {
        let keyword = self.tree.keyword(stx)?;
        Some(chars(&self.strings, keyword.symbol(self.mc).name(self.mc)).collect())
    }

    /// An identifier named `name`, in the scopes of `from`, where it is: what a form that binds
    /// `from` binds besides.
    fn named_after(&mut self, from: Stx, name: &str) -> Result<Stx, ExpandError> {
        let (symbol, scopes) = (self.symbol(name)?, self.tree.scopes_of(from)?);
        Ok(self.tree.id(symbol, scopes, self.tree.span(from))?)
    }

    /// The parts of `form`, a `struct` form.
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
        let specs = match self.tree.view(next)? {
            View::List(specs, None) => specs,
            View::Datum(Value::NIL) => Vec::new(),
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

    /// The struct type `id` stands for, if it's the name of one's constructor.
    pub(crate) fn struct_info(&mut self, id: Stx) -> Result<Option<Info<'gc>>, ExpandError> {
        if !self.is_id(id) {
            return Ok(None);
        }
        let of = |def: &StructDef, kind: Value<'gc>| Info { kind, fields: def.fields.to_vec(), sealed: def.sealed, match_only: def.match_only };
        Ok(match self.resolve(id)? {
            Binding::Slot(slot) => self.builder.struct_def(slot).map(|(def, kind)| of(def, kind)),
            Binding::Import(import) => import.struct_def(self.mc).map(|(def, kind)| of(def, kind)),
            _ => None,
        })
    }

    /// What `form` says of its type. Its supertype is a struct that isn't sealed.
    fn struct_parts(&mut self, form: &Form) -> Result<Parts<'gc>, ExpandError> {
        let parent = match form.parent {
            None => None,
            Some(id) => match self.struct_info(id)? {
                Some(parent) if !parent.sealed => Some(parent),
                _ => return Err(self.error(ExpandErrorKind::BadSyntax, id)),
            },
        };
        let name = self.text(form.name).expect("an identifier");
        let mut fields = parent.as_ref().map_or(Vec::new(), |parent| parent.fields.clone());
        let inherited = fields.len();
        for field in &form.fields {
            fields.push(Field { name: self.text(field.id).expect("an identifier").into(), mutable: field.mutable });
        }
        let Some(named) = structs::members(&name, &fields[inherited..], inherited) else { return Err(self.error(OutOfMemory, form.name)) };
        let mut members = Vec::with_capacity(named.len() + form.constructors.len());
        for (name, member) in named {
            members.push((if member == Member::Make { form.name } else { self.named_after(form.name, &name)? }, member));
            // The constructors of other names go after the one that has the struct's name.
            if member == Member::Make {
                members.extend(form.constructors.iter().map(|&id| (id, Member::Make)));
            }
        }
        Ok(Parts { parent, fields, members })
    }

    /// The symbol of a struct form's name, and the fields it declares, as its type is made of
    /// them.
    fn struct_names(&self, form: &Form) -> (Value<'gc>, Vec<Declaration<'gc>>) {
        let symbol = |id: Stx| self.tree.symbol(id).expect("an identifier").value(self.mc);
        let declared = |field: &FieldSpec| Declaration { name: symbol(field.id), mutable: field.mutable };
        (symbol(form.name), form.fields.iter().map(declared).collect())
    }

    /// Declares what `form`, a struct form that's the module's top-level form `index`, defines,
    /// and makes its type, which the module's code has as a constant.
    pub(crate) fn declare_struct(&mut self, form: Stx, index: u32) -> Result<Declared, ExpandError> {
        let parts = self.struct_form(form)?;
        let Parts { parent, fields, members } = self.struct_parts(&parts)?;
        let above = parent.map_or(Value::FALSE, |parent| parent.kind);
        let (name, own) = self.struct_names(&parts);
        let kind = structs::make_type(self.mc, name, above, &own, parts.flags).map_err(|fault| match fault {
            Fault::OutOfMemory => self.error(OutOfMemory, form),
            _ => self.error(ExpandErrorKind::BadSyntax, form),
        })?;
        let mut slots = Vec::with_capacity(members.len());
        for (id, member) in members {
            slots.push((self.define_top(id, index)?, member));
        }
        let sealed = parts.flags.contains(TypeFlags::SEALED);
        Ok(Declared::new(&mut self.builder, kind, fields, sealed, slots))
    }

    /// The code of a struct form at the top level, which defines each of the form's variables.
    pub(crate) fn lower_struct(&mut self, declared: Declared) -> Core<'gc> {
        let (_, kind) = self.builder.struct_def(declared.constructor()).expect("a declared struct");
        declared.define(kind, self)
    }

    /// An expression for the type of `info`, at `at`.
    pub(crate) fn struct_type(&mut self, info: &Info<'gc>, at: Stx) -> Result<Stx, ExpandError> {
        let kind = self.value(info.kind, at)?;
        self.quoted(kind, at)
    }

    /// `(struct-copy name e [field value] ...)`: `(let ((t e)) (let ((v value)) ... (name field
    /// ...)))`, a call of the struct's constructor, each field its `v` or a read of that field
    /// of `t`, which checks that `t` is of the type.
    pub(crate) fn struct_copy(&mut self, stx: Stx, name: Stx, e: Stx, updates: &[Stx]) -> Result<Stx, ExpandError> {
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
            // A subtype's field of a name is the one meant, over its supertype's.
            let Some(k) = named.and_then(|named| info.fields.iter().rposition(|f| *f.name == *named)) else { return Err(self.error(bad, field)) };
            if given[k].is_some() {
                return Err(self.error(ExpandErrorKind::Duplicate, field));
            }
            let temp = self.introduce(&format!("v{i}"), stx)?;
            given[k] = Some(temp);
            binds.push((temp, value));
        }
        let all_given = given.iter().all(Option::is_some);
        let mut fields = Vec::with_capacity(given.len());
        for (k, given) in given.into_iter().enumerate() {
            fields.push(match given {
                Some(temp) => temp,
                None => {
                    let k = self.value(Value::fixnum(k as i64).ok_or_else(|| self.error(OutOfMemory, stx))?, stx)?;
                    self.list(&[get, source, kind, k], stx)?
                }
            });
        }
        let mut body = self.list(&[&[name], fields.as_slice()].concat(), stx)?;
        // Nothing has read a field of the source, to find it's not of the type.
        if all_given {
            let zero = self.value(Value::fixnum(0).expect("zero is a fixnum"), stx)?;
            let (test, not_one) = (self.build(stx, is, &[&[source, kind]])?, self.list(&[get, source, kind, zero], stx)?);
            body = self.build(stx, "if", &[&[test, body, not_one]])?;
        }
        for (temp, value) in binds.into_iter().rev() {
            body = self.with_temp(stx, temp, value, body)?;
        }
        self.with_temp(stx, source, e, body)
    }
}
