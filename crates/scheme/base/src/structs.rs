//! `struct`, whose types [`ragwort_vm::structs`] has.
//!
//! `(struct name (field ...) option ...)`, or `(struct name super (field ...) option ...)` for a
//! subtype of the struct type `super`, defines `struct:name` as the type, `name` as its
//! constructor, of all the fields, the supertype's first, `name?` as its predicate, an accessor
//! `name-field` for each field, and a mutator `set-name-field!` for each mutable one. A field
//! is its name, or `(name #:mutable)`. The options are `#:mutable`, which makes every field
//! mutable, `#:identity-eq?`, which makes a struct of the type `equal?` only to itself, as a
//! subtype of such a type's are too, where otherwise it's `equal?` to another of its type with
//! `equal?` fields, `#:constructor-name id` and `#:extra-constructor-name id`, which both define
//! `id` as a constructor too, and `#:transparent`, which every struct is.
//!
//! The constructor named as the type is stands for the type where a struct's name goes, in this
//! module or one that requires it: as a supertype, in a `match` pattern `(name pattern ...)`,
//! which matches a struct of the type whose fields match the patterns, and in `(struct-copy name
//! e [field value] ...)`, a new struct of the type with the fields of `e`'s value, which is
//! one, but for those given.
//!
//! Code that has a type, as `struct:name` is, can use it itself: `(struct-fields type)` lists its
//! fields' names, and `(make-struct type v ...)`, `(struct? v type)`, `(struct-ref s type k)` and
//! `(struct-set! s type k v)` make, tell, and read and set a field of a struct of it, field `k`
//! being the one whose name is `k`th in that list. `struct-set!` sets any field: a field that
//! isn't mutable is one the form defines no mutator for.
//!
//! What a form defines is made as [`ragwort_compiler::structs`] says, as native ragwort's is. A
//! form in a body makes a new type each time the body runs.

use ragwort_compiler::module::{Field, Inline, StructDef};
use ragwort_compiler::structs::{self, Declared, Member};
use ragwort_compiler::{Core, Place, Var};
use ragwort_types::gc::{OutOfMemory, Value};
use ragwort_types::pair::Pairs;
use ragwort_types::string::chars;
use ragwort_vm::Fault;

use crate::expand::{Binding, Expander};
use crate::tree::{Stx, View};
use crate::{ExpandError, ExpandErrorKind};

/// A struct form's parts: its fields, each with whether it's mutable, the names of its
/// constructors besides its own, and whether its structs are `equal?` only to themselves.
struct Form {
    name: Stx,
    parent: Option<Stx>,
    fields: Vec<(Stx, bool)>,
    constructors: Vec<Stx>,
    identity: bool,
}

/// What a struct form says of its type: its supertype, if it has one, all its fields, and what
/// it defines, each with its identifier: the type, then the constructor named for it, then the
/// rest.
struct Parts<'gc> {
    parent: Option<Info<'gc>>,
    fields: Vec<Field>,
    members: Vec<(Stx, Member)>,
}

/// Where a struct type is, to code that uses it.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Kind<'gc> {
    Constant(Value<'gc>),
    Local(Var),
}

impl<'gc> Kind<'gc> {
    pub(crate) fn core(self) -> Core<'gc> {
        match self {
            Kind::Constant(kind) => Core::Quote(kind),
            Kind::Local(var) => Core::Ref(Place::Local(var)),
        }
    }
}

/// A struct type, as the name of its constructor stands for it: its fields are all of them, its
/// supertype's first.
#[derive(Clone, Debug)]
pub(crate) struct Info<'gc> {
    pub(crate) kind: Kind<'gc>,
    /// The identifier of the local the type is in, if it's in one.
    holder: Option<Stx>,
    pub(crate) fields: Vec<Field>,
}

/// What a local that a struct form in a body defines is: the type, or a procedure of the type
/// in the given local, with what a call of it does.
pub(crate) enum Local {
    Type,
    Procedure(Inline, Var),
}

impl<'a, 'gc> Expander<'a, 'gc> {
    /// The name of the keyword `stx` is, if it's one.
    fn keyword_name(&self, stx: Stx) -> Option<String> {
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
                fields.push((spec, false));
                continue;
            }
            match *self.proper(spec)?.as_slice() {
                [id] if self.is_id(id) => fields.push((id, false)),
                [id, option] if self.is_id(id) && self.keyword_name(option).as_deref() == Some("mutable") => fields.push((id, true)),
                _ => return Err(self.error(bad, spec)),
            }
        }
        self.distinct(&fields.iter().map(|&(id, _)| id).collect::<Vec<_>>())?;
        let (mut constructors, mut identity) = (Vec::new(), false);
        while let Some(option) = rest.next() {
            match self.keyword_name(option).as_deref() {
                Some("mutable") => fields.iter_mut().for_each(|(_, mutable)| *mutable = true),
                Some("identity-eq?") => identity = true,
                Some("transparent") => {}
                Some("constructor-name" | "extra-constructor-name") => {
                    let Some(id) = rest.next().filter(|&id| self.is_id(id)) else { return Err(self.error(bad, option)) };
                    constructors.push(id);
                }
                _ => return Err(self.error(bad, option)),
            }
        }
        Ok(Form { name, parent, fields, constructors, identity })
    }

    /// The struct type `id` stands for, if it's the name of one's constructor.
    pub(crate) fn struct_info(&mut self, id: Stx) -> Result<Option<Info<'gc>>, ExpandError> {
        if !self.is_id(id) {
            return Ok(None);
        }
        let of = |def: &StructDef, kind: Value<'gc>| Info { kind: Kind::Constant(kind), holder: None, fields: def.fields.to_vec() };
        Ok(match self.resolve(id)? {
            Binding::Local(var) => self.struct_infos.get(&var).cloned(),
            Binding::Slot(slot) => self.builder.struct_def(slot).map(|(def, kind)| of(def, kind)),
            Binding::Import(import) => import.struct_def(self.mc).map(|(def, kind)| of(def, kind)),
            _ => None,
        })
    }

    /// What `form` says of its type.
    fn struct_parts(&mut self, form: &Form) -> Result<Parts<'gc>, ExpandError> {
        let parent = match form.parent {
            None => None,
            Some(id) => match self.struct_info(id)? {
                Some(parent) => Some(parent),
                None => return Err(self.error(ExpandErrorKind::BadSyntax, id)),
            },
        };
        let name = self.text(form.name).expect("an identifier");
        let mut fields = parent.as_ref().map_or(Vec::new(), |parent| parent.fields.clone());
        let inherited = fields.len();
        for &(id, mutable) in &form.fields {
            fields.push(Field { name: self.text(id).expect("an identifier").into(), mutable });
        }
        let Some(named) = structs::members(&name, &fields[inherited..], inherited) else { return Err(self.error(OutOfMemory, form.name)) };
        let mut members = Vec::with_capacity(named.len() + form.constructors.len());
        for (name, member) in named {
            members.push((if member == Member::Make { form.name } else { self.named_after(form.name, &name)? }, member));
            // The constructors of other names go after the one named for the type.
            if member == Member::Make {
                members.extend(form.constructors.iter().map(|&id| (id, Member::Make)));
            }
        }
        Ok(Parts { parent, fields, members })
    }

    /// The symbol of a struct form's name, and the list of its own fields' names, as its type
    /// is made of them.
    fn struct_names(&mut self, form: &Form) -> Result<(Value<'gc>, Value<'gc>), ExpandError> {
        let symbol = |this: &Self, id: Stx| this.tree.symbol(id).expect("an identifier").value(this.mc);
        let own: Vec<Value<'gc>> = form.fields.iter().map(|&(id, _)| symbol(self, id)).collect();
        Ok((symbol(self, form.name), Pairs::new(self.mc).list(&own)?))
    }

    /// Declares what `form`, a struct form that's the module's top-level form `index`, defines,
    /// and makes its type, which the module's code has as a constant.
    pub(crate) fn declare_struct(&mut self, form: Stx, index: u32) -> Result<Declared, ExpandError> {
        let parts = self.struct_form(form)?;
        let Parts { parent, fields, members } = self.struct_parts(&parts)?;
        let above = match parent.map(|parent| parent.kind) {
            None => Value::FALSE,
            Some(Kind::Constant(kind)) => kind,
            Some(Kind::Local(_)) => return Err(self.error(ExpandErrorKind::BadSyntax, form)),
        };
        let (name, own) = self.struct_names(&parts)?;
        let kind = structs::make_type(self.mc, name, above, own, parts.identity).map_err(|fault| match fault {
            Fault::OutOfMemory => self.error(OutOfMemory, form),
            _ => self.error(ExpandErrorKind::BadSyntax, form),
        })?;
        let mut slots = Vec::with_capacity(members.len());
        for (id, member) in members {
            slots.push((self.define_top(id, index)?, member));
        }
        Declared::new(&mut self.builder, kind, fields, slots).ok_or_else(|| self.error(OutOfMemory, form))
    }

    /// The code of a struct form at the top level, which defines each of its variables.
    pub(crate) fn lower_struct(&mut self, declared: Declared) -> Core<'gc> {
        let (_, kind) = self.builder.struct_def(declared.constructor()).expect("a declared struct");
        declared.define(kind, self)
    }

    /// Binds what `form`, a struct form in a body, defines, each to a local, and gives each
    /// identifier it binds with its local and its value. The type is made when the body runs.
    pub(crate) fn local_struct(&mut self, form: Stx) -> Result<Vec<(Stx, Var, Core<'gc>)>, ExpandError> {
        let parts = self.struct_form(form)?;
        let Parts { parent, fields, members } = self.struct_parts(&parts)?;
        let (name, own) = self.struct_names(&parts)?;
        let count = u32::try_from(fields.len()).map_err(|_| self.error(OutOfMemory, form))?;
        let above = parent.map_or(Core::Quote(Value::FALSE), |parent| parent.kind.core());
        let mut made = Vec::with_capacity(members.len());
        let mut holder = None;
        for (id, member) in members {
            let var = self.local(id)?;
            let (kind, holder) = *holder.get_or_insert((var, id));
            let value = match member {
                Member::Type => structs::type_maker(name, above.clone(), own, parts.identity),
                _ => structs::value(member, Core::Ref(Place::Local(kind)), count, self),
            };
            let local = match structs::inline(member, 0, count) {
                Some(inline) => Local::Procedure(inline, kind),
                None => Local::Type,
            };
            self.struct_locals.insert(var, local);
            // The first constructor is the one named for the type.
            if member == Member::Make && made.len() == 1 {
                self.struct_infos.insert(var, Info { kind: Kind::Local(kind), holder: Some(holder), fields: fields.clone() });
            }
            made.push((id, var, value));
        }
        Ok(made)
    }

    /// An expression for the type of `info`, at `at`.
    pub(crate) fn struct_type(&mut self, info: &Info<'gc>, at: Stx) -> Result<Stx, ExpandError> {
        match (info.kind, info.holder) {
            (Kind::Constant(kind), _) => {
                let kind = self.value(kind, at)?;
                self.quoted(kind, at)
            }
            (Kind::Local(_), holder) => Ok(holder.expect("a type in a local has its identifier")),
        }
    }

    /// `(struct-copy name e [field value] ...)`: `(let ((t e)) (let ((v value)) ... (make-struct
    /// type field ...)))`, each field its `v` or `(struct-ref t type k)`, which checks that `t`
    /// is of the type.
    pub(crate) fn struct_copy(&mut self, stx: Stx, name: Stx, e: Stx, updates: &[Stx]) -> Result<Stx, ExpandError> {
        let bad = ExpandErrorKind::BadSyntax;
        let Some(info) = self.struct_info(name)? else { return Err(self.error(bad, name)) };
        let (make, is, get) = ("make-struct", "struct?", "struct-ref");
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
                    self.build(stx, get, &[&[source, kind, k]])?
                }
            });
        }
        let mut body = self.build(stx, make, &[&[kind], &fields])?;
        // Nothing has read a field of the source, to find it's not of the type.
        if all_given {
            let zero = self.value(Value::fixnum(0).expect("zero is a fixnum"), stx)?;
            let (test, not_one) = (self.build(stx, is, &[&[source, kind]])?, self.build(stx, get, &[&[source, kind, zero]])?);
            body = self.build(stx, "if", &[&[test, body, not_one]])?;
        }
        for (temp, value) in binds.into_iter().rev() {
            body = self.with_temp(stx, temp, value, body)?;
        }
        self.with_temp(stx, source, e, body)
    }
}
