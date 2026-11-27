//! The static value type and its conversions.

use std::fmt;

use ragwort_types::gc::{self, ForeignRoot, Mutation, OutOfMemory};
use ragwort_types::num::{Nums, int};

use crate::handle::{Bytevector, Coroutine, External, Keyword, Number, Other, Pair, Procedure, String, Struct, Symbol, Table, Vector};

/// The error of a conversion to a value of the arena.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Error {
    /// The arena has no room for the value.
    OutOfMemory,
    /// The handle is of an object of another arena.
    Foreign,
}

impl From<OutOfMemory> for Error {
    fn from(_: OutOfMemory) -> Self {
        Self::OutOfMemory
    }
}

impl From<ForeignRoot> for Error {
    fn from(_: ForeignRoot) -> Self {
        Self::Foreign
    }
}

impl fmt::Display for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::OutOfMemory => formatter.write_str("out of memory"),
            Self::Foreign => formatter.write_str("the value belongs to another arena"),
        }
    }
}

impl std::error::Error for Error {}

/// A value with no lifetime.
///
/// A value that is not an object is held as plain Rust data. An object is held as a handle of its kind, which keeps the object alive.
/// [`Value::from_gc`] makes one inside a step, and [`Value::to_gc`] gives the arena's value back inside a later step.
///
/// Two values are equal if they are the same plain data, or handles of the same object.
#[derive(Clone, PartialEq, Debug)]
pub enum Value {
    /// `#t` or `#f`.
    Boolean(bool),
    /// The empty list.
    Null,
    /// `#nil`.
    Nil,
    /// `#none`.
    None,
    /// The value of an expression that has no useful value.
    Void,
    /// An integer that fits in an `i64`. A larger one is a [`Value::Number`].
    Integer(i64),
    /// A flonum.
    Float(f64),
    Char(char),
    String(String),
    Symbol(Symbol),
    Keyword(Keyword),
    /// A number that is neither a [`Value::Integer`] nor a [`Value::Float`]: a larger integer, a ratio or a complex number.
    Number(Number),
    Bytevector(Bytevector),
    Pair(Pair),
    Vector(Vector),
    Table(Table),
    Struct(Struct),
    Procedure(Procedure),
    Coroutine(Coroutine),
    External(External),
    /// A value of any other kind, such as a string cursor, a condition or a syntax object.
    Other(Other),
}

impl Value {
    /// Returns `value` as a static value. An object gets a handle, which can fail for lack of memory.
    pub fn from_gc<'gc>(mc: &Mutation<'gc>, value: gc::Value<'gc>) -> Result<Self, OutOfMemory> {
        if let Some(integer) = value.as_fixnum() {
            return Ok(Self::Integer(integer));
        }
        if let Some(float) = value.as_flonum(mc) {
            return Ok(Self::Float(float));
        }
        if let Some(plain) = Self::plain(value) {
            return Ok(plain);
        }
        if let Some(string) = String::of(mc, value)? {
            return Ok(Self::String(string));
        }
        if let Some(pair) = Pair::of(mc, value)? {
            return Ok(Self::Pair(pair));
        }
        if let Some(table) = Table::of(mc, value)? {
            return Ok(Self::Table(table));
        }
        if let Some(procedure) = Procedure::of(mc, value)? {
            return Ok(Self::Procedure(procedure));
        }
        if let Some(symbol) = Symbol::of(mc, value)? {
            return Ok(Self::Symbol(symbol));
        }
        if let Some(vector) = Vector::of(mc, value)? {
            return Ok(Self::Vector(vector));
        }
        if let Some(keyword) = Keyword::of(mc, value)? {
            return Ok(Self::Keyword(keyword));
        }
        let nums = Nums::new(mc);
        if let Some(integer) = nums.integer(value)
            && let Some(small) = int::to_i64(&nums, integer)
        {
            return Ok(Self::Integer(small));
        }
        if let Some(number) = Number::of(mc, value)? {
            return Ok(Self::Number(number));
        }
        if let Some(bytevector) = Bytevector::of(mc, value)? {
            return Ok(Self::Bytevector(bytevector));
        }
        if let Some(instance) = Struct::of(mc, value)? {
            return Ok(Self::Struct(instance));
        }
        if let Some(coroutine) = Coroutine::of(mc, value)? {
            return Ok(Self::Coroutine(coroutine));
        }
        if let Some(external) = External::of(mc, value)? {
            return Ok(Self::External(external));
        }
        Ok(Self::Other(Other::of(mc, value)?.expect("any value has a handle")))
    }

    /// Returns `value` as plain data, if it is one of the constants or a character.
    fn plain(value: gc::Value<'_>) -> Option<Self> {
        if value == gc::Value::TRUE {
            Some(Self::Boolean(true))
        } else if value == gc::Value::FALSE {
            Some(Self::Boolean(false))
        } else if value == gc::Value::NULL {
            Some(Self::Null)
        } else if value == gc::Value::NIL {
            Some(Self::Nil)
        } else if value == gc::Value::NONE {
            Some(Self::None)
        } else if value == gc::Value::VOID {
            Some(Self::Void)
        } else {
            value.as_char().map(Self::Char)
        }
    }

    /// Returns the value as a value of the arena. Fails if a handle is of an object of another arena. An integer or a flonum that does not
    /// fit in a value word is allocated, which can fail for lack of memory.
    pub fn to_gc<'gc>(&self, mc: &Mutation<'gc>) -> Result<gc::Value<'gc>, Error> {
        Ok(match self {
            Self::Boolean(flag) => {
                if *flag {
                    gc::Value::TRUE
                } else {
                    gc::Value::FALSE
                }
            }
            Self::Null => gc::Value::NULL,
            Self::Nil => gc::Value::NIL,
            Self::None => gc::Value::NONE,
            Self::Void => gc::Value::VOID,
            Self::Integer(integer) => match gc::Value::fixnum(*integer) {
                Some(value) => value,
                // The only failure of making an integer is the lack of memory.
                None => int::from_i64(&Nums::new(mc), *integer).map_err(|_| Error::OutOfMemory)?.value(),
            },
            Self::Float(float) => gc::Value::flonum(mc, *float)?,
            Self::Char(character) => gc::Value::char(*character),
            Self::String(string) => string.value(mc)?,
            Self::Symbol(symbol) => symbol.value(mc)?,
            Self::Keyword(keyword) => keyword.value(mc)?,
            Self::Number(number) => number.value(mc)?,
            Self::Bytevector(bytevector) => bytevector.value(mc)?,
            Self::Pair(pair) => pair.value(mc)?,
            Self::Vector(vector) => vector.value(mc)?,
            Self::Table(table) => table.value(mc)?,
            Self::Struct(instance) => instance.value(mc)?,
            Self::Procedure(procedure) => procedure.value(mc)?,
            Self::Coroutine(coroutine) => coroutine.value(mc)?,
            Self::External(external) => external.value(mc)?,
            Self::Other(other) => other.value(mc)?,
        })
    }

    /// Returns the name of the value's kind, for messages.
    pub fn type_name(&self) -> &'static str {
        match self {
            Self::Boolean(_) => "boolean",
            Self::Null => "empty list",
            Self::Nil => "nil",
            Self::None => "none",
            Self::Void => "void",
            Self::Integer(_) => "integer",
            Self::Float(_) => "float",
            Self::Char(_) => "character",
            Self::String(_) => "string",
            Self::Symbol(_) => "symbol",
            Self::Keyword(_) => "keyword",
            Self::Number(_) => "number",
            Self::Bytevector(_) => "bytevector",
            Self::Pair(_) => "pair",
            Self::Vector(_) => "vector",
            Self::Table(_) => "table",
            Self::Struct(_) => "struct",
            Self::Procedure(_) => "procedure",
            Self::Coroutine(_) => "coroutine",
            Self::External(_) => "external value",
            Self::Other(_) => "value",
        }
    }
}

/// Defines the conversions from the type of a variant to a [`Value`].
macro_rules! from {
    ($($variant:ident($from:ty),)*) => {$(
        impl From<$from> for Value {
            fn from(value: $from) -> Self {
                Self::$variant(value)
            }
        }
    )*};
}

from! {
    Boolean(bool),
    Integer(i64),
    Float(f64),
    Char(char),
    String(String),
    Symbol(Symbol),
    Keyword(Keyword),
    Number(Number),
    Bytevector(Bytevector),
    Pair(Pair),
    Vector(Vector),
    Table(Table),
    Struct(Struct),
    Procedure(Procedure),
    Coroutine(Coroutine),
    External(External),
    Other(Other),
}
