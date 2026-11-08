//! An [`Intrinsic`] computes a value from its arguments in place, inside a step: it never touches frames
//! or calls a procedure, so it can't be captured halfway or re-enter the VM. Anything that calls a
//! procedure or changes the continuation is a [`crate::Request`] instead.

use std::cmp::Ordering;

use ragwort_types::Error;
use ragwort_types::bytevector::{AnyBytevector, Bytevectors};
use ragwort_types::gc::{Frame, Mutation, ScratchVec, Value};
use ragwort_types::named;
use ragwort_types::num::{ComplexHost, ComplexView, Number, Nums, RationalHost, RationalView, RealHost, RealView, complex, int, real};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::string::{self, Strings};
use ragwort_types::symbol::{Keyword, Symbol, Symbols};
use ragwort_types::syntax::Syntax;
use ragwort_types::vector::{AnyVector, Vectors};

use crate::op::Fuel;
use crate::{Fault, coroutine, equal, prompts, syntax};
use crate::objects::{self, BoxFields, Condition, ConditionFields, KeywordProcedureFields, ModuleFields, MultiValue, MultiValueFields, Tag, TaskFields};

named! {
    #[repr(u16)]
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum Intrinsic {
        /// `+`: fixnums are added in place, anything else by the generic add.
        Add = "+",
        /// `(- z)` negates, `(- z1 z2 ...)` subtracts the rest from the first.
        Sub = "-",
        /// `*`: fixnums are multiplied in place, anything else by the generic multiply.
        Mul = "*",
        /// `(/ z)` is the reciprocal, `(/ z1 z2 ...)` divides the first by the rest. Fixnums that
        /// divide exactly stay in place; an exact zero divisor faults with
        /// [`NumError::DivideByZero`](ragwort_types::num::NumError::DivideByZero).
        Div = "/",
        /// `(= z1 z2 ...)`: whether the numbers are all the same value, whatever their
        /// exactness. NaN is `=` to nothing.
        NumEq = "=",
        /// `(< x1 x2 ...)`: whether the reals increase. Each argument is checked, whatever the
        /// answer; NaN makes it, and the others, `#f`.
        Lt = "<",
        /// `(> x1 x2 ...)`: whether the reals decrease.
        Gt = ">",
        /// `(<= x1 x2 ...)`: whether no real is less than the one before it.
        Le = "<=",
        /// `(>= x1 x2 ...)`: whether no real is more than the one before it.
        Ge = ">=",
        /// `(expt z w)`: `z` to the power `w`, exact when both are exact and `w` is an integer.
        /// An exact result is charged fuel for its size before it's computed.
        Expt = "expt",
        /// `(quotient n m)`: `n / m` truncated, of integers, exact or not.
        Quotient = "quotient",
        /// `(remainder n m)`: what `quotient` leaves, with `n`'s sign.
        Remainder = "remainder",
        /// `(modulo n m)`: `n` mod `m`, with `m`'s sign.
        Modulo = "modulo",
        /// (cons a d)
        Cons = "cons",
        /// (car lst)
        Car = "car",
        // `caar` to `cddddr`: the `car`s and `cdr`s their names spell, the last letter first.
        /// (cdr lst)
        Cdr = "cdr",
        Caar = "caar",
        Cadr = "cadr",
        Cdar = "cdar",
        Cddr = "cddr",
        Caaar = "caaar",
        Caadr = "caadr",
        Cadar = "cadar",
        Caddr = "caddr",
        Cdaar = "cdaar",
        Cdadr = "cdadr",
        Cddar = "cddar",
        Cdddr = "cdddr",
        Caaaar = "caaaar",
        Caaadr = "caaadr",
        Caadar = "caadar",
        Caaddr = "caaddr",
        Cadaar = "cadaar",
        Cadadr = "cadadr",
        Caddar = "caddar",
        Cadddr = "cadddr",
        Cdaaar = "cdaaar",
        Cdaadr = "cdaadr",
        Cdadar = "cdadar",
        Cdaddr = "cdaddr",
        Cddaar = "cddaar",
        Cddadr = "cddadr",
        Cdddar = "cdddar",
        Cddddr = "cddddr",
        /// `eq?`.
        Eq = "eq?",
        /// `eqv?`: `eq?`, or numbers of the same exactness and value.
        Eqv = "eqv?",
        /// `equal?`: `eqv?`, or strings, pairs, vectors or boxes with `equal?` contents. It ends on
        /// cyclic ones, and spends a unit of fuel for each 1024 values it compares, faulting with
        /// [`Fault::OutOfFuel`] as soon as there's none left.
        Equal = "equal?",
        /// `null?`.
        IsNull = "null?",
        /// `pair?`.
        IsPair = "pair?",
        /// `list?`: whether `x` is `()` or a chain of pairs ending in `()`, in constant time.
        IsList = "list?",
        /// `(length xs)`: the length of the proper list `xs`, in constant time.
        Length = "length",
        /// `(list-tail xs k)`.
        ListTail = "list-tail",
        /// `(list-ref xs k)`.
        ListRef = "list-ref",
        /// `(reverse xs)`.
        Reverse = "reverse",
        /// `(append list ... [obj])`.
        Append = "append",
        /// `(memq x xs)`.
        Memq = "memq",
        /// `(memv x xs)`.
        Memv = "memv",
        /// `(member x xs)`.
        Member = "member",
        /// `(assq x xs)`.
        Assq = "assq",
        /// `(assv x xs)`.
        Assv = "assv",
        /// `(assoc x xs)`.
        Assoc = "assoc",
        /// `box?`.
        IsBox = "box?",
        /// `not`: `#t` if `x` is `#f`, `#f` otherwise.
        Not = "not",
        /// `boolean?`.
        IsBoolean = "boolean?",
        /// `keyword?`: whether `x` is a keyword, `#:name`.
        IsKeyword = "keyword?",
        /// `symbol?`: whether `x` is a symbol.
        IsSymbol = "symbol?",
        /// `string?`: whether `x` is a string.
        IsString = "string?",
        /// `(string-length s)`: how many characters `s` has.
        StringLength = "string-length",
        /// `(string-append s ...)`: the strings' characters, in order, in a new string. Long
        /// ones are joined, not copied.
        StringAppend = "string-append",
        /// `(substring s start [end])`: the characters of `s` from `start` up to `end`, or its end.
        Substring = "substring",
        /// `(string-ref s k)`: the `k`th character of `s`, from 0.
        StringRef = "string-ref",
        /// `(string=? s1 s2 ...)`: whether the strings have the same characters. Each argument is
        /// checked, whatever the answer.
        StringEq = "string=?",
        /// `(string<? s1 s2 ...)`: whether the strings increase, by code point, a prefix first.
        StringLt = "string<?",
        /// `(string>? s1 s2 ...)`: whether the strings decrease.
        StringGt = "string>?",
        /// `(string<=? s1 s2 ...)`: whether no string is less than the one before it.
        StringLe = "string<=?",
        /// `(string>=? s1 s2 ...)`: whether no string is more than the one before it.
        StringGe = "string>=?",
        /// `(string->list s [start [end]])`: a list of the characters of `s`, or of that range.
        StringToList = "string->list",
        /// `(number->string z [radix])`: `z` written as the reader reads it, in radix 2, 8, 10
        /// or 16. Inexact numbers are exact in radixes but 10.
        NumberToString = "number->string",
        /// `(string-join strs [sep])`: the strings of list `strs`, `sep` between each two, `" "`
        /// if it's not given.
        StringJoin = "string-join",
        /// `char?`: whether `x` is a character.
        IsChar = "char?",
        /// `(char->integer c)`: `c`'s code point.
        CharToInteger = "char->integer",
        /// `(integer->char n)`: the character whose code point is `n`, which is a Unicode scalar
        /// value: up to `#x10FFFF`, and not a surrogate.
        IntegerToChar = "integer->char",
        /// `(char=? c1 c2 ...)`: whether the characters are the same. Each argument is checked,
        /// whatever the answer.
        CharEq = "char=?",
        /// `(char<? c1 c2 ...)`: whether the characters' code points increase.
        CharLt = "char<?",
        /// `(char>? c1 c2 ...)`: whether they decrease.
        CharGt = "char>?",
        /// `(char<=? c1 c2 ...)`: whether no code point is less than the one before it.
        CharLe = "char<=?",
        /// `(char>=? c1 c2 ...)`: whether no code point is more than the one before it.
        CharGe = "char>=?",
        /// `(%keyword-procedure plain core keywords required)`: a keyword procedure, as a `lambda`
        /// with keyword parameters makes. See [`crate::keyword`].
        MakeKeywordProcedure = "%keyword-procedure",
        /// `(procedure-keywords f)`: the keywords `f` requires and those it takes, as two sorted
        /// lists, both empty for a procedure without keyword parameters.
        ProcedureKeywords = "procedure-keywords",
        /// `(symbol->string s)`: the symbol's name.
        SymbolToString = "symbol->string",
        /// `(string->symbol s)`: the symbol named `s`, the one the reader reads for that name.
        StringToSymbol = "string->symbol",
        /// `(keyword->string k)`: the keyword's name, without its `#:`.
        KeywordToString = "keyword->string",
        /// `(string->keyword s)`: the keyword named `s`, the one the reader reads as `#:s`.
        StringToKeyword = "string->keyword",
        /// `(void x ...)`: void, whatever it's given.
        Void = "void",
        /// `bytevector?`.
        IsBytevector = "bytevector?",
        /// `(make-bytevector k [byte])`: a mutable bytevector of `k` copies of `byte`, or of 0.
        MakeBytevector = "make-bytevector",
        /// `(bytevector-length bv)`.
        BytevectorLength = "bytevector-length",
        /// `(bytevector-u8-ref bv k)`.
        BytevectorRef = "bytevector-u8-ref",
        /// `(bytevector-u8-set! bv k byte)` of a mutable bytevector, returning void.
        BytevectorSet = "bytevector-u8-set!",
        /// `vector?`.
        IsVector = "vector?",
        /// `(make-vector k [fill])`: a mutable vector of `k` copies of `fill`, or of 0.
        MakeVector = "make-vector",
        /// `(vector x ...)`: a mutable vector of the `x`s.
        MakeVectorOf = "vector",
        /// `(vector-length v)`.
        VectorLength = "vector-length",
        /// `(vector-ref v k)`.
        VectorRef = "vector-ref",
        /// `(vector-set! v k x)` of a mutable vector, returning void.
        VectorSet = "vector-set!",
        /// `(vector->list v)`: a new list of `v`'s elements.
        VectorToList = "vector->list",
        /// `(list->vector xs)`: a mutable vector of the proper list `xs`'s elements.
        ListToVector = "list->vector",
        /// `(box x)`: create a new box holding `x` returning the newly created box
        MakeBox = "box",
        /// `(unbox b)`: returns the contents of the box `b`
        Unbox = "unbox",
        /// `(set-box! b x)`: sets the contents of the box `b` to `x` returning void.
        SetBox = "set-box!",
        /// `(make-winder before after)`: what `dynamic-wind` puts in the task's winders.
        MakeWinder = "make-winder",
        /// `(default-continuation-prompt-tag)`.
        DefaultPromptTag = "default-continuation-prompt-tag",
        /// `(make-continuation-prompt-tag [name])`.
        MakePromptTag = "make-continuation-prompt-tag",
        /// `(values x ...)`: `x` alone, or any other number of values as a [`MultiValue`].
        Values = "values",
        /// `(values? x)`: whether `x` is a [`MultiValue`].
        IsValues = "values?",
        /// `(values-length mv)`.
        ValuesLength = "values-length",
        /// `(values-ref mv k)`.
        ValuesRef = "values-ref",
        /// `(module-ref m k)`: variable `k` of the [`objects::Module`] `m`, or
        /// [`Fault::Unbound`] if it isn't defined, as code of another module reads one it
        /// exports that it sets.
        ModuleRef = "module-ref",
        /// `(make-error message irritant ...)`: a `Condition` of [`Fault::Error`], which the
        /// prelude's `error` raises.
        MakeError = "make-error",
        /// `(make-syntax-error message form subform ...)`: a condition of kind `syntax`, its
        /// irritants the malformed `form` and the `subform`s of it that are.
        MakeSyntaxError = "make-syntax-error",
        /// `procedure?`: whether `x` is a [`objects::Closure`] or [`objects::Continuation`].
        IsProcedure = "procedure?",
        /// `continuation?`: whether `x` is a [`objects::Continuation`], composable or not.
        IsContinuation = "continuation?",
        /// `(make-coroutine f)`: a pending coroutine that the first `co/resume` of it starts by
        /// calling the procedure `f`.
        MakeCoroutine = "make-coroutine",
        /// `coroutine?`.
        IsCoroutine = "coroutine?",
        /// `(coroutine-state co)`: 0 if `co` is pending, 1 running, 2 finished and 3 failed.
        CoroutineState = "coroutine-state",
        /// `error-object?`: whether `x` is a `Condition`, as `make-error` and VM faults make.
        IsErrorObject = "error-object?",
        /// `(error-object-message c)`: what `error` was given, or for a VM fault, its kind in
        /// words.
        ErrorObjectMessage = "error-object-message",
        /// `(error-object-irritants c)`.
        ErrorObjectIrritants = "error-object-irritants",
        /// `(error-object-kind c)`: which of [`Fault::KINDS`] the condition is, as a fixnum.
        ErrorObjectKind = "error-object-kind",
        /// `syntax?`.
        IsSyntax = "syntax?",
        /// `identifier?`: whether `x` is the syntax of a symbol.
        IsIdentifier = "identifier?",
        /// `(syntax-e stx)`: what `stx` wraps, a symbol, a list or vector of syntax, or a
        /// literal.
        SyntaxE = "syntax-e",
        /// `(syntax->datum stx)`: the datum `stx` stands for, with all its syntax unwrapped.
        SyntaxToDatum = "syntax->datum",
        /// `(datum->syntax context datum)`: `datum` as syntax, with the scopes and span of the
        /// syntax `context`, or none if it's `#f`. What's syntax already in it stays as it is. Its
        /// identifiers named as `context` is refer to what it does.
        DatumToSyntax = "datum->syntax",
        /// `(bound-identifier=? a b)`: whether a binding of the identifier `a` would bind `b`:
        /// they have the same name and scopes.
        BoundIdentifierEq = "bound-identifier=?",
        /// `(free-identifier=? a b)`: whether the identifiers `a` and `b` refer to the same
        /// binding, as the expander found it when it made them. Identifiers it didn't make, such as
        /// temporaries, are the same only as each other, by name.
        FreeIdentifierEq = "free-identifier=?",
        /// `(generate-temporaries list name)`: an identifier for each element of `list`, of
        /// syntax or not, each in a new scope of its own, so it's apart from every other. It's
        /// named as the element is if that's an identifier, or else `name`.
        GenerateTemporaries = "generate-temporaries",
        /// `(syntax-match pattern input)`: a vector of what the variables of the
        /// [`SyntaxPattern`](crate::objects::SyntaxPattern) matched in `input`, or `#f`.
        SyntaxMatch = "syntax-match",
        /// `(syntax-build template value ...)`: the syntax the
        /// [`SyntaxTemplate`](crate::objects::SyntaxTemplate) makes of what its pattern variables
        /// matched.
        SyntaxBuild = "syntax-build",
    }
}

impl Intrinsic {
    /// How many arguments it takes, or `None` for any number.
    pub fn arity(self) -> Option<u8> {
        match self {
            Intrinsic::Add | Intrinsic::Sub | Intrinsic::Mul | Intrinsic::Div | Intrinsic::Append => None,
            Intrinsic::NumEq | Intrinsic::Lt | Intrinsic::Gt | Intrinsic::Le | Intrinsic::Ge => None,
            Intrinsic::MakePromptTag | Intrinsic::Values | Intrinsic::MakeError | Intrinsic::MakeSyntaxError | Intrinsic::Void | Intrinsic::MakeBytevector | Intrinsic::SyntaxBuild => None,
            Intrinsic::MakeVector | Intrinsic::MakeVectorOf => None,
            Intrinsic::IsVector | Intrinsic::VectorLength | Intrinsic::VectorToList | Intrinsic::ListToVector => Some(1),
            Intrinsic::VectorRef => Some(2),
            Intrinsic::VectorSet => Some(3),
            Intrinsic::DefaultPromptTag => Some(0),
            Intrinsic::IsErrorObject => Some(1),
            Intrinsic::ErrorObjectMessage | Intrinsic::ErrorObjectIrritants | Intrinsic::ErrorObjectKind => Some(1),
            Intrinsic::IsBytevector | Intrinsic::BytevectorLength | Intrinsic::IsProcedure | Intrinsic::IsContinuation => Some(1),
            Intrinsic::MakeCoroutine | Intrinsic::IsCoroutine | Intrinsic::CoroutineState => Some(1),
            Intrinsic::Car | Intrinsic::Cdr | Intrinsic::IsNull | Intrinsic::IsPair | Intrinsic::IsList | Intrinsic::Length | Intrinsic::Reverse | Intrinsic::IsBox | Intrinsic::MakeBox | Intrinsic::Unbox => Some(1),
            Intrinsic::IsValues | Intrinsic::ValuesLength | Intrinsic::Not | Intrinsic::IsBoolean | Intrinsic::IsKeyword => Some(1),
            Intrinsic::KeywordToString | Intrinsic::StringToKeyword | Intrinsic::IsSymbol => Some(1),
            Intrinsic::SymbolToString | Intrinsic::StringToSymbol => Some(1),
            Intrinsic::Expt | Intrinsic::Quotient | Intrinsic::Remainder | Intrinsic::Modulo => Some(2),
            Intrinsic::IsString | Intrinsic::StringLength => Some(1),
            Intrinsic::StringAppend | Intrinsic::Substring | Intrinsic::StringToList | Intrinsic::NumberToString => None,
            Intrinsic::StringEq | Intrinsic::StringLt | Intrinsic::StringGt | Intrinsic::StringLe | Intrinsic::StringGe => None,
            Intrinsic::StringRef => Some(2),
            Intrinsic::StringJoin => None,
            Intrinsic::MakeKeywordProcedure => Some(4),
            Intrinsic::ProcedureKeywords => Some(1),
            Intrinsic::IsChar | Intrinsic::CharToInteger | Intrinsic::IntegerToChar => Some(1),
            Intrinsic::CharEq | Intrinsic::CharLt | Intrinsic::CharGt | Intrinsic::CharLe | Intrinsic::CharGe => None,
            Intrinsic::IsSyntax | Intrinsic::IsIdentifier | Intrinsic::SyntaxE | Intrinsic::SyntaxToDatum => Some(1),
            Intrinsic::DatumToSyntax | Intrinsic::BoundIdentifierEq | Intrinsic::FreeIdentifierEq | Intrinsic::GenerateTemporaries | Intrinsic::SyntaxMatch => Some(2),
            Intrinsic::Caar | Intrinsic::Cadr | Intrinsic::Cdar | Intrinsic::Cddr | Intrinsic::Caaar | Intrinsic::Caadr | Intrinsic::Cadar | Intrinsic::Caddr | Intrinsic::Cdaar | Intrinsic::Cdadr | Intrinsic::Cddar | Intrinsic::Cdddr | Intrinsic::Caaaar | Intrinsic::Caaadr | Intrinsic::Caadar | Intrinsic::Caaddr | Intrinsic::Cadaar | Intrinsic::Cadadr | Intrinsic::Caddar | Intrinsic::Cadddr | Intrinsic::Cdaaar | Intrinsic::Cdaadr | Intrinsic::Cdadar | Intrinsic::Cdaddr | Intrinsic::Cddaar | Intrinsic::Cddadr | Intrinsic::Cdddar | Intrinsic::Cddddr => Some(1),
            Intrinsic::BytevectorRef | Intrinsic::ListTail | Intrinsic::ListRef | Intrinsic::Memq | Intrinsic::Memv | Intrinsic::Member | Intrinsic::Assq | Intrinsic::Assv | Intrinsic::Assoc => Some(2),
            Intrinsic::BytevectorSet => Some(3),
            Intrinsic::Cons | Intrinsic::Eq | Intrinsic::Eqv | Intrinsic::Equal | Intrinsic::SetBox | Intrinsic::ValuesRef | Intrinsic::MakeWinder | Intrinsic::ModuleRef => Some(2),
        }
    }

    /// Whether a call on constant arguments has no side effects, reads no mutable state, and
    /// allocates no fresh identity-bearing objects, so a compiler can evaluate it at compile time
    /// via [`Intrinsic::run`].
    pub const fn is_pure_foldable(self) -> bool {
        use Intrinsic::*;
        matches!(
            self,
            Add | Sub
                | Mul
                | Div
                | NumEq
                | Lt
                | Gt
                | Le
                | Ge
                | Expt
                | Quotient
                | Remainder
                | Modulo
                | StringLength
                | StringRef
                | StringEq
                | StringLt
                | StringGt
                | StringLe
                | StringGe
                | CharToInteger
                | IntegerToChar
                | CharEq
                | CharLt
                | CharGt
                | CharLe
                | CharGe
                | Car
                | Cdr
                | Caar
                | Cadr
                | Cdar
                | Cddr
                | Caaar
                | Caadr
                | Cadar
                | Caddr
                | Cdaar
                | Cdadr
                | Cddar
                | Cdddr
                | Caaaar
                | Caaadr
                | Caadar
                | Caaddr
                | Cadaar
                | Cadadr
                | Caddar
                | Cadddr
                | Cdaaar
                | Cdaadr
                | Cdadar
                | Cdaddr
                | Cddaar
                | Cddadr
                | Cdddar
                | Cddddr
                | Eq
                | Eqv
                | Equal
                | IsNull
                | IsPair
                | IsList
                | Length
                | ListTail
                | ListRef
                | Memq
                | Memv
                | Member
                | Assq
                | Assv
                | Assoc
                | IsBox
                | Not
                | IsBoolean
                | IsKeyword
                | IsSymbol
                | IsString
                | IsChar
                | Void
                | IsBytevector
                | BytevectorLength
                | BytevectorRef
                | IsVector
                | VectorLength
                | VectorRef
                | DefaultPromptTag
                | IsValues
                | ValuesLength
                | ValuesRef
                | IsProcedure
                | IsContinuation
                | IsCoroutine
                | IsErrorObject
                | IsSyntax
                | IsIdentifier
        )
    }

    /// Whether a direct call with valid arity cannot fault and has no side effects, so it can be
    /// dropped in an effect context once its arguments have been evaluated for their effects.
    pub const fn is_discardable(self) -> bool {
        use Intrinsic::*;
        matches!(
            self,
            Cons | MakeBox
                | MakeWinder
                | Eq
                | Eqv
                | IsNull
                | IsPair
                | IsList
                | IsBox
                | Not
                | IsBoolean
                | IsKeyword
                | IsSymbol
                | IsString
                | IsChar
                | Void
                | IsBytevector
                | IsVector
                | MakeVectorOf
                | DefaultPromptTag
                | Values
                | IsValues
                | IsProcedure
                | IsContinuation
                | IsCoroutine
                | IsErrorObject
                | IsSyntax
                | IsIdentifier
        )
    }

    /// Whether `self` is a 1-argument type predicate.
    pub const fn is_type_predicate(self) -> bool {
        use Intrinsic::*;
        matches!(
            self,
            IsNull
                | IsPair
                | IsBoolean
                | IsKeyword
                | IsSymbol
                | IsString
                | IsChar
                | IsBox
                | IsBytevector
                | IsVector
                | IsList
                | IsValues
                | IsProcedure
                | IsContinuation
                | IsCoroutine
                | IsErrorObject
        )
    }

    /// Whether no value can satisfy both `self` and `other`.
    pub fn is_disjoint_predicate(self, other: Self) -> bool {
        use Intrinsic::*;
        if self == other {
            return false;
        }
        !matches!(
            (self, other),
            (IsList, IsNull | IsPair)
                | (IsNull | IsPair, IsList)
                | (IsProcedure, IsContinuation)
                | (IsContinuation, IsProcedure)
        )
    }

    /// Whether any normal return value of `self` is guaranteed not to be `#f`.
    pub const fn is_always_truthy(self) -> bool {
        use Intrinsic::*;
        matches!(
            self,
            Add | Sub
                | Mul
                | Div
                | Expt
                | Quotient
                | Remainder
                | Modulo
                | StringLength
                | StringAppend
                | Substring
                | StringRef
                | StringToList
                | NumberToString
                | StringJoin
                | CharToInteger
                | IntegerToChar
                | Cons
                | Length
                | Reverse
                | Void
                | MakeBytevector
                | BytevectorLength
                | BytevectorRef
                | MakeVector
                | MakeVectorOf
                | VectorLength
                | VectorSet
                | VectorToList
                | ListToVector
                | MakeBox
                | MakeWinder
                | DefaultPromptTag
                | MakePromptTag
                | ValuesLength
                | BytevectorSet
                | SetBox
                | MakeError
                | MakeSyntaxError
                | MakeCoroutine
                | CoroutineState
                | ErrorObjectMessage
                | ErrorObjectIrritants
                | ErrorObjectKind
        )
    }

    /// Whether a 2-argument call of `self` is commutative (`f(a, b) == f(b, a)`).
    pub const fn is_commutative_binary(self) -> bool {
        use Intrinsic::*;
        matches!(self, Add | Mul | Eq | Eqv | Equal)
    }

    /// Decomposes `car`..`cddddr` into `(first_is_car, remaining_cxr)`.
    ///
    /// For instance, `Cadr` (`(car (cdr x))`) returns `Some((false, Some(Car)))`: take `cdr`
    /// first (`false`), then apply `Car`.
    pub const fn cxr_step(self) -> Option<(bool, Option<Intrinsic>)> {
        use Intrinsic::*;
        Some(match self {
            Car => (true, None),
            Cdr => (false, None),
            Caar => (true, Some(Car)),
            Cadr => (false, Some(Car)),
            Cdar => (true, Some(Cdr)),
            Cddr => (false, Some(Cdr)),
            Caaar => (true, Some(Caar)),
            Caadr => (false, Some(Caar)),
            Cadar => (true, Some(Cadr)),
            Caddr => (false, Some(Cadr)),
            Cdaar => (true, Some(Cdar)),
            Cdadr => (false, Some(Cdar)),
            Cddar => (true, Some(Cddr)),
            Cdddr => (false, Some(Cddr)),
            Caaaar => (true, Some(Caaar)),
            Caaadr => (false, Some(Caaar)),
            Caadar => (true, Some(Caadr)),
            Caaddr => (false, Some(Caadr)),
            Cadaar => (true, Some(Cadar)),
            Cadadr => (false, Some(Cadar)),
            Caddar => (true, Some(Caddr)),
            Cadddr => (false, Some(Caddr)),
            Cdaaar => (true, Some(Cdaar)),
            Cdaadr => (false, Some(Cdaar)),
            Cdadar => (true, Some(Cdadr)),
            Cdaddr => (false, Some(Cdadr)),
            Cddaar => (true, Some(Cddar)),
            Cddadr => (false, Some(Cddar)),
            Cdddar => (true, Some(Cdddr)),
            Cddddr => (false, Some(Cdddr)),
            _ => return None,
        })
    }

    /// Runs it on `args`, as the VM does on registers, but without a frame: for a compiler folding
    /// a call of constants, for one. Whether a call can be folded, as one that makes a new box
    /// or sets one can't, is the caller's to know.
    #[inline]
    pub fn run<'gc>(self, mc: &Mutation<'gc>, args: &[Value<'gc>], fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        if self.arity().is_some_and(|arity| usize::from(arity) != args.len()) {
            return Err(Fault::Arity);
        }
        self.apply(mc, |i| args[i], args.len(), fuel)
    }

    /// Runs it on the `args` registers from `base`, which the caller has checked are in the
    /// frame and as many as it takes, spending `fuel` on what does a lot of work.
    #[inline(always)]
    pub(crate) fn exec<'gc>(self, mc: &Mutation<'gc>, frame: Frame<'_, 'gc>, base: u8, args: u8, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        self.apply(mc, |i| frame.get(base + i as u8), usize::from(args), fuel)
    }

    /// Runs a 1-argument intrinsic on register `a`, which the caller has checked it takes.
    #[inline(always)]
    pub(crate) fn exec1<'gc>(self, mc: &Mutation<'gc>, frame: Frame<'_, 'gc>, a: u8, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        self.apply(mc, |_| frame.get(a), 1, fuel)
    }

    /// Runs a 2-argument intrinsic on registers `(a, b)`, which the caller has checked it takes.
    #[inline(always)]
    pub(crate) fn exec2<'gc>(self, mc: &Mutation<'gc>, frame: Frame<'_, 'gc>, a: u8, b: u8, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        self.apply(mc, |i| frame.get(if i == 0 { a } else { b }), 2, fuel)
    }

    /// Runs a 3-argument intrinsic on registers `(a, b, c)`, which the caller has checked it takes.
    #[inline(always)]
    pub(crate) fn exec3<'gc>(self, mc: &Mutation<'gc>, frame: Frame<'_, 'gc>, a: u8, b: u8, c: u8, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        self.apply(mc, |i| frame.get([a, b, c][i]), 3, fuel)
    }

    /// Runs it on the `args` values `arg` reads, as many as it takes.
    #[inline(always)]
    fn apply<'gc>(self, mc: &Mutation<'gc>, arg: impl Fn(usize) -> Value<'gc>, args: usize, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        let boolean = |b: bool| if b { Value::TRUE } else { Value::FALSE };
        Ok(match self {
            Intrinsic::Add => arith(mc, fuel, fixnum(0), (0..args).map(&arg), Value::fixnum_add, |h, a, b| complex::add(h, a, b))?,
            Intrinsic::Mul => arith(mc, fuel, fixnum(1), (0..args).map(&arg), Value::fixnum_mul, |h, a, b| complex::mul(h, a, b))?,
            Intrinsic::Sub | Intrinsic::Div if args == 0 => return Err(Fault::Arity),
            Intrinsic::Sub => {
                let (first, rest) = if args == 1 { (fixnum(0), 0) } else { (arg(0), 1) };
                arith(mc, fuel, first, (rest..args).map(&arg), Value::fixnum_sub, |h, a, b| complex::sub(h, a, b))?
            }
            Intrinsic::Div => {
                let (first, rest) = if args == 1 { (fixnum(1), 0) } else { (arg(0), 1) };
                arith(mc, fuel, first, (rest..args).map(&arg), fixnum_div, |h, a, b| complex::div(h, a, b))?
            }
            Intrinsic::NumEq | Intrinsic::Lt | Intrinsic::Gt | Intrinsic::Le | Intrinsic::Ge if args == 0 => return Err(Fault::Arity),
            Intrinsic::NumEq | Intrinsic::Lt | Intrinsic::Gt | Intrinsic::Le | Intrinsic::Ge => boolean(compare(mc, self, (0..args).map(&arg))?),
            Intrinsic::Cons => made(mc, fuel, Pairs::new(mc).cons(arg(0), arg(1))?.value(mc)),
            Intrinsic::Car => car(mc, arg(0))?,
            Intrinsic::Cdr => cdr(mc, arg(0))?,
            Intrinsic::Caar => car(mc, car(mc, arg(0))?)?,
            Intrinsic::Cadr => car(mc, cdr(mc, arg(0))?)?,
            Intrinsic::Cdar => cdr(mc, car(mc, arg(0))?)?,
            Intrinsic::Cddr => cdr(mc, cdr(mc, arg(0))?)?,
            Intrinsic::Caaar => car(mc, car(mc, car(mc, arg(0))?)?)?,
            Intrinsic::Caadr => car(mc, car(mc, cdr(mc, arg(0))?)?)?,
            Intrinsic::Cadar => car(mc, cdr(mc, car(mc, arg(0))?)?)?,
            Intrinsic::Caddr => car(mc, cdr(mc, cdr(mc, arg(0))?)?)?,
            Intrinsic::Cdaar => cdr(mc, car(mc, car(mc, arg(0))?)?)?,
            Intrinsic::Cdadr => cdr(mc, car(mc, cdr(mc, arg(0))?)?)?,
            Intrinsic::Cddar => cdr(mc, cdr(mc, car(mc, arg(0))?)?)?,
            Intrinsic::Cdddr => cdr(mc, cdr(mc, cdr(mc, arg(0))?)?)?,
            Intrinsic::Caaaar => car(mc, car(mc, car(mc, car(mc, arg(0))?)?)?)?,
            Intrinsic::Caaadr => car(mc, car(mc, car(mc, cdr(mc, arg(0))?)?)?)?,
            Intrinsic::Caadar => car(mc, car(mc, cdr(mc, car(mc, arg(0))?)?)?)?,
            Intrinsic::Caaddr => car(mc, car(mc, cdr(mc, cdr(mc, arg(0))?)?)?)?,
            Intrinsic::Cadaar => car(mc, cdr(mc, car(mc, car(mc, arg(0))?)?)?)?,
            Intrinsic::Cadadr => car(mc, cdr(mc, car(mc, cdr(mc, arg(0))?)?)?)?,
            Intrinsic::Caddar => car(mc, cdr(mc, cdr(mc, car(mc, arg(0))?)?)?)?,
            Intrinsic::Cadddr => car(mc, cdr(mc, cdr(mc, cdr(mc, arg(0))?)?)?)?,
            Intrinsic::Cdaaar => cdr(mc, car(mc, car(mc, car(mc, arg(0))?)?)?)?,
            Intrinsic::Cdaadr => cdr(mc, car(mc, car(mc, cdr(mc, arg(0))?)?)?)?,
            Intrinsic::Cdadar => cdr(mc, car(mc, cdr(mc, car(mc, arg(0))?)?)?)?,
            Intrinsic::Cdaddr => cdr(mc, car(mc, cdr(mc, cdr(mc, arg(0))?)?)?)?,
            Intrinsic::Cddaar => cdr(mc, cdr(mc, car(mc, car(mc, arg(0))?)?)?)?,
            Intrinsic::Cddadr => cdr(mc, cdr(mc, car(mc, cdr(mc, arg(0))?)?)?)?,
            Intrinsic::Cdddar => cdr(mc, cdr(mc, cdr(mc, car(mc, arg(0))?)?)?)?,
            Intrinsic::Cddddr => cdr(mc, cdr(mc, cdr(mc, cdr(mc, arg(0))?)?)?)?,
            Intrinsic::Eq => boolean(arg(0) == arg(1)),
            Intrinsic::Eqv => boolean(equal::eqv(mc, arg(0), arg(1))),
            Intrinsic::Equal => {
                let most = fuel.left().saturating_add(1).saturating_mul(equal::PER_FUEL) - 1;
                let (same, compared) = equal::equal(mc, arg(0), arg(1), most)?;
                fuel.spend(compared / equal::PER_FUEL)?;
                boolean(same)
            }
            Intrinsic::IsNull => boolean(arg(0) == Value::NIL),
            Intrinsic::IsPair => boolean(Pair::of(arg(0)).is_some()),
            Intrinsic::IsList => boolean(Pairs::new(mc).is_list(arg(0))),
            Intrinsic::Length => {
                let len = Pairs::new(mc).list_len(arg(0)).ok_or(Fault::WrongType)?;
                i64::try_from(len).ok().and_then(Value::fixnum).ok_or(Fault::OutOfRange)?
            }
            Intrinsic::ListTail => list_tail(mc, arg(0), index(arg(1))?, false, fuel)?,
            Intrinsic::ListRef => {
                let tail = list_tail(mc, arg(0), index(arg(1))?, true, fuel)?;
                Pair::of(tail).ok_or(Fault::WrongType)?.head(mc)
            }
            Intrinsic::Reverse => reverse(mc, arg(0), fuel)?,
            Intrinsic::Append => append(mc, (0..args).map(arg), fuel)?,
            Intrinsic::Memq | Intrinsic::Memv | Intrinsic::Member | Intrinsic::Assq | Intrinsic::Assv | Intrinsic::Assoc => {
                find(mc, self, arg(0), arg(1), fuel)?
            }
            Intrinsic::IsBox => boolean(arg(0).downcast::<objects::Box>(mc).is_some()),
            Intrinsic::Not => boolean(arg(0) == Value::FALSE),
            Intrinsic::IsBoolean => boolean(arg(0) == Value::TRUE || arg(0) == Value::FALSE),
            Intrinsic::IsKeyword => boolean(Keyword::of(arg(0)).is_some()),
            Intrinsic::IsSymbol => boolean(Symbol::of(arg(0)).is_some()),
            Intrinsic::IsString => boolean(Strings::new(mc).string(arg(0)).is_some()),
            Intrinsic::StringLength => {
                let strings = Strings::new(mc);
                fixnum(string::len(&strings, strings.string(arg(0)).ok_or(Fault::WrongType)?) as i64)
            }
            Intrinsic::StringAppend => string_append(mc, (0..args).map(arg), fuel)?,
            Intrinsic::Substring | Intrinsic::StringToList if !(1..=3).contains(&args) || self == Intrinsic::Substring && args == 1 => {
                return Err(Fault::Arity);
            }
            Intrinsic::Substring | Intrinsic::StringToList => {
                let strings = Strings::new(mc);
                let s = strings.string(arg(0)).ok_or(Fault::WrongType)?;
                let start = if args > 1 { index(arg(1))? } else { 0 };
                let end = if args > 2 { index(arg(2))? } else { string::len(&strings, s) };
                let part = if (start, end) == (0, string::len(&strings, s)) { s } else { string::substring(&strings, s, start, end)? };
                if self == Intrinsic::Substring {
                    made(mc, fuel, part.value())
                } else {
                    fuel.spend((end - start) as u64 / equal::PER_FUEL)?;
                    let mut chars = ScratchVec::new(mc);
                    for c in string::chars(&strings, part) {
                        chars.push(Value::char(c))?;
                    }
                    made(mc, fuel, Pairs::new(mc).list(&chars)?)
                }
            }
            Intrinsic::StringRef => {
                let strings = Strings::new(mc);
                Value::char(string::char_at(&strings, strings.string(arg(0)).ok_or(Fault::WrongType)?, index(arg(1))?)?)
            }
            Intrinsic::StringEq | Intrinsic::StringLt | Intrinsic::StringGt | Intrinsic::StringLe | Intrinsic::StringGe if args == 0 => {
                return Err(Fault::Arity);
            }
            Intrinsic::StringEq | Intrinsic::StringLt | Intrinsic::StringGt | Intrinsic::StringLe | Intrinsic::StringGe => {
                boolean(compare_strings(mc, self, (0..args).map(&arg))?)
            }
            Intrinsic::StringJoin if !(1..=2).contains(&args) => return Err(Fault::Arity),
            Intrinsic::StringJoin => string_join(mc, arg(0), (args == 2).then(|| arg(1)), fuel)?,
            Intrinsic::IsChar => boolean(arg(0).as_char().is_some()),
            Intrinsic::CharToInteger => fixnum(i64::from(u32::from(arg(0).as_char().ok_or(Fault::WrongType)?))),
            Intrinsic::IntegerToChar => {
                let n = arg(0).as_fixnum().ok_or(Fault::WrongType)?;
                Value::char(u32::try_from(n).ok().and_then(char::from_u32).ok_or(Fault::OutOfRange)?)
            }
            Intrinsic::CharEq | Intrinsic::CharLt | Intrinsic::CharGt | Intrinsic::CharLe | Intrinsic::CharGe if args == 0 => {
                return Err(Fault::Arity);
            }
            Intrinsic::CharEq | Intrinsic::CharLt | Intrinsic::CharGt | Intrinsic::CharLe | Intrinsic::CharGe => {
                boolean(compare_chars(self, (0..args).map(&arg))?)
            }
            Intrinsic::NumberToString if !(1..=2).contains(&args) => return Err(Fault::Arity),
            Intrinsic::NumberToString => {
                let h = Nums::new(mc);
                let z = h.number(arg(0)).ok_or(Fault::WrongType)?;
                let radix = if args == 2 { arg(1).as_fixnum().ok_or(Fault::WrongType)? } else { 10 };
                let radix = [2, 8, 10, 16].into_iter().find(|&r| r == radix).ok_or(Fault::OutOfRange)? as u32;
                if let Some(n) = arg(0).as_fixnum() {
                    return Ok(made(mc, fuel, fixnum_to_string(mc, n, radix)?));
                }
                // Writing a bignum takes about its digits squared.
                let words = exact_bits(&h, z) / 64;
                fuel.spend(words.saturating_mul(words) / equal::PER_FUEL)?;
                let text = complex::to_string(&h, z, radix)?;
                made(mc, fuel, string::from_str(&Strings::new(mc), &text)?.value())
            }
            Intrinsic::Quotient | Intrinsic::Remainder | Intrinsic::Modulo => divide(mc, fuel, self, arg(0), arg(1))?,
            Intrinsic::SymbolToString => Symbol::of(arg(0)).ok_or(Fault::WrongType)?.name(mc).value(),
            Intrinsic::StringToSymbol => {
                let strings = Strings::new(mc);
                let name = strings.string(arg(0)).ok_or(Fault::WrongType)?;
                made(mc, fuel, Symbols::of_arena(mc)?.intern(&strings, name)?.value(mc))
            }
            Intrinsic::Expt => {
                let h = Nums::new(mc);
                let (z, w) = (h.number(arg(0)).ok_or(Fault::WrongType)?, h.number(arg(1)).ok_or(Fault::WrongType)?);
                charge_power(mc, &h, fuel, z, w)?;
                made(mc, fuel, complex::expt(&h, z, w)?.value())
            }
            Intrinsic::KeywordToString => Keyword::of(arg(0)).ok_or(Fault::WrongType)?.symbol(mc).name(mc).value(),
            Intrinsic::StringToKeyword => {
                let strings = Strings::new(mc);
                let name = strings.string(arg(0)).ok_or(Fault::WrongType)?;
                let symbols = Symbols::of_arena(mc)?;
                let keyword = symbols.keyword(mc, symbols.intern(&strings, name)?)?;
                made(mc, fuel, keyword.value(mc))
            }
            Intrinsic::Void => Value::VOID,
            Intrinsic::IsBytevector => boolean(AnyBytevector::of(arg(0)).is_some()),
            Intrinsic::MakeBytevector => {
                let fill = match args {
                    1 => 0,
                    2 => byte(arg(1))?,
                    _ => return Err(Fault::Arity),
                };
                made(mc, fuel, Bytevectors::new(mc).make(index(arg(0))?, fill)?.value(mc))
            }
            Intrinsic::BytevectorLength => {
                let len = AnyBytevector::of(arg(0)).ok_or(Fault::WrongType)?.len(mc);
                Value::fixnum(len as i64).expect("lengths are fixnums")
            }
            Intrinsic::BytevectorRef => {
                let bytes = AnyBytevector::of(arg(0)).ok_or(Fault::WrongType)?;
                let byte = bytes.get(mc, index(arg(1))?).ok_or(Fault::OutOfRange)?;
                Value::fixnum(i64::from(byte)).expect("bytes are fixnums")
            }
            Intrinsic::BytevectorSet => {
                let bytes = AnyBytevector::of(arg(0)).ok_or(Fault::WrongType)?;
                let byte = byte(arg(2))?;
                let AnyBytevector::Mutable(bytes) = bytes else { return Err(Fault::Immutable) };
                if !bytes.set(mc, index(arg(1))?, byte) {
                    return Err(Fault::OutOfRange);
                }
                Value::VOID
            }
            Intrinsic::IsVector => boolean(AnyVector::of(arg(0)).is_some()),
            Intrinsic::MakeVector => {
                let fill = match args {
                    1 => fixnum(0),
                    2 => arg(1),
                    _ => return Err(Fault::Arity),
                };
                let len = index(arg(0))?;
                fuel.spend(len as u64 / equal::PER_FUEL)?;
                made(mc, fuel, Vectors::new(mc).make(len, fill)?.value(mc))
            }
            Intrinsic::MakeVectorOf => {
                let vector = Vectors::new(mc).make(args, Value::VOID)?;
                let items = vector.items(mc);
                (0..args).for_each(|i| items.set(mc, i, arg(i)));
                made(mc, fuel, vector.value(mc))
            }
            Intrinsic::VectorLength => {
                let len = AnyVector::of(arg(0)).ok_or(Fault::WrongType)?.len(mc);
                Value::fixnum(len as i64).expect("lengths are fixnums")
            }
            Intrinsic::VectorRef => AnyVector::of(arg(0)).ok_or(Fault::WrongType)?.get(mc, index(arg(1))?).ok_or(Fault::OutOfRange)?,
            Intrinsic::VectorSet => {
                let AnyVector::Mutable(vector) = AnyVector::of(arg(0)).ok_or(Fault::WrongType)? else { return Err(Fault::Immutable) };
                let (items, k) = (vector.items(mc), index(arg(1))?);
                if k >= items.len() {
                    return Err(Fault::OutOfRange);
                }
                items.set(mc, k, arg(2));
                Value::VOID
            }
            Intrinsic::VectorToList => {
                let vector = AnyVector::of(arg(0)).ok_or(Fault::WrongType)?;
                let len = vector.len(mc);
                fuel.spend(len as u64 / equal::PER_FUEL)?;
                let pairs = Pairs::new(mc);
                let mut list = Value::NIL;
                for i in (0..len).rev() {
                    list = pairs.cons(vector.get(mc, i).expect("in range"), list)?.value(mc);
                }
                made(mc, fuel, list)
            }
            Intrinsic::ListToVector => {
                let pairs = Pairs::new(mc);
                let len = pairs.list_len(arg(0)).ok_or(Fault::WrongType)?;
                fuel.spend(len / equal::PER_FUEL)?;
                let vector = Vectors::new(mc).make(usize::try_from(len).map_err(|_| Fault::OutOfMemory)?, Value::VOID)?;
                let items = vector.items(mc);
                pairs.elements(arg(0)).enumerate().for_each(|(i, x)| items.set(mc, i, x));
                made(mc, fuel, vector.value(mc))
            }
            Intrinsic::MakeBox => made(mc, fuel, Value::object(mc, objects::Box::new(mc, arg(0))?)),
            Intrinsic::MakeWinder => made(mc, fuel, Value::object(mc, objects::Winder::new(mc, arg(0), arg(1))?)),
            Intrinsic::Unbox => arg(0).downcast::<objects::Box>(mc).ok_or(Fault::WrongType)?.value(mc),
            Intrinsic::SetBox => {
                arg(0).downcast::<objects::Box>(mc).ok_or(Fault::WrongType)?.set_value(mc, arg(1));
                Value::VOID
            }
            Intrinsic::DefaultPromptTag => prompts::default_tag(),
            Intrinsic::MakePromptTag => match args {
                0 => made(mc, fuel, Value::object(mc, Tag::new(mc, Value::VOID)?)),
                1 => made(mc, fuel, Value::object(mc, Tag::new(mc, arg(0))?)),
                _ => return Err(Fault::Arity),
            },
            Intrinsic::Values => made(mc, fuel, values(mc, (0..args).map(arg))?),
            Intrinsic::IsValues => boolean(arg(0).downcast::<MultiValue>(mc).is_some()),
            Intrinsic::ValuesLength => {
                let items = arg(0).downcast::<MultiValue>(mc).ok_or(Fault::WrongType)?.items(mc);
                Value::fixnum(items.len() as i64).ok_or(Fault::WrongType)?
            }
            Intrinsic::ValuesRef => {
                let items = arg(0).downcast::<MultiValue>(mc).ok_or(Fault::WrongType)?.items(mc);
                let k = index(arg(1))?;
                if k >= items.len() {
                    return Err(Fault::OutOfRange);
                }
                items.get(k)
            }
            Intrinsic::ModuleRef => {
                let items = arg(0).downcast::<objects::Module>(mc).ok_or(Fault::WrongType)?.items(mc);
                let k = arg(1).as_fixnum().ok_or(Fault::WrongType)?;
                let value = usize::try_from(k).ok().filter(|&k| k < items.len()).map(|k| items.get(k)).ok_or(Fault::OutOfRange)?;
                if value == Value::UNDEFINED {
                    return Err(Fault::Unbound);
                }
                value
            }
            Intrinsic::MakeError if args == 0 => return Err(Fault::Arity),
            Intrinsic::MakeSyntaxError if args < 2 => return Err(Fault::Arity),
            Intrinsic::MakeError | Intrinsic::MakeSyntaxError => {
                let pairs = Pairs::new(mc);
                let mut irritants = Value::NIL;
                for i in (1..args).rev() {
                    irritants = pairs.cons(arg(i), irritants)?.value(mc);
                }
                let fault = if self == Intrinsic::MakeError { Fault::Error } else { Fault::Syntax };
                made(mc, fuel, Value::object(mc, Condition::new(mc, mc.frozen(fault)?, arg(0), irritants)?))
            }
            Intrinsic::IsProcedure => boolean(is_procedure(mc, arg(0))),
            Intrinsic::MakeKeywordProcedure => {
                let (plain, core) = (arg(0), arg(1));
                if plain != Value::FALSE && !is_procedure(mc, plain) || !is_procedure(mc, core) {
                    return Err(Fault::WrongType);
                }
                made(mc, fuel, Value::object(mc, objects::KeywordProcedure::new(mc, plain, core, arg(2), arg(3))?))
            }
            Intrinsic::ProcedureKeywords => {
                let f = arg(0);
                if !is_procedure(mc, f) {
                    return Err(Fault::WrongType);
                }
                let (required, keywords) = match f.downcast::<objects::KeywordProcedure>(mc) {
                    Some(k) => (k.required(mc), k.keywords(mc)),
                    None => (Value::NIL, Value::NIL),
                };
                values(mc, [required, keywords].into_iter())?
            }
            Intrinsic::IsContinuation => boolean(arg(0).downcast::<objects::Continuation>(mc).is_some()),
            Intrinsic::MakeCoroutine => {
                let body = arg(0);
                if !is_procedure(mc, body) {
                    return Err(Fault::WrongType);
                }
                made(mc, fuel, Value::object(mc, coroutine::new(mc, body)?))
            }
            Intrinsic::IsCoroutine => boolean(coroutine::of(mc, arg(0)).is_some()),
            Intrinsic::CoroutineState => {
                let co = coroutine::of(mc, arg(0)).ok_or(Fault::WrongType)?;
                Value::fixnum(i64::from(co.state(mc))).expect("states are fixnums")
            }
            Intrinsic::IsErrorObject => boolean(arg(0).downcast::<Condition>(mc).is_some()),
            Intrinsic::IsSyntax => boolean(Syntax::of(arg(0)).is_some()),
            Intrinsic::IsIdentifier => boolean(syntax::is_identifier(mc, arg(0))),
            Intrinsic::SyntaxE => syntax::unwrap(mc, arg(0))?,
            Intrinsic::SyntaxToDatum => syntax::to_datum(mc, arg(0), fuel)?,
            Intrinsic::DatumToSyntax => {
                let syntax = syntax::to_syntax(mc, arg(0), arg(1), fuel)?;
                made(mc, fuel, syntax)
            }
            Intrinsic::BoundIdentifierEq => boolean(syntax::same_identifier(mc, arg(0), arg(1), fuel)?),
            Intrinsic::FreeIdentifierEq => boolean(syntax::same_binding(mc, arg(0), arg(1))?),
            Intrinsic::SyntaxMatch => {
                let matched = crate::syntax_case::matched(mc, arg(0), arg(1), fuel)?;
                made(mc, fuel, matched)
            }
            Intrinsic::SyntaxBuild if args == 0 => return Err(Fault::Arity),
            Intrinsic::SyntaxBuild => {
                let values: Vec<_> = (1..args).map(&arg).collect();
                let built = crate::syntax_case::build(mc, arg(0), &values, fuel)?;
                made(mc, fuel, built)
            }
            Intrinsic::GenerateTemporaries => {
                let temporaries = syntax::temporaries(mc, arg(0), arg(1), fuel)?;
                made(mc, fuel, temporaries)
            }
            Intrinsic::ErrorObjectMessage => {
                let c = arg(0).downcast::<Condition>(mc).ok_or(Fault::WrongType)?;
                match c.message(mc) {
                    Value::VOID => {
                        let kind = c.fault(mc).ok_or(Fault::Malformed)?.kind();
                        let words = Fault::KINDS[kind].replace('-', " ");
                        made(mc, fuel, string::from_str(&Strings::new(mc), &words)?.value())
                    }
                    message => message,
                }
            }
            Intrinsic::ErrorObjectIrritants => arg(0).downcast::<Condition>(mc).ok_or(Fault::WrongType)?.irritants(mc),
            Intrinsic::ErrorObjectKind => {
                let c = arg(0).downcast::<Condition>(mc).ok_or(Fault::WrongType)?;
                Value::fixnum(c.fault(mc).ok_or(Fault::Malformed)?.kind() as i64).expect("kinds are fixnums")
            }
        })
    }
}

#[inline(always)]
fn car<'gc>(mc: &Mutation<'gc>, x: Value<'gc>) -> Result<Value<'gc>, Fault> {
    Ok(Pair::of(x).ok_or(Fault::WrongType)?.head(mc))
}

#[inline(always)]
fn cdr<'gc>(mc: &Mutation<'gc>, x: Value<'gc>) -> Result<Value<'gc>, Fault> {
    Ok(Pair::of(x).ok_or(Fault::WrongType)?.tail(mc))
}

fn fixnum<'gc>(n: i64) -> Value<'gc> {
    Value::fixnum(n).expect("a small fixnum")
}

/// `a / b` if both are fixnums and it's one.
fn fixnum_div<'gc>(a: Value<'gc>, b: Value<'gc>) -> Option<Value<'gc>> {
    let (a, b) = (a.as_fixnum()?, b.as_fixnum()?);
    (b != 0 && a % b == 0).then(|| a / b).and_then(Value::fixnum)
}

/// `first` combined with each of `rest` in turn, by `fast` while that's of two fixnums and makes
/// one, and otherwise by `generic`, on the numeric tower.
#[inline(always)]
fn arith<'gc>(
    mc: &Mutation<'gc>,
    fuel: &mut Fuel,
    first: Value<'gc>,
    rest: impl Iterator<Item = Value<'gc>>,
    fast: impl Fn(Value<'gc>, Value<'gc>) -> Option<Value<'gc>>,
    generic: impl Fn(&Nums<'_, 'gc>, Number<'gc>, Number<'gc>) -> Result<Number<'gc>, Error>,
) -> Result<Value<'gc>, Fault> {
    let mut acc = first;
    for x in rest {
        acc = match fast(acc, x) {
            Some(acc) => acc,
            None => {
                let h = Nums::new(mc);
                let (a, b) = (h.number(acc).ok_or(Fault::WrongType)?, h.number(x).ok_or(Fault::WrongType)?);
                made(mc, fuel, generic(&h, a, b)?.value())
            }
        };
    }
    Ok(acc)
}

/// `quotient`, `remainder` or `modulo` of `n` and `m`, in place if they're fixnums.
fn divide<'gc>(mc: &Mutation<'gc>, fuel: &mut Fuel, op: Intrinsic, n: Value<'gc>, m: Value<'gc>) -> Result<Value<'gc>, Fault> {
    if let (Some(a), Some(b)) = (n.as_fixnum(), m.as_fixnum())
        && b != 0
    {
        // Fixnums are narrower than an i64, so neither can overflow.
        let fast = match op {
            Intrinsic::Quotient => a / b,
            Intrinsic::Remainder => a % b,
            _ => {
                let r = a % b;
                if r != 0 && (r < 0) != (b < 0) { r + b } else { r }
            }
        };
        if let Some(v) = Value::fixnum(fast) {
            return Ok(v);
        }
    }
    let h = Nums::new(mc);
    let (x, y) = (h.real(n).ok_or(Fault::WrongType)?, h.real(m).ok_or(Fault::WrongType)?);
    let generic = match op {
        Intrinsic::Quotient => real::quotient(&h, x, y),
        Intrinsic::Remainder => real::remainder(&h, x, y),
        _ => real::modulo(&h, x, y),
    };
    Ok(made(mc, fuel, generic?.value()))
}

/// `n` in `radix`, its digits written on the stack.
fn fixnum_to_string<'gc>(mc: &Mutation<'gc>, n: i64, radix: u32) -> Result<Value<'gc>, Fault> {
    // 64 binary digits and a sign.
    let mut digits = [0u8; 65];
    let (mut at, mut left) = (digits.len(), n.unsigned_abs());
    loop {
        at -= 1;
        digits[at] = b"0123456789abcdef"[(left % radix as u64) as usize];
        left /= radix as u64;
        if left == 0 {
            break;
        }
    }
    if n < 0 {
        at -= 1;
        digits[at] = b'-';
    }
    let text = std::str::from_utf8(&digits[at..]).expect("digits are ASCII");
    Ok(string::from_str(&Strings::new(mc), text)?.value())
}

/// Whether `v` can be called: a closure, a continuation or a keyword procedure.
fn is_procedure<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> bool {
    v.downcast::<objects::Closure>(mc).is_some()
        || v.downcast::<objects::Continuation>(mc).is_some()
        || v.downcast::<objects::KeywordProcedure>(mc).is_some()
}

/// The bits of `z`'s exact parts, past each one's first, so 0, 1 and -1 have none.
fn exact_bits<'gc>(h: &Nums<'_, 'gc>, z: Number<'gc>) -> u64 {
    let bits = |n| int::integer_length(h, n).saturating_sub(1);
    let real = |r| match h.real_view(r) {
        RealView::Flonum(_) => 0,
        RealView::Exact(q) => match h.rational_view(q) {
            RationalView::Integer(n) => bits(n),
            RationalView::Ratio { num, den } => bits(num) + bits(den),
        },
    };
    match h.complex_view(z) {
        ComplexView::Real(r) => real(r),
        ComplexView::Complex { re, im } => real(re) + real(im),
    }
}

/// Whether each of `xs` is as `op` says of the next, all of them characters.
fn compare_chars<'gc>(op: Intrinsic, xs: impl Iterator<Item = Value<'gc>>) -> Result<bool, Fault> {
    let (mut before, mut so_far) = (None, true);
    for x in xs {
        let x = x.as_char().ok_or(Fault::WrongType)?;
        if let Some(b) = before {
            so_far &= match op {
                Intrinsic::CharEq => b == x,
                Intrinsic::CharLt => b < x,
                Intrinsic::CharGt => b > x,
                Intrinsic::CharLe => b <= x,
                _ => b >= x,
            };
        }
        before = Some(x);
    }
    Ok(so_far)
}

/// `(string-join strs [sep])`: the strings of proper list `strs` with `sep`, or a space, between.
fn string_join<'gc>(mc: &Mutation<'gc>, strs: Value<'gc>, sep: Option<Value<'gc>>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
    let (strings, pairs) = (Strings::new(mc), Pairs::new(mc));
    let sep = match sep {
        Some(v) => strings.string(v).ok_or(Fault::WrongType)?,
        None => string::from_str(&strings, " ")?,
    };
    let n = pairs.list_len(strs).ok_or(Fault::WrongType)?;
    if n == 0 {
        return Ok(string::empty(&strings)?.value());
    }
    fuel.spend(n / equal::PER_FUEL)?;
    let mut items = pairs.elements(strs).map(|v| strings.string(v).ok_or(Fault::WrongType));
    // Most joins are of a few strings, whose parts fit on the stack.
    let joined = if n <= 4 {
        let mut parts = [sep; 7];
        for (i, s) in items.enumerate() {
            parts[2 * i] = s?;
        }
        string::concat_all(&strings, &parts[..2 * n as usize - 1])?
    } else {
        let mut parts = ScratchVec::new(mc);
        parts.push(items.next().ok_or(Fault::WrongType)??)?;
        for s in items {
            parts.push(sep)?;
            parts.push(s?)?;
        }
        string::concat_all(&strings, &parts)?
    };
    Ok(made(mc, fuel, joined.value()))
}

/// Whether each of `xs` is as `op` says of the next, all of them strings.
fn compare_strings<'gc>(mc: &Mutation<'gc>, op: Intrinsic, xs: impl Iterator<Item = Value<'gc>>) -> Result<bool, Fault> {
    let strings = Strings::new(mc);
    let (mut before, mut so_far) = (None, true);
    for x in xs {
        let x = strings.string(x).ok_or(Fault::WrongType)?;
        if let Some(b) = before
            && so_far
        {
            so_far = match op {
                Intrinsic::StringEq => string::equal(&strings, b, x)?,
                Intrinsic::StringLt => string::compare(&strings, b, x)?.is_lt(),
                Intrinsic::StringGt => string::compare(&strings, b, x)?.is_gt(),
                Intrinsic::StringLe => string::compare(&strings, b, x)?.is_le(),
                _ => string::compare(&strings, b, x)?.is_ge(),
            };
        }
        before = Some(x);
    }
    Ok(so_far)
}

/// Charges for `z^w` before it's computed, if it's exact: memory for its digits, and fuel for
/// the squarings that make them, about their count squared.
fn charge_power<'gc>(mc: &Mutation<'gc>, h: &Nums<'_, 'gc>, fuel: &mut Fuel, z: Number<'gc>, w: Number<'gc>) -> Result<(), Fault> {
    let ComplexView::Real(e) = h.complex_view(w) else { return Ok(()) };
    let RealView::Exact(e) = h.real_view(e) else { return Ok(()) };
    let RationalView::Integer(e) = h.rational_view(e) else { return Ok(()) };
    // An exponent past an i64 is too big for anything but 0, 1 and -1, which `expt` sees to.
    let Some(e) = int::to_i64(h, e) else { return Ok(()) };
    let words = exact_bits(h, z).saturating_mul(e.unsigned_abs()) / 64;
    mc.ensure(usize::try_from(words.saturating_mul(8)).unwrap_or(usize::MAX))?;
    fuel.spend(words.saturating_mul(words) / equal::PER_FUEL)
}

/// Whether each of `xs` is as `op` says of the next: for `=`, numbers, and for the others, reals.
/// Each is checked, whatever the answer.
fn compare<'gc>(mc: &Mutation<'gc>, op: Intrinsic, mut xs: impl Iterator<Item = Value<'gc>>) -> Result<bool, Fault> {
    let holds = |order: Ordering| match op {
        Intrinsic::Lt => order.is_lt(),
        Intrinsic::Gt => order.is_gt(),
        Intrinsic::Le => order.is_le(),
        Intrinsic::Ge => order.is_ge(),
        _ => order.is_eq(),
    };
    let h = Nums::new(mc);
    let number = |x: Value<'gc>| h.number(x).ok_or(Fault::WrongType);
    let real = |x: Value<'gc>| h.real(x).ok_or(Fault::WrongType);
    let check = |x: Value<'gc>| if op == Intrinsic::NumEq { number(x).map(drop) } else { real(x).map(drop) };
    let mut before = xs.next().ok_or(Fault::Arity)?;
    let mut so_far = true;
    if before.as_fixnum().is_none() {
        check(before)?;
    }
    for x in xs {
        let fixnums = before.as_fixnum().zip(x.as_fixnum());
        if fixnums.is_none() {
            check(x)?;
        }
        if so_far {
            so_far = match fixnums {
                Some((a, b)) => holds(a.cmp(&b)),
                None if op == Intrinsic::NumEq => complex::equal(&h, number(before)?, number(x)?)?,
                None => real::compare(&h, real(before)?, real(x)?)?.is_some_and(holds),
            };
        }
        before = x;
    }
    Ok(so_far)
}

/// `(reverse xs)`: a new list with the elements of proper list `xs` in reverse order.
fn reverse<'gc>(mc: &Mutation<'gc>, xs: Value<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
    let pairs = Pairs::new(mc);
    let len = pairs.list_len(xs).ok_or(Fault::WrongType)?;
    if len == 0 {
        return Ok(Value::NIL);
    }
    fuel.spend(len / equal::PER_FUEL)?;
    let mut acc = Value::NIL;
    for item in pairs.elements(xs) {
        acc = pairs.cons(item, acc)?.value(mc);
    }
    Ok(made(mc, fuel, acc))
}

/// `memq`, `memv`, `member`, `assq`, `assv` and `assoc`.
fn find<'gc>(mc: &Mutation<'gc>, kind: Intrinsic, x: Value<'gc>, mut xs: Value<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
    let assoc = matches!(kind, Intrinsic::Assq | Intrinsic::Assv | Intrinsic::Assoc);
    let mut steps = 0u64;
    while xs != Value::NIL {
        let pair = Pair::of(xs).ok_or(Fault::WrongType)?;
        let item = pair.head(mc);
        let candidate = if assoc { Pair::of(item).ok_or(Fault::WrongType)?.head(mc) } else { item };
        let prev = steps / equal::PER_FUEL;
        let matched = match kind {
            Intrinsic::Memq | Intrinsic::Assq => {
                steps += 1;
                x == candidate
            }
            Intrinsic::Memv | Intrinsic::Assv => {
                steps += 1;
                equal::eqv(mc, x, candidate)
            }
            _ => {
                let most = fuel
                    .left()
                    .saturating_add(1)
                    .saturating_mul(equal::PER_FUEL)
                    .saturating_sub(steps % equal::PER_FUEL)
                    .saturating_sub(1);
                let (same, compared) = equal::equal(mc, x, candidate, most)?;
                steps = steps.saturating_add(compared);
                same
            }
        };
        fuel.spend(steps / equal::PER_FUEL - prev)?;
        if matched {
            return Ok(if assoc { item } else { xs });
        }
        xs = pair.tail(mc);
    }
    Ok(Value::FALSE)
}

fn string_append<'gc>(mc: &Mutation<'gc>, args: impl ExactSizeIterator<Item = Value<'gc>>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
    let strings = Strings::new(mc);
    let n = args.len();
    fuel.spend(n as u64 / equal::PER_FUEL)?;
    let mut args = args.map(|v| strings.string(v).ok_or(Fault::WrongType));
    let Some(first) = args.next().transpose()? else { return Ok(string::empty(&strings)?.value()) };
    // Most calls have a few parts, which fit on the stack.
    let joined = if n <= 8 {
        let mut parts = [first; 8];
        for (part, s) in parts[1..].iter_mut().zip(args) {
            *part = s?;
        }
        string::concat_all(&strings, &parts[..n])?
    } else {
        let mut parts = ScratchVec::new(mc);
        parts.push(first)?;
        for s in args {
            parts.push(s?)?;
        }
        string::concat_all(&strings, &parts)?
    };
    Ok(made(mc, fuel, joined.value()))
}

/// `(append list ... [obj])`: copies each proper list before the last non-empty argument onto
/// the tail. Since pairs are immutable, trailing `'()` arguments after a proper list need no copy.
fn append<'gc>(mc: &Mutation<'gc>, args: impl ExactSizeIterator<Item = Value<'gc>>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
    let pairs = Pairs::new(mc);
    let mut lists = ScratchVec::new(mc);
    let len = args.len();
    for (i, v) in args.enumerate() {
        if i + 1 < len && !pairs.is_list(v) {
            return Err(Fault::WrongType);
        }
        lists.push(v)?;
    }
    let Some(mut last) = len.checked_sub(1) else { return Ok(Value::NIL) };
    while last > 0 && lists[last] == Value::NIL {
        last -= 1;
    }
    let tail = lists[last];
    let total: u64 = (0..last).map(|i| pairs.list_len(lists[i]).unwrap_or(0)).sum();
    if total == 0 {
        return Ok(tail);
    }
    fuel.spend(total / equal::PER_FUEL)?;
    let mut items = ScratchVec::new(mc);
    for &list in &lists[..last] {
        for item in pairs.elements(list) {
            items.push(item)?;
        }
    }
    Ok(made(mc, fuel, pairs.list_with_tail(items.iter().copied(), tail)?))
}

/// The tail of `xs` after `k` pairs, faulting if `need_pair` and that tail isn't a pair.
fn list_tail<'gc>(mc: &Mutation<'gc>, mut xs: Value<'gc>, k: usize, need_pair: bool, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
    if let Some(len) = Pairs::new(mc).list_len(xs) {
        let max = if need_pair { len } else { len.saturating_add(1) };
        if k as u64 >= max {
            return Err(Fault::OutOfRange);
        }
    }
    fuel.spend(k as u64 / equal::PER_FUEL)?;
    for _ in 0..k {
        let pair = Pair::of(xs).ok_or(if xs == Value::NIL { Fault::OutOfRange } else { Fault::WrongType })?;
        xs = pair.tail(mc);
    }
    if need_pair && Pair::of(xs).is_none() {
        return Err(if xs == Value::NIL { Fault::OutOfRange } else { Fault::WrongType });
    }
    Ok(xs)
}

/// A byte: a fixnum from 0 to 255, or [`Fault::WrongType`].
fn byte(v: Value<'_>) -> Result<u8, Fault> {
    v.as_fixnum().and_then(|b| u8::try_from(b).ok()).ok_or(Fault::WrongType)
}

/// An index: a fixnum, or [`Fault::WrongType`], and not negative, or [`Fault::OutOfRange`].
fn index(v: Value<'_>) -> Result<usize, Fault> {
    let k = v.as_fixnum().ok_or(Fault::WrongType)?;
    usize::try_from(k).map_err(|_| Fault::OutOfRange)
}

/// `value`, just made. If making it has made the step due, the run pauses at its next call or
/// jump, so the step can end and the collector keep up.
#[inline(always)]
pub(crate) fn made<'gc>(mc: &Mutation<'gc>, fuel: &mut Fuel, value: Value<'gc>) -> Value<'gc> {
    if mc.step_due() {
        fuel.pause();
    }
    value
}

/// What `(values x ...)` returns for `values`: one as itself, any other number as a [`MultiValue`].
pub(crate) fn values<'gc>(mc: &Mutation<'gc>, values: impl ExactSizeIterator<Item = Value<'gc>>) -> Result<Value<'gc>, Fault> {
    let mut values = values.peekable();
    if values.len() == 1 {
        return values.next().ok_or(Fault::Malformed);
    }
    let object = MultiValue::new(mc, values.len(), Value::VOID)?;
    let items = object.items(mc);
    values.enumerate().for_each(|(i, value)| items.set(mc, i, value));
    Ok(Value::object(mc, object))
}
