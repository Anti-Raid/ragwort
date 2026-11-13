//! An [`Intrinsic`] evaluates a primitive operation directly from its arguments within the
//! current VM step. It does not inspect or manipulate execution frames and never invokes procedures,
//! preventing suspension mid-execution or re-entrancy into the VM. Operations that call procedures
//! or alter continuations are dispatched as [`crate::Request`]s instead.
//!
//! A few intrinsics inspect or manipulate the running task's dynamic state; see
//! [`Intrinsic::is_dynamic`].

use std::cmp::Ordering;

use ragwort_types::{Error, Wire};
use ragwort_types::bytevector::{AnyBytevector, Bytevectors};
use ragwort_types::gc::{Gc, Mutation, ScratchVec, Value};
use ragwort_types::named;
use ragwort_types::num::rational::Round;
use ragwort_types::num::{ComplexHost, ComplexView, Integer, Number, NumError, Nums, RationalHost, RationalView, RealHost, RealView, complex, int, literal, real};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::string::{self, Str, StrError, Strings};
use ragwort_types::symbol::{Keyword, Symbol, Symbols};
use ragwort_types::syntax::Syntax;
use ragwort_types::vector::{AnyVector, Vectors};

use crate::op::{Context, Fuel};
use crate::report::Failure;
use crate::{Fault, coroutine, equal, prompts, structs, syntax};
use crate::objects::{self, BoxFields, Condition, ConditionFields, KeywordProcedureFields, ModuleFields, MultiValue, MultiValueFields, StructFields, StructTypeFields, Tag, Task, TaskFields};

named! {
    #[repr(u16)]
    #[data(Traits)]
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Wire)]
    pub enum Intrinsic {
        /// `+`: adds numbers, computing fixnum addition in place and delegating other numeric
        /// representations to generic addition.
        Add = ("+", any(FOLD | REORDER | TRUTHY | COMMUTE)),
        /// `-`: unary `(- z)` computes arithmetic negation; variadic `(- z1 z2 ...)` subtracts each
        /// subsequent number from the first.
        Sub = ("-", any(FOLD | REORDER | TRUTHY)),
        /// `*`: multiplies numbers, computing fixnum multiplication in place and delegating other
        /// numeric representations to generic multiplication.
        Mul = ("*", any(FOLD | REORDER | TRUTHY | COMMUTE)),
        /// `/`: unary `(/ z)` computes the reciprocal `1 / z`; variadic `(/ z1 z2 ...)` divides `z1` by each
        /// subsequent number. Exact integer divisions that divide evenly remain fixnums; dividing by an
        /// exact zero raises [`NumError::DivideByZero`].
        Div = ("/", any(FOLD | TRUTHY)),
        /// `(= z1 z2 ...)`: returns `#t` if all numeric arguments are numerically equal, regardless of
        /// exactness, and `#f` otherwise. Any comparison involving NaN evaluates to `#f`.
        NumEq = ("=", any(FOLD)),
        /// `(< x1 x2 ...)`: returns `#t` if the real arguments form a strictly monotonically increasing
        /// sequence. All arguments are type-checked even if an early comparison fails; comparing against
        /// NaN yields `#f`.
        Lt = ("<", any(FOLD)),
        /// `(> x1 x2 ...)`: returns `#t` if the real arguments form a strictly monotonically decreasing
        /// sequence, and `#f` otherwise.
        Gt = (">", any(FOLD)),
        /// `(<= x1 x2 ...)`: returns `#t` if the real arguments form a monotonically non-decreasing
        /// sequence, and `#f` otherwise.
        Le = ("<=", any(FOLD)),
        /// `(>= x1 x2 ...)`: returns `#t` if the real arguments form a monotonically non-increasing
        /// sequence, and `#f` otherwise.
        Ge = (">=", any(FOLD)),
        /// `(expt z w)`: computes `z` raised to the power `w`, returning an exact result when `z` and `w`
        /// are both exact and `w` is an integer. Pre-charges VM fuel based on the estimated bit size of
        /// exact results prior to computation.
        Expt = ("expt", takes(2, FOLD | TRUTHY)),
        /// `(quotient n m)`: computes the truncated quotient `n / m` for exact or inexact integers.
        Quotient = ("quotient", takes(2, FOLD | TRUTHY)),
        /// `(remainder n m)`: computes the remainder of truncated division `n / m`, matching the sign
        /// of dividend `n`.
        Remainder = ("remainder", takes(2, FOLD | TRUTHY)),
        /// `(modulo n m)`: computes `n` modulo `m` (floor division remainder), matching the sign of
        /// divisor `m`.
        Modulo = ("modulo", takes(2, FOLD | TRUTHY)),
        /// `(floor-quotient n m)`: computes the quotient `n / m` rounded toward negative infinity (floor
        /// division) for exact or inexact integers.
        FloorQuotient = ("floor-quotient", takes(2, FOLD | TRUTHY)),
        /// `(bitwise-and n ...)`: computes the bitwise AND of exact integers in two's complement
        /// representation; returns `-1` if called with no arguments.
        BitwiseAnd = ("bitwise-and", any(FOLD | TRUTHY | COMMUTE)),
        /// `(bitwise-ior n ...)`: computes the bitwise inclusive OR of exact integers in two's complement
        /// representation; returns `0` if called with no arguments.
        BitwiseIor = ("bitwise-ior", any(FOLD | TRUTHY | COMMUTE)),
        /// `(bitwise-xor n ...)`: computes the bitwise exclusive OR of exact integers in two's complement
        /// representation; returns `0` if called with no arguments.
        BitwiseXor = ("bitwise-xor", any(FOLD | TRUTHY | COMMUTE)),
        /// `(bitwise-not n)`: computes the bitwise NOT (one's complement, `-n - 1`) of an exact integer.
        BitwiseNot = ("bitwise-not", takes(1, FOLD | TRUTHY)),
        /// `(arithmetic-shift n count)`: performs an arithmetic shift of `n` by `count` bit positions
        /// (`n * 2^count`), shifting left for positive counts and right with sign extension (rounding down)
        /// for negative counts.
        ArithmeticShift = ("arithmetic-shift", takes(2, FOLD | TRUTHY)),
        /// `(integer-length n)`: returns the number of bits required to represent exact integer `n` in
        /// two's complement form, excluding the sign bit.
        IntegerLength = ("integer-length", takes(1, FOLD | TRUTHY)),
        /// `(bit-count n)`: returns the population count (number of set bits) of non-negative integer `n`,
        /// or the number of cleared bits if `n` is negative.
        BitCount = ("bit-count", takes(1, FOLD | TRUTHY)),
        /// `(bit-set? index n)`: returns `#t` if the bit at zero-based position `index` in exact integer `n`
        /// is set (1), and `#f` otherwise.
        IsBitSet = ("bit-set?", takes(2, FOLD)),
        /// `(bit-field n start end)`: extracts the bits in the half-open index range `[start, end)` from
        /// integer `n` as an unsigned non-negative integer.
        BitField = ("bit-field", takes(3, FOLD | TRUTHY)),
        /// `(bit-field-replace dest source start end)`: returns `dest` with the bits in index range
        /// `[start, end)` replaced by the lowest `end - start` bits of `source`.
        BitFieldReplace = ("bit-field-replace", takes(4, FOLD | TRUTHY)),
        /// `number?`: returns `#t` if `x` is any number (equivalent to `complex?`), and `#f` otherwise.
        IsNumber = ("number?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `real?`: returns `#t` if `x` is a real number (a number whose imaginary part is zero), and `#f`
        /// otherwise.
        IsReal = ("real?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `rational?`: returns `#t` if `x` is a rational number (an exact rational number or a finite
        /// flonum), and `#f` otherwise.
        IsRational = ("rational?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `integer?`: returns `#t` if `x` is an integer (either an exact integer or an inexact flonum
        /// with no fractional part), and `#f` otherwise.
        IsInteger = ("integer?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `exact-integer?`: returns `#t` if `x` is an exact integer, and `#f` otherwise.
        IsExactInteger = ("exact-integer?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `(exact? z)`: returns `#t` if number `z` is exact, and `#f` otherwise.
        IsExact = ("exact?", takes(1, FOLD)),
        /// `(inexact? z)`: returns `#t` if number `z` is inexact, and `#f` otherwise.
        IsInexact = ("inexact?", takes(1, FOLD)),
        /// `(nan? z)`: returns `#t` if either the real or imaginary component of `z` is NaN, and `#f`
        /// otherwise.
        IsNan = ("nan?", takes(1, FOLD)),
        /// `(infinite? z)`: returns `#t` if either the real or imaginary component of `z` is infinite,
        /// and `#f` otherwise.
        IsInfinite = ("infinite?", takes(1, FOLD)),
        /// `(finite? z)`: returns `#t` if all components of `z` are finite (neither infinite nor NaN),
        /// and `#f` otherwise.
        IsFinite = ("finite?", takes(1, FOLD)),
        /// `(zero? z)`: returns `#t` if `z` is numerically zero (exact `0`, `0.0`, or `-0.0`), and `#f`
        /// otherwise.
        IsZero = ("zero?", takes(1, FOLD)),
        /// `(positive? x)`: returns `#t` if real number `x` is strictly positive (`x > 0`); returns `#f`
        /// for zero, negative numbers, or NaN.
        IsPositive = ("positive?", takes(1, FOLD)),
        /// `(negative? x)`: returns `#t` if real number `x` is strictly negative (`x < 0`); returns `#f`
        /// for zero (including `-0.0`), positive numbers, or NaN.
        IsNegative = ("negative?", takes(1, FOLD)),
        /// `(odd? n)`: returns `#t` if integer `n` (exact or inexact) is odd, and `#f` otherwise.
        IsOdd = ("odd?", takes(1, FOLD)),
        /// `(even? n)`: returns `#t` if integer `n` (exact or inexact) is even, and `#f` otherwise.
        IsEven = ("even?", takes(1, FOLD)),
        /// `(max x1 x2 ...)`: returns the maximum of the real arguments, coercing the result to inexact
        /// if any argument is inexact.
        Max = ("max", any(FOLD | TRUTHY)),
        /// `(min x1 x2 ...)`: returns the minimum of the real arguments, coercing the result to inexact
        /// if any argument is inexact.
        Min = ("min", any(FOLD | TRUTHY)),
        /// `(abs x)`: returns the absolute value of real number `x`.
        Abs = ("abs", takes(1, FOLD | TRUTHY)),
        /// `(gcd n ...)`: returns the non-negative greatest common divisor of integer arguments (or `0`
        /// if called with no arguments); result is inexact if any argument is inexact.
        Gcd = ("gcd", any(FOLD | TRUTHY)),
        /// `(lcm n ...)`: returns the non-negative least common multiple of integer arguments (or `1`
        /// if called with no arguments); result is inexact if any argument is inexact.
        Lcm = ("lcm", any(FOLD | TRUTHY)),
        /// `(numerator x)`: returns the numerator of rational number `x` reduced to lowest terms,
        /// preserving the exactness of `x`.
        Numerator = ("numerator", takes(1, FOLD | TRUTHY)),
        /// `(denominator x)`: returns the positive denominator of rational number `x` reduced to lowest
        /// terms, preserving the exactness of `x`.
        Denominator = ("denominator", takes(1, FOLD | TRUTHY)),
        /// `(floor x)`: rounds real number `x` to the nearest integer toward negative infinity,
        /// preserving inexact representation for flonums.
        Floor = ("floor", takes(1, FOLD | TRUTHY)),
        /// `(ceiling x)`: rounds real number `x` to the nearest integer toward positive infinity,
        /// preserving inexact representation for flonums.
        Ceiling = ("ceiling", takes(1, FOLD | TRUTHY)),
        /// `(truncate x)`: rounds real number `x` to the nearest integer toward zero, preserving inexact
        /// representation for flonums.
        Truncate = ("truncate", takes(1, FOLD | TRUTHY)),
        /// `(round x)`: rounds real number `x` to the nearest integer, breaking ties toward the nearest
        /// even integer (round-to-even) and preserving inexact representation for flonums.
        Round = ("round", takes(1, FOLD | TRUTHY)),
        /// `(integer-sqrt n)`: returns the integer square root `⌊√n⌋` of non-negative exact integer `n`.
        IntegerSqrt = ("integer-sqrt", takes(1, FOLD | TRUTHY)),
        /// `(exact z)`: converts number `z` to an exact representation, raising a fault if `z` is
        /// infinite or NaN.
        Exact = ("exact", takes(1, FOLD | TRUTHY)),
        /// `(inexact z)`: converts number `z` to an inexact representation.
        Inexact = ("inexact", takes(1, FOLD | TRUTHY)),
        /// `(string->number s [radix])`: parses string `s` as a number using the specified `radix`
        /// (2, 8, 10, or 16; default 10 unless overridden by an explicit radix prefix), returning `#f`
        /// if parsing fails.
        StringToNumber = ("string->number", any(FOLD)),
        /// `(exp z)`: computes the exponential `e^z`, returning exact `1` when `z` is exact `0`.
        Exp = ("exp", takes(1, FOLD | TRUTHY)),
        /// `(log z [base])`: computes the natural logarithm of `z`, or the logarithm of `z` with respect
        /// to the given `base`.
        Log = ("log", any(FOLD | TRUTHY)),
        /// `(sin z)`: computes the sine of `z`.
        Sin = ("sin", takes(1, FOLD | TRUTHY)),
        /// `(cos z)`: computes the cosine of `z`.
        Cos = ("cos", takes(1, FOLD | TRUTHY)),
        /// `(tan z)`: computes the tangent of `z`.
        Tan = ("tan", takes(1, FOLD | TRUTHY)),
        /// `(asin z)`: computes the arc sine of `z`.
        Asin = ("asin", takes(1, FOLD | TRUTHY)),
        /// `(acos z)`: computes the arc cosine of `z`.
        Acos = ("acos", takes(1, FOLD | TRUTHY)),
        /// `(atan z)` or `(atan y x)`: computes the arc tangent of `z`, or the angle (argument) of the
        /// Cartesian coordinate `(x, y)`.
        Atan = ("atan", any(FOLD | TRUTHY)),
        /// `(sqrt z)`: computes the principal square root of `z`, returning an exact result when `z` is an
        /// exact number whose square root is rational.
        Sqrt = ("sqrt", takes(1, FOLD | TRUTHY)),
        /// `(make-rectangular x y)`: constructs the complex number `x + yi` from real components `x`
        /// and `y`.
        MakeRectangular = ("make-rectangular", takes(2, FOLD | TRUTHY)),
        /// `(make-polar m a)`: constructs a complex number from polar magnitude `m` and angle `a`.
        MakePolar = ("make-polar", takes(2, FOLD | TRUTHY)),
        /// `(real-part z)`: returns the real component of complex number `z`.
        RealPart = ("real-part", takes(1, FOLD | TRUTHY)),
        /// `(imag-part z)`: returns the imaginary component of complex number `z`, returning exact `0`
        /// if `z` is real.
        ImagPart = ("imag-part", takes(1, FOLD | TRUTHY)),
        /// `(magnitude z)`: returns the magnitude (absolute value) of complex number `z`.
        Magnitude = ("magnitude", takes(1, FOLD | TRUTHY)),
        /// `(angle z)`: returns the angle (argument in radians) of complex number `z`.
        Angle = ("angle", takes(1, FOLD | TRUTHY)),
        /// `(cons a d)`: allocates and returns a new immutable pair with head `a` (`car`) and tail `d`
        /// (`cdr`).
        Cons = ("cons", takes(2, DISCARD | TRUTHY)),
        /// `(car lst)`: returns the head (first element) of pair `lst`.
        Car = ("car", takes(1, FOLD | REORDER)),
        // The composite accessors `caar` through `cddddr` apply `car` and `cdr` operations in
        // right-to-left order according to the characters in their names.
        /// `(cdr lst)`: returns the tail (second element) of pair `lst`.
        Cdr = ("cdr", takes(1, FOLD | REORDER)),
        Caar = ("caar", takes(1, FOLD | REORDER)),
        Cadr = ("cadr", takes(1, FOLD | REORDER)),
        Cdar = ("cdar", takes(1, FOLD | REORDER)),
        Cddr = ("cddr", takes(1, FOLD | REORDER)),
        Caaar = ("caaar", takes(1, FOLD)),
        Caadr = ("caadr", takes(1, FOLD)),
        Cadar = ("cadar", takes(1, FOLD)),
        Caddr = ("caddr", takes(1, FOLD)),
        Cdaar = ("cdaar", takes(1, FOLD)),
        Cdadr = ("cdadr", takes(1, FOLD)),
        Cddar = ("cddar", takes(1, FOLD)),
        Cdddr = ("cdddr", takes(1, FOLD)),
        Caaaar = ("caaaar", takes(1, FOLD)),
        Caaadr = ("caaadr", takes(1, FOLD)),
        Caadar = ("caadar", takes(1, FOLD)),
        Caaddr = ("caaddr", takes(1, FOLD)),
        Cadaar = ("cadaar", takes(1, FOLD)),
        Cadadr = ("cadadr", takes(1, FOLD)),
        Caddar = ("caddar", takes(1, FOLD)),
        Cadddr = ("cadddr", takes(1, FOLD)),
        Cdaaar = ("cdaaar", takes(1, FOLD)),
        Cdaadr = ("cdaadr", takes(1, FOLD)),
        Cdadar = ("cdadar", takes(1, FOLD)),
        Cdaddr = ("cdaddr", takes(1, FOLD)),
        Cddaar = ("cddaar", takes(1, FOLD)),
        Cddadr = ("cddadr", takes(1, FOLD)),
        Cdddar = ("cdddar", takes(1, FOLD)),
        Cddddr = ("cddddr", takes(1, FOLD)),
        /// `(eq? a b)`: returns `#t` if `a` and `b` share identical pointer or immediate value identity,
        /// and `#f` otherwise.
        Eq = ("eq?", takes(2, FOLD | DISCARD | COMMUTE)),
        /// `(eqv? a b)`: returns `#t` if `a` and `b` satisfy `eq?` or are numbers with identical numeric
        /// value and exactness, and `#f` otherwise.
        Eqv = ("eqv?", takes(2, FOLD | DISCARD | COMMUTE)),
        /// `(equal? a b)`: returns `#t` if `a` and `b` satisfy `eqv?` or are recursively structurally
        /// equivalent (comparing strings, pairs, vectors, or boxes by content). Terminates on cyclic
        /// structures and deducts one VM fuel unit per 1,024 comparisons, raising [`Fault::OutOfFuel`]
        /// if fuel is exhausted.
        Equal = ("equal?", takes(2, FOLD | COMMUTE)),
        /// `(null? x)`: returns `#t` if `x` is the empty list `'()`, and `#f` otherwise.
        IsNull = ("null?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `(pair? x)`: returns `#t` if `x` is a pair, and `#f` otherwise.
        IsPair = ("pair?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `(list? x)`: returns `#t` if `x` is a proper list (either the empty list `'()` or a chain of
        /// pairs terminating in `'()`), evaluated in $O(1)$ constant time.
        IsList = ("list?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `(length xs)`: returns the number of elements in proper list `xs`, evaluated in $O(1)$
        /// constant time.
        Length = ("length", takes(1, FOLD | TRUTHY)),
        /// `(list-tail xs k)`: returns the sublist resulting from omitting the first `k` elements of list `xs`.
        ListTail = ("list-tail", takes(2, FOLD)),
        /// `(list-ref xs k)`: returns the `k`th element (zero-indexed) of list `xs`.
        ListRef = ("list-ref", takes(2, FOLD)),
        /// `(reverse xs)`: returns a newly allocated list containing the elements of proper list `xs` in
        /// reverse order.
        Reverse = ("reverse", takes(1, TRUTHY)),
        /// `(append list ... [obj])`: concatenates proper lists onto a final terminal value `obj` without
        /// copying the final argument.
        Append = ("append", any(0)),
        /// `(memq x xs)`: returns the first sublist of `xs` whose `car` is `eq?` to `x`, or `#f` if not
        /// found.
        Memq = ("memq", takes(2, FOLD)),
        /// `(memv x xs)`: returns the first sublist of `xs` whose `car` is `eqv?` to `x`, or `#f` if not
        /// found.
        Memv = ("memv", takes(2, FOLD)),
        /// `(member x xs)`: returns the first sublist of `xs` whose `car` is `equal?` to `x`, or `#f` if
        /// not found.
        Member = ("member", takes(2, FOLD)),
        /// `(assq x xs)`: returns the first pair in association list `xs` whose `car` is `eq?` to `x`,
        /// or `#f` if not found.
        Assq = ("assq", takes(2, FOLD)),
        /// `(assv x xs)`: returns the first pair in association list `xs` whose `car` is `eqv?` to `x`,
        /// or `#f` if not found.
        Assv = ("assv", takes(2, FOLD)),
        /// `(assoc x xs)`: returns the first pair in association list `xs` whose `car` is `equal?` to `x`,
        /// or `#f` if not found.
        Assoc = ("assoc", takes(2, FOLD)),
        /// `(box? x)`: returns `#t` if `x` is a box, and `#f` otherwise.
        IsBox = ("box?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `(not x)`: boolean negation, returning `#t` if `x` is `#f`, and `#f` for any other value.
        Not = ("not", takes(1, FOLD | DISCARD)),
        /// `(boolean? x)`: returns `#t` if `x` is a boolean (`#t` or `#f`), and `#f` otherwise.
        IsBoolean = ("boolean?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `(keyword? x)`: returns `#t` if `x` is a keyword (e.g. `#:name`), and `#f` otherwise.
        IsKeyword = ("keyword?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `(symbol? x)`: returns `#t` if `x` is an interned symbol, and `#f` otherwise.
        IsSymbol = ("symbol?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `(string? x)`: returns `#t` if `x` is a string, and `#f` otherwise.
        IsString = ("string?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `(string-length s)`: returns the character count (Unicode scalar values) of string `s`.
        StringLength = ("string-length", takes(1, FOLD | TRUTHY)),
        /// `(string-append s ...)`: concatenates string arguments into a newly constructed string, using
        /// shared immutable representations for long strings to avoid copying.
        StringAppend = ("string-append", any(TRUTHY)),
        /// `(substring s start [end])`: extracts a substring of `s` over index range `[start, end)`
        /// (defaulting `end` to the length of `s`).
        Substring = ("substring", any(TRUTHY)),
        /// `(string-ref s k)`: returns the `k`th character (zero-indexed Unicode scalar value) of string `s`.
        StringRef = ("string-ref", takes(2, FOLD | TRUTHY)),
        /// `(string=? s1 s2 ...)`: returns `#t` if all string arguments contain identical sequences
        /// of characters; all arguments are checked for correct types even if a comparison fails.
        StringEq = ("string=?", any(FOLD)),
        /// `(string<? s1 s2 ...)`: returns `#t` if the string arguments form a strictly increasing
        /// sequence in lexicographical order by Unicode code point.
        StringLt = ("string<?", any(FOLD)),
        /// `(string>? s1 s2 ...)`: returns `#t` if the string arguments form a strictly decreasing
        /// sequence in lexicographical order by Unicode code point.
        StringGt = ("string>?", any(FOLD)),
        /// `(string<=? s1 s2 ...)`: returns `#t` if the string arguments form a monotonically
        /// non-decreasing sequence in lexicographical order by Unicode code point.
        StringLe = ("string<=?", any(FOLD)),
        /// `(string>=? s1 s2 ...)`: returns `#t` if the string arguments form a monotonically
        /// non-increasing sequence in lexicographical order by Unicode code point.
        StringGe = ("string>=?", any(FOLD)),
        /// `(string->list s [start [end]])`: returns a newly allocated list of characters from string
        /// `s` within the optional index range `[start, end)`.
        StringToList = ("string->list", any(TRUTHY)),
        /// `(number->string z [radix])`: formats number `z` as a string in radix 2, 8, 10, or 16
        /// (default 10); non-decimal radixes format inexact numbers by converting them to exact
        /// rationals first.
        NumberToString = ("number->string", any(TRUTHY)),
        /// `(string-join strs [sep])`: concatenates the elements of string list `strs`, inserting
        /// delimiter `sep` (default `" "`) between adjacent elements.
        StringJoin = ("string-join", any(TRUTHY)),
        /// `char?`: returns `#t` if `x` is a character (Unicode scalar value), and `#f` otherwise.
        IsChar = ("char?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `(char->integer c)`: returns the Unicode code point of character `c` as an exact integer.
        CharToInteger = ("char->integer", takes(1, FOLD | TRUTHY)),
        /// `(integer->char n)`: converts an exact integer code point `n` into a character, requiring
        /// `n` to be a valid Unicode scalar value (in `0..=0xD7FF` or `0xE000..=0x10FFFF`).
        IntegerToChar = ("integer->char", takes(1, FOLD | TRUTHY)),
        /// `(char-alphabetic? c)`: returns `#t` if character `c` possesses the Unicode `Alphabetic`
        /// property, and `#f` otherwise.
        IsCharAlphabetic = ("char-alphabetic?", takes(1, FOLD)),
        /// `(char-numeric? c)`: returns `#t` if character `c` is a decimal digit in any Unicode script,
        /// and `#f` otherwise.
        IsCharNumeric = ("char-numeric?", takes(1, FOLD)),
        /// `(char-whitespace? c)`: returns `#t` if character `c` possesses the Unicode `White_Space`
        /// property, and `#f` otherwise.
        IsCharWhitespace = ("char-whitespace?", takes(1, FOLD)),
        /// `(char-upper-case? c)`: returns `#t` if character `c` possesses the Unicode `Uppercase`
        /// property, and `#f` otherwise.
        IsCharUpperCase = ("char-upper-case?", takes(1, FOLD)),
        /// `(char-lower-case? c)`: returns `#t` if character `c` possesses the Unicode `Lowercase`
        /// property, and `#f` otherwise.
        IsCharLowerCase = ("char-lower-case?", takes(1, FOLD)),
        /// `(digit-value c)`: returns the numeric value (0–9) of character `c` if it represents a
        /// decimal digit in any Unicode script, or `#f` otherwise.
        DigitValue = ("digit-value", takes(1, FOLD)),
        /// `(char-upcase c)`: returns the uppercase mapping of character `c` if the mapping produces
        /// a single character, or `c` unchanged if multi-character expansion is required.
        CharUpcase = ("char-upcase", takes(1, FOLD | TRUTHY)),
        /// `(char-downcase c)`: returns the lowercase mapping of character `c` if the mapping
        /// produces a single character, or `c` unchanged otherwise.
        CharDowncase = ("char-downcase", takes(1, FOLD | TRUTHY)),
        /// `(char-foldcase c)`: returns the Unicode case-folded equivalent of character `c` if the
        /// result is a single character, or `c` unchanged otherwise.
        CharFoldcase = ("char-foldcase", takes(1, FOLD | TRUTHY)),
        /// `(char-ci=? c1 c2 ...)`: case-insensitive character equality; returns `#t` if all arguments
        /// are equal after Unicode case-folding.
        CharCiEq = ("char-ci=?", any(FOLD)),
        /// `(char-ci<? c1 c2 ...)`: returns `#t` if the characters form a strictly increasing sequence
        /// after Unicode case-folding.
        CharCiLt = ("char-ci<?", any(FOLD)),
        /// `(char-ci>? c1 c2 ...)`: returns `#t` if the characters form a strictly decreasing sequence
        /// after Unicode case-folding.
        CharCiGt = ("char-ci>?", any(FOLD)),
        /// `(char-ci<=? c1 c2 ...)`: returns `#t` if the characters form a monotonically non-decreasing
        /// sequence after Unicode case-folding.
        CharCiLe = ("char-ci<=?", any(FOLD)),
        /// `(char-ci>=? c1 c2 ...)`: returns `#t` if the characters form a monotonically non-increasing
        /// sequence after Unicode case-folding.
        CharCiGe = ("char-ci>=?", any(FOLD)),
        /// `(make-string k [c])`: allocates a newly constructed string of length `k` filled with
        /// character `c` (defaulting to space `' '`).
        MakeString = ("make-string", any(TRUTHY)),
        /// `(list->string chars)`: constructs and returns a string from a proper list of characters `chars`.
        ListToString = ("list->string", takes(1, TRUTHY)),
        /// `(string-upcase s)`: returns a newly allocated string containing the full Unicode uppercase
        /// mapping of `s`, expanding single characters to multi-character sequences where standard
        /// mappings require.
        StringUpcase = ("string-upcase", takes(1, TRUTHY)),
        /// `(string-downcase s)`: returns a newly allocated string containing the full Unicode
        /// lowercase mapping of `s`.
        StringDowncase = ("string-downcase", takes(1, TRUTHY)),
        /// `(string-foldcase s)`: returns a newly allocated string transformed according to full
        /// Unicode case folding, normalizing case distinctions for case-insensitive comparisons.
        StringFoldcase = ("string-foldcase", takes(1, TRUTHY)),
        /// `(string-ci=? s1 s2 ...)`: returns `#t` if all string arguments are identical after applying
        /// full Unicode case folding.
        StringCiEq = ("string-ci=?", any(FOLD)),
        /// `(string-ci<? s1 s2 ...)`: returns `#t` if the strings form a strictly increasing sequence
        /// under Unicode case-folded lexicographical comparison.
        StringCiLt = ("string-ci<?", any(FOLD)),
        /// `(string-ci>? s1 s2 ...)`: returns `#t` if the strings form a strictly decreasing sequence
        /// under Unicode case-folded lexicographical comparison.
        StringCiGt = ("string-ci>?", any(FOLD)),
        /// `(string-ci<=? s1 s2 ...)`: returns `#t` if the strings form a monotonically non-decreasing
        /// sequence under Unicode case-folded lexicographical comparison.
        StringCiLe = ("string-ci<=?", any(FOLD)),
        /// `(string-ci>=? s1 s2 ...)`: returns `#t` if the strings form a monotonically non-increasing
        /// sequence under Unicode case-folded lexicographical comparison.
        StringCiGe = ("string-ci>=?", any(FOLD)),
        /// `(string->vector s [start [end]])`: allocates a mutable vector containing the characters of
        /// string `s` within index range `[start, end)`.
        StringToVector = ("string->vector", any(TRUTHY)),
        /// `(vector->string v [start [end]])`: constructs a string from the characters in vector `v`
        /// within index range `[start, end)`.
        VectorToString = ("vector->string", any(TRUTHY)),
        /// `(string->utf8 s [start [end]])`: encodes the characters of `s` in range `[start, end)` into
        /// a newly allocated bytevector containing UTF-8 bytes.
        StringToUtf8 = ("string->utf8", any(TRUTHY)),
        /// `(utf8->string bv [start [end]])`: decodes the bytes of bytevector `bv` in range `[start, end)`
        /// into a string, raising a fault if the bytes do not form valid UTF-8.
        Utf8ToString = ("utf8->string", any(TRUTHY)),
        /// `(string-prefix? s prefix)`: returns `#t` if string `s` begins with `prefix`, and `#f`
        /// otherwise.
        IsStringPrefix = ("string-prefix?", takes(2, FOLD)),
        /// `(string-suffix? s suffix)`: returns `#t` if string `s` ends with `suffix`, and `#f`
        /// otherwise.
        IsStringSuffix = ("string-suffix?", takes(2, FOLD)),
        /// `(string-contains? s part)`: returns `#t` if substring `part` occurs anywhere within
        /// string `s`, and `#f` otherwise.
        IsStringContains = ("string-contains?", takes(2, FOLD)),
        /// `(string-find s part [start])`: returns the character index of the first occurrence of
        /// `part` in `s` at or after `start`, or `#f` if not found.
        StringFind = ("string-find", any(FOLD)),
        /// `(string-find-last s part [end])`: returns the character index of the last occurrence of
        /// `part` in `s` ending before index `end`, or `#f` if not found.
        StringFindLast = ("string-find-last", any(FOLD)),
        /// `(string-split s sep trim? repeat?)`: splits `s` by delimiter string `sep` (or runs of
        /// whitespace if `sep` is `#f`), returning a list of substrings with optional boundary trimming
        /// (`trim?`) and collapsing of repeated delimiters (`repeat?`).
        StringSplit = ("string-split", takes(4, TRUTHY)),
        /// `(string-trim s sep left? right? repeat?)`: strips occurrences of delimiter `sep` (or
        /// whitespace if `sep` is `#f`) from the start (`left?`) and/or end (`right?`) of string `s`,
        /// collapsing repeated occurrences if `repeat?` is true.
        StringTrim = ("string-trim", takes(5, TRUTHY)),
        /// `(string-replace s from to all?)`: replaces occurrences of substring `from` with `to` in
        /// string `s`, substituting all matches if `all?` is true or only the first match if `#f`.
        StringReplace = ("string-replace", takes(4, TRUTHY)),
        /// `(char=? c1 c2 ...)`: returns `#t` if all character arguments have identical Unicode code
        /// points; validates character types across all arguments even if an inequality is found.
        CharEq = ("char=?", any(FOLD)),
        /// `(char<? c1 c2 ...)`: returns `#t` if the characters form a strictly increasing sequence
        /// by Unicode code point value.
        CharLt = ("char<?", any(FOLD)),
        /// `(char>? c1 c2 ...)`: returns `#t` if the characters form a strictly decreasing sequence
        /// by Unicode code point value.
        CharGt = ("char>?", any(FOLD)),
        /// `(char<=? c1 c2 ...)`: returns `#t` if the characters form a monotonically non-decreasing
        /// sequence by Unicode code point value.
        CharLe = ("char<=?", any(FOLD)),
        /// `(char>=? c1 c2 ...)`: returns `#t` if the characters form a monotonically non-increasing
        /// sequence by Unicode code point value.
        CharGe = ("char>=?", any(FOLD)),
        /// `(%keyword-procedure plain core keywords required)`: constructs a keyword-accepting procedure
        /// wrapper from a plain procedure, core implementation, list of accepted keywords, and list of
        /// required keywords; see [`crate::keyword`].
        MakeKeywordProcedure = ("%keyword-procedure", takes(4, 0)),
        /// `(make-struct-type name parent fields field-flags flags)`: internal compiler intrinsic
        /// constructing a new struct type descriptor; see [`crate::structs::make_type`]. Flagged as
        /// [internal](Intrinsic::is_internal).
        MakeStructType = ("make-struct-type", takes(5, TRUTHY | INTERNAL)),
        /// `(make-struct type v ...)`: internal compiler intrinsic allocating an instance of struct
        /// `type`, supplying field values corresponding to all declared fields. Flagged as
        /// [internal](Intrinsic::is_internal).
        MakeStruct = ("make-struct", any(TRUTHY | INTERNAL)),
        /// `(struct? v)`: returns `#t` if `v` is an instance of any struct type, and `#f` otherwise.
        IsStruct = ("struct?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `(struct-type? v)`: returns `#t` if `v` is a struct type descriptor (e.g. `struct:name`),
        /// and `#f` otherwise.
        IsStructType = ("struct-type?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `(struct-derived-from? v type)`: returns `#t` if `v` is an instance of `type` or any
        /// descendant subtype in its inheritance hierarchy, and `#f` otherwise.
        IsStructDerivedFrom = ("struct-derived-from?", takes(2, FOLD | REORDER)),
        /// `(struct-ref s type k)`: internal compiler intrinsic reading field index `k` of struct
        /// instance `s`, validating that `s` instantiates `type`. Flagged as
        /// [internal](Intrinsic::is_internal).
        StructRef = ("struct-ref", takes(3, REORDER | INTERNAL)),
        /// `(struct-field s k)`: unchecked field accessor emitted by the compiler when the instance
        /// type and field offset `k` have been statically verified. Flagged as
        /// [internal](Intrinsic::is_internal).
        StructField = ("struct-field", takes(2, DISCARD | INTERNAL)),
        /// `(struct-fixed-field s k)`: unchecked immutable field accessor emitted by the compiler
        /// for statically verified struct types and immutable fields, enabling common subexpression
        /// elimination. Flagged as [internal](Intrinsic::is_internal).
        StructFixedField = ("struct-fixed-field", takes(2, DISCARD | INTERNAL)),
        /// `(struct-set! s type k v)`: internal compiler intrinsic mutating field index `k` of struct
        /// instance `s` to `v`, validating `type` conformance and raising [`Fault::Immutable`] if the
        /// field is not mutable. Flagged as [internal](Intrinsic::is_internal).
        StructSet = ("struct-set!", takes(4, INTERNAL)),
        /// `(struct-fields type)`: returns a list of symbols representing field names declared by
        /// `type`, ordering inherited supertype fields before subtype fields.
        StructFields = ("struct-fields", takes(1, TRUTHY)),
        /// `(struct-field-mutable? type k)`: returns `#t` if field index `k` of `type` is declared
        /// mutable, and `#f` otherwise.
        IsStructFieldMutable = ("struct-field-mutable?", takes(2, FOLD | REORDER)),
        /// `(struct-type s)`: returns the struct type descriptor associated with struct instance `s`.
        StructType = ("struct-type", takes(1, FOLD | REORDER | TRUTHY)),
        /// `(struct->list s)`: returns a newly allocated list containing the field values of struct
        /// instance `s`, ordered according to `(struct-fields (struct-type s))`.
        StructToList = ("struct->list", takes(1, TRUTHY)),
        /// `(procedure-keywords f)`: returns two sorted lists `(required-keywords, accepted-keywords)`
        /// accepted by procedure `f`; returns two empty lists if `f` accepts no keywords.
        ProcedureKeywords = ("procedure-keywords", takes(1, 0)),
        /// `(symbol->string s)`: returns the string representation of interned symbol `s`.
        SymbolToString = ("symbol->string", takes(1, 0)),
        /// `(string->symbol s)`: interns string `s` and returns the corresponding canonical symbol.
        StringToSymbol = ("string->symbol", takes(1, 0)),
        /// `(keyword->string k)`: returns the string name of keyword `k`, excluding its leading `#:`. 
        KeywordToString = ("keyword->string", takes(1, 0)),
        /// `(string->keyword s)`: constructs an interned keyword corresponding to identifier string
        /// `s` (read as `#:s`).
        StringToKeyword = ("string->keyword", takes(1, 0)),
        /// `(void x ...)`: ignores all arguments and returns the Scheme void value `#<void>`.
        Void = ("void", any(FOLD | DISCARD | TRUTHY)),
        /// `(bytevector? x)`: returns `#t` if `x` is a bytevector, and `#f` otherwise.
        IsBytevector = ("bytevector?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `(make-bytevector k [byte])`: allocates a mutable bytevector of length `k` initialized with
        /// `byte` (defaulting to 0).
        MakeBytevector = ("make-bytevector", any(TRUTHY)),
        /// `(bytevector-length bv)`: returns the length in bytes of bytevector `bv`.
        BytevectorLength = ("bytevector-length", takes(1, FOLD | TRUTHY)),
        /// `(bytevector-int-ref bv k big kind)`: decodes an integer starting at byte offset `k` in
        /// bytevector `bv`; `big` specifies endianness (`#t` for big-endian, `#f` for little-endian), and
        /// `kind` indicates byte width (1 to 8), with negative values indicating signed integers and
        /// positive values indicating unsigned.
        BytevectorRef = ("bytevector-int-ref", takes(4, FOLD | TRUTHY)),
        /// `(bytevector-int-set! bv k n big kind)`: encodes exact integer `n` into mutable bytevector
        /// `bv` at byte offset `k` using the endianness `big` and byte-width/signedness format `kind`,
        /// returning `#<void>`.
        BytevectorSet = ("bytevector-int-set!", takes(5, TRUTHY)),
        /// `(vector? x)`: returns `#t` if `x` is a vector, and `#f` otherwise.
        IsVector = ("vector?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `(make-vector k [fill])`: allocates a mutable vector of length `k` with each element
        /// initialized to `fill` (defaulting to `0`).
        MakeVector = ("make-vector", any(TRUTHY)),
        /// `(vector x ...)`: allocates and returns a mutable vector containing the argument elements `x ...`.
        MakeVectorOf = ("vector", any(DISCARD | TRUTHY)),
        /// `(vector-length v)`: returns the number of elements in vector `v`.
        VectorLength = ("vector-length", takes(1, FOLD | TRUTHY)),
        /// `(vector-ref v k)`: returns the element at zero-based index `k` in vector `v`.
        VectorRef = ("vector-ref", takes(2, FOLD)),
        /// `(vector-set! v k x)`: mutates index `k` of vector `v` to hold `x`, returning `#<void>`.
        VectorSet = ("vector-set!", takes(3, TRUTHY)),
        /// `(vector->list v)`: constructs and returns a newly allocated list containing the elements
        /// of vector `v`.
        VectorToList = ("vector->list", takes(1, TRUTHY)),
        /// `(list->vector xs)`: allocates and returns a mutable vector populated with the elements of
        /// proper list `xs`.
        ListToVector = ("list->vector", takes(1, TRUTHY)),
        /// `(box x)`: allocates and returns a newly created mutable box initialized with value `x`.
        MakeBox = ("box", takes(1, DISCARD | TRUTHY)),
        /// `(unbox b)`: dereferences box `b`, returning its current stored value.
        Unbox = ("unbox", takes(1, REORDER)),
        /// `(set-box! b x)`: mutates box `b` to store value `x`, returning `#<void>`.
        SetBox = ("set-box!", takes(2, TRUTHY)),
        /// `(make-winder before after)`: constructs a dynamic winder object with `before` and `after`
        /// thunks for stack unwinding and rewinding in `dynamic-wind`.
        MakeWinder = ("make-winder", takes(2, DISCARD | TRUTHY)),
        /// `(default-continuation-prompt-tag)`: returns the default continuation prompt tag for
        /// delimited continuations.
        DefaultPromptTag = ("default-continuation-prompt-tag", takes(0, FOLD | DISCARD | TRUTHY)),
        /// `(make-continuation-prompt-tag [name])`: allocates a fresh unique continuation prompt tag,
        /// optionally annotated with symbol `name`.
        MakePromptTag = ("make-continuation-prompt-tag", any(TRUTHY)),
        /// `(values x ...)`: returns multiple values; single values are returned directly, while zero
        /// or multiple values are packaged into a [`MultiValue`] object.
        Values = ("values", any(DISCARD)),
        /// `(values? x)`: returns `#t` if `x` is a multiple-value container ([`MultiValue`]), and `#f`
        /// otherwise.
        IsValues = ("values?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `(values-length mv)`: returns the count of values contained in [`MultiValue`] `mv`.
        ValuesLength = ("values-length", takes(1, FOLD | TRUTHY)),
        /// `(values-ref mv k)`: returns the `k`th value (zero-indexed) in [`MultiValue`] `mv`.
        ValuesRef = ("values-ref", takes(2, FOLD)),
        /// `(module-ref m k)`: retrieves exported variable `k` from [`objects::Module`] `m`, or raises
        /// [`Fault::Unbound`] if undefined (used when referencing exported mutable bindings across module
        /// boundaries).
        ModuleRef = ("module-ref", takes(2, 0)),
        /// `(make-error message irritant ...)`: constructs a [`Condition`] of kind [`Fault::Error`]
        /// containing `message` and optional `irritants`, raised by standard `error`.
        MakeError = ("make-error", any(TRUTHY)),
        /// `(make-syntax-error message form subform ...)`: constructs a macro syntax error condition
        /// with explanatory `message`, identifying malformed `form` and relevant `subform` context.
        MakeSyntaxError = ("make-syntax-error", any(TRUTHY)),
        /// `(procedure? x)`: returns `#t` if `x` is callable (a closure, continuation, or keyword
        /// procedure), and `#f` otherwise.
        IsProcedure = ("procedure?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `(continuation? x)`: returns `#t` if `x` is a continuation object ([`objects::Continuation`]),
        /// whether delimited/composable or undelimited, and `#f` otherwise.
        IsContinuation = ("continuation?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `(make-coroutine f)`: constructs a new suspended coroutine initialized to invoke procedure
        /// `f` upon its first resumption via `co/resume`.
        MakeCoroutine = ("make-coroutine", takes(1, TRUTHY)),
        /// `(coroutine? x)`: returns `#t` if `x` is a coroutine object, and `#f` otherwise.
        IsCoroutine = ("coroutine?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `(coroutine-state co)`: returns an integer encoding the execution state of coroutine `co`
        /// (0: pending, 1: running, 2: finished, 3: failed).
        CoroutineState = ("coroutine-state", takes(1, TRUTHY)),
        /// `(error-object? x)`: returns `#t` if `x` is an error condition object ([`Condition`]),
        /// whether created by `make-error` or VM faults, and `#f` otherwise.
        IsErrorObject = ("error-object?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `(error-object-message c)`: returns the error message string from condition `c`, or a
        /// descriptive textual representation of the fault kind for VM-generated faults.
        ErrorObjectMessage = ("error-object-message", takes(1, TRUTHY)),
        /// `(error-object-irritants c)`: returns the list of irritant objects associated with condition `c`.
        ErrorObjectIrritants = ("error-object-irritants", takes(1, TRUTHY)),
        /// `(error-object-kind c)`: returns the fault kind symbol corresponding to condition `c` from
        /// [`Fault::KINDS`].
        ErrorObjectKind = ("error-object-kind", takes(1, TRUTHY)),
        /// `(error-object-traceback c)`: returns the calls in progress when condition `c` was first raised, innermost first, as a list of `(name file line)` entries. `name` is the procedure's symbol or `#f`; `file` and `line` say where the procedure is defined, and are `#f` when that is unknown.
        ErrorObjectTraceback = ("error-object-traceback", takes(1, 0)),
        /// `(error-object-who c)`: returns the name of the built-in operation or host function that raised condition `c` as a symbol, or `#f` if `c` was not raised by one.
        ErrorObjectWho = ("error-object-who", takes(1, 0)),
        /// `(syntax? x)`: returns `#t` if `x` is a syntax object, and `#f` otherwise.
        IsSyntax = ("syntax?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `(identifier? x)`: returns `#t` if syntax object `x` wraps a symbol, and `#f` otherwise.
        IsIdentifier = ("identifier?", takes(1, FOLD | DISCARD | PREDICATE)),
        /// `(syntax-e stx)`: unwraps the immediate syntax layer of `stx`, returning an interned symbol,
        /// list/vector of syntax objects, or literal datum.
        SyntaxE = ("syntax-e", takes(1, 0)),
        /// `(syntax->datum stx)`: recursively unwraps syntax object `stx` and all nested syntax
        /// wrappers, producing a pure Scheme datum.
        SyntaxToDatum = ("syntax->datum", takes(1, 0)),
        /// `(datum->syntax context datum)`: wraps `datum` as a syntax object inheriting lexical scopes
        /// and source spans from `context` (or empty scopes if `context` is `#f`); existing nested
        /// syntax objects retain their original scoping.
        DatumToSyntax = ("datum->syntax", takes(2, 0)),
        /// `(bound-identifier=? a b)`: returns `#t` if identifiers `a` and `b` share identical symbolic
        /// names and identical lexical scope sets, meaning a binding for `a` would capture `b`.
        BoundIdentifierEq = ("bound-identifier=?", takes(2, 0)),
        /// `(free-identifier=? a b)`: returns `#t` if identifiers `a` and `b` resolve to the same lexical
        /// or top-level binding in their respective lexical environments.
        FreeIdentifierEq = ("free-identifier=?", takes(2, 0)),
        /// `(generate-temporaries list name)`: generates a list of fresh temporary identifiers
        /// corresponding to the elements of `list`, each tagged with a unique scope to prevent
        /// unintended capture; identifiers take their base symbol from the corresponding element (if an
        /// identifier) or default to `name`.
        GenerateTemporaries = ("generate-temporaries", takes(2, 0)),
        /// `(syntax-match pattern input)`: matches syntax `input` against compiled
        /// [`SyntaxPattern`](crate::objects::SyntaxPattern), returning a vector of matched pattern
        /// variable bindings on success, or `#f` if the pattern does not match.
        SyntaxMatch = ("syntax-match", takes(2, 0)),
        /// `(syntax-build template value ...)`: instantiates
        /// [`SyntaxTemplate`](crate::objects::SyntaxTemplate) using the vector/list of pattern variable
        /// bindings `value ...` to construct a new syntax object.
        SyntaxBuild = ("syntax-build", any(0)),
        /// `(mark-value key default)`: retrieves the value of the closest continuation mark associated
        /// with `key` in the running task's continuation, or returns `default` if no such mark exists.
        MarkValue = ("mark-value", takes(2, DISCARD | DYNAMIC)),
        /// `(frame-mark key default)`: retrieves the value of the closest continuation mark for `key`
        /// within the current delimited prompt frame, or returns `default` if none is found prior to the
        /// prompt.
        FrameMark = ("frame-mark", takes(2, DISCARD | DYNAMIC)),
        /// `(frame-marks key default tag)`: returns a list containing the nearest continuation mark for
        /// `key` in each delimited prompt segment (innermost segment first), substituting `default` for
        /// segments lacking a mark, delimited by prompt `tag` (or traversing the entire continuation if
        /// `tag` is `#f`).
        FrameMarks = ("frame-marks", takes(3, DYNAMIC)),
        /// `(co/running)`: returns the currently executing coroutine object, or in a standalone task,
        /// returns the task itself.
        Running = ("co/running", takes(0, DISCARD | TRUTHY | DYNAMIC)),
        /// `(winders)`: returns the list of active dynamic winders for the current task delimited by
        /// the nearest continuation prompt, ordered innermost first.
        Winders = ("winders", takes(0, DISCARD | DYNAMIC)),
        /// `(set-winders! winders)`: replaces the active dynamic winders of the current task with
        /// `winders` (which must be `'()` or a list of winder objects).
        SetWinders = ("set-winders!", takes(1, DYNAMIC)),
    }
}

/// Static metadata and behavioral properties declared for an intrinsic.
#[derive(Clone, Copy)]
struct Traits {
    /// The required argument count for the intrinsic, or `None` if it accepts a variable number
    /// of arguments.
    arity: Option<u8>,
    /// Bitflags defining intrinsic attributes, such as [`FOLD`], [`DISCARD`], and [`PREDICATE`].
    is: u16,
}

/// Constructs a [`Traits`] descriptor for an intrinsic requiring a fixed `arity` and the specified
/// attribute `is` bitflags (e.g. `FOLD | TRUTHY`, or `0` for no flags).
const fn takes(arity: u8, is: u16) -> Traits {
    Traits { arity: Some(arity), is }
}

/// Constructs a [`Traits`] descriptor for a variadic intrinsic accepting any number of arguments
/// with the given attribute `is` bitflags.
const fn any(is: u16) -> Traits {
    Traits { arity: None, is }
}

/// Flag indicating that invocations with constant arguments can be evaluated at compile time;
/// see [`Intrinsic::is_pure_foldable`].
const FOLD: u16 = 1 << 0;
/// Flag indicating that an unused call can be eliminated as dead code; see
/// [`Intrinsic::is_discardable`]. Unless flagged as [`DYNAMIC`], calls can also be safely
/// reordered.
const DISCARD: u16 = 1 << 1;
/// Flag indicating that calls have no observable side effects and can be evaluated in any
/// order, even if a call may fault on invalid operands; see [`Intrinsic::is_reorderable`].
const REORDER: u16 = 1 << 2;
/// Flag indicating that the intrinsic is a unary type predicate that inspects a value's type and
/// never faults; see [`Intrinsic::is_type_predicate`].
const PREDICATE: u16 = 1 << 3;
/// Flag indicating that normal execution of the intrinsic never returns the boolean false
/// value (`#f`); see [`Intrinsic::is_always_truthy`].
const TRUTHY: u16 = 1 << 4;
/// Flag designating an internal primitive that may only be emitted by the compiler and is
/// inaccessible to user-level code; see [`Intrinsic::is_internal`].
const INTERNAL: u16 = 1 << 5;
/// Flag indicating that the intrinsic inspects or mutates dynamic execution state of the
/// current task (such as continuation marks or winders); see [`Intrinsic::is_dynamic`].
const DYNAMIC: u16 = 1 << 6;
/// Flag indicating that binary applications of the intrinsic are commutative
/// (`f(a, b) == f(b, a)`); see [`Intrinsic::is_commutative_binary`].
const COMMUTE: u16 = 1 << 7;

/// Lookup table mapping each intrinsic to its [`Traits`] descriptor indexed by its discriminant
/// in [`Intrinsic::ALL`], allowing $O(1)$ property queries via a simple memory load.
const TRAITS: [Traits; Intrinsic::ALL.len()] = {
    let mut traits = [any(0); Intrinsic::ALL.len()];
    let mut i = 0;
    while i < traits.len() {
        traits[i] = Intrinsic::ALL[i].data();
        i += 1;
    }
    traits
};

impl Intrinsic {
    /// Returns the required parameter count for the intrinsic, or `None` if it accepts variable
    /// arguments.
    #[inline]
    pub fn arity(self) -> Option<u8> {
        TRAITS[self as usize].arity
    }

    /// Returns whether the intrinsic's trait mask includes all bits specified in `flags`.
    const fn has(self, flags: u16) -> bool {
        TRAITS[self as usize].is & flags == flags
    }

    /// Returns whether invoking this intrinsic on constant arguments is referentially
    /// transparent (causing no side effects, reading no mutable state, and allocating no
    /// identity-bearing mutable objects), permitting compile-time constant folding via
    /// [`Intrinsic::run`].
    pub const fn is_pure_foldable(self) -> bool {
        self.has(FOLD)
    }

    /// Returns whether a direct call with correct arity is guaranteed not to fault and
    /// produces no side effects, enabling dead-code elimination in effect contexts after
    /// evaluating argument expressions.
    pub const fn is_discardable(self) -> bool {
        self.has(DISCARD)
    }

    /// Returns whether a direct call with correct arity has no side effects and depends on no
    /// mutable state, allowing calls to be safely reordered; if an operand is invalid (such as
    /// taking `car` of a non-pair), reordering only affects which fault is triggered first.
    /// Intrinsics that access task state ([`Intrinsic::is_dynamic`]) are not reorderable.
    pub const fn is_reorderable(self) -> bool {
        (self.has(DISCARD) && !self.has(DYNAMIC)) || self.has(REORDER)
    }

    /// Returns whether `self` is a unary type predicate that tests any input value for a
    /// specific type and never faults. If this predicate holds for a value, any disjoint
    /// predicate that it does not [imply](Intrinsic::implies) is guaranteed to evaluate to false.
    pub const fn is_type_predicate(self) -> bool {
        self.has(PREDICATE)
    }

    /// Returns whether the type predicate `self` subsumes `other`, meaning that any value
    /// satisfying `self` necessarily satisfies `other` (for example, `null?` implies `list?`, and
    /// `integer?` implies `number?`).
    pub const fn implies(self, other: Self) -> bool {
        use Intrinsic::*;
        matches!(
            (self, other),
            (IsNull, IsList)
                | (IsContinuation, IsProcedure)
                | (IsIdentifier, IsSyntax)
                | (IsReal | IsRational | IsInteger | IsExactInteger, IsNumber)
                | (IsRational | IsInteger | IsExactInteger, IsReal)
                | (IsInteger | IsExactInteger, IsRational)
                | (IsExactInteger, IsInteger)
        )
    }

    /// Returns whether the type predicates `self` and `other` are mutually exclusive, such that
    /// no value can satisfy both, unless one implies the other or they represent overlapping types
    /// like `list?` and `pair?` (where a proper non-empty list is also a pair).
    pub fn is_disjoint_predicate(self, other: Self) -> bool {
        use Intrinsic::*;
        self != other && !self.implies(other) && !other.implies(self) && !matches!((self, other), (IsList, IsPair) | (IsPair, IsList))
    }

    /// Returns whether successful (non-faulting) execution of this intrinsic is guaranteed to
    /// return a truthy value (any value other than `#f`).
    pub const fn is_always_truthy(self) -> bool {
        self.has(TRUTHY)
    }

    /// Returns whether `self` is an internal compiler-only intrinsic that user-level source
    /// code cannot directly invoke unless explicitly permitted by embedding configuration.
    ///
    /// Internal intrinsics provide primitive building blocks for struct definitions:
    ///
    /// - `make-struct-type`: creates a struct type descriptor.
    /// - `make-struct`, `struct-ref`, and `struct-set!`: provide constructor, accessor, and
    ///   mutator implementations.
    /// - `struct-field` and `struct-fixed-field`: allow optimized unchecked field reads emitted
    ///   when the compiler verifies struct types statically.
    ///
    /// Direct access to these intrinsics is restricted to ensure struct abstraction boundaries
    /// and field safety are preserved.
    pub const fn is_internal(self) -> bool {
        self.has(INTERNAL)
    }

    /// Returns whether the intrinsic inspects or mutates dynamic task execution state (such
    /// as continuation marks, prompt tags, dynamic winders, or task identity). For example,
    /// `(mark-value key default)` retrieves dynamic parameter values.
    ///
    /// - All dynamic intrinsics except `set-winders!` are read-only.
    /// - Within a single execution frame, continuation marks and prompts change only across
    ///   requests, while winders are updated when `dynamic-wind` calls `set-winders!`.
    /// - The compiler will never reorder or constant-fold dynamic intrinsics; only unused
    ///   read-only dynamic calls may be eliminated, never `set-winders!`.
    /// - Invocations via [`Intrinsic::run`] fault with [`Fault::Malformed`] because no task
    ///   context is available.
    pub const fn is_dynamic(self) -> bool {
        self.has(DYNAMIC)
    }

    /// Returns whether binary invocations of `self` satisfy commutativity
    /// (`f(a, b) == f(b, a)`).
    pub const fn is_commutative_binary(self) -> bool {
        self.has(COMMUTE)
    }

    /// Decomposes a composite pair accessor (`car` through `cddddr`) into
    /// `(first_is_car, remaining_cxr)`.
    ///
    /// For example, `Cadr` (`(car (cdr x))`) yields `Some((false, Some(Car)))`, indicating that
    /// `cdr` is evaluated first (`false`), followed by applying `Car` to the result.
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

    /// Evaluates a struct-related intrinsic using the arguments supplied by `arg`.
    #[inline(never)]
    fn structs<'gc>(self, mc: &Mutation<'gc>, arg: impl Fn(usize) -> Value<'gc>, args: usize, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        let boolean = |b: bool| if b { Value::TRUE } else { Value::FALSE };
        Ok(match self {
            Intrinsic::MakeStructType => made(mc, fuel, Value::object(mc, structs::make_type(mc, arg(0), arg(1), arg(2), arg(3), arg(4))?)),
            Intrinsic::MakeStruct if args == 0 => return Err(Fault::Arity),
            Intrinsic::MakeStruct => {
                let kind = structs::type_of(mc, arg(0))?;
                made(mc, fuel, Value::object(mc, structs::make(mc, kind, (1..args).map(&arg))?))
            }
            Intrinsic::StructFields => {
                let names = AnyVector::of(structs::type_of(mc, arg(0))?.names(mc)).ok_or(Fault::Malformed)?;
                fuel.spend(names.len(mc) as u64 / equal::PER_FUEL)?;
                let mut listed = ScratchVec::new(mc);
                for i in 0..names.len(mc) {
                    listed.push(names.get(mc, i).ok_or(Fault::Malformed)?)?;
                }
                made(mc, fuel, Pairs::new(mc).list(&listed)?)
            }
            Intrinsic::IsStruct => boolean(arg(0).downcast::<objects::Struct>(mc).is_some()),
            Intrinsic::IsStructType => boolean(arg(0).downcast::<objects::StructType>(mc).is_some()),
            Intrinsic::IsStructFieldMutable => {
                let kind = structs::type_of(mc, arg(0))?;
                let k = index(arg(1))?;
                if k >= kind.fields(mc) as usize {
                    return Err(Fault::OutOfRange);
                }
                boolean(structs::is_mutable(mc, kind, k))
            }
            Intrinsic::StructType => {
                let made_as = arg(0).downcast::<objects::Struct>(mc).and_then(|s| s.kind(mc)).ok_or(Fault::WrongType)?;
                Value::object(mc, made_as)
            }
            Intrinsic::StructToList => {
                let fields = arg(0).downcast::<objects::Struct>(mc).ok_or(Fault::WrongType)?.items(mc);
                fuel.spend(fields.len() as u64 / equal::PER_FUEL)?;
                let mut listed = ScratchVec::new(mc);
                for i in 0..fields.len() {
                    listed.push(fields.get(i))?;
                }
                made(mc, fuel, Pairs::new(mc).list(&listed)?)
            }
            Intrinsic::StructSet => {
                let kind = structs::type_of(mc, arg(1))?;
                let fields = structs::of(mc, arg(0), kind).ok_or(Fault::WrongType)?.items(mc);
                // An instance of this struct type is guaranteed to have allocated at least as
                // many fields as specified by the type descriptor.
                let k = index(arg(2))?;
                if k >= kind.fields(mc) as usize {
                    return Err(Fault::OutOfRange);
                }
                if !structs::is_mutable(mc, kind, k) {
                    return Err(Fault::Immutable);
                }
                fields.set(mc, k, arg(3));
                Value::VOID
            }
            _ => unreachable!("{self:?} isn't a struct procedure"),
        })
    }

    /// Evaluates advanced character and string manipulation intrinsics on the arguments
    /// retrieved by `arg`.
    #[inline(never)]
    fn text<'gc>(self, mc: &Mutation<'gc>, arg: impl Fn(usize) -> Value<'gc>, args: usize, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        let boolean = |b: bool| if b { Value::TRUE } else { Value::FALSE };
        let strings = Strings::new(mc);
        let string_of = |v: Value<'gc>| strings.string(v).ok_or(Fault::WrongType);
        let char_of = |v: Value<'gc>| v.as_char().ok_or(Fault::WrongType);
        // Deducts VM fuel proportional to the string's character length for a full traversal.
        let spend = |fuel: &mut Fuel, s| fuel.spend(string::len(&strings, s) as u64 / equal::PER_FUEL);
        let made_of = match self {
            Intrinsic::IsCharAlphabetic => return Ok(boolean(char_of(arg(0))?.is_alphabetic())),
            Intrinsic::IsCharNumeric => return Ok(boolean(string::digit_value(char_of(arg(0))?).is_some())),
            Intrinsic::IsCharWhitespace => return Ok(boolean(char_of(arg(0))?.is_whitespace())),
            Intrinsic::IsCharUpperCase => return Ok(boolean(char_of(arg(0))?.is_uppercase())),
            Intrinsic::IsCharLowerCase => return Ok(boolean(char_of(arg(0))?.is_lowercase())),
            Intrinsic::DigitValue => return Ok(string::digit_value(char_of(arg(0))?).map_or(Value::FALSE, |d| fixnum(i64::from(d)))),
            Intrinsic::CharUpcase => return Ok(Value::char(string::upcase_char(char_of(arg(0))?))),
            Intrinsic::CharDowncase => return Ok(Value::char(string::downcase_char(char_of(arg(0))?))),
            Intrinsic::CharFoldcase => return Ok(Value::char(string::foldcase_char(char_of(arg(0))?))),
            Intrinsic::CharCiEq | Intrinsic::CharCiLt | Intrinsic::CharCiGt | Intrinsic::CharCiLe | Intrinsic::CharCiGe if args == 0 => return Err(Fault::Arity),
            Intrinsic::CharCiEq | Intrinsic::CharCiLt | Intrinsic::CharCiGt | Intrinsic::CharCiLe | Intrinsic::CharCiGe => {
                return Ok(boolean(compare_chars(self, (0..args).map(&arg))?));
            }
            Intrinsic::StringCiEq | Intrinsic::StringCiLt | Intrinsic::StringCiGt | Intrinsic::StringCiLe | Intrinsic::StringCiGe if args == 0 => {
                return Err(Fault::Arity);
            }
            Intrinsic::StringCiEq | Intrinsic::StringCiLt | Intrinsic::StringCiGt | Intrinsic::StringCiLe | Intrinsic::StringCiGe => {
                return Ok(boolean(compare_strings(mc, self, (0..args).map(&arg), fuel)?));
            }
            Intrinsic::MakeString if !(1..=2).contains(&args) => return Err(Fault::Arity),
            Intrinsic::MakeString => {
                let n = index(arg(0))?;
                let c = if args == 2 { char_of(arg(1))? } else { ' ' };
                fuel.spend(n as u64 / equal::PER_FUEL)?;
                string::repeat(&strings, c, n)?.value()
            }
            Intrinsic::ListToString => {
                let pairs = Pairs::new(mc);
                let n = pairs.list_len(arg(0)).ok_or(Fault::WrongType)?;
                fuel.spend(n / equal::PER_FUEL)?;
                let mut chars = ScratchVec::new(mc);
                for x in pairs.elements(arg(0)) {
                    chars.push(char_of(x)?)?;
                }
                string::from_chars(&strings, chars.iter().copied())?.value()
            }
            Intrinsic::StringUpcase | Intrinsic::StringDowncase | Intrinsic::StringFoldcase => {
                let s = string_of(arg(0))?;
                spend(fuel, s)?;
                let mapped = match self {
                    Intrinsic::StringUpcase => string::upcase(&strings, s)?,
                    Intrinsic::StringDowncase => string::downcase(&strings, s)?,
                    _ => string::foldcase(&strings, s)?,
                };
                mapped.value()
            }
            Intrinsic::StringToVector | Intrinsic::VectorToString | Intrinsic::StringToUtf8 | Intrinsic::Utf8ToString if !(1..=3).contains(&args) => {
                return Err(Fault::Arity);
            }
            Intrinsic::StringToVector | Intrinsic::StringToUtf8 => {
                let s = string_of(arg(0))?;
                let (start, end) = range(string::len(&strings, s), &arg, args)?;
                let part = string::substring(&strings, s, start, end)?;
                spend(fuel, part)?;
                if self == Intrinsic::StringToVector {
                    let vector = Vectors::new(mc).make(end - start, Value::VOID)?;
                    let items = vector.items(mc);
                    string::chars(&strings, part).enumerate().for_each(|(i, c)| items.set(mc, i, Value::char(c)));
                    vector.value(mc)
                } else {
                    let mut bytes = ScratchVec::new(mc);
                    let mut buffer = [0; 4];
                    for c in string::chars(&strings, part) {
                        for &b in c.encode_utf8(&mut buffer).as_bytes() {
                            bytes.push(b)?;
                        }
                    }
                    Bytevectors::new(mc).from_slice(&bytes)?.value(mc)
                }
            }
            Intrinsic::VectorToString => {
                let vector = AnyVector::of(arg(0)).ok_or(Fault::WrongType)?;
                let (start, end) = range(vector.len(mc), &arg, args)?;
                fuel.spend((end - start) as u64 / equal::PER_FUEL)?;
                let mut chars = ScratchVec::new(mc);
                for i in start..end {
                    chars.push(char_of(vector.get(mc, i).ok_or(Fault::OutOfRange)?)?)?;
                }
                string::from_chars(&strings, chars.iter().copied())?.value()
            }
            Intrinsic::Utf8ToString => {
                let bytes = AnyBytevector::of(arg(0)).ok_or(Fault::WrongType)?;
                let (start, end) = range(bytes.len(mc), &arg, args)?;
                fuel.spend((end - start) as u64 / equal::PER_FUEL)?;
                let part = bytes.bytes(mc, start, end);
                let text = std::str::from_utf8(&part).map_err(|_| Fault::Str(StrError::NotUtf8))?;
                string::from_str(&strings, text)?.value()
            }
            Intrinsic::IsStringPrefix | Intrinsic::IsStringSuffix | Intrinsic::IsStringContains => {
                let (s, part) = (string_of(arg(0))?, string_of(arg(1))?);
                spend(fuel, s)?;
                return Ok(boolean(match self {
                    Intrinsic::IsStringPrefix => string::starts_with(&strings, s, part)?,
                    Intrinsic::IsStringSuffix => string::ends_with(&strings, s, part)?,
                    _ => string::find(&strings, s, part, 0)?.is_some(),
                }));
            }
            Intrinsic::StringFind | Intrinsic::StringFindLast if !(2..=3).contains(&args) => return Err(Fault::Arity),
            Intrinsic::StringFind | Intrinsic::StringFindLast => {
                let (s, part) = (string_of(arg(0))?, string_of(arg(1))?);
                spend(fuel, s)?;
                let found = if self == Intrinsic::StringFind {
                    string::find(&strings, s, part, if args == 3 { index(arg(2))? } else { 0 })?
                } else {
                    string::rfind(&strings, s, part, if args == 3 { index(arg(2))? } else { string::len(&strings, s) })?
                };
                return Ok(found.map_or(Value::FALSE, |i| fixnum(i as i64)));
            }
            Intrinsic::StringSplit => {
                let s = string_of(arg(0))?;
                let sep = if arg(1) == Value::FALSE { None } else { Some(string_of(arg(1))?) };
                spend(fuel, s)?;
                string_split(mc, s, sep, arg(2) != Value::FALSE, arg(3) != Value::FALSE)?
            }
            Intrinsic::StringTrim => {
                let s = string_of(arg(0))?;
                let sep = if arg(1) == Value::FALSE { None } else { Some(string_of(arg(1))?) };
                spend(fuel, s)?;
                let (left, right, repeat) = (arg(2) != Value::FALSE, arg(3) != Value::FALSE, arg(4) != Value::FALSE);
                trimmed(&strings, s, sep, left, right, repeat)?.value()
            }
            Intrinsic::StringReplace => {
                let (s, from, to) = (string_of(arg(0))?, string_of(arg(1))?, string_of(arg(2))?);
                spend(fuel, s)?;
                string_replace(mc, s, from, to, arg(3) != Value::FALSE)?
            }
            _ => unreachable!("{self:?} isn't a text procedure"),
        };
        Ok(made(mc, fuel, made_of))
    }

    /// Evaluates advanced numeric intrinsics (beyond basic arithmetic) on the arguments
    /// retrieved by `arg`.
    #[inline(never)]
    fn numeric<'gc>(self, mc: &Mutation<'gc>, arg: impl Fn(usize) -> Value<'gc>, args: usize, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        let h = Nums::new(mc);
        let boolean = |b: bool| if b { Value::TRUE } else { Value::FALSE };
        let number = |v: Value<'gc>| h.number(v).ok_or(Fault::WrongType);
        let real = |v: Value<'gc>| h.real(v).ok_or(Fault::WrongType);
        let made_of = match self {
            Intrinsic::IsNumber => return Ok(boolean(h.number(arg(0)).is_some())),
            Intrinsic::IsReal => return Ok(boolean(h.real(arg(0)).is_some())),
            Intrinsic::IsRational => {
                let finite = |x| !matches!(h.real_view(x), RealView::Flonum(f) if !f.is_finite());
                return Ok(boolean(h.real(arg(0)).is_some_and(finite)));
            }
            Intrinsic::IsInteger => return Ok(boolean(h.real(arg(0)).is_some_and(|x| real::is_integer(&h, x)))),
            Intrinsic::IsExactInteger => return Ok(boolean(h.integer(arg(0)).is_some())),
            Intrinsic::IsExact | Intrinsic::IsInexact => return Ok(boolean(complex::is_exact(&h, number(arg(0))?) == (self == Intrinsic::IsExact))),
            Intrinsic::IsNan | Intrinsic::IsInfinite | Intrinsic::IsFinite => {
                let parts = match h.complex_view(number(arg(0))?) {
                    ComplexView::Real(x) => [x, x],
                    ComplexView::Complex { re, im } => [re, im],
                };
                let floats = parts.map(|x| match h.real_view(x) {
                    RealView::Flonum(f) => f,
                    RealView::Exact(_) => 0.0,
                });
                return Ok(boolean(match self {
                    Intrinsic::IsNan => floats.iter().any(|f| f.is_nan()),
                    Intrinsic::IsInfinite => floats.iter().any(|f| f.is_infinite()),
                    _ => floats.iter().all(|f| f.is_finite()),
                }));
            }
            Intrinsic::IsZero => {
                return Ok(boolean(match h.complex_view(number(arg(0))?) {
                    ComplexView::Real(x) => real::sign(&h, x) == Some(Ordering::Equal),
                    ComplexView::Complex { .. } => false,
                }));
            }
            Intrinsic::IsPositive | Intrinsic::IsNegative => {
                let want = if self == Intrinsic::IsPositive { Ordering::Greater } else { Ordering::Less };
                return Ok(boolean(real::sign(&h, real(arg(0))?) == Some(want)));
            }
            Intrinsic::IsOdd | Intrinsic::IsEven => {
                let even = match arg(0).as_fixnum() {
                    Some(n) => n % 2 == 0,
                    None => int::is_even(&h, integral(mc, &h, arg(0))?.0),
                };
                return Ok(boolean(even == (self == Intrinsic::IsEven)));
            }
            Intrinsic::Max | Intrinsic::Min if args == 0 => return Err(Fault::Arity),
            Intrinsic::Max | Intrinsic::Min => {
                let max = self == Intrinsic::Max;
                let mut acc = real(arg(0))?;
                for i in 1..args {
                    let x = real(arg(i))?;
                    acc = match (acc.value().as_fixnum(), x.value().as_fixnum()) {
                        (Some(a), Some(b)) => if (b > a) == max { x } else { acc },
                        _ if max => real::max(&h, acc, x)?,
                        _ => real::min(&h, acc, x)?,
                    };
                }
                h.of_real(acc)
            }
            // Because fixnums use strictly fewer bits than an i64, `n.abs()` cannot overflow
            // 64-bit integer limits, although the absolute value may exceed the fixnum range and
            // require bignum promotion.
            Intrinsic::Abs => match arg(0).as_fixnum().and_then(|n| Value::fixnum(n.abs())) {
                Some(n) => return Ok(n),
                None => h.of_real(real::abs(&h, real(arg(0))?)?),
            },
            Intrinsic::Gcd | Intrinsic::Lcm => {
                let gcd = self == Intrinsic::Gcd;
                let (mut acc, mut exact) = (int::from_i64(&h, if gcd { 0 } else { 1 })?, true);
                for i in 0..args {
                    let (n, is_exact) = integral(mc, &h, arg(i))?;
                    exact &= is_exact;
                    let words = int::integer_length(&h, acc).max(int::integer_length(&h, n)) / 64;
                    fuel.spend(words.saturating_mul(words) / equal::PER_FUEL)?;
                    acc = if gcd { int::gcd(&h, acc, n)? } else { int::lcm(&h, acc, n)? };
                }
                let acc = h.of_rational(h.of_int(acc));
                h.of_real(if exact { acc } else { real::inexact(&h, acc)? })
            }
            Intrinsic::Numerator => h.of_real(real::numerator(&h, real(arg(0))?)?),
            Intrinsic::Denominator => h.of_real(real::denominator(&h, real(arg(0))?)?),
            Intrinsic::Floor | Intrinsic::Ceiling | Intrinsic::Truncate | Intrinsic::Round => {
                if arg(0).is_fixnum() {
                    return Ok(arg(0));
                }
                let x = real(arg(0))?;
                charge_squared(&h, fuel, h.of_real(x))?;
                let mode = match self {
                    Intrinsic::Floor => Round::Floor,
                    Intrinsic::Ceiling => Round::Ceiling,
                    Intrinsic::Truncate => Round::Truncate,
                    _ => Round::Nearest,
                };
                h.of_real(real::round(&h, x, mode)?)
            }
            Intrinsic::IntegerSqrt => {
                let n = h.integer(arg(0)).ok_or(Fault::WrongType)?;
                if int::sign(&h, n) == Ordering::Less {
                    return Err(Fault::OutOfRange);
                }
                charge_squared(&h, fuel, number(arg(0))?)?;
                h.of_real(h.of_rational(h.of_int(int::isqrt(&h, n)?)))
            }
            Intrinsic::Exact => complex::exact(&h, number(arg(0))?)?,
            Intrinsic::Inexact => complex::inexact(&h, number(arg(0))?)?,
            Intrinsic::StringToNumber if !(1..=2).contains(&args) => return Err(Fault::Arity),
            Intrinsic::StringToNumber => {
                let strings = Strings::new(mc);
                let s = strings.string(arg(0)).ok_or(Fault::WrongType)?;
                let radix = if args == 2 { arg(1).as_fixnum().ok_or(Fault::WrongType)? } else { 10 };
                let radix = [2, 8, 10, 16].into_iter().find(|&r| r == radix).ok_or(Fault::OutOfRange)? as u32;
                // Parsing a multi-precision integer has approximately quadratic computational
                // complexity relative to its digit count (up to 4 bits per digit).
                let len = string::len(&strings, s);
                let words = (len as u64).saturating_mul(4) / 64;
                fuel.spend(words.saturating_mul(words) / equal::PER_FUEL)?;
                mc.ensure(len.saturating_mul(4))?;
                let text: String = string::chars(&strings, s).collect();
                match literal::parse_in(&h, &text, radix)? {
                    Some(z) => z,
                    None => return Ok(Value::FALSE),
                }
            }
            Intrinsic::Exp => complex::exp(&h, number(arg(0))?)?,
            Intrinsic::Log if !(1..=2).contains(&args) => return Err(Fault::Arity),
            Intrinsic::Log if args == 2 => complex::log_base(&h, number(arg(0))?, number(arg(1))?)?,
            Intrinsic::Log => complex::log(&h, number(arg(0))?)?,
            Intrinsic::Sin => complex::sin(&h, number(arg(0))?)?,
            Intrinsic::Cos => complex::cos(&h, number(arg(0))?)?,
            Intrinsic::Tan => complex::tan(&h, number(arg(0))?)?,
            Intrinsic::Asin => complex::asin(&h, number(arg(0))?)?,
            Intrinsic::Acos => complex::acos(&h, number(arg(0))?)?,
            Intrinsic::Atan if !(1..=2).contains(&args) => return Err(Fault::Arity),
            Intrinsic::Atan if args == 2 => h.of_real(complex::atan2(&h, real(arg(0))?, real(arg(1))?)?),
            Intrinsic::Atan => complex::atan(&h, number(arg(0))?)?,
            Intrinsic::Sqrt => {
                let z = number(arg(0))?;
                charge_squared(&h, fuel, z)?;
                complex::sqrt(&h, z)?
            }
            Intrinsic::MakeRectangular => complex::rectangular(&h, real(arg(0))?, real(arg(1))?)?,
            Intrinsic::MakePolar => complex::polar(&h, real(arg(0))?, real(arg(1))?)?,
            Intrinsic::RealPart => h.of_real(complex::real_part(&h, number(arg(0))?)),
            Intrinsic::ImagPart => h.of_real(complex::imag_part(&h, number(arg(0))?)?),
            Intrinsic::Magnitude => h.of_real(complex::magnitude(&h, number(arg(0))?)?),
            Intrinsic::Angle => h.of_real(complex::angle(&h, number(arg(0))?)?),
            _ => unreachable!("{self:?} isn't numeric"),
        };
        Ok(made(mc, fuel, made_of.value()))
    }

    /// Evaluates the intrinsic directly on slice `args` without an active VM frame or task
    /// context, intended for compile-time constant folding. Callers are responsible for
    /// verifying whether the invocation is pure and foldable (e.g. operations creating or
    /// mutating boxes cannot be folded). Invoking dynamic intrinsics that require task state
    /// results in a [`Fault::Malformed`].
    #[inline]
    pub fn run<'gc>(self, mc: &Mutation<'gc>, args: &[Value<'gc>], fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        self.run_in(mc, None, args, fuel)
    }

    /// Evaluates the intrinsic on slice `args` within the context of the optionally provided `task`.
    #[inline]
    pub(crate) fn run_in<'gc>(self, mc: &Mutation<'gc>, task: Option<Gc<'gc, Task>>, args: &[Value<'gc>], fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        if self.arity().is_some_and(|arity| usize::from(arity) != args.len()) {
            return Err(Fault::Arity);
        }
        self.apply(mc, task, |i| args[i], args.len(), fuel)
    }

    /// Executes the intrinsic within execution context `cx`, reading `args` registers starting
    /// from frame register `base`. The caller must have verified that the registers reside within
    /// the frame and match the required arity. Deducts VM fuel for computationally intensive
    /// operations.
    #[inline(always)]
    pub(crate) fn exec<'gc>(self, cx: &mut Context<'_, 'gc>, base: u8, args: u8) -> Result<Value<'gc>, Fault> {
        let frame = cx.frame;
        self.apply(cx.mc, Some(cx.task), |i| frame.get(base + i as u8), usize::from(args), &mut cx.fuel)
    }

    /// Executes a unary intrinsic on operand register `a`, assuming the caller has verified
    /// the intrinsic accepts exactly one argument.
    #[inline(always)]
    pub(crate) fn exec1<'gc>(self, cx: &mut Context<'_, 'gc>, a: u8) -> Result<Value<'gc>, Fault> {
        let frame = cx.frame;
        self.apply(cx.mc, Some(cx.task), |_| frame.get(a), 1, &mut cx.fuel)
    }

    /// Executes a binary intrinsic on operand registers `a` and `b`, assuming the caller
    /// has verified the intrinsic accepts exactly two arguments.
    #[inline(always)]
    pub(crate) fn exec2<'gc>(self, cx: &mut Context<'_, 'gc>, a: u8, b: u8) -> Result<Value<'gc>, Fault> {
        let frame = cx.frame;
        self.apply(cx.mc, Some(cx.task), |i| frame.get(if i == 0 { a } else { b }), 2, &mut cx.fuel)
    }

    /// Executes a ternary intrinsic on operand registers `a`, `b`, and `c`, assuming the
    /// caller has verified the intrinsic accepts exactly three arguments.
    #[inline(always)]
    pub(crate) fn exec3<'gc>(self, cx: &mut Context<'_, 'gc>, a: u8, b: u8, c: u8) -> Result<Value<'gc>, Fault> {
        let frame = cx.frame;
        self.apply(cx.mc, Some(cx.task), |i| frame.get([a, b, c][i]), 3, &mut cx.fuel)
    }

    /// Evaluates less common dynamic intrinsics that inspect or mutate the running `task`'s
    /// state.
    #[inline(never)]
    fn dynamic<'gc>(self, mc: &Mutation<'gc>, task: Gc<'gc, Task>, arg: impl Fn(usize) -> Value<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        if self == Intrinsic::FrameMarks {
            let tag = if arg(2) == Value::FALSE { None } else { Some(prompts::tag_of(mc, arg(2))?) };
            return Ok(made(mc, fuel, prompts::part_marks(mc, task, arg(0), arg(1), tag)?));
        }
        let winders = arg(0);
        if winders != Value::NIL && !Pair::of(winders).is_some_and(|cell| cell.head(mc).downcast::<objects::Winder>(mc).is_some()) {
            return Err(Fault::WrongType);
        }
        task.set_winders(mc, winders);
        Ok(Value::VOID)
    }

    /// Evaluates the intrinsic on `args` operands accessed via the `arg` closure, passing the
    /// optional running `task` context if present.
    #[inline(always)]
    fn apply<'gc>(self, mc: &Mutation<'gc>, task: Option<Gc<'gc, Task>>, arg: impl Fn(usize) -> Value<'gc>, args: usize, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        let boolean = |b: bool| if b { Value::TRUE } else { Value::FALSE };
        Ok(match self {
            Intrinsic::MarkValue => prompts::mark(mc, task.ok_or(Fault::Malformed)?, arg(0), arg(1))?,
            Intrinsic::FrameMark => prompts::frame_mark(mc, task.ok_or(Fault::Malformed)?, arg(0), arg(1))?,
            Intrinsic::Running => Value::object(mc, task.ok_or(Fault::Malformed)?),
            Intrinsic::Winders => task.ok_or(Fault::Malformed)?.winders(mc),
            Intrinsic::FrameMarks | Intrinsic::SetWinders => self.dynamic(mc, task.ok_or(Fault::Malformed)?, arg, fuel)?,
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
                boolean(compare_strings(mc, self, (0..args).map(&arg), fuel)?)
            }
            Intrinsic::StringJoin if !(1..=2).contains(&args) => return Err(Fault::Arity),
            Intrinsic::StringJoin => string_join(mc, arg(0), (args == 2).then(|| arg(1)), fuel)?,
            Intrinsic::IsChar => boolean(arg(0).as_char().is_some()),
            Intrinsic::CharToInteger => fixnum(i64::from(u32::from(arg(0).as_char().ok_or(Fault::WrongType)?))),
            Intrinsic::IntegerToChar => {
                let n = arg(0).as_fixnum().ok_or_else(|| not_fixnum(mc, arg(0)))?;
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
                // Formatting a multi-precision integer as text has approximately quadratic
                // computational complexity relative to its digit count.
                let words = exact_bits(&h, z) / 64;
                fuel.spend(words.saturating_mul(words) / equal::PER_FUEL)?;
                let text = complex::to_string(&h, z, radix)?;
                made(mc, fuel, string::from_str(&Strings::new(mc), &text)?.value())
            }
            Intrinsic::Quotient | Intrinsic::Remainder | Intrinsic::Modulo | Intrinsic::FloorQuotient => divide(mc, fuel, self, arg(0), arg(1))?,
            Intrinsic::IsNumber
            | Intrinsic::IsReal
            | Intrinsic::IsRational
            | Intrinsic::IsInteger
            | Intrinsic::IsExactInteger
            | Intrinsic::IsExact
            | Intrinsic::IsInexact
            | Intrinsic::IsNan
            | Intrinsic::IsInfinite
            | Intrinsic::IsFinite
            | Intrinsic::IsZero
            | Intrinsic::IsPositive
            | Intrinsic::IsNegative
            | Intrinsic::IsOdd
            | Intrinsic::IsEven
            | Intrinsic::Max
            | Intrinsic::Min
            | Intrinsic::Abs
            | Intrinsic::Gcd
            | Intrinsic::Lcm
            | Intrinsic::Numerator
            | Intrinsic::Denominator
            | Intrinsic::Floor
            | Intrinsic::Ceiling
            | Intrinsic::Truncate
            | Intrinsic::Round
            | Intrinsic::IntegerSqrt
            | Intrinsic::Exact
            | Intrinsic::Inexact
            | Intrinsic::StringToNumber
            | Intrinsic::Exp
            | Intrinsic::Log
            | Intrinsic::Sin
            | Intrinsic::Cos
            | Intrinsic::Tan
            | Intrinsic::Asin
            | Intrinsic::Acos
            | Intrinsic::Atan
            | Intrinsic::Sqrt
            | Intrinsic::MakeRectangular
            | Intrinsic::MakePolar
            | Intrinsic::RealPart
            | Intrinsic::ImagPart
            | Intrinsic::Magnitude
            | Intrinsic::Angle => self.numeric(mc, arg, args, fuel)?,
            Intrinsic::IsStructDerivedFrom => boolean(structs::of(mc, arg(0), structs::type_of(mc, arg(1))?).is_some()),
            Intrinsic::StructRef => structs::field_of(mc, arg(0), arg(1), index(arg(2))?)?,
            Intrinsic::StructField | Intrinsic::StructFixedField => structs::field(mc, arg(0), index(arg(1))?)?,
            Intrinsic::MakeStructType
            | Intrinsic::MakeStruct
            | Intrinsic::IsStruct
            | Intrinsic::IsStructType
            | Intrinsic::StructSet
            | Intrinsic::StructFields
            | Intrinsic::IsStructFieldMutable
            | Intrinsic::StructType
            | Intrinsic::StructToList => {
                self.structs(mc, arg, args, fuel)?
            }
            Intrinsic::IsCharAlphabetic
            | Intrinsic::IsCharNumeric
            | Intrinsic::IsCharWhitespace
            | Intrinsic::IsCharUpperCase
            | Intrinsic::IsCharLowerCase
            | Intrinsic::DigitValue
            | Intrinsic::CharUpcase
            | Intrinsic::CharDowncase
            | Intrinsic::CharFoldcase
            | Intrinsic::CharCiEq
            | Intrinsic::CharCiLt
            | Intrinsic::CharCiGt
            | Intrinsic::CharCiLe
            | Intrinsic::CharCiGe
            | Intrinsic::MakeString
            | Intrinsic::ListToString
            | Intrinsic::StringUpcase
            | Intrinsic::StringDowncase
            | Intrinsic::StringFoldcase
            | Intrinsic::StringCiEq
            | Intrinsic::StringCiLt
            | Intrinsic::StringCiGt
            | Intrinsic::StringCiLe
            | Intrinsic::StringCiGe
            | Intrinsic::StringToVector
            | Intrinsic::VectorToString
            | Intrinsic::StringToUtf8
            | Intrinsic::Utf8ToString
            | Intrinsic::IsStringPrefix
            | Intrinsic::IsStringSuffix
            | Intrinsic::IsStringContains
            | Intrinsic::StringFind
            | Intrinsic::StringFindLast
            | Intrinsic::StringSplit
            | Intrinsic::StringTrim
            | Intrinsic::StringReplace => self.text(mc, arg, args, fuel)?,
            Intrinsic::BitwiseAnd => bitwise(mc, fuel, -1, (0..args).map(&arg), |a, b| a & b, |h, a, b| int::bitwise_and(h, a, b))?,
            Intrinsic::BitwiseIor => bitwise(mc, fuel, 0, (0..args).map(&arg), |a, b| a | b, |h, a, b| int::bitwise_or(h, a, b))?,
            Intrinsic::BitwiseXor => bitwise(mc, fuel, 0, (0..args).map(&arg), |a, b| a ^ b, |h, a, b| int::bitwise_xor(h, a, b))?,
            Intrinsic::BitwiseNot | Intrinsic::ArithmeticShift | Intrinsic::BitField | Intrinsic::BitFieldReplace => {
                let h = Nums::new(mc);
                let n = h.integer(arg(0)).ok_or(Fault::WrongType)?;
                let (len, negative) = (int::integer_length(&h, n), int::sign(&h, n) == Ordering::Less);
                let made_of = match self {
                    Intrinsic::BitwiseNot => int::bitwise_not(&h, n)?,
                    Intrinsic::ArithmeticShift => {
                        let count = arg(1).as_fixnum().ok_or(Fault::WrongType)?;
                        // Shifting zero produces zero without allocating additional bits, whereas
                        // left-shifting negative one increases its two's complement bit width.
                        if n.value() != fixnum(0) {
                            charge_bits(mc, fuel, len.saturating_add(count.max(0) as u64))?;
                        }
                        int::arithmetic_shift(&h, n, count)?
                    }
                    Intrinsic::BitField => {
                        let (start, end) = bit_range(arg(1), arg(2))?;
                        charge_bits(mc, fuel, if negative { end - start } else { len.saturating_sub(start).min(end - start) })?;
                        int::bit_field(&h, n, start, end)?
                    }
                    _ => {
                        let (source, (start, end)) = (h.integer(arg(1)).ok_or(Fault::WrongType)?, bit_range(arg(2), arg(3))?);
                        let field = if int::sign(&h, source) == Ordering::Less { end - start } else { int::integer_length(&h, source).min(end - start) };
                        let bits = if negative { end } else if field == 0 { len } else { len.max(start + field) };
                        charge_bits(mc, fuel, bits)?;
                        int::bit_field_replace(&h, n, source, start, end)?
                    }
                };
                made(mc, fuel, made_of.value())
            }
            Intrinsic::IntegerLength | Intrinsic::BitCount => {
                let h = Nums::new(mc);
                let n = h.integer(arg(0)).ok_or(Fault::WrongType)?;
                let bits = if self == Intrinsic::IntegerLength {
                    int::integer_length(&h, n)
                } else {
                    fuel.spend(int::integer_length(&h, n) / 64 / equal::PER_FUEL)?;
                    int::bit_count(&h, n)?
                };
                fixnum(i64::try_from(bits).map_err(|_| Fault::OutOfRange)?)
            }
            Intrinsic::IsBitSet => {
                let h = Nums::new(mc);
                let n = h.integer(arg(1)).ok_or(Fault::WrongType)?;
                // Testing bit flags on a negative multi-precision integer may require scanning
                // past its least significant set bit, traversing multiple words.
                if int::sign(&h, n) == Ordering::Less {
                    fuel.spend(int::integer_length(&h, n) / 64 / equal::PER_FUEL)?;
                }
                boolean(int::bit_set(&h, n, index(arg(0))? as u64))
            }
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
                    2 => byte(mc, arg(1))?,
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
                let (big, (size, signed)) = (big_endian(arg(2))?, int_kind(arg(3))?);
                let n = bytes.get_uint(mc, index(arg(1))?, size).ok_or(Fault::OutOfRange)?;
                let unused = 64 - size as u32 * 8;
                let n = if big { n.swap_bytes() >> unused } else { n };
                let h = Nums::new(mc);
                if signed {
                    let n = ((n << unused) as i64) >> unused;
                    match Value::fixnum(n) {
                        Some(n) => n,
                        None => made(mc, fuel, int::from_i64(&h, n)?.value()),
                    }
                } else {
                    match i64::try_from(n).ok().and_then(Value::fixnum) {
                        Some(n) => n,
                        None => made(mc, fuel, int::from_u64(&h, n)?.value()),
                    }
                }
            }
            Intrinsic::BytevectorSet => {
                let bytes = AnyBytevector::of(arg(0)).ok_or(Fault::WrongType)?;
                let h = Nums::new(mc);
                let n = h.integer(arg(2)).ok_or(Fault::WrongType)?;
                let (big, (size, signed)) = (big_endian(arg(3))?, int_kind(arg(4))?);
                let unused = 64 - size as u32 * 8;
                let n = if signed {
                    int::to_i64(&h, n).filter(|&n| (n << unused) >> unused == n).map(|n| n as u64)
                } else {
                    int::to_u64(&h, n).filter(|&n| n <= u64::MAX >> unused)
                };
                let n = n.ok_or(Fault::OutOfRange)?;
                let AnyBytevector::Mutable(bytes) = bytes else { return Err(Fault::Immutable) };
                let n = if big { (n << unused).swap_bytes() } else { n };
                if !bytes.set_uint(mc, index(arg(1))?, size, n) {
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
                made(mc, fuel, Value::object(mc, Condition::new(mc, mc.frozen(Failure { fault, operation: None })?, arg(0), irritants, Value::FALSE)?))
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
                        let words = c.failure(mc).ok_or(Fault::Malformed)?.fault.message();
                        made(mc, fuel, string::from_str(&Strings::new(mc), words)?.value())
                    }
                    message => message,
                }
            }
            Intrinsic::ErrorObjectIrritants => arg(0).downcast::<Condition>(mc).ok_or(Fault::WrongType)?.irritants(mc),
            Intrinsic::ErrorObjectWho => {
                let c = arg(0).downcast::<Condition>(mc).ok_or(Fault::WrongType)?;
                made(mc, fuel, crate::report::who(mc, c)?)
            }
            Intrinsic::ErrorObjectTraceback => {
                let c = arg(0).downcast::<Condition>(mc).ok_or(Fault::WrongType)?;
                made(mc, fuel, crate::report::traceback(mc, c)?)
            }
            Intrinsic::ErrorObjectKind => {
                let c = arg(0).downcast::<Condition>(mc).ok_or(Fault::WrongType)?;
                let name = Fault::KINDS[c.failure(mc).ok_or(Fault::Malformed)?.fault.kind()];
                made(mc, fuel, Symbols::of_arena(mc)?.intern_str(&Strings::new(mc), name)?.value(mc))
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

/// Returns `Some(a / b)` if both `a` and `b` are fixnums, division by zero does not occur, and
/// the quotient is exactly representable as a fixnum; otherwise returns `None`.
fn fixnum_div<'gc>(a: Value<'gc>, b: Value<'gc>) -> Option<Value<'gc>> {
    let (a, b) = (a.as_fixnum()?, b.as_fixnum()?);
    (b != 0 && a % b == 0).then(|| a / b).and_then(Value::fixnum)
}

/// Folds `first` across elements of `rest`, using the optimized `fast` closure while operands
/// and intermediate results remain fixnums, falling back to `generic` operations over the full
/// numeric tower when fixnums overflow or operands require multi-precision or floating-point
/// representations.
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

/// Applies bitwise operation `op` across `first` and all elements of `rest` (requiring exact
/// integers), executing unboxed fixnum operations while values remain fixnums and falling back to
/// arbitrary-precision integers as necessary.
fn bitwise<'gc>(
    mc: &Mutation<'gc>,
    fuel: &mut Fuel,
    first: i64,
    rest: impl Iterator<Item = Value<'gc>>,
    fast: fn(i64, i64) -> i64,
    generic: impl Fn(&Nums<'_, 'gc>, Integer<'gc>, Integer<'gc>) -> Result<Integer<'gc>, Error>,
) -> Result<Value<'gc>, Fault> {
    let h = Nums::new(mc);
    let mut acc = fixnum(first);
    for x in rest {
        acc = match (acc.as_fixnum(), x.as_fixnum()) {
            // Bitwise operations on two fixnum values are guaranteed to produce a result that
            // fits within a fixnum.
            (Some(a), Some(b)) => fixnum(fast(a, b)),
            _ => {
                let (a, b) = (h.integer(acc).ok_or(Fault::WrongType)?, h.integer(x).ok_or(Fault::WrongType)?);
                made(mc, fuel, generic(&h, a, b)?.value())
            }
        };
    }
    Ok(acc)
}

/// Deducts fuel and reserves memory proportional to creating an integer of approximately `bits`
/// bits, preventing unbounded allocation during operations like arithmetic shifts that expand
/// numbers significantly.
fn charge_bits(mc: &Mutation<'_>, fuel: &mut Fuel, bits: u64) -> Result<(), Fault> {
    let words = bits / 64;
    if words < equal::PER_FUEL {
        return Ok(());
    }
    mc.ensure(usize::try_from(words.saturating_mul(8)).unwrap_or(usize::MAX))?;
    fuel.spend(words / equal::PER_FUEL)
}

/// Extracts and validates bit indices `(start, end)`, ensuring `start <= end` and returning
/// them as `(u64, u64)` or faulting on invalid bounds.
fn bit_range(start: Value<'_>, end: Value<'_>) -> Result<(u64, u64), Fault> {
    let (start, end) = (index(start)? as u64, index(end)? as u64);
    if end < start {
        return Err(Fault::OutOfRange);
    }
    Ok((start, end))
}

/// Parses a bytevector endianness indicator value into a boolean (`true` for big-endian `#t`,
/// `false` for little-endian `#f`).
fn big_endian(v: Value<'_>) -> Result<bool, Fault> {
    if v == Value::TRUE || v == Value::FALSE { Ok(v == Value::TRUE) } else { Err(Fault::WrongType) }
}

/// Parses a bytevector integer size and signedness descriptor, returning the byte width (1 to
/// 8) and a boolean indicating whether the integer is signed.
fn int_kind(v: Value<'_>) -> Result<(usize, bool), Fault> {
    let kind = v.as_fixnum().ok_or(Fault::WrongType)?;
    let size = kind.unsigned_abs() as usize;
    if !(1..=8).contains(&size) {
        return Err(Fault::OutOfRange);
    }
    Ok((size, kind < 0))
}

/// Computes `quotient`, `remainder`, `modulo`, or `floor-quotient` for `n` and `m`, using fast
/// in-place fixnum arithmetic when both operands are fixnums and non-zero, and falling back to
/// arbitrary-precision arithmetic otherwise.
fn divide<'gc>(mc: &Mutation<'gc>, fuel: &mut Fuel, op: Intrinsic, n: Value<'gc>, m: Value<'gc>) -> Result<Value<'gc>, Fault> {
    if let (Some(a), Some(b)) = (n.as_fixnum(), m.as_fixnum())
        && b != 0
    {
        // Because fixnums use strictly fewer bits than an i64, operations cannot trigger 64-bit
        // signed integer overflow (such as `i64::MIN / -1`).
        let fast = match op {
            Intrinsic::Quotient => a / b,
            Intrinsic::Remainder => a % b,
            Intrinsic::FloorQuotient => {
                let q = a / b;
                if a % b != 0 && (a < 0) != (b < 0) { q - 1 } else { q }
            }
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
        Intrinsic::FloorQuotient => real::floor_quotient(&h, x, y),
        _ => real::modulo(&h, x, y),
    };
    Ok(made(mc, fuel, generic?.value()))
}

/// Formats fixnum `n` in the given `radix` (2, 8, 10, or 16) by writing characters into a
/// stack-allocated buffer and constructing a Scheme string.
fn fixnum_to_string<'gc>(mc: &Mutation<'gc>, n: i64, radix: u32) -> Result<Value<'gc>, Fault> {
    // Buffer size of 65 bytes accommodates the worst-case representation: 64 base-2 digits
    // plus an optional minus sign.
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

/// Returns whether value `v` is callable as a procedure (a closure, a continuation, or a
/// keyword procedure).
fn is_procedure<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> bool {
    v.downcast::<objects::Closure>(mc).is_some()
        || v.downcast::<objects::Continuation>(mc).is_some()
        || v.downcast::<objects::KeywordProcedure>(mc).is_some()
}

/// Returns the total significant bit count of exact parts in number `z` beyond the initial
/// bit, such that 0, 1, and -1 yield zero bits.
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

/// Deducts VM fuel proportional to the square of the bit-length of the exact components of `z`,
/// modeling the quadratic complexity of multi-precision division and multiplication.
fn charge_squared<'gc>(h: &Nums<'_, 'gc>, fuel: &mut Fuel, z: Number<'gc>) -> Result<(), Fault> {
    let words = exact_bits(h, z) / 64;
    fuel.spend(words.saturating_mul(words) / equal::PER_FUEL)
}

/// Extracts `v` as an exact integer and returns a tuple containing the integer and a boolean
/// flag that is `true` if `v` was already an exact integer, or `false` if it was an inexact
/// floating-point number with an integral value.
fn integral<'gc>(mc: &Mutation<'gc>, h: &Nums<'_, 'gc>, v: Value<'gc>) -> Result<(Integer<'gc>, bool), Fault> {
    if let Some(n) = h.integer(v) {
        return Ok((n, true));
    }
    match v.as_flonum(mc) {
        Some(f) if f.is_finite() && f.fract() == 0.0 => Ok((int::from_integral_f64(h, f)?, false)),
        _ if h.number(v).is_some() => Err(Fault::Num(NumError::NotInteger)),
        _ => Err(Fault::WrongType),
    }
}

/// Verifies that all elements in `xs` are characters and evaluates whether relational operator
/// `op` holds pairwise across consecutive character elements.
fn compare_chars<'gc>(op: Intrinsic, xs: impl Iterator<Item = Value<'gc>>) -> Result<bool, Fault> {
    let (mut before, mut so_far) = (None, true);
    for x in xs {
        let x = x.as_char().ok_or(Fault::WrongType)?;
        let x = if matches!(op, Intrinsic::CharCiEq | Intrinsic::CharCiLt | Intrinsic::CharCiGt | Intrinsic::CharCiLe | Intrinsic::CharCiGe) {
            string::foldcase_char(x)
        } else {
            x
        };
        if let Some(b) = before {
            so_far &= match op {
                Intrinsic::CharEq | Intrinsic::CharCiEq => b == x,
                Intrinsic::CharLt | Intrinsic::CharCiLt => b < x,
                Intrinsic::CharGt | Intrinsic::CharCiGt => b > x,
                Intrinsic::CharLe | Intrinsic::CharCiLe => b <= x,
                _ => b >= x,
            };
        }
        before = Some(x);
    }
    Ok(so_far)
}

/// Resolves an index range `[start, end)` from optional start (`arg(1)`) and end (`arg(2)`)
/// arguments for a sequence of length `len`, defaulting to `0` and `len` respectively and
/// ensuring `0 <= start <= end <= len`.
fn range<'gc>(len: usize, arg: &impl Fn(usize) -> Value<'gc>, args: usize) -> Result<(usize, usize), Fault> {
    let start = if args > 1 { index(arg(1))? } else { 0 };
    let end = if args > 2 { index(arg(2))? } else { len };
    if start > end || end > len {
        return Err(Fault::OutOfRange);
    }
    Ok((start, end))
}

/// Strips occurrences of `sep` (or whitespace if `sep` is `None`) from the start (`left`) and/or
/// end (`right`) of string `s`, removing either a single instance or repeated contiguous
/// instances if `repeat` is true.
fn trimmed<'gc>(strings: &Strings<'_, 'gc>, s: Str<'gc>, sep: Option<Str<'gc>>, left: bool, right: bool, repeat: bool) -> Result<Str<'gc>, Fault> {
    let Some(sep) = sep else {
        return Ok(match (left, right) {
            (true, true) => string::trim(strings, s)?,
            (true, false) => string::trim_start(strings, s)?,
            (false, true) => string::trim_end(strings, s)?,
            (false, false) => s,
        });
    };
    let (n, m) = (string::len(strings, s), string::len(strings, sep));
    if m == 0 {
        return Ok(s);
    }
    let at = |i: usize| -> Result<bool, Fault> { Ok(string::equal(strings, string::substring(strings, s, i, i + m)?, sep)?) };
    let (mut start, mut end) = (0, n);
    while left && start + m <= end && at(start)? {
        start += m;
        if !repeat {
            break;
        }
    }
    while right && end >= start + m && at(end - m)? {
        end -= m;
        if !repeat {
            break;
        }
    }
    Ok(if (start, end) == (0, n) { s } else { string::substring(strings, s, start, end)? })
}

/// Implements Racket-compatible `(string-split s [sep] #:trim? trim #:repeat? repeat)`, splitting
/// `s` by `sep` (or runs of whitespace if `sep` is `None`), with optional boundary trimming and
/// collapsing of consecutive delimiters.
fn string_split<'gc>(mc: &Mutation<'gc>, s: Str<'gc>, sep: Option<Str<'gc>>, trim: bool, repeat: bool) -> Result<Value<'gc>, Fault> {
    let strings = Strings::new(mc);
    let mut pieces = ScratchVec::new(mc);
    match sep {
        None if trim => {
            for piece in string::split_whitespace(&strings, s) {
                pieces.push(piece?.value())?;
            }
        }
        // When trimming is disabled, boundary whitespace produces an empty string segment at
        // the beginning or end of the output.
        None => {
            let (mut start, mut space) = (0, false);
            for (i, c) in string::chars(&strings, s).enumerate() {
                if c.is_whitespace() && !space {
                    pieces.push(string::substring(&strings, s, start, i)?.value())?;
                } else if !c.is_whitespace() && space {
                    start = i;
                }
                space = c.is_whitespace();
            }
            let n = string::len(&strings, s);
            pieces.push(string::substring(&strings, s, if space { n } else { start }, n)?.value())?;
        }
        Some(sep) => {
            let s = if trim { trimmed(&strings, s, Some(sep), true, true, repeat)? } else { s };
            if trim && string::len(&strings, s) == 0 {
                return Ok(Value::NIL);
            }
            let all = string::split(&strings, s, sep).collect::<Result<Vec<_>, _>>()?;
            let last = all.len().saturating_sub(1);
            // Consecutive delimiter occurrences are treated as a single boundary when
            // collapsing is enabled, suppressing intermediate empty strings.
            for (i, piece) in all.into_iter().enumerate() {
                if !repeat || i == 0 || i == last || string::len(&strings, piece) > 0 {
                    pieces.push(piece.value())?;
                }
            }
        }
    }
    Ok(Pairs::new(mc).list(&pieces)?)
}

/// Returns string `s` with occurrences of `from` replaced by `to` (replacing all matches if
/// `all` is true, or only the first match otherwise). An empty `from` pattern matches before each
/// character and after the final character.
fn string_replace<'gc>(mc: &Mutation<'gc>, s: Str<'gc>, from: Str<'gc>, to: Str<'gc>, all: bool) -> Result<Value<'gc>, Fault> {
    let strings = Strings::new(mc);
    let (n, m) = (string::len(&strings, s), string::len(&strings, from));
    let mut parts = ScratchVec::new(mc);
    if m == 0 {
        parts.push(to)?;
        if !all {
            parts.push(s)?;
        } else {
            for i in 0..n {
                parts.push(string::substring(&strings, s, i, i + 1)?)?;
                parts.push(to)?;
            }
        }
    } else {
        let mut at = 0;
        while let Some(i) = string::find(&strings, s, from, at)? {
            parts.push(string::substring(&strings, s, at, i)?)?;
            parts.push(to)?;
            at = i + m;
            if !all {
                break;
            }
        }
        if parts.is_empty() {
            return Ok(s.value());
        }
        parts.push(string::substring(&strings, s, at, n)?)?;
    }
    Ok(string::concat_all(&strings, &parts)?.value())
}

/// Implements `(string-join strs [sep])`, concatenating the strings in proper list `strs`
/// separated by delimiter `sep` (defaulting to a single space `" "`).
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
    // Small joins consisting of up to four strings use a stack-allocated buffer to avoid
    // heap allocation overhead.
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

/// Evaluates whether relational operator `op` holds pairwise across consecutive strings in
/// `xs`. Prior to each string comparison, VM fuel is deducted proportional to the length of the
/// shorter string.
fn compare_strings<'gc>(mc: &Mutation<'gc>, op: Intrinsic, xs: impl Iterator<Item = Value<'gc>>, fuel: &mut Fuel) -> Result<bool, Fault> {
    let strings = Strings::new(mc);
    let (mut before, mut so_far) = (None, true);
    for x in xs {
        let x = strings.string(x).ok_or(Fault::WrongType)?;
        if let Some(b) = before
            && so_far
        {
            fuel.spend(string::len(&strings, b).min(string::len(&strings, x)) as u64 / equal::PER_FUEL)?;
            so_far = match op {
                Intrinsic::StringEq => string::equal(&strings, b, x)?,
                Intrinsic::StringCiEq => string::compare_ci(&strings, b, x)?.is_eq(),
                Intrinsic::StringCiLt => string::compare_ci(&strings, b, x)?.is_lt(),
                Intrinsic::StringCiGt => string::compare_ci(&strings, b, x)?.is_gt(),
                Intrinsic::StringCiLe => string::compare_ci(&strings, b, x)?.is_le(),
                Intrinsic::StringCiGe => string::compare_ci(&strings, b, x)?.is_ge(),
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

/// Deducts VM fuel and reserves heap memory before calculating exact exponentiation `z^w`,
/// accounting for both the memory footprint of the digits and the quadratic work required by
/// exponentiation-by-squaring.
fn charge_power<'gc>(mc: &Mutation<'gc>, h: &Nums<'_, 'gc>, fuel: &mut Fuel, z: Number<'gc>, w: Number<'gc>) -> Result<(), Fault> {
    let ComplexView::Real(e) = h.complex_view(w) else { return Ok(()) };
    let RealView::Exact(e) = h.real_view(e) else { return Ok(()) };
    let RationalView::Integer(e) = h.rational_view(e) else { return Ok(()) };
    // An exact integer exponent that exceeds 64 bits would exhaust available memory for any
    // base other than 0, 1, or -1 (which are handled as special cases by `expt`).
    let Some(e) = int::to_i64(h, e) else { return Ok(()) };
    let words = exact_bits(h, z).saturating_mul(e.unsigned_abs()) / 64;
    mc.ensure(usize::try_from(words.saturating_mul(8)).unwrap_or(usize::MAX))?;
    fuel.spend(words.saturating_mul(words) / equal::PER_FUEL)
}

/// Tests whether relational operator `op` holds across pairwise consecutive numeric arguments
/// in `xs` (`=` accepts general complex numbers, whereas inequality operators require real
/// numbers). All arguments are validated for correct numeric types even if an earlier
/// comparison fails.
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

/// Implements `(reverse xs)`, constructing and returning a newly allocated proper list
/// containing the elements of `xs` in reverse order while deducting fuel for list traversal.
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

/// Implements list searching intrinsics `memq`, `memv`, `member`, `assq`, `assv`, and `assoc`
/// using the equality semantics appropriate for each variant.
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
    // Common string concatenations with up to eight arguments use a stack-allocated array
    // to avoid heap allocation overhead.
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

/// Implements `(append list ... [obj])`, copying each proper list preceding the final
/// non-empty argument onto the terminal tail. Because pairs are immutable, trailing empty list
/// `'()` arguments following a proper list require no copying.
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

/// Traverses `k` pair links starting from `xs` and returns the resulting sublist tail, faulting
/// if `xs` is too short or if `need_pair` is true and the resulting tail is not a pair.
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

/// Validates that `v` is a fixnum in the range `0..=255`, returning `u8` on success,
/// [`Fault::OutOfRange`] for any other exact integer, or [`Fault::WrongType`].
fn byte<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> Result<u8, Fault> {
    let b = v.as_fixnum().ok_or_else(|| not_fixnum(mc, v))?;
    u8::try_from(b).map_err(|_| Fault::OutOfRange)
}

/// Returns the fault for `v`, which is not a fixnum, as an argument that must be an integer in a
/// range that fixnums cover: [`Fault::OutOfRange`] for an exact integer too large to be a fixnum,
/// and [`Fault::WrongType`] for anything else.
fn not_fixnum<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> Fault {
    if Nums::new(mc).integer(v).is_some() { Fault::OutOfRange } else { Fault::WrongType }
}

/// Validates that `v` is a non-negative fixnum, returning `usize` on success, or
/// [`Fault::WrongType`] if not a fixnum or [`Fault::OutOfRange`] if negative.
fn index(v: Value<'_>) -> Result<usize, Fault> {
    let k = v.as_fixnum().ok_or(Fault::WrongType)?;
    usize::try_from(k).map_err(|_| Fault::OutOfRange)
}

/// Returns newly allocated `value`, pausing the VM fuel budget if GC step thresholds have
/// been reached so the execution step can yield and the garbage collector can proceed at the next
/// call or jump boundary.
#[inline(always)]
pub(crate) fn made<'gc>(mc: &Mutation<'gc>, fuel: &mut Fuel, value: Value<'gc>) -> Value<'gc> {
    if mc.step_due() {
        fuel.pause();
    }
    value
}

/// Constructs the return representation for `(values x ...)`: returns a single value as
/// itself, or packages zero or multiple values into a [`MultiValue`].
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
