//! An [`Intrinsic`] evaluates a primitive operation directly from its arguments within the
//! current VM step. It does not inspect or manipulate execution frames and never invokes procedures,
//! preventing suspension mid-execution or re-entrancy into the VM. Operations that call procedures
//! or alter continuations are dispatched as [`crate::Request`]s instead.
//!
//! A few intrinsics inspect or manipulate the running task's dynamic state; see
//! [`Intrinsic::is_dynamic`].

mod control;
mod lists;
mod numeric;
mod operands;
mod structs;
mod syntax;
mod text;
mod vectors;

pub(crate) use self::operands::{Operands, Registers};
use self::lists::{append, car, cdr, find, list_tail, reverse};
use self::numeric::{arith, charge_power, compare, divide, exact_bits, fixnum_to_string};
use self::text::{compare_chars, compare_strings, string_append, string_join};

use ragwort_types::Wire;
use ragwort_types::gc::{Gc, Mutation, ScratchVec, Value};
use ragwort_types::named;
use ragwort_types::num::{Nums, complex};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::string::{self, Strings};
use ragwort_types::symbol::{Keyword, Symbol};
use ragwort_types::vector::AnyVector;

use crate::op::{Context, Fuel};
use crate::{Fault, equal, prompts};
use crate::objects::{self, BoxFields, Condition, ModuleFields, Task, TaskFields};

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
        /// exact zero raises [`NumError::DivideByZero`](ragwort_types::num::NumError::DivideByZero).
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
        /// `(procedure-keywords f)`: returns a pair of two sorted lists. Its head lists the keywords
        /// procedure `f` requires and its tail the keywords `f` accepts. Both are empty if `f` accepts
        /// no keywords.
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
        /// `(values x)`: returns `x`. With any other number of arguments it fails with
        /// [`Fault::ValueCount`], because an intrinsic returns one value. The compiler emits
        /// [`Op::ReturnValues`](crate::Op::ReturnValues) for a `values` call in tail position instead.
        Values = ("values", any(DISCARD)),
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
        /// (0: pending, 1: running, 2: dead, 3: failed, 4: closing).
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
        self.apply(mc, task, args, fuel)
    }

    /// Executes the intrinsic within execution context `cx`, reading `args` registers starting
    /// from frame register `base`. The caller must have verified that the registers reside within
    /// the frame and match the required arity. Deducts VM fuel for computationally intensive
    /// operations.
    #[inline(always)]
    pub(crate) fn exec<'gc>(self, cx: &mut Context<'_, 'gc>, base: u8, args: u8) -> Result<Value<'gc>, Fault> {
        let operands = Registers { frame: cx.frame, base, count: args };
        self.apply(cx.mc, Some(cx.task), operands, &mut cx.fuel)
    }

    /// Executes a unary intrinsic on operand register `register`, assuming the caller has verified
    /// the intrinsic accepts exactly one argument.
    #[inline(always)]
    pub(crate) fn exec1<'gc>(self, cx: &mut Context<'_, 'gc>, register: u8) -> Result<Value<'gc>, Fault> {
        let operands = [cx.frame.get(register)];
        self.apply(cx.mc, Some(cx.task), operands, &mut cx.fuel)
    }

    /// Executes a binary intrinsic on operand registers `first` and `second`, assuming the caller
    /// has verified the intrinsic accepts exactly two arguments.
    #[inline(always)]
    pub(crate) fn exec2<'gc>(self, cx: &mut Context<'_, 'gc>, first: u8, second: u8) -> Result<Value<'gc>, Fault> {
        let operands = [cx.frame.get(first), cx.frame.get(second)];
        self.apply(cx.mc, Some(cx.task), operands, &mut cx.fuel)
    }

    /// Executes a ternary intrinsic on operand registers `first`, `second`, and `third`, assuming the
    /// caller has verified the intrinsic accepts exactly three arguments.
    #[inline(always)]
    pub(crate) fn exec3<'gc>(self, cx: &mut Context<'_, 'gc>, first: u8, second: u8, third: u8) -> Result<Value<'gc>, Fault> {
        let operands = [cx.frame.get(first), cx.frame.get(second), cx.frame.get(third)];
        self.apply(cx.mc, Some(cx.task), operands, &mut cx.fuel)
    }

    /// Evaluates the intrinsic on `operands`, passing the optional running `task` context if
    /// present.
    #[inline(always)]
    fn apply<'gc>(self, mc: &Mutation<'gc>, task: Option<Gc<'gc, Task>>, operands: impl Operands<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        Ok(match self {
            Intrinsic::MarkValue => prompts::mark(mc, task.ok_or(Fault::Malformed)?, operands.get(0), operands.get(1))?,
            Intrinsic::FrameMark => prompts::frame_mark(mc, task.ok_or(Fault::Malformed)?, operands.get(0), operands.get(1))?,
            Intrinsic::Running => Value::object(mc, task.ok_or(Fault::Malformed)?),
            Intrinsic::Winders => task.ok_or(Fault::Malformed)?.winders(mc),
            Intrinsic::FrameMarks | Intrinsic::SetWinders => self.dynamic(mc, task.ok_or(Fault::Malformed)?, operands, fuel)?,
            Intrinsic::Add => arith(mc, fuel, self, fixnum(0), operands.from(0))?,
            Intrinsic::Mul => arith(mc, fuel, self, fixnum(1), operands.from(0))?,
            Intrinsic::Sub | Intrinsic::Div if operands.count() == 0 => return Err(Fault::Arity),
            Intrinsic::Sub => {
                let (first, rest) = if operands.count() == 1 { (fixnum(0), 0) } else { (operands.get(0), 1) };
                arith(mc, fuel, self, first, operands.from(rest))?
            }
            Intrinsic::Div => {
                let (first, rest) = if operands.count() == 1 { (fixnum(1), 0) } else { (operands.get(0), 1) };
                arith(mc, fuel, self, first, operands.from(rest))?
            }
            Intrinsic::NumEq | Intrinsic::Lt | Intrinsic::Gt | Intrinsic::Le | Intrinsic::Ge if operands.count() == 0 => return Err(Fault::Arity),
            Intrinsic::NumEq | Intrinsic::Lt | Intrinsic::Gt | Intrinsic::Le | Intrinsic::Ge => boolean(compare(mc, self, operands.from(0))?),
            Intrinsic::Cons => made(mc, fuel, Pairs::new(mc).cons(operands.get(0), operands.get(1))?.value(mc)),
            Intrinsic::Car => car(mc, operands.get(0))?,
            Intrinsic::Cdr => cdr(mc, operands.get(0))?,
            Intrinsic::Caar => car(mc, car(mc, operands.get(0))?)?,
            Intrinsic::Cadr => car(mc, cdr(mc, operands.get(0))?)?,
            Intrinsic::Cdar => cdr(mc, car(mc, operands.get(0))?)?,
            Intrinsic::Cddr => cdr(mc, cdr(mc, operands.get(0))?)?,
            Intrinsic::Caaar => car(mc, car(mc, car(mc, operands.get(0))?)?)?,
            Intrinsic::Caadr => car(mc, car(mc, cdr(mc, operands.get(0))?)?)?,
            Intrinsic::Cadar => car(mc, cdr(mc, car(mc, operands.get(0))?)?)?,
            Intrinsic::Caddr => car(mc, cdr(mc, cdr(mc, operands.get(0))?)?)?,
            Intrinsic::Cdaar => cdr(mc, car(mc, car(mc, operands.get(0))?)?)?,
            Intrinsic::Cdadr => cdr(mc, car(mc, cdr(mc, operands.get(0))?)?)?,
            Intrinsic::Cddar => cdr(mc, cdr(mc, car(mc, operands.get(0))?)?)?,
            Intrinsic::Cdddr => cdr(mc, cdr(mc, cdr(mc, operands.get(0))?)?)?,
            Intrinsic::Caaaar => car(mc, car(mc, car(mc, car(mc, operands.get(0))?)?)?)?,
            Intrinsic::Caaadr => car(mc, car(mc, car(mc, cdr(mc, operands.get(0))?)?)?)?,
            Intrinsic::Caadar => car(mc, car(mc, cdr(mc, car(mc, operands.get(0))?)?)?)?,
            Intrinsic::Caaddr => car(mc, car(mc, cdr(mc, cdr(mc, operands.get(0))?)?)?)?,
            Intrinsic::Cadaar => car(mc, cdr(mc, car(mc, car(mc, operands.get(0))?)?)?)?,
            Intrinsic::Cadadr => car(mc, cdr(mc, car(mc, cdr(mc, operands.get(0))?)?)?)?,
            Intrinsic::Caddar => car(mc, cdr(mc, cdr(mc, car(mc, operands.get(0))?)?)?)?,
            Intrinsic::Cadddr => car(mc, cdr(mc, cdr(mc, cdr(mc, operands.get(0))?)?)?)?,
            Intrinsic::Cdaaar => cdr(mc, car(mc, car(mc, car(mc, operands.get(0))?)?)?)?,
            Intrinsic::Cdaadr => cdr(mc, car(mc, car(mc, cdr(mc, operands.get(0))?)?)?)?,
            Intrinsic::Cdadar => cdr(mc, car(mc, cdr(mc, car(mc, operands.get(0))?)?)?)?,
            Intrinsic::Cdaddr => cdr(mc, car(mc, cdr(mc, cdr(mc, operands.get(0))?)?)?)?,
            Intrinsic::Cddaar => cdr(mc, cdr(mc, car(mc, car(mc, operands.get(0))?)?)?)?,
            Intrinsic::Cddadr => cdr(mc, cdr(mc, car(mc, cdr(mc, operands.get(0))?)?)?)?,
            Intrinsic::Cdddar => cdr(mc, cdr(mc, cdr(mc, car(mc, operands.get(0))?)?)?)?,
            Intrinsic::Cddddr => cdr(mc, cdr(mc, cdr(mc, cdr(mc, operands.get(0))?)?)?)?,
            Intrinsic::Eq => boolean(operands.get(0) == operands.get(1)),
            Intrinsic::Eqv => boolean(equal::eqv(mc, operands.get(0), operands.get(1))),
            Intrinsic::Equal => {
                let most = fuel.left().saturating_add(1).saturating_mul(equal::PER_FUEL) - 1;
                let (same, compared) = equal::equal(mc, operands.get(0), operands.get(1), most)?;
                fuel.spend(compared / equal::PER_FUEL)?;
                boolean(same)
            }
            Intrinsic::IsNull => boolean(operands.get(0) == Value::NIL),
            Intrinsic::IsPair => boolean(Pair::of(operands.get(0)).is_some()),
            Intrinsic::IsList => boolean(Pairs::new(mc).is_list(operands.get(0))),
            Intrinsic::Length => {
                let len = Pairs::new(mc).list_len(operands.get(0)).ok_or(Fault::WrongType)?;
                i64::try_from(len).ok().and_then(Value::fixnum).ok_or(Fault::OutOfRange)?
            }
            Intrinsic::ListTail => list_tail(mc, operands.get(0), index(operands.get(1))?, false, fuel)?,
            Intrinsic::ListRef => {
                let tail = list_tail(mc, operands.get(0), index(operands.get(1))?, true, fuel)?;
                Pair::of(tail).ok_or(Fault::WrongType)?.head(mc)
            }
            Intrinsic::Reverse => reverse(mc, operands.get(0), fuel)?,
            Intrinsic::Append => append(mc, operands.from(0), fuel)?,
            Intrinsic::Memq | Intrinsic::Memv | Intrinsic::Member | Intrinsic::Assq | Intrinsic::Assv | Intrinsic::Assoc => {
                find(mc, self, operands.get(0), operands.get(1), fuel)?
            }
            Intrinsic::IsBox => boolean(operands.get(0).downcast::<objects::Box>(mc).is_some()),
            Intrinsic::Not => boolean(operands.get(0) == Value::FALSE),
            Intrinsic::IsBoolean => boolean(operands.get(0) == Value::TRUE || operands.get(0) == Value::FALSE),
            Intrinsic::IsKeyword => boolean(Keyword::of(operands.get(0)).is_some()),
            Intrinsic::IsSymbol => boolean(Symbol::of(operands.get(0)).is_some()),
            Intrinsic::IsString => boolean(Strings::new(mc).string(operands.get(0)).is_some()),
            Intrinsic::StringLength => {
                let strings = Strings::new(mc);
                fixnum(string::len(&strings, strings.string(operands.get(0)).ok_or(Fault::WrongType)?) as i64)
            }
            Intrinsic::StringAppend => string_append(mc, operands.from(0), fuel)?,
            Intrinsic::Substring | Intrinsic::StringToList if !(1..=3).contains(&operands.count()) || self == Intrinsic::Substring && operands.count() == 1 => {
                return Err(Fault::Arity);
            }
            Intrinsic::Substring | Intrinsic::StringToList => {
                let strings = Strings::new(mc);
                let string = strings.string(operands.get(0)).ok_or(Fault::WrongType)?;
                let start = if operands.count() > 1 { index(operands.get(1))? } else { 0 };
                let end = if operands.count() > 2 { index(operands.get(2))? } else { string::len(&strings, string) };
                let part = if (start, end) == (0, string::len(&strings, string)) { string } else { string::substring(&strings, string, start, end)? };
                if self == Intrinsic::Substring {
                    made(mc, fuel, part.value())
                } else {
                    fuel.spend((end - start) as u64 / equal::PER_FUEL)?;
                    let mut chars = ScratchVec::new(mc);
                    for character in string::chars(&strings, part) {
                        chars.push(Value::char(character))?;
                    }
                    made(mc, fuel, Pairs::new(mc).list(&chars)?)
                }
            }
            Intrinsic::StringRef => {
                let strings = Strings::new(mc);
                Value::char(string::char_at(&strings, strings.string(operands.get(0)).ok_or(Fault::WrongType)?, index(operands.get(1))?)?)
            }
            Intrinsic::StringEq | Intrinsic::StringLt | Intrinsic::StringGt | Intrinsic::StringLe | Intrinsic::StringGe if operands.count() == 0 => {
                return Err(Fault::Arity);
            }
            Intrinsic::StringEq | Intrinsic::StringLt | Intrinsic::StringGt | Intrinsic::StringLe | Intrinsic::StringGe => {
                boolean(compare_strings(mc, self, operands.from(0), fuel)?)
            }
            Intrinsic::StringJoin if !(1..=2).contains(&operands.count()) => return Err(Fault::Arity),
            Intrinsic::StringJoin => string_join(mc, operands.get(0), (operands.count() == 2).then(|| operands.get(1)), fuel)?,
            Intrinsic::IsChar => boolean(operands.get(0).as_char().is_some()),
            Intrinsic::CharToInteger => fixnum(i64::from(u32::from(operands.get(0).as_char().ok_or(Fault::WrongType)?))),
            Intrinsic::IntegerToChar => {
                let code = operands.get(0).as_fixnum().ok_or_else(|| not_fixnum(mc, operands.get(0)))?;
                Value::char(u32::try_from(code).ok().and_then(char::from_u32).ok_or(Fault::OutOfRange)?)
            }
            Intrinsic::CharEq | Intrinsic::CharLt | Intrinsic::CharGt | Intrinsic::CharLe | Intrinsic::CharGe if operands.count() == 0 => {
                return Err(Fault::Arity);
            }
            Intrinsic::CharEq | Intrinsic::CharLt | Intrinsic::CharGt | Intrinsic::CharLe | Intrinsic::CharGe => {
                boolean(compare_chars(self, operands.from(0))?)
            }
            Intrinsic::NumberToString if !(1..=2).contains(&operands.count()) => return Err(Fault::Arity),
            Intrinsic::NumberToString => {
                let nums = Nums::new(mc);
                let number = nums.number(operands.get(0)).ok_or(Fault::WrongType)?;
                let radix = if operands.count() == 2 { operands.get(1).as_fixnum().ok_or(Fault::WrongType)? } else { 10 };
                let radix = [2, 8, 10, 16].into_iter().find(|&allowed| allowed == radix).ok_or(Fault::OutOfRange)? as u32;
                if let Some(integer) = operands.get(0).as_fixnum() {
                    return Ok(made(mc, fuel, fixnum_to_string(mc, integer, radix)?));
                }
                // Formatting a multi-precision integer as text has approximately quadratic
                // computational complexity relative to its digit count.
                let words = exact_bits(&nums, number) / 64;
                fuel.spend(words.saturating_mul(words) / equal::PER_FUEL)?;
                let text = complex::to_string(&nums, number, radix)?;
                made(mc, fuel, string::from_str(&Strings::new(mc), &text)?.value())
            }
            Intrinsic::Quotient | Intrinsic::Remainder | Intrinsic::Modulo | Intrinsic::FloorQuotient => divide(mc, fuel, self, operands.get(0), operands.get(1))?,
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
            | Intrinsic::Angle => self.numeric(mc, operands, fuel)?,
            Intrinsic::IsStructDerivedFrom => boolean(crate::structs::of(mc, operands.get(0), crate::structs::type_of(mc, operands.get(1))?).is_some()),
            Intrinsic::StructRef => crate::structs::field_of(mc, operands.get(0), operands.get(1), index(operands.get(2))?)?,
            Intrinsic::StructField | Intrinsic::StructFixedField => crate::structs::field(mc, operands.get(0), index(operands.get(1))?)?,
            Intrinsic::MakeStructType
            | Intrinsic::MakeStruct
            | Intrinsic::IsStruct
            | Intrinsic::IsStructType
            | Intrinsic::StructSet
            | Intrinsic::StructFields
            | Intrinsic::IsStructFieldMutable
            | Intrinsic::StructType
            | Intrinsic::StructToList => {
                self.structs(mc, operands, fuel)?
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
            | Intrinsic::StringReplace => self.text(mc, operands, fuel)?,
            Intrinsic::BitwiseAnd
            | Intrinsic::BitwiseIor
            | Intrinsic::BitwiseXor
            | Intrinsic::BitwiseNot
            | Intrinsic::ArithmeticShift
            | Intrinsic::BitField
            | Intrinsic::BitFieldReplace
            | Intrinsic::IntegerLength
            | Intrinsic::BitCount
            | Intrinsic::IsBitSet => self.bits(mc, operands, fuel)?,
            Intrinsic::SymbolToString
            | Intrinsic::StringToSymbol
            | Intrinsic::KeywordToString
            | Intrinsic::StringToKeyword => self.names(mc, operands, fuel)?,
            Intrinsic::Expt => {
                let nums = Nums::new(mc);
                let (base, exponent) = (nums.number(operands.get(0)).ok_or(Fault::WrongType)?, nums.number(operands.get(1)).ok_or(Fault::WrongType)?);
                charge_power(mc, &nums, fuel, base, exponent)?;
                made(mc, fuel, complex::expt(&nums, base, exponent)?.value())
            }
            Intrinsic::Void => Value::VOID,
            Intrinsic::IsBytevector
            | Intrinsic::MakeBytevector
            | Intrinsic::BytevectorLength
            | Intrinsic::BytevectorRef
            | Intrinsic::BytevectorSet => self.bytevector(mc, operands, fuel)?,
            Intrinsic::IsVector => boolean(AnyVector::of(operands.get(0)).is_some()),
            Intrinsic::MakeVector
            | Intrinsic::MakeVectorOf
            | Intrinsic::VectorToList
            | Intrinsic::ListToVector => self.vector(mc, operands, fuel)?,
            Intrinsic::VectorLength => {
                let len = AnyVector::of(operands.get(0)).ok_or(Fault::WrongType)?.len(mc);
                Value::fixnum(len as i64).expect("lengths are fixnums")
            }
            Intrinsic::VectorRef => AnyVector::of(operands.get(0)).ok_or(Fault::WrongType)?.get(mc, index(operands.get(1))?).ok_or(Fault::OutOfRange)?,
            Intrinsic::VectorSet => {
                let AnyVector::Mutable(vector) = AnyVector::of(operands.get(0)).ok_or(Fault::WrongType)? else { return Err(Fault::Immutable) };
                let (items, position) = (vector.items(mc), index(operands.get(1))?);
                if position >= items.len() {
                    return Err(Fault::OutOfRange);
                }
                items.set(mc, position, operands.get(2));
                Value::VOID
            }
            Intrinsic::MakeBox => made(mc, fuel, Value::object(mc, objects::Box::new(mc, operands.get(0))?)),
            Intrinsic::MakeWinder => made(mc, fuel, Value::object(mc, objects::Winder::new(mc, operands.get(0), operands.get(1))?)),
            Intrinsic::Unbox => operands.get(0).downcast::<objects::Box>(mc).ok_or(Fault::WrongType)?.value(mc),
            Intrinsic::SetBox => {
                operands.get(0).downcast::<objects::Box>(mc).ok_or(Fault::WrongType)?.set_value(mc, operands.get(1));
                Value::VOID
            }
            Intrinsic::DefaultPromptTag => prompts::default_tag(),
            Intrinsic::MakePromptTag
            | Intrinsic::Values
            | Intrinsic::MakeKeywordProcedure
            | Intrinsic::ProcedureKeywords
            | Intrinsic::IsContinuation
            | Intrinsic::MakeCoroutine
            | Intrinsic::IsCoroutine
            | Intrinsic::CoroutineState => self.control(mc, operands, fuel)?,
            Intrinsic::ModuleRef => {
                let items = operands.get(0).downcast::<objects::Module>(mc).ok_or(Fault::WrongType)?.items(mc);
                let slot = operands.get(1).as_fixnum().ok_or(Fault::WrongType)?;
                let value = usize::try_from(slot).ok().filter(|&slot| slot < items.len()).map(|slot| items.get(slot)).ok_or(Fault::OutOfRange)?;
                if value == Value::UNDEFINED {
                    return Err(Fault::Unbound);
                }
                value
            }
            Intrinsic::MakeError
            | Intrinsic::MakeSyntaxError
            | Intrinsic::ErrorObjectMessage
            | Intrinsic::ErrorObjectIrritants
            | Intrinsic::ErrorObjectWho
            | Intrinsic::ErrorObjectTraceback
            | Intrinsic::ErrorObjectKind => self.condition(mc, operands, fuel)?,
            Intrinsic::IsProcedure => boolean(is_procedure(mc, operands.get(0))),
            Intrinsic::IsErrorObject => boolean(operands.get(0).downcast::<Condition>(mc).is_some()),
            Intrinsic::IsSyntax
            | Intrinsic::IsIdentifier
            | Intrinsic::SyntaxE
            | Intrinsic::SyntaxToDatum
            | Intrinsic::DatumToSyntax
            | Intrinsic::BoundIdentifierEq
            | Intrinsic::FreeIdentifierEq
            | Intrinsic::SyntaxMatch
            | Intrinsic::SyntaxBuild
            | Intrinsic::GenerateTemporaries => self.syntax(mc, operands, fuel)?,
        })
    }
}

fn boolean<'gc>(flag: bool) -> Value<'gc> {
    if flag { Value::TRUE } else { Value::FALSE }
}

fn fixnum<'gc>(integer: i64) -> Value<'gc> {
    Value::fixnum(integer).expect("a small fixnum")
}

/// Returns whether value `value` is callable as a procedure (a closure, a continuation, or a
/// keyword procedure).
pub(crate) fn is_procedure<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> bool {
    value.downcast::<objects::Closure>(mc).is_some()
        || value.downcast::<objects::Continuation>(mc).is_some()
        || value.downcast::<objects::KeywordProcedure>(mc).is_some()
}

/// Resolves an index range `[start, end)` from the optional start (operand 1) and end (operand 2)
/// arguments for a sequence of length `len`, defaulting to `0` and `len` respectively and
/// ensuring `0 <= start <= end <= len`.
fn range<'gc>(len: usize, operands: impl Operands<'gc>) -> Result<(usize, usize), Fault> {
    let start = if operands.count() > 1 { index(operands.get(1))? } else { 0 };
    let end = if operands.count() > 2 { index(operands.get(2))? } else { len };
    if start > end || end > len {
        return Err(Fault::OutOfRange);
    }
    Ok((start, end))
}

/// Returns the fault for an argument `value` that must be a small integer but is not a fixnum:
/// [`Fault::OutOfRange`] if `value` is an exact integer too large to be a fixnum,
/// and [`Fault::WrongType`] otherwise.
fn not_fixnum<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> Fault {
    if Nums::new(mc).integer(value).is_some() { Fault::OutOfRange } else { Fault::WrongType }
}

/// Validates that `value` is a non-negative fixnum, returning `usize` on success, or
/// [`Fault::WrongType`] if not a fixnum or [`Fault::OutOfRange`] if negative.
fn index(value: Value<'_>) -> Result<usize, Fault> {
    let number = value.as_fixnum().ok_or(Fault::WrongType)?;
    usize::try_from(number).map_err(|_| Fault::OutOfRange)
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

