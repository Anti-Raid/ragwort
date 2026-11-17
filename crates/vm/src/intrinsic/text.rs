//! Character, string, symbol and keyword intrinsics.

use ragwort_types::bytevector::{AnyBytevector, Bytevectors};
use ragwort_types::gc::{Mutation, ScratchVec, Value};
use ragwort_types::pair::Pairs;
use ragwort_types::string::{self, Str, StrError, Strings};
use ragwort_types::symbol::{Keyword, Symbol, Symbols};
use ragwort_types::vector::{EveryVector, Vectors};

use crate::op::Fuel;
use crate::{Fault, equal};

use super::{Intrinsic, Operands, boolean, fixnum, index, made, range};

impl Intrinsic {
    /// Evaluates advanced character and string manipulation intrinsics on `operands`.
    #[inline(never)]
    pub(super) fn text<'gc>(self, mc: &Mutation<'gc>, operands: impl Operands<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        #[inline(always)]
        fn string_of<'gc>(strings: &Strings<'_, 'gc>, value: Value<'gc>) -> Result<Str<'gc>, Fault> {
            strings.string(value).ok_or(Fault::WrongType)
        }
        #[inline(always)]
        fn char_of(value: Value<'_>) -> Result<char, Fault> {
            value.as_char().ok_or(Fault::WrongType)
        }
        // Deducts VM fuel proportional to the string's character length for a full traversal.
        #[inline(always)]
        fn spend<'gc>(fuel: &mut Fuel, strings: &Strings<'_, 'gc>, string: Str<'gc>) -> Result<(), Fault> {
            fuel.spend(string::len(strings, string) as u64 / equal::PER_FUEL)
        }
        let strings = Strings::new(mc);
        let made_of = match self {
            Intrinsic::IsCharAlphabetic => return Ok(boolean(char_of(operands.get(0))?.is_alphabetic())),
            Intrinsic::IsCharNumeric => return Ok(boolean(string::digit_value(char_of(operands.get(0))?).is_some())),
            Intrinsic::IsCharWhitespace => return Ok(boolean(char_of(operands.get(0))?.is_whitespace())),
            Intrinsic::IsCharUpperCase => return Ok(boolean(char_of(operands.get(0))?.is_uppercase())),
            Intrinsic::IsCharLowerCase => return Ok(boolean(char_of(operands.get(0))?.is_lowercase())),
            Intrinsic::DigitValue => return Ok(string::digit_value(char_of(operands.get(0))?).map_or(Value::FALSE, |digit| fixnum(i64::from(digit)))),
            Intrinsic::CharUpcase => return Ok(Value::char(string::upcase_char(char_of(operands.get(0))?))),
            Intrinsic::CharDowncase => return Ok(Value::char(string::downcase_char(char_of(operands.get(0))?))),
            Intrinsic::CharFoldcase => return Ok(Value::char(string::foldcase_char(char_of(operands.get(0))?))),
            Intrinsic::CharCiEq | Intrinsic::CharCiLt | Intrinsic::CharCiGt | Intrinsic::CharCiLe | Intrinsic::CharCiGe if operands.count() == 0 => return Err(Fault::Arity),
            Intrinsic::CharCiEq | Intrinsic::CharCiLt | Intrinsic::CharCiGt | Intrinsic::CharCiLe | Intrinsic::CharCiGe => {
                return Ok(boolean(compare_chars(self, operands.from(0))?));
            }
            Intrinsic::StringCiEq | Intrinsic::StringCiLt | Intrinsic::StringCiGt | Intrinsic::StringCiLe | Intrinsic::StringCiGe if operands.count() == 0 => {
                return Err(Fault::Arity);
            }
            Intrinsic::StringCiEq | Intrinsic::StringCiLt | Intrinsic::StringCiGt | Intrinsic::StringCiLe | Intrinsic::StringCiGe => {
                return Ok(boolean(compare_strings(mc, self, operands.from(0), fuel)?));
            }
            Intrinsic::MakeString if !(1..=2).contains(&operands.count()) => return Err(Fault::Arity),
            Intrinsic::MakeString => {
                let len = index(operands.get(0))?;
                let fill = if operands.count() == 2 { char_of(operands.get(1))? } else { ' ' };
                fuel.spend(len as u64 / equal::PER_FUEL)?;
                string::repeat(&strings, fill, len)?.value()
            }
            Intrinsic::ListToString => {
                let pairs = Pairs::new(mc);
                let len = pairs.list_len(operands.get(0)).ok_or(Fault::WrongType)?;
                fuel.spend(len / equal::PER_FUEL)?;
                let mut chars = ScratchVec::new(mc);
                for item in pairs.elements(operands.get(0)) {
                    chars.push(char_of(item)?)?;
                }
                string::from_chars(&strings, chars.iter().copied())?.value()
            }
            Intrinsic::StringUpcase | Intrinsic::StringDowncase | Intrinsic::StringFoldcase => {
                let string = string_of(&strings, operands.get(0))?;
                spend(fuel, &strings, string)?;
                let mapped = match self {
                    Intrinsic::StringUpcase => string::upcase(&strings, string)?,
                    Intrinsic::StringDowncase => string::downcase(&strings, string)?,
                    _ => string::foldcase(&strings, string)?,
                };
                mapped.value()
            }
            Intrinsic::StringToVector | Intrinsic::VectorToString | Intrinsic::StringToUtf8 | Intrinsic::Utf8ToString if !(1..=3).contains(&operands.count()) => {
                return Err(Fault::Arity);
            }
            Intrinsic::StringToVector | Intrinsic::StringToUtf8 => {
                let string = string_of(&strings, operands.get(0))?;
                let (start, end) = range(string::len(&strings, string), operands)?;
                let part = string::substring(&strings, string, start, end)?;
                spend(fuel, &strings, part)?;
                if self == Intrinsic::StringToVector {
                    let vector = Vectors::new(mc).make(end - start, Value::VOID)?;
                    let items = vector.items(mc);
                    string::chars(&strings, part).enumerate().for_each(|(i, character)| items.set(mc, i, Value::char(character)));
                    vector.value(mc)
                } else {
                    let mut bytes = ScratchVec::new(mc);
                    let mut buffer = [0; 4];
                    for character in string::chars(&strings, part) {
                        for &byte in character.encode_utf8(&mut buffer).as_bytes() {
                            bytes.push(byte)?;
                        }
                    }
                    Bytevectors::new(mc).from_slice(&bytes)?.value(mc)
                }
            }
            Intrinsic::VectorToString => {
                let vector = EveryVector::of(operands.get(0)).ok_or(Fault::WrongType)?;
                let (start, end) = range(vector.len(mc), operands)?;
                fuel.spend((end - start) as u64 / equal::PER_FUEL)?;
                let mut chars = ScratchVec::new(mc);
                for i in start..end {
                    chars.push(char_of(vector.get(mc, i)?.ok_or(Fault::OutOfRange)?)?)?;
                }
                string::from_chars(&strings, chars.iter().copied())?.value()
            }
            Intrinsic::Utf8ToString => {
                let bytes = AnyBytevector::of(operands.get(0)).ok_or(Fault::WrongType)?;
                let (start, end) = range(bytes.len(mc), operands)?;
                fuel.spend((end - start) as u64 / equal::PER_FUEL)?;
                let part = bytes.bytes(mc, start, end);
                let text = std::str::from_utf8(&part).map_err(|_| Fault::Str(StrError::NotUtf8))?;
                string::from_str(&strings, text)?.value()
            }
            Intrinsic::IsStringPrefix | Intrinsic::IsStringSuffix | Intrinsic::IsStringContains => {
                let (string, part) = (string_of(&strings, operands.get(0))?, string_of(&strings, operands.get(1))?);
                spend(fuel, &strings, string)?;
                return Ok(boolean(match self {
                    Intrinsic::IsStringPrefix => string::starts_with(&strings, string, part)?,
                    Intrinsic::IsStringSuffix => string::ends_with(&strings, string, part)?,
                    _ => string::find(&strings, string, part, 0)?.is_some(),
                }));
            }
            Intrinsic::StringFind | Intrinsic::StringFindLast if !(2..=3).contains(&operands.count()) => return Err(Fault::Arity),
            Intrinsic::StringFind | Intrinsic::StringFindLast => {
                let (string, part) = (string_of(&strings, operands.get(0))?, string_of(&strings, operands.get(1))?);
                spend(fuel, &strings, string)?;
                let found = if self == Intrinsic::StringFind {
                    string::find(&strings, string, part, if operands.count() == 3 { index(operands.get(2))? } else { 0 })?
                } else {
                    string::rfind(&strings, string, part, if operands.count() == 3 { index(operands.get(2))? } else { string::len(&strings, string) })?
                };
                return Ok(found.map_or(Value::FALSE, |position| fixnum(position as i64)));
            }
            Intrinsic::StringSplit => {
                let string = string_of(&strings, operands.get(0))?;
                let sep = if operands.get(1).is_false() { None } else { Some(string_of(&strings, operands.get(1))?) };
                spend(fuel, &strings, string)?;
                string_split(mc, string, sep, operands.get(2).is_true(), operands.get(3).is_true())?
            }
            Intrinsic::StringTrim => {
                let string = string_of(&strings, operands.get(0))?;
                let sep = if operands.get(1).is_false() { None } else { Some(string_of(&strings, operands.get(1))?) };
                spend(fuel, &strings, string)?;
                let (left, right, repeat) = (operands.get(2).is_true(), operands.get(3).is_true(), operands.get(4).is_true());
                trimmed(&strings, string, sep, left, right, repeat)?.value()
            }
            Intrinsic::StringReplace => {
                let (string, from, to) = (string_of(&strings, operands.get(0))?, string_of(&strings, operands.get(1))?, string_of(&strings, operands.get(2))?);
                spend(fuel, &strings, string)?;
                string_replace(mc, string, from, to, operands.get(3).is_true())?
            }
            _ => unreachable!("{self:?} isn't a text procedure"),
        };
        Ok(made(mc, fuel, made_of))
    }

    /// Evaluates a symbol or keyword conversion on `operands`.
    #[inline(never)]
    pub(super) fn names<'gc>(self, mc: &Mutation<'gc>, operands: impl Operands<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        Ok(match self {
            Intrinsic::SymbolToString => Symbol::of(operands.get(0)).ok_or(Fault::WrongType)?.name(mc).value(),
            Intrinsic::StringToSymbol => {
                let strings = Strings::new(mc);
                let name = strings.string(operands.get(0)).ok_or(Fault::WrongType)?;
                made(mc, fuel, Symbols::of_arena(mc)?.intern(&strings, name)?.value(mc))
            }
            Intrinsic::KeywordToString => Keyword::of(operands.get(0)).ok_or(Fault::WrongType)?.symbol(mc).name(mc).value(),
            Intrinsic::StringToKeyword => {
                let strings = Strings::new(mc);
                let name = strings.string(operands.get(0)).ok_or(Fault::WrongType)?;
                let symbols = Symbols::of_arena(mc)?;
                let keyword = symbols.keyword(mc, symbols.intern(&strings, name)?)?;
                made(mc, fuel, keyword.value(mc))
            }
            _ => unreachable!("{self:?} isn't a symbol or keyword conversion"),
        })
    }
}

/// Verifies that all elements in `xs` are characters and evaluates whether relational operator
/// `op` holds pairwise across consecutive character elements.
pub(super) fn compare_chars<'gc>(op: Intrinsic, xs: impl Iterator<Item = Value<'gc>>) -> Result<bool, Fault> {
    let (mut before, mut so_far) = (None, true);
    for value in xs {
        let character = value.as_char().ok_or(Fault::WrongType)?;
        let character = if matches!(op, Intrinsic::CharCiEq | Intrinsic::CharCiLt | Intrinsic::CharCiGt | Intrinsic::CharCiLe | Intrinsic::CharCiGe) {
            string::foldcase_char(character)
        } else {
            character
        };
        if let Some(previous) = before {
            so_far &= match op {
                Intrinsic::CharEq | Intrinsic::CharCiEq => previous == character,
                Intrinsic::CharLt | Intrinsic::CharCiLt => previous < character,
                Intrinsic::CharGt | Intrinsic::CharCiGt => previous > character,
                Intrinsic::CharLe | Intrinsic::CharCiLe => previous <= character,
                _ => previous >= character,
            };
        }
        before = Some(character);
    }
    Ok(so_far)
}

/// Strips occurrences of `sep` (or whitespace if `sep` is `None`) from the start (`left`) and/or
/// end (`right`) of string `string`, removing either a single instance or repeated contiguous
/// instances if `repeat` is true.
fn trimmed<'gc>(strings: &Strings<'_, 'gc>, string: Str<'gc>, sep: Option<Str<'gc>>, left: bool, right: bool, repeat: bool) -> Result<Str<'gc>, Fault> {
    /// Returns whether the `width` characters of `string` from `offset` equal `sep`.
    #[inline(always)]
    fn at<'gc>(strings: &Strings<'_, 'gc>, string: Str<'gc>, sep: Str<'gc>, width: usize, offset: usize) -> Result<bool, Fault> {
        Ok(string::equal(strings, string::substring(strings, string, offset, offset + width)?, sep)?)
    }
    let Some(sep) = sep else {
        return Ok(match (left, right) {
            (true, true) => string::trim(strings, string)?,
            (true, false) => string::trim_start(strings, string)?,
            (false, true) => string::trim_end(strings, string)?,
            (false, false) => string,
        });
    };
    let (len, width) = (string::len(strings, string), string::len(strings, sep));
    if width == 0 {
        return Ok(string);
    }
    let (mut start, mut end) = (0, len);
    while left && start + width <= end && at(strings, string, sep, width, start)? {
        start += width;
        if !repeat {
            break;
        }
    }
    while right && end >= start + width && at(strings, string, sep, width, end - width)? {
        end -= width;
        if !repeat {
            break;
        }
    }
    Ok(if (start, end) == (0, len) { string } else { string::substring(strings, string, start, end)? })
}

/// Implements Racket-compatible `(string-split string [sep] #:trim? trim #:repeat? repeat)`, splitting
/// `string` by `sep` (or runs of whitespace if `sep` is `None`), with optional boundary trimming and
/// collapsing of consecutive delimiters.
fn string_split<'gc>(mc: &Mutation<'gc>, string: Str<'gc>, sep: Option<Str<'gc>>, trim: bool, repeat: bool) -> Result<Value<'gc>, Fault> {
    let strings = Strings::new(mc);
    let mut pieces = ScratchVec::new(mc);
    match sep {
        None if trim => {
            for piece in string::split_whitespace(&strings, string) {
                pieces.push(piece?.value())?;
            }
        }
        // When trimming is disabled, boundary whitespace produces an empty string segment at
        // the beginning or end of the output.
        None => {
            let (mut start, mut space) = (0, false);
            for (i, character) in string::chars(&strings, string).enumerate() {
                if character.is_whitespace() && !space {
                    pieces.push(string::substring(&strings, string, start, i)?.value())?;
                } else if !character.is_whitespace() && space {
                    start = i;
                }
                space = character.is_whitespace();
            }
            let len = string::len(&strings, string);
            pieces.push(string::substring(&strings, string, if space { len } else { start }, len)?.value())?;
        }
        Some(sep) => {
            let string = if trim { trimmed(&strings, string, Some(sep), true, true, repeat)? } else { string };
            if trim && string::len(&strings, string) == 0 {
                return Ok(Value::NULL);
            }
            let all = string::split(&strings, string, sep).collect::<Result<Vec<_>, _>>()?;
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

/// Returns string `string` with occurrences of `from` replaced by `to` (replacing all matches if
/// `all` is true, or only the first match otherwise). An empty `from` pattern matches before each
/// character and after the final character.
fn string_replace<'gc>(mc: &Mutation<'gc>, string: Str<'gc>, from: Str<'gc>, to: Str<'gc>, all: bool) -> Result<Value<'gc>, Fault> {
    let strings = Strings::new(mc);
    let (len, width) = (string::len(&strings, string), string::len(&strings, from));
    let mut parts = ScratchVec::new(mc);
    if width == 0 {
        parts.push(to)?;
        if !all {
            parts.push(string)?;
        } else {
            for i in 0..len {
                parts.push(string::substring(&strings, string, i, i + 1)?)?;
                parts.push(to)?;
            }
        }
    } else {
        let mut at = 0;
        while let Some(found) = string::find(&strings, string, from, at)? {
            parts.push(string::substring(&strings, string, at, found)?)?;
            parts.push(to)?;
            at = found + width;
            if !all {
                break;
            }
        }
        if parts.is_empty() {
            return Ok(string.value());
        }
        parts.push(string::substring(&strings, string, at, len)?)?;
    }
    Ok(string::concat_all(&strings, &parts)?.value())
}

/// Implements `(string-join strs [sep])`, concatenating the strings in proper list `strs`
/// separated by delimiter `sep` (defaulting to a single space `" "`).
pub(super) fn string_join<'gc>(mc: &Mutation<'gc>, strs: Value<'gc>, sep: Option<Value<'gc>>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
    let (strings, pairs) = (Strings::new(mc), Pairs::new(mc));
    let sep = match sep {
        Some(value) => strings.string(value).ok_or(Fault::WrongType)?,
        None => string::from_str(&strings, " ")?,
    };
    let count = pairs.list_len(strs).ok_or(Fault::WrongType)?;
    if count == 0 {
        return Ok(string::empty(&strings)?.value());
    }
    fuel.spend(count / equal::PER_FUEL)?;
    let mut items = pairs.elements(strs).map(|value| strings.string(value).ok_or(Fault::WrongType));
    // Small joins consisting of up to four strings use a stack-allocated buffer to avoid
    // heap allocation overhead.
    let joined = if count <= 4 {
        let mut parts = [sep; 7];
        for (i, item) in items.enumerate() {
            parts[2 * i] = item?;
        }
        string::concat_all(&strings, &parts[..2 * count as usize - 1])?
    } else {
        let mut parts = ScratchVec::new(mc);
        parts.push(items.next().ok_or(Fault::WrongType)??)?;
        for item in items {
            parts.push(sep)?;
            parts.push(item?)?;
        }
        string::concat_all(&strings, &parts)?
    };
    Ok(made(mc, fuel, joined.value()))
}

/// Evaluates whether relational operator `op` holds pairwise across consecutive strings in
/// `xs`. Prior to each string comparison, VM fuel is deducted proportional to the length of the
/// shorter string.
pub(super) fn compare_strings<'gc>(mc: &Mutation<'gc>, op: Intrinsic, xs: impl Iterator<Item = Value<'gc>>, fuel: &mut Fuel) -> Result<bool, Fault> {
    let strings = Strings::new(mc);
    let (mut before, mut so_far) = (None, true);
    for value in xs {
        let string = strings.string(value).ok_or(Fault::WrongType)?;
        if let Some(previous) = before
            && so_far
        {
            fuel.spend(string::len(&strings, previous).min(string::len(&strings, string)) as u64 / equal::PER_FUEL)?;
            so_far = match op {
                Intrinsic::StringEq => string::equal(&strings, previous, string)?,
                Intrinsic::StringCiEq => string::compare_ci(&strings, previous, string)?.is_eq(),
                Intrinsic::StringCiLt => string::compare_ci(&strings, previous, string)?.is_lt(),
                Intrinsic::StringCiGt => string::compare_ci(&strings, previous, string)?.is_gt(),
                Intrinsic::StringCiLe => string::compare_ci(&strings, previous, string)?.is_le(),
                Intrinsic::StringCiGe => string::compare_ci(&strings, previous, string)?.is_ge(),
                Intrinsic::StringLt => string::compare(&strings, previous, string)?.is_lt(),
                Intrinsic::StringGt => string::compare(&strings, previous, string)?.is_gt(),
                Intrinsic::StringLe => string::compare(&strings, previous, string)?.is_le(),
                _ => string::compare(&strings, previous, string)?.is_ge(),
            };
        }
        before = Some(string);
    }
    Ok(so_far)
}

pub(super) fn string_append<'gc>(mc: &Mutation<'gc>, args: impl ExactSizeIterator<Item = Value<'gc>>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
    let strings = Strings::new(mc);
    let count = args.len();
    fuel.spend(count as u64 / equal::PER_FUEL)?;
    let mut args = args.map(|value| strings.string(value).ok_or(Fault::WrongType));
    let Some(first) = args.next().transpose()? else { return Ok(string::empty(&strings)?.value()) };
    // Common string concatenations with up to eight arguments use a stack-allocated array
    // to avoid heap allocation overhead.
    let joined = if count <= 8 {
        let mut parts = [first; 8];
        for (part, arg) in parts[1..].iter_mut().zip(args) {
            *part = arg?;
        }
        string::concat_all(&strings, &parts[..count])?
    } else {
        let mut parts = ScratchVec::new(mc);
        parts.push(first)?;
        for arg in args {
            parts.push(arg?)?;
        }
        string::concat_all(&strings, &parts)?
    };
    Ok(made(mc, fuel, joined.value()))
}
