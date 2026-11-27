//! Writes values as Scheme text, as R7RS's `write`, `write-shared` and `display` do.
//!
//! - The output of `write` reads back as the value that was written. The exceptions are values with no
//!   read syntax: tables, structs, and procedures and other objects that are written as `#<...>`.
//! - A symbol that would not read back as itself is written between `|`s, in the form that the parser reads.
//! - A table is written as `#table((key . value) ...)`, with its entries in the order in which they were added.
//!   That form does not read back.
//!
//! Cycles, shared data and the output limit:
//!
//! - Pairs and immutable vectors cannot change after they are created. So every cycle goes through
//!   a mutable vector, an external vector, a struct or a table.
//! - `write` and `display` label each of those containers that a cycle leads back to. The first
//!   occurrence is written as `#n=` and the datum, and each later occurrence as `#n#`. So printing always terminates.
//! - `write-shared` labels every datum that is reached more than once, in the same way.
//! - `write` and `display` write a datum that is shared without a cycle in full each time. That output
//!   can be exponentially long, so printing fails with [`PrintError::TooLong`] once the output exceeds the caller's limit.
//! - The walk that finds cycles or shared data stops at the same limit. Each datum that the walk visits adds
//!   at least one byte to the output.
//! - Neither the walk nor the printer recurses on the native stack.

#[cfg(test)]
#[path = "tests/printer.rs"]
mod tests;

use std::collections::HashMap;
use std::fmt::{self, Write as _};
use std::hash::{BuildHasherDefault, Hasher};

use ragwort_parser_scheme::{ends_name, might_be_number, number, starts_numeric};
use ragwort_types::Error;
use ragwort_types::bytevector::Bytevectors;
use ragwort_types::external::ExternalRef;
use ragwort_types::gc::{Gc, Mutation, Value};
use ragwort_types::num::{Nums, complex};
use ragwort_types::pair::Pair;
use ragwort_types::string::{self, Strings};
use ragwort_types::symbol::{Keyword, Symbol};
use ragwort_types::syntax::{Abbreviation, Syntax, SyntaxKind};
use ragwort_types::table::Table;
use ragwort_types::vector::{EveryVector, ExternVector, Vector};
use ragwort_vm::report::{Failure, Raised, Report};
use ragwort_vm::objects::{Closure, Condition, ConditionFields, Continuation, KeywordProcedure, Tag, Task};
use ragwort_vm::objects::{Struct, StructFields, StructType, StructTypeFields};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Mode {
    /// Writes as `write` does: the text can be read back, and cycles are labelled.
    Write,
    /// Writes as `write-shared` does: like `write`, but every shared datum is labelled.
    Shared,
    /// Writes as `display` does: strings and characters are written as their text, and symbols as their names.
    Display,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PrintError {
    /// The text grew past the limit.
    TooLong,
    /// The arena reported an error while a number was being converted to text.
    Arena(Error),
}

impl From<Error> for PrintError {
    fn from(error: Error) -> Self {
        Self::Arena(error)
    }
}

impl From<fmt::Error> for PrintError {
    fn from(_: fmt::Error) -> Self {
        Self::TooLong
    }
}

impl fmt::Display for PrintError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TooLong => formatter.write_str("text too long to print"),
            Self::Arena(error) => write!(formatter, "{error:?} while printing"),
        }
    }
}

impl std::error::Error for PrintError {}

/// Formats `report` as the text shown for an uncaught raised value. The value itself is limited to `limit` bytes.
///
/// The first line is `error:` and the message of an error object, or `uncaught:` and the written form of any other value. Each call of the trace follows on a line of its own, innermost first, as `  in name (file:line)`, where the line is that of the call or operation in progress. A procedure the compiler inlined is marked `[inlined]`, and top-level code is shown as `  at file:line`.
///
/// ```text
/// error: car: wrong type of argument: 5
///   in first [inlined] (bot.rg:2)
///   in inner (bot.rg:5)
///   in main (bot.rg:9)
///   at bot.rg:12
/// ```
pub fn render<'gc>(mc: &Mutation<'gc>, report: &Report<'gc>, limit: usize) -> String {
    let (label, mode) = if matches!(report.error, Raised::Value(_)) { ("uncaught", Mode::Write) } else { ("error", Mode::Display) };
    let mut text = format!("{label}: {}", to_string(mc, report.value, mode, limit).unwrap_or_else(|_| "...".to_string()));
    for context in &report.trace.contexts {
        let place = context.file.as_ref().map(|file| format!("{file}:{}", context.line));
        if context.top_level {
            // Top-level code has no name to show, so it is listed only when its position is known.
            if let Some(place) = place {
                text.push_str(&format!("\n  at {place}"));
            }
            continue;
        }
        text.push_str("\n  in ");
        text.push_str(context.procedure.as_deref().unwrap_or("(anonymous)"));
        if context.inlined {
            text.push_str(" [inlined]");
        }
        if let Some(place) = place {
            text.push_str(&format!(" ({place})"));
        }
    }
    if report.trace.truncated {
        text.push_str("\n  ...");
    }
    text
}

/// Returns `value` written as text in `mode`. Fails with [`PrintError::TooLong`] if the text is longer than `limit` bytes.
pub fn to_string<'gc>(mc: &Mutation<'gc>, value: Value<'gc>, mode: Mode, limit: usize) -> Result<String, PrintError> {
    let mut out = String::new();
    print(mc, value, mode, limit, &mut out)?;
    Ok(out)
}

/// Appends `value` to `out` as text in `mode`. Fails with [`PrintError::TooLong`] once it has
/// appended more than `limit` bytes. The text appended up to then stays in `out`.
pub fn print<'gc>(mc: &Mutation<'gc>, value: Value<'gc>, mode: Mode, limit: usize, out: &mut String) -> Result<(), PrintError> {
    let labels = match mode {
        _ if !is_container(mc, value) => Map::default(),
        Mode::Shared => shared(mc, value, limit)?,
        Mode::Write | Mode::Display => cycles(mc, value, limit)?,
    };
    let start = out.len();
    let mut printer = Printer { mc, mode, out, limit: start.saturating_add(limit), strings: Strings::new(mc), nums: Nums::new(mc), labels, next: 0, in_syntax: 0 };
    printer.run(value)
}

/// A hasher for the bits of a value. The keys are object indexes, and one multiplication mixes them well enough.
#[derive(Default)]
struct Fold(u64);

impl Hasher for Fold {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        for &byte in bytes {
            self.write_u64(self.0 ^ u64::from(byte));
        }
    }

    fn write_u64(&mut self, value: u64) {
        let product = u128::from(value) * 0x9e37_79b9_7f4a_7c15;
        self.0 = product as u64 ^ (product >> 64) as u64;
    }
}

type Map<V> = HashMap<u64, V, BuildHasherDefault<Fold>>;

#[derive(Clone, Copy)]
enum Label {
    /// The datum gets its label number when it is first written.
    Pending,
    Number(u64),
}

/// Returns whether `value` holds other values that the printer writes.
fn is_container<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> bool {
    Pair::of(value).is_some()
        || EveryVector::of(value).is_some()
        || Table::of(value).is_some()
        || Syntax::of(value).is_some()
        || value.downcast::<Condition>(mc).is_some()
        || value.downcast::<Struct>(mc).is_some()
}

/// Returns the `i`th of the values held by `value` that the printer writes, or `None` if there are no more.
fn child<'gc>(mc: &Mutation<'gc>, value: Value<'gc>, i: usize) -> Option<Value<'gc>> {
    if let Some(pair) = Pair::of(value) {
        return [pair.head(mc), pair.tail(mc)].get(i).copied();
    }
    // An external vector reads its elements from the host as the walk reaches them. If an element cannot be read because allocation fails, the vector is treated as ending there.
    if let Some(vector) = EveryVector::of(value) {
        return vector.get(mc, i).ok().flatten();
    }
    // Both slots of a removed entry hold `Value::BROKEN`. It is not a container, so the walks skip it.
    if let Some(table) = Table::of(value) {
        return table.held(mc, i);
    }
    if let Some(syntax) = Syntax::of(value) {
        return if i == 0 { Some(syntax.datum(mc)) } else { None };
    }
    if let Some(made) = value.downcast::<Struct>(mc) {
        let fields = made.items(mc);
        return if i < fields.len() { Some(fields.get(i)) } else { None };
    }
    let condition = value.downcast::<Condition>(mc)?;
    [condition.message(mc), condition.irritants(mc)].get(i).copied()
}

/// Returns the labels for the mutable vectors, external vectors, structs and tables in `root` that a cycle leads back to. Each container that the walk visits adds at least
/// one byte to the output, so the walk fails once it has visited more than `limit` containers. Syntax objects are not counted, because nested syntax is written as its datum alone.
fn cycles<'gc>(mc: &Mutation<'gc>, root: Value<'gc>, limit: usize) -> Result<Map<Label>, PrintError> {
    let (mut on_path, mut labels) = (Map::default(), Map::default());
    fn mutable<'gc>(mc: &Mutation<'gc>, value: Value<'gc>) -> bool {
        Vector::of(value).is_some() || ExternVector::of(value).is_some() || Table::of(value).is_some() || value.downcast::<Struct>(mc).is_some()
    }
    if mutable(mc, root) {
        on_path.insert(root.to_bits(), ());
    }
    let (mut path, mut walked) = (vec![(root, 0)], 0usize);
    while let Some((parent, index)) = path.last_mut() {
        let Some(item) = child(mc, *parent, *index) else {
            if mutable(mc, *parent) {
                on_path.remove(&parent.to_bits());
            }
            path.pop();
            continue;
        };
        *index += 1;
        if !is_container(mc, item) {
            continue;
        }
        if mutable(mc, item) {
            // A labelled container is written in full once and as its label after that, so it is not walked again.
            if on_path.contains_key(&item.to_bits()) || labels.contains_key(&item.to_bits()) {
                labels.insert(item.to_bits(), Label::Pending);
                continue;
            }
            on_path.insert(item.to_bits(), ());
        }
        walked += usize::from(Syntax::of(item).is_none());
        if walked > limit {
            return Err(PrintError::TooLong);
        }
        path.push((item, 0));
    }
    Ok(labels)
}

/// Returns the labels for the containers in `root` that are reached more than once. Each container is walked once.
/// The walk fails past `limit` containers for the same reason as in [`cycles`], and it does not count syntax objects either.
fn shared<'gc>(mc: &Mutation<'gc>, root: Value<'gc>, limit: usize) -> Result<Map<Label>, PrintError> {
    let (mut seen, mut labels) = (Map::default(), Map::default());
    seen.insert(root.to_bits(), ());
    let (mut path, mut walked) = (vec![(root, 0)], 0usize);
    while let Some((parent, index)) = path.last_mut() {
        let Some(item) = child(mc, *parent, *index) else {
            path.pop();
            continue;
        };
        *index += 1;
        if !is_container(mc, item) {
            continue;
        }
        if seen.insert(item.to_bits(), ()).is_some() {
            labels.insert(item.to_bits(), Label::Pending);
        } else {
            walked += usize::from(Syntax::of(item).is_none());
            if walked > limit {
                return Err(PrintError::TooLong);
            }
            path.push((item, 0));
        }
    }
    Ok(labels)
}

/// A piece of output that is still to be written. The work stack is popped from its end, so pieces are pushed in reverse order.
enum Work<'gc> {
    Value(Value<'gc>),
    Text(&'static str),
    /// The rest of a list, after an item.
    Tail(Value<'gc>),
    /// The items of a vector or the fields of a struct, from index `at` on.
    Items(Value<'gc>, usize),
    /// The entries of a table from entry number `at` on. The flag is true if an entry was already written, so the next entry needs a space before it.
    Entries(Table<'gc>, usize, bool),
    /// Marks the end of the datum of the outermost syntax object.
    LeaveSyntax,
    /// Switches the printer to the given mode for the work that follows.
    Mode(Mode),
}

struct Printer<'a, 'gc> {
    mc: &'a Mutation<'gc>,
    mode: Mode,
    out: &'a mut String,
    /// The maximum length, in bytes, that `out` can grow to.
    limit: usize,
    strings: Strings<'a, 'gc>,
    nums: Nums<'a, 'gc>,
    labels: Map<Label>,
    next: u64,
    /// Nonzero while the value being written is inside a syntax object. A syntax object inside another is written as
    /// its datum alone.
    in_syntax: usize,
}

impl<'gc> Printer<'_, 'gc> {
    fn run(&mut self, value: Value<'gc>) -> Result<(), PrintError> {
        let mut work = vec![Work::Value(value)];
        while let Some(next) = work.pop() {
            match next {
                Work::Value(value) => self.value(value, &mut work)?,
                Work::Text(text) => self.out.push_str(text),
                Work::Tail(rest) => {
                    if let Some(pair) = Pair::of(rest).filter(|_| !self.labels.contains_key(&rest.to_bits())) {
                        self.out.push(' ');
                        work.extend([Work::Tail(pair.tail(self.mc)), Work::Value(pair.head(self.mc))]);
                    } else if rest != Value::NULL {
                        self.out.push_str(" . ");
                        work.push(Work::Value(rest));
                    }
                }
                Work::Items(of, at) => {
                    if let Some(item) = child(self.mc, of, at) {
                        if at > 0 {
                            self.out.push(' ');
                        }
                        work.extend([Work::Items(of, at + 1), Work::Value(item)]);
                    }
                }
                Work::Entries(table, mut at, written) => {
                    // Both slots of a removed entry hold `Value::BROKEN`. Such an entry is skipped.
                    while table.held(self.mc, 2 * at) == Some(Value::BROKEN) {
                        at += 1;
                    }
                    if let (Some(key), Some(value)) = (table.held(self.mc, 2 * at), table.held(self.mc, 2 * at + 1)) {
                        self.out.push_str(if written { " (" } else { "(" });
                        work.extend([Work::Entries(table, at + 1, true), Work::Text(")"), Work::Value(value), Work::Text(" . "), Work::Value(key)]);
                    }
                }
                Work::LeaveSyntax => self.in_syntax -= 1,
                Work::Mode(mode) => self.mode = mode,
            }
            if self.out.len() > self.limit {
                return Err(PrintError::TooLong);
            }
        }
        Ok(())
    }

    fn value(&mut self, value: Value<'gc>, work: &mut Vec<Work<'gc>>) -> Result<(), PrintError> {
        let mc = self.mc;
        if !self.labels.is_empty()
            && let Some(label) = self.labels.get_mut(&value.to_bits())
        {
            match *label {
                Label::Number(number) => return Ok(write!(self.out, "#{number}#")?),
                Label::Pending => {
                    *label = Label::Number(self.next);
                    write!(self.out, "#{}=", self.next)?;
                    self.next += 1;
                }
            }
        }
        if let Some(pair) = Pair::of(value) {
            self.out.push('(');
            work.extend([Work::Text(")"), Work::Tail(pair.tail(mc)), Work::Value(pair.head(mc))]);
        } else if EveryVector::of(value).is_some() {
            self.out.push_str("#(");
            work.extend([Work::Text(")"), Work::Items(value, 0)]);
        } else if let Some(table) = Table::of(value) {
            self.out.push_str("#table(");
            work.extend([Work::Text(")"), Work::Entries(table, 0, false)]);
        } else if let Some(syntax) = Syntax::of(value) {
            self.syntax(syntax, work);
        } else if let Some(condition) = value.downcast::<Condition>(mc) {
            self.condition(condition, work)?;
        } else if let Some(made) = value.downcast::<Struct>(mc) {
            self.out.push_str("#(struct:");
            self.type_name(made.kind(mc).map(|kind| kind.name(mc)));
            if !made.items(mc).is_empty() {
                self.out.push(' ');
            }
            work.extend([Work::Text(")"), Work::Items(value, 0)]);
        } else if let Some(kind) = value.downcast::<StructType>(mc) {
            self.out.push_str("#<struct-type:");
            self.type_name(Some(kind.name(mc)));
            self.out.push('>');
        } else {
            self.atom(value)?;
        }
        Ok(())
    }

    /// Writes the name of a struct type as plain text, never between `|`s.
    fn type_name(&mut self, name: Option<Value<'gc>>) {
        if let Some(name) = name.and_then(Symbol::of) {
            let _ = write!(self.out, "{}", string::display(&self.strings, name.name(self.mc)));
        }
    }

    fn syntax(&mut self, syntax: Syntax<'gc>, work: &mut Vec<Work<'gc>>) {
        let datum = syntax.datum(self.mc);
        if self.in_syntax == 0 {
            self.out.push_str("#<syntax ");
            self.in_syntax += 1;
            work.extend([Work::Text(">"), Work::LeaveSyntax]);
        }
        if let Some(SyntaxKind::Abbreviation(abbreviation)) = syntax.kind(self.mc) {
            self.out.push_str(prefix(abbreviation));
        }
        work.push(Work::Value(datum));
    }

    fn condition(&mut self, condition: Gc<'gc, Condition>, work: &mut Vec<Work<'gc>>) -> Result<(), PrintError> {
        let mc = self.mc;
        let Some(&Failure { fault, operation }) = condition.failure(mc) else {
            self.out.push_str("#<error>");
            return Ok(());
        };
        let (message, irritants) = (condition.message(mc), condition.irritants(mc));
        if self.mode == Mode::Display {
            // The irritants are written even when the condition is displayed, so that a string irritant keeps its quotes.
            work.extend([Work::Mode(Mode::Display), Work::Tail(irritants), Work::Mode(Mode::Write)]);
            if irritants != Value::NULL {
                work.push(Work::Text(":"));
            }
        } else {
            self.out.push_str("#<error ");
            work.extend([Work::Text(">"), Work::Tail(irritants)]);
        }
        // A fault raised by the VM has no message of its own and is described by its kind.
        if message == Value::VOID {
            work.push(Work::Text(fault.message()));
        } else {
            work.push(Work::Value(message));
        }
        if let Some(operation) = operation {
            work.extend([Work::Text(": "), Work::Text(operation.name())]);
        }
        Ok(())
    }

    fn atom(&mut self, value: Value<'gc>) -> Result<(), PrintError> {
        let mc = self.mc;
        let write = self.mode != Mode::Display;
        if let Some(fixnum) = value.as_fixnum() {
            write!(self.out, "{fixnum}")?;
        } else if let Some(text) = self.strings.string(value) {
            if write {
                self.write_string(text, '"');
            } else {
                // Stop writing once we exceed the remaining byte budget, so multi-byte UTF-8 doesn't overshoot it.
                let mut written = 0;
                let room = self.room();
                for character in string::chars(&self.strings, text) {
                    let len = character.len_utf8();
                    self.out.push(character);
                    written += len;
                    if written > room {
                        break;
                    }
                }
            }
        } else if let Some(symbol) = Symbol::of(value) {
            self.symbol(symbol, write)?;
        } else if let Some(keyword) = Keyword::of(value) {
            let name = string::to_string(&self.strings, keyword.symbol(self.mc).name(self.mc));
            self.out.push_str("#:");
            let bars = name.is_empty() || name.bytes().any(ends_name) || name.chars().any(|character| character.is_control() || character.is_whitespace());
            if write && bars { self.write_text(name.chars(), '|') } else { self.out.push_str(&name) }
        } else if let Some(character) = value.as_char() {
            if write {
                self.write_char(character);
            } else {
                self.out.push(character);
            }
        } else if let Some((offset, _)) = value.as_cursor() {
            write!(self.out, "#<string-cursor {offset}>")?;
        } else if let Some(number) = self.nums.number(value) {
            self.number(number)?;
        } else if let Some(bytes) = Bytevectors::new(mc).bytevector(value) {
            self.out.push_str("#u8(");
            // Each byte takes at least one character of output. Copy out only as many bytes as could still fit.
            let shown = bytes.len(mc).min(self.room().saturating_add(1));
            for (i, byte) in bytes.bytes(mc, 0, shown).iter().enumerate() {
                if i > 0 {
                    self.out.push(' ');
                }
                write!(self.out, "{byte}")?;
            }
            self.out.push(')');
        } else if let Some(external) = ExternalRef::of(value) {
            // An external reference is written as the name of its kind, which the host chose.
            write!(self.out, "#<{}>", external.name(mc))?;
        } else if let Some(name) = ragwort_vm::report::procedure_name(mc, value) {
            self.out.push_str("#<procedure ");
            self.symbol(name, false)?;
            self.out.push('>');
        } else {
            self.out.push_str(match value {
                Value::NULL => "()",
                Value::TRUE => "#t",
                Value::FALSE => "#f",
                Value::NIL => "#nil",
                Value::NONE => "#none",
                Value::VOID => "#<void>",
                Value::UNDEFINED => "#<undefined>",
                Value::UNSUPPLIED => "#<unsupplied>",
                Value::VALUES => "#<values>",
                _ if value.downcast::<Closure>(mc).is_some() || value.downcast::<KeywordProcedure>(mc).is_some() => "#<procedure>",
                _ if value.downcast::<Continuation>(mc).is_some() => "#<continuation>",
                _ if value.downcast::<Task>(mc).is_some() => "#<coroutine>",
                Value::DEFAULT_TAG => "#<prompt-tag>",
                _ if value.downcast::<Tag>(mc).is_some() => "#<prompt-tag>",
                _ => "#<object>",
            });
        }
        Ok(())
    }

    fn number(&mut self, number: ragwort_types::num::Number<'gc>) -> Result<(), PrintError> {
        self.out.push_str(&complex::to_string(&self.nums, number, 10)?);
        Ok(())
    }

    fn symbol(&mut self, symbol: Symbol<'gc>, write: bool) -> Result<(), PrintError> {
        let name = string::to_string(&self.strings, symbol.name(self.mc));
        if write && self.needs_bars(&name) {
            self.write_text(name.chars(), '|');
        } else {
            self.out.push_str(&name);
        }
        Ok(())
    }

    /// Returns whether the parser would read `name` as something other than the identifier with that name.
    fn needs_bars(&self, name: &str) -> bool {
        name.is_empty()
            || name == "."
            || name.starts_with('#')
            || name.bytes().any(ends_name)
            || name.chars().any(|character| character.is_control() || character.is_whitespace())
            || starts_numeric(name)
            || might_be_number(name) && number::parse(&self.nums, name).map_or(true, |parsed| parsed.is_some())
    }

    fn write_string(&mut self, text: ragwort_types::string::Str<'gc>, quote: char) {
        // Each character takes at least one byte of output. Take only as many characters as could still fit.
        let strings = self.strings;
        let most = self.room().saturating_add(1);
        self.write_text(string::chars(&strings, text).take(most), quote);
    }

    /// Returns the number of bytes that can still be written before the output exceeds its limit.
    fn room(&self) -> usize {
        self.limit.saturating_sub(self.out.len())
    }

    /// Writes `chars` between two `quote` characters. A character that would not read back is written as an escape.
    fn write_text(&mut self, chars: impl Iterator<Item = char>, quote: char) {
        self.out.push(quote);
        for character in chars {
            match character {
                '\\' => self.out.push_str("\\\\"),
                _ if character == quote => {
                    self.out.push('\\');
                    self.out.push(character);
                }
                '\n' => self.out.push_str("\\n"),
                '\t' => self.out.push_str("\\t"),
                '\r' => self.out.push_str("\\r"),
                '\x07' => self.out.push_str("\\a"),
                '\x08' => self.out.push_str("\\b"),
                '\0' => self.out.push_str("\\0"),
                _ if unseen(character) => _ = write!(self.out, "\\x{:x};", character as u32),
                _ => self.out.push(character),
            }
        }
        self.out.push(quote);
    }

    fn write_char(&mut self, character: char) {
        let name = match character {
            '\x07' => "alarm",
            '\x08' => "backspace",
            '\x7f' => "delete",
            '\x1b' => "escape",
            '\n' => "newline",
            '\0' => "null",
            '\r' => "return",
            ' ' => "space",
            '\t' => "tab",
            // A zero-width joiner or a variation selector shows nothing on its own either, so it is written by code point.
            _ if unseen(character) || character.is_whitespace() || character == '\u{200d}' || ('\u{fe00}'..='\u{fe0f}').contains(&character) => {
                _ = write!(self.out, "#\\x{:x}", character as u32);
                return;
            }
            _ => {
                self.out.push_str("#\\");
                self.out.push(character);
                return;
            }
        };
        self.out.push_str("#\\");
        self.out.push_str(name);
    }
}

/// Returns whether `character` is invisible when written. Such characters are control characters, noncharacters, and format characters that
/// only affect layout, such as zero-width spaces and direction marks. The zero-width joiner and the variation
/// selectors are excluded, because emoji sequences contain them.
fn unseen(character: char) -> bool {
    let code = character as u32;
    character.is_control()
        || (0xFDD0..=0xFDEF).contains(&code)
        || code & 0xFFFE == 0xFFFE
        || matches!(code, 0xAD | 0x200B | 0x200C | 0x200E | 0x200F | 0x202A..=0x202E | 0x2060..=0x2064 | 0x2066..=0x206F | 0xFEFF | 0xFFF9..=0xFFFB)
}

/// Returns the text that `abbreviation` is written as.
fn prefix(abbreviation: Abbreviation) -> &'static str {
    match abbreviation {
        Abbreviation::Quote => "'",
        Abbreviation::Quasiquote => "`",
        Abbreviation::Unquote => ",",
        Abbreviation::UnquoteSplicing => ",@",
        Abbreviation::Syntax => "#'",
        Abbreviation::Quasisyntax => "#`",
        Abbreviation::Unsyntax => "#,",
        Abbreviation::UnsyntaxSplicing => "#,@",
    }
}
