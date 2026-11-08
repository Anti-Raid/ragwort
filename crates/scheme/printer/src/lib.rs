//! Values as Scheme text, as R7RS's `write`, `write-shared` and `display` write them. What
//! `write` writes reads back as what it was, but for procedures and the VM's other objects,
//! written `#<...>`. Symbols that wouldn't read back as themselves are written in `|`, as the
//! parser would read them.
//!
//! Pairs and the other data but mutable vectors can't change, so a cycle goes through a mutable
//! vector: those a cycle comes back to are labelled `#n=`, and with `write-shared`, every datum
//! that's shared, so printing always ends. Without `write-shared`, data shared without a cycle
//! are written out each time, which can be exponentially long, so output stops at a limit, and
//! so does the walk that finds the cycles, which writes no more than it walks. Neither recurses
//! on the native stack.

#[cfg(test)]
#[path = "tests/printer.rs"]
mod tests;

use std::collections::HashMap;
use std::fmt::{self, Write as _};
use std::hash::{BuildHasherDefault, Hasher};

use ragwort_parser_scheme::{ends_name, might_be_number, number, starts_numeric};
use ragwort_types::Error;
use ragwort_types::bytevector::Bytevectors;
use ragwort_types::gc::{Gc, Mutation, Value};
use ragwort_types::num::{Nums, complex};
use ragwort_types::pair::Pair;
use ragwort_types::string::{self, Strings};
use ragwort_types::symbol::{Keyword, Symbol};
use ragwort_types::syntax::{Abbreviation, Syntax, SyntaxKind};
use ragwort_types::vector::{AnyVector, Vector};
use ragwort_vm::Fault;
use ragwort_vm::objects::{Closure, Condition, ConditionFields, Continuation, ExternalRef, KeywordProcedure, MultiValue, MultiValueFields, Tag, Task};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Mode {
    /// As `write`: to be read back, with cycles labelled.
    Write,
    /// As `write-shared`: as `write`, with everything shared labelled.
    Shared,
    /// As `display`: strings and characters as their text, symbols as their names.
    Display,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PrintError {
    /// The text grew past the limit.
    TooLong,
    /// The arena couldn't do what writing a number took.
    Arena(Error),
}

impl From<Error> for PrintError {
    fn from(e: Error) -> Self {
        Self::Arena(e)
    }
}

impl From<fmt::Error> for PrintError {
    fn from(_: fmt::Error) -> Self {
        Self::TooLong
    }
}

impl fmt::Display for PrintError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TooLong => f.write_str("text too long to print"),
            Self::Arena(e) => write!(f, "{e:?} while printing"),
        }
    }
}

impl std::error::Error for PrintError {}

/// `value` as text, in `mode`, of at most `limit` bytes.
pub fn to_string<'gc>(mc: &Mutation<'gc>, value: Value<'gc>, mode: Mode, limit: usize) -> Result<String, PrintError> {
    let mut out = String::new();
    print(mc, value, mode, limit, &mut out)?;
    Ok(out)
}

/// Appends `value` to `out` as text, in `mode`. Fails with [`PrintError::TooLong`] once it's
/// appended more than `limit` bytes, leaving what it appended.
pub fn print<'gc>(mc: &Mutation<'gc>, value: Value<'gc>, mode: Mode, limit: usize, out: &mut String) -> Result<(), PrintError> {
    let labels = match mode {
        _ if !is_container(mc, value) => Map::default(),
        Mode::Shared => shared(mc, value),
        Mode::Write | Mode::Display => cycles(mc, value, limit)?,
    };
    let start = out.len();
    let mut printer = Printer { mc, mode, out, limit: start.saturating_add(limit), strings: Strings::new(mc), nums: Nums::new(mc), labels, next: 0, in_syntax: 0 };
    printer.run(value)
}

/// Value bits are object indexes, which a multiply mixes well enough.
#[derive(Default)]
struct Fold(u64);

impl Hasher for Fold {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.write_u64(self.0 ^ u64::from(b));
        }
    }

    fn write_u64(&mut self, n: u64) {
        let m = u128::from(n) * 0x9e37_79b9_7f4a_7c15;
        self.0 = m as u64 ^ (m >> 64) as u64;
    }
}

type Map<V> = HashMap<u64, V, BuildHasherDefault<Fold>>;

#[derive(Clone, Copy)]
enum Label {
    /// To be labelled where it's first written.
    Pending,
    Number(u64),
}

/// Whether `v` holds other values the printer writes.
fn is_container<'gc>(mc: &Mutation<'gc>, v: Value<'gc>) -> bool {
    Pair::of(v).is_some() || AnyVector::of(v).is_some() || Syntax::of(v).is_some() || v.downcast::<MultiValue>(mc).is_some() || v.downcast::<Condition>(mc).is_some()
}

/// The `i`th value `v` holds that's written, if it has one.
fn child<'gc>(mc: &Mutation<'gc>, v: Value<'gc>, i: usize) -> Option<Value<'gc>> {
    if let Some(pair) = Pair::of(v) {
        return [pair.head(mc), pair.tail(mc)].get(i).copied();
    }
    if let Some(vector) = AnyVector::of(v) {
        return vector.get(mc, i);
    }
    if let Some(syntax) = Syntax::of(v) {
        return (i == 0).then(|| syntax.datum(mc));
    }
    if let Some(many) = v.downcast::<MultiValue>(mc) {
        let items = many.items(mc);
        return (i < items.len()).then(|| items.get(i));
    }
    let condition = v.downcast::<Condition>(mc)?;
    if condition.fault(mc) != Some(&Fault::Error) {
        return None;
    }
    [condition.message(mc), condition.irritants(mc)].get(i).copied()
}

/// The mutable vectors in `root` that a cycle comes back to. What's walked is written at least
/// as long, but for syntax, which is written as its datum, so the walk stops past `limit`.
fn cycles<'gc>(mc: &Mutation<'gc>, root: Value<'gc>, limit: usize) -> Result<Map<Label>, PrintError> {
    let (mut on_path, mut labels) = (Map::default(), Map::default());
    let mutable = |v: Value<'gc>| Vector::of(v).is_some();
    if mutable(root) {
        on_path.insert(root.to_bits(), ());
    }
    let (mut path, mut walked) = (vec![(root, 0)], 0usize);
    while let Some((v, i)) = path.last_mut() {
        let Some(c) = child(mc, *v, *i) else {
            if mutable(*v) {
                on_path.remove(&v.to_bits());
            }
            path.pop();
            continue;
        };
        *i += 1;
        if !is_container(mc, c) {
            continue;
        }
        if mutable(c) {
            // One that's labelled is written in full once, and after as its label.
            if on_path.contains_key(&c.to_bits()) || labels.contains_key(&c.to_bits()) {
                labels.insert(c.to_bits(), Label::Pending);
                continue;
            }
            on_path.insert(c.to_bits(), ());
        }
        walked += usize::from(Syntax::of(c).is_none());
        if walked > limit {
            return Err(PrintError::TooLong);
        }
        path.push((c, 0));
    }
    Ok(labels)
}

/// What in `root` is reached more than once.
fn shared<'gc>(mc: &Mutation<'gc>, root: Value<'gc>) -> Map<Label> {
    let (mut seen, mut labels) = (Map::default(), Map::default());
    seen.insert(root.to_bits(), ());
    let mut path = vec![(root, 0)];
    while let Some((v, i)) = path.last_mut() {
        let Some(c) = child(mc, *v, *i) else {
            path.pop();
            continue;
        };
        *i += 1;
        if !is_container(mc, c) {
            continue;
        }
        if seen.insert(c.to_bits(), ()).is_some() {
            labels.insert(c.to_bits(), Label::Pending);
        } else {
            path.push((c, 0));
        }
    }
    labels
}

/// What's left to write, last first.
enum Work<'gc> {
    Value(Value<'gc>),
    Text(&'static str),
    /// The rest of a list, after an item.
    Tail(Value<'gc>),
    /// The items of a vector or of multiple values from `at`.
    Items(Value<'gc>, usize),
    /// The end of a syntax object's datum.
    LeaveSyntax,
}

struct Printer<'a, 'gc> {
    mc: &'a Mutation<'gc>,
    mode: Mode,
    out: &'a mut String,
    /// The length `out` can grow to.
    limit: usize,
    strings: Strings<'a, 'gc>,
    nums: Nums<'a, 'gc>,
    labels: Map<Label>,
    next: u64,
    /// How many syntax objects the value being written is in. Syntax in syntax is written as
    /// its datum.
    in_syntax: usize,
}

impl<'gc> Printer<'_, 'gc> {
    fn run(&mut self, value: Value<'gc>) -> Result<(), PrintError> {
        let mut work = vec![Work::Value(value)];
        while let Some(next) = work.pop() {
            match next {
                Work::Value(v) => self.value(v, &mut work)?,
                Work::Text(text) => self.out.push_str(text),
                Work::Tail(rest) => {
                    if rest == Value::NIL {
                    } else if let Some(pair) = Pair::of(rest).filter(|_| !self.labels.contains_key(&rest.to_bits())) {
                        self.out.push(' ');
                        work.extend([Work::Tail(pair.tail(self.mc)), Work::Value(pair.head(self.mc))]);
                    } else {
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
                Work::LeaveSyntax => self.in_syntax -= 1,
            }
            if self.out.len() > self.limit {
                return Err(PrintError::TooLong);
            }
        }
        Ok(())
    }

    fn value(&mut self, v: Value<'gc>, work: &mut Vec<Work<'gc>>) -> Result<(), PrintError> {
        let mc = self.mc;
        if !self.labels.is_empty()
            && let Some(label) = self.labels.get_mut(&v.to_bits())
        {
            match *label {
                Label::Number(n) => return Ok(write!(self.out, "#{n}#")?),
                Label::Pending => {
                    *label = Label::Number(self.next);
                    write!(self.out, "#{}=", self.next)?;
                    self.next += 1;
                }
            }
        }
        if let Some(pair) = Pair::of(v) {
            self.out.push('(');
            work.extend([Work::Text(")"), Work::Tail(pair.tail(mc)), Work::Value(pair.head(mc))]);
        } else if AnyVector::of(v).is_some() {
            self.out.push_str("#(");
            work.extend([Work::Text(")"), Work::Items(v, 0)]);
        } else if let Some(syntax) = Syntax::of(v) {
            self.syntax(syntax, work);
        } else if let Some(many) = v.downcast::<MultiValue>(mc) {
            self.out.push_str("#<values");
            if !many.items(mc).is_empty() {
                self.out.push(' ');
            }
            work.extend([Work::Text(">"), Work::Items(v, 0)]);
        } else if let Some(condition) = v.downcast::<Condition>(mc) {
            self.condition(condition, work)?;
        } else {
            self.atom(v)?;
        }
        Ok(())
    }

    fn syntax(&mut self, syntax: Syntax<'gc>, work: &mut Vec<Work<'gc>>) {
        let datum = syntax.datum(self.mc);
        if self.in_syntax == 0 {
            self.out.push_str("#<syntax ");
            self.in_syntax += 1;
            work.extend([Work::Text(">"), Work::LeaveSyntax]);
        }
        if let Some(SyntaxKind::Abbreviation(a)) = syntax.kind(self.mc) {
            self.out.push_str(prefix(a));
        }
        work.push(Work::Value(datum));
    }

    fn condition(&mut self, condition: Gc<'gc, Condition>, work: &mut Vec<Work<'gc>>) -> Result<(), PrintError> {
        let mc = self.mc;
        match condition.fault(mc) {
            Some(Fault::Error) => {
                self.out.push_str("#<error ");
                work.extend([Work::Text(">"), Work::Tail(condition.irritants(mc)), Work::Value(condition.message(mc))]);
            }
            Some(fault) => write!(self.out, "#<error {fault:?}>")?,
            None => self.out.push_str("#<error>"),
        }
        Ok(())
    }

    fn atom(&mut self, v: Value<'gc>) -> Result<(), PrintError> {
        let mc = self.mc;
        let write = self.mode != Mode::Display;
        if let Some(n) = v.as_fixnum() {
            write!(self.out, "{n}")?;
        } else if let Some(s) = self.strings.string(v) {
            if write {
                self.write_string(s, '"');
            } else {
                write!(self.out, "{}", string::display(&self.strings, s))?;
            }
        } else if let Some(symbol) = Symbol::of(v) {
            self.symbol(symbol, write)?;
        } else if let Some(keyword) = Keyword::of(v) {
            let name = string::display(&self.strings, keyword.symbol(self.mc).name(self.mc)).to_string();
            self.out.push_str("#:");
            let bars = name.is_empty() || name.bytes().any(ends_name) || name.chars().any(|c| c.is_control() || c.is_whitespace());
            if write && bars { self.write_text(name.chars(), '|') } else { self.out.push_str(&name) }
        } else if let Some(c) = v.as_char() {
            if write {
                self.write_char(c);
            } else {
                self.out.push(c);
            }
        } else if let Some(z) = self.nums.number(v) {
            self.number(z)?;
        } else if let Some(bytes) = Bytevectors::new(mc).bytevector(v) {
            self.out.push_str("#u8(");
            for (i, b) in bytes.to_vec(mc).into_iter().enumerate() {
                if i > 0 {
                    self.out.push(' ');
                }
                write!(self.out, "{b}")?;
            }
            self.out.push(')');
        } else {
            self.out.push_str(match v {
                Value::NIL => "()",
                Value::TRUE => "#t",
                Value::FALSE => "#f",
                Value::VOID => "#<void>",
                Value::UNDEFINED => "#<undefined>",
                Value::UNSUPPLIED => "#<unsupplied>",
                _ if v.downcast::<Closure>(mc).is_some() || v.downcast::<KeywordProcedure>(mc).is_some() => "#<procedure>",
                _ if v.downcast::<Continuation>(mc).is_some() => "#<continuation>",
                _ if v.downcast::<ExternalRef>(mc).is_some() => "#<external>",
                _ if v.downcast::<Task>(mc).is_some() => "#<coroutine>",
                _ if v.downcast::<Tag>(mc).is_some() => "#<prompt-tag>",
                _ => "#<object>",
            });
        }
        Ok(())
    }

    fn number(&mut self, z: ragwort_types::num::Number<'gc>) -> Result<(), PrintError> {
        self.out.push_str(&complex::to_string(&self.nums, z, 10)?);
        Ok(())
    }

    fn symbol(&mut self, symbol: Symbol<'gc>, write: bool) -> Result<(), PrintError> {
        let name = string::display(&self.strings, symbol.name(self.mc)).to_string();
        if write && self.needs_bars(&name) {
            self.write_text(name.chars(), '|');
        } else {
            self.out.push_str(&name);
        }
        Ok(())
    }

    /// Whether the parser would read `name` as other than the identifier it names.
    fn needs_bars(&self, name: &str) -> bool {
        name.is_empty()
            || name == "."
            || name.starts_with('#')
            || name.bytes().any(ends_name)
            || name.chars().any(|c| c.is_control() || c.is_whitespace())
            || starts_numeric(name)
            || might_be_number(name) && number::parse(&self.nums, name).map_or(true, |n| n.is_some())
    }

    fn write_string(&mut self, s: ragwort_types::string::Str<'gc>, quote: char) {
        let chars: Vec<char> = string::chars(&self.strings, s).collect();
        self.write_text(chars.into_iter(), quote);
    }

    /// `chars` between `quote`s, with escapes for what wouldn't read back.
    fn write_text(&mut self, chars: impl Iterator<Item = char>, quote: char) {
        self.out.push(quote);
        for c in chars {
            match c {
                '\\' => self.out.push_str("\\\\"),
                _ if c == quote => {
                    self.out.push('\\');
                    self.out.push(c);
                }
                '\n' => self.out.push_str("\\n"),
                '\t' => self.out.push_str("\\t"),
                '\r' => self.out.push_str("\\r"),
                '\x07' => self.out.push_str("\\a"),
                '\x08' => self.out.push_str("\\b"),
                '\0' => self.out.push_str("\\0"),
                _ if unseen(c) => _ = write!(self.out, "\\x{:x};", c as u32),
                _ => self.out.push(c),
            }
        }
        self.out.push(quote);
    }

    fn write_char(&mut self, c: char) {
        let name = match c {
            '\x07' => "alarm",
            '\x08' => "backspace",
            '\x7f' => "delete",
            '\x1b' => "escape",
            '\n' => "newline",
            '\0' => "null",
            '\r' => "return",
            ' ' => "space",
            '\t' => "tab",
            // Alone, what joins or varies emoji shows nothing either.
            _ if unseen(c) || c.is_whitespace() || c == '\u{200d}' || ('\u{fe00}'..='\u{fe0f}').contains(&c) => {
                _ = write!(self.out, "#\\x{:x}", c as u32);
                return;
            }
            _ => {
                self.out.push_str("#\\");
                self.out.push(c);
                return;
            }
        };
        self.out.push_str("#\\");
        self.out.push_str(name);
    }
}

/// What `a` is written as.
/// Whether `c` shows nothing where it's written: controls, noncharacters, and the marks that
/// only steer layout, such as zero-width spaces and direction marks. Joiners and variation
/// selectors are left out, as emoji are made of them.
fn unseen(c: char) -> bool {
    let n = c as u32;
    c.is_control()
        || (0xFDD0..=0xFDEF).contains(&n)
        || n & 0xFFFE == 0xFFFE
        || matches!(n, 0xAD | 0x200B | 0x200C | 0x200E | 0x200F | 0x202A..=0x202E | 0x2060..=0x2064 | 0x2066..=0x206F | 0xFEFF | 0xFFF9..=0xFFFB)
}

fn prefix(a: Abbreviation) -> &'static str {
    match a {
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
