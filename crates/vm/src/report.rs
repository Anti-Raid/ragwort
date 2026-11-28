//! Describes runtime errors: identifies the operation that raised a fault and the values it was given.

use ragwort_types::Wire;
use ragwort_types::gc::raw::Raw;
use ragwort_types::gc::{Frame, Gc, Mutation, Slots, Value};
use ragwort_types::num::NumError;
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::string::{self, StrError, Strings};
use ragwort_types::symbol::Symbol;
use ragwort_types::syntax::SyntaxSource;
use ragwort_types::vector::{AnyVector, Vectors};

use crate::frame::{self, CLOSURE, Link};
use crate::objects::{Bytecode, BytecodeFields, HINT_KEY, HINT_SLOTS, HintsFields, Sites, SitesFields, Closure, ClosureFields, Condition, ConditionFields, FramesFields, KeywordProcedure, KeywordProcedureFields, ModuleFields, Prompt, PromptFields, Task, TaskFields};
use crate::segments::records;
use crate::{Fault, HostDef, Intrinsic, Op, coroutine};

/// A built-in operation that can raise a fault.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Wire)]
pub enum Operation {
    Intrinsic(Intrinsic),
    Host(&'static HostDef),
}

impl Operation {
    /// Returns the name programs call the operation by, such as `car`.
    pub fn name(self) -> &'static str {
        match self {
            Operation::Intrinsic(intrinsic) => intrinsic.name(),
            Operation::Host(host) => host.name,
        }
    }
}

/// The payload of a [`Condition`]: the kind of fault, and the operation that raised it when the VM could identify one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Wire)]
pub struct Failure {
    pub fault: Fault,
    pub operation: Option<Operation>,
}

/// Returns the name of `procedure`: the symbol its definition or binding form bound it to. Returns `None` for an anonymous procedure and for a value that is not a procedure written in the language.
pub fn procedure_name<'gc>(mc: &Mutation<'gc>, procedure: Value<'gc>) -> Option<Symbol<'gc>> {
    let procedure = match procedure.downcast::<KeywordProcedure>(mc) {
        Some(keyword) => keyword.core(mc),
        None => procedure,
    };
    Symbol::of(procedure.downcast::<Closure>(mc)?.code(mc)?.name(mc))
}

/// One row of a compiled function's position table: the instructions from index `pc` up to the next row's `pc` come from byte `offset` of a source. `source` indexes the items of the [`Sites`] object that holds the table. `inlined` is the number of the [`Scope`] the instructions were inlined as part of, counted from one, or 0 for code written in the function itself.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Wire)]
pub struct Line {
    pub pc: u32,
    pub source: u32,
    pub offset: u32,
    pub inlined: u32,
}

/// An inlined call: a procedure whose body the compiler copied into its caller. `name` indexes the items of the [`Sites`] object for the procedure's name, a symbol or `#f`. The remaining fields give the position of the call that was replaced, as a [`Line`] does.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Wire)]
pub struct Scope {
    pub name: u32,
    pub source: u32,
    pub offset: u32,
    pub inlined: u32,
}

/// The position tables of every function compiled together: the rows of all the functions, each function owning one range of them, and the inlined calls the rows refer to.
#[derive(Clone, Debug, Default, PartialEq, Eq, Wire)]
pub struct Table {
    pub lines: Box<[Line]>,
    pub scopes: Box<[Scope]>,
}

/// The operation blamed for a fault, when it has a name, and the values it was given.
pub(crate) struct Origin<'gc> {
    pub(crate) operation: Option<Operation>,
    pub(crate) irritants: Value<'gc>,
}

fn list<'gc>(mc: &Mutation<'gc>, values: impl DoubleEndedIterator<Item = Value<'gc>>) -> Result<Value<'gc>, Fault> {
    let pairs = Pairs::new(mc);
    let mut list = Value::NULL;
    for value in values.rev() {
        list = pairs.cons(value, list)?.value(mc);
    }
    Ok(list)
}

fn count<'gc>(number: u8) -> Value<'gc> {
    Value::fixnum(i64::from(number)).unwrap_or(Value::VOID)
}

/// Identifies the origin of `fault` from the instruction that raised it: the instruction before `pc` in `code`, executing in `frame`.
///
/// Returns an origin with no name and no irritants when the instruction does not explain the fault.
pub(crate) fn origin<'gc>(mc: &Mutation<'gc>, frame: Frame<'_, 'gc>, code: Gc<'gc, Bytecode>, pc: usize, received: Value<'gc>, fault: Fault) -> Result<Origin<'gc>, Fault> {
    let unknown = Origin { operation: None, irritants: Value::NULL };
    let Some(&op) = pc.checked_sub(1).and_then(|at| code.ops(mc)?.get(at)) else { return Ok(unknown) };
    let (operation, irritants) = match op {
        Op::CallIntrinsic1 { a: operand, intrinsic, .. } | Op::BranchIntrinsic1 { a: operand, intrinsic, .. } => (Some(Operation::Intrinsic(intrinsic)), list(mc, [frame.get(operand)].into_iter())?),
        Op::CallIntrinsic2 { a: left, b: right, intrinsic, .. } | Op::BranchIntrinsic2 { a: left, b: right, intrinsic, .. } => (Some(Operation::Intrinsic(intrinsic)), list(mc, [frame.get(left), frame.get(right)].into_iter())?),
        Op::CallIntrinsic3 { a: first, b: second, c: third, intrinsic, .. } => (Some(Operation::Intrinsic(intrinsic)), list(mc, [frame.get(first), frame.get(second), frame.get(third)].into_iter())?),
        Op::CallIntrinsic { base, args, intrinsic } | Op::TailCallIntrinsic { base, args, intrinsic } | Op::ApplyIntrinsic { base, args, intrinsic } => {
            (Some(Operation::Intrinsic(intrinsic)), list(mc, (0..args).map(|i| frame.get(base.wrapping_add(i))))?)
        }
        Op::TableRefHinted { table, hint, .. } => (Some(Operation::Intrinsic(Intrinsic::TableRef)), list(mc, [frame.get(table), hint_key(mc, code, hint), Value::FALSE].into_iter())?),
        Op::TableRefOrHinted { table, default, hint, .. } => (Some(Operation::Intrinsic(Intrinsic::TableRef)), list(mc, [frame.get(table), hint_key(mc, code, hint), frame.get(default)].into_iter())?),
        Op::TableSetHinted { table, value, hint, .. } => (Some(Operation::Intrinsic(Intrinsic::TableSet)), list(mc, [frame.get(table), hint_key(mc, code, hint), frame.get(value)].into_iter())?),
        Op::AddImm { a: operand, imm, .. } => (Some(Operation::Intrinsic(Intrinsic::Add)), list(mc, [frame.get(operand), Value::fixnum(i64::from(imm)).unwrap_or(Value::VOID)].into_iter())?),
        Op::StructField { a: instance, .. } | Op::StructRef { a: instance, .. } => (None, list(mc, [frame.get(instance)].into_iter())?),
        Op::Call { base, args } if fault == Fault::Arity => (None, list(mc, [frame.get(base), count(args)].into_iter())?),
        // A failed tail call has already moved the callee into the frame's closure register.
        Op::TailCall { args, .. } if fault == Fault::Arity => (None, list(mc, [frame.get(CLOSURE), count(args)].into_iter())?),
        // `received` is the number of values the accumulator held. A load takes exactly one value, so the irritant is that number.
        Op::LoadAcc { .. } if fault == Fault::ValueCount => (None, list(mc, [received].into_iter())?),
        // A receiving call passes the values in the accumulator, so `received` is its number of arguments. A failed tail call has already moved the callee, as above.
        Op::CallReceived { base } if fault == Fault::Arity => (None, list(mc, [frame.get(base), received].into_iter())?),
        Op::TailCallReceived { .. } if fault == Fault::Arity => (None, list(mc, [frame.get(CLOSURE), received].into_iter())?),
        Op::LoadSlotChecked { slot, .. } | Op::StoreSlotChecked { slot, .. } if fault == Fault::Unbound => {
            let names = code.module(mc).and_then(|module| AnyVector::of(module.names(mc)));
            let Some(name) = names.and_then(|names| names.get(mc, slot as usize)) else { return Ok(unknown) };
            (None, list(mc, [name].into_iter())?)
        }
        Op::CallHost { base, args, host } | Op::TailCallHost { base, args, host } => {
            let hosts = code.module(mc).and_then(|module| module.hosts(mc));
            let Some(def) = hosts.and_then(|hosts| hosts.get(host as usize)) else { return Ok(unknown) };
            (Some(Operation::Host(def)), list(mc, (0..args).map(|i| frame.get(base.wrapping_add(i))))?)
        }
        _ => return Ok(unknown),
    };
    Ok(Origin { operation, irritants })
}

/// The maximum number of calls a trace records. A deeper call stack is recorded from its innermost call outward and marked as truncated.
const TRACE: usize = 64;

/// The entries of a trace being recorded: alternating bytecode objects and instruction indexes, held on the stack so that recording allocates nothing until the trace is complete.
struct Entries<'gc> {
    values: [Value<'gc>; 2 * TRACE + 1],
    len: usize,
}

impl<'gc> Entries<'gc> {
    /// Appends a call into `code` that returns to instruction `pc`. Returns `false` if the trace is full.
    fn push(&mut self, mc: &Mutation<'gc>, code: Gc<'gc, Bytecode>, pc: usize) -> bool {
        if self.len >= 2 * TRACE {
            return false;
        }
        self.values[self.len] = Value::object(mc, code);
        self.values[self.len + 1] = Value::fixnum(pc as i64).unwrap_or(Value::VOID);
        self.len += 2;
        true
    }
}

/// Appends the calls held by the continuation records of `chain` to `entries`, innermost first. Returns `false` once `entries` is full.
fn calls<'gc>(mc: &Mutation<'gc>, chain: Value<'gc>, entries: &mut Entries<'gc>) -> bool {
    for record in records(mc, chain) {
        let Some(segment) = record.segment(mc) else { return true };
        let Some(link) = Link::of(record.link(mc)) else { continue };
        // Each link gives the distance down to the frame it returns into and the instruction that frame resumes at. A frame that cannot be read ends the record's part of the trace.
        for caller in frame::callers(mc, segment.slots(mc), record.start(mc) as usize, record.end(mc) as usize, link) {
            let Ok(caller) = caller else { break };
            let Some(code) = segment.slots(mc).get(caller.at).downcast::<Closure>(mc).and_then(|closure| closure.code(mc)) else { break };
            if !entries.push(mc, code, caller.pc) {
                return false;
            }
        }
    }
    true
}

/// Appends the calls in the parked frames of `task` to `entries`, innermost first: the frame that switched away, then its callers down to the bottom frame of the task's stack. Returns `false` once `entries` is full.
fn parked<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, entries: &mut Entries<'gc>) -> bool {
    fn code<'gc>(mc: &Mutation<'gc>, slots: Slots<'gc>, at: usize) -> Option<Gc<'gc, Bytecode>> {
        if at < slots.len() {
            slots.get(at).downcast::<Closure>(mc).and_then(|closure| closure.code(mc))
        } else {
            None
        }
    }
    let (true, Some(segment)) = (coroutine::is_parked(mc, task), task.segment(mc)) else { return true };
    let slots = segment.slots(mc);
    let (fp, pc) = (task.park_fp(mc) as usize, task.park_pc(mc) as usize);
    let Some(top) = code(mc, slots, fp) else { return true };
    if !entries.push(mc, top, pc) {
        return false;
    }
    let Ok(link) = frame::link_at(mc, slots, fp) else { return true };
    for caller in frame::callers(mc, slots, task.base(mc) as usize, fp, link) {
        let Ok(caller) = caller else { break };
        let Some(code) = code(mc, slots, caller.at) else { break };
        if !entries.push(mc, code, caller.pc) {
            return false;
        }
    }
    true
}

/// Records the calls in progress when a condition is raised by `task`, innermost first.
///
/// `first` is the function that raised a fault and the index of the instruction after the failed one. The VM discards that function's frame before raising, so it is not among the continuation records. The walk covers the task's continuation, its enclosing prompts, and the tasks that resumed it.
///
/// Returns a vector of alternating bytecode objects and instruction indexes. A trailing `#f` marks a trace that stopped at [`TRACE`] calls.
pub(crate) fn capture<'gc>(mc: &Mutation<'gc>, task: Gc<'gc, Task>, first: Option<(Gc<'gc, Bytecode>, usize)>) -> Result<Value<'gc>, Fault> {
    let mut entries = Entries { values: [Value::FALSE; 2 * TRACE + 1], len: 0 };
    if let Some((code, pc)) = first {
        entries.push(mc, code, pc);
    }
    let mut complete = true;
    let mut running = Some(task);
    let mut tasks = 0;
    while let Some(task) = running.filter(|_| complete && tasks < TRACE) {
        // A task that is waiting for the coroutine it resumed may be parked. Its frames are then on its segment, above every record on its chain.
        complete = parked(mc, task, &mut entries) && calls(mc, task.chain(mc), &mut entries);
        let mut prompts = task.prompts(mc);
        while let Some(cell) = Pair::of(prompts).filter(|_| complete) {
            if let Some(prompt) = cell.head(mc).downcast::<Prompt>(mc) {
                complete = calls(mc, prompt.chain(mc), &mut entries);
            }
            prompts = cell.tail(mc);
        }
        running = coroutine::of(mc, task.resumer(mc));
        tasks += 1;
    }
    // The slot after the last entry already holds `#f`, which marks a truncated trace when it is included.
    let len = if complete {
        entries.len
    } else {
        entries.len + 1
    };
    Ok(Vectors::new(mc).immutable_from_slice(&entries.values[..len])?.value(mc))
}

/// One entry of a call trace: a procedure that was running when an error was raised.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Context {
    /// The procedure's name, or `None` for an anonymous procedure and for top-level code.
    pub procedure: Option<String>,
    /// Whether the entry is the code of a top-level form and not a procedure.
    pub top_level: bool,
    /// The name of the source the entry's position is in, which is a file path for code loaded from a file. `None` when the source is unknown.
    pub file: Option<String>,
    /// The one-based line of the call or operation that was in progress in the procedure, or the line where the procedure is defined when its code records no positions. 0 when unknown.
    pub line: u32,
    /// Whether the compiler inlined the procedure into its caller, so that it had no frame of its own.
    pub inlined: bool,
}

/// The call trace of a raised condition, innermost call first.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Trace {
    pub contexts: Vec<Context>,
    /// Whether the call stack was deeper than the trace records, so that the outermost calls are missing.
    pub truncated: bool,
}

/// One entry of a trace before its name and position are converted for a reader: the procedure's name value, the source and byte offset the entry reports, and whether the procedure was inlined.
struct Entry<'gc> {
    name: Value<'gc>,
    source: Value<'gc>,
    offset: u32,
    inlined: bool,
}

/// Appends the entries for one recorded call to `entries`: the procedures inlined around the instruction before `pc` in `code`, innermost first, and then the procedure `code` itself.
///
/// Each entry reports the position of the call or operation that was in progress in it. A function compiled without positions reports where it is defined.
fn located<'gc>(mc: &Mutation<'gc>, code: Gc<'gc, Bytecode>, pc: usize, entries: &mut Vec<Entry<'gc>>) {
    fn item<'gc>(items: Slots<'gc>, index: u32) -> Value<'gc> {
        if (index as usize) < items.len() {
            items.get(index as usize)
        } else {
            Value::FALSE
        }
    }
    let (mut source, mut offset) = (code.source(mc), code.start(mc));
    let sites = code.sites(mc).downcast::<Sites>(mc);
    if let Some(sites) = sites
        && let Some(table) = sites.table(mc)
    {
        let items = sites.items(mc);
        let (start, len) = (code.lines_start(mc) as usize, code.lines_len(mc) as usize);
        let rows = table.lines.get(start..start + len).unwrap_or(&[]);
        let target = u32::try_from(pc.saturating_sub(1)).unwrap_or(u32::MAX);
        let row = rows.partition_point(|row| row.pc <= target).checked_sub(1).map(|at| rows[at]);
        if let Some(row) = row.filter(|row| row.source != u32::MAX) {
            (source, offset) = (item(items, row.source), row.offset);
            let mut inlined = row.inlined;
            // An inlined call has a higher number than the call that encloses it, so the numbers decrease along the chain of enclosing calls. A scope that breaks this rule ends the walk.
            while let Some(scope) = (inlined as usize).checked_sub(1).and_then(|at| table.scopes.get(at)) {
                entries.push(Entry { name: item(items, scope.name), source, offset, inlined: true });
                if scope.source == u32::MAX || scope.inlined >= inlined {
                    (source, offset) = (code.source(mc), code.start(mc));
                    break;
                }
                (source, offset, inlined) = (item(items, scope.source), scope.offset, scope.inlined);
            }
        }
    }
    entries.push(Entry { name: code.name(mc), source, offset, inlined: false });
}

/// Returns the entries of the trace recorded in `condition`, innermost first, and whether the trace was truncated.
fn recorded<'gc>(mc: &Mutation<'gc>, condition: Gc<'gc, Condition>) -> (Vec<Entry<'gc>>, bool) {
    let mut entries = Vec::new();
    let Some(calls) = AnyVector::of(condition.trace(mc)) else { return (entries, false) };
    let len = calls.len(mc);
    for at in (0..len.saturating_sub(1)).step_by(2) {
        let code = calls.get(mc, at).and_then(|entry| entry.downcast::<Bytecode>(mc));
        let pc = calls.get(mc, at + 1).and_then(|entry| entry.as_fixnum()).and_then(|pc| usize::try_from(pc).ok());
        if let Some((code, pc)) = code.zip(pc) {
            located(mc, code, pc, &mut entries);
        }
    }
    (entries, len % 2 == 1)
}

/// Returns the name of `source` and the one-based line of byte `offset` in it. The name is `None` if the source has no name. The line is 0 if `source` is neither a source object nor a string.
fn place<'gc>(mc: &Mutation<'gc>, source: Value<'gc>, offset: u32) -> (Option<String>, u32) {
    let strings = Strings::new(mc);
    // If `source` is a string, it is the file name and `offset` is already a line number. Code inlined from another module records its origin this way.
    if let Some(name) = strings.string(source) {
        return (Some(string::to_string(&strings, name)), offset);
    }
    let Some(source) = SyntaxSource::of(source) else { return (None, 0) };
    let file = source.name(mc).map(|name| String::from_utf8_lossy(name.bytes(mc)).into_owned());
    let line = source.location(mc, offset).map_or(0, |location| location.line);
    (file, line)
}

/// Returns the call trace recorded in `raised` when it was raised. The trace is empty if `raised` is not a condition or has never been raised.
pub fn trace<'gc>(mc: &Mutation<'gc>, raised: Value<'gc>) -> Trace {
    let Some(condition) = raised.downcast::<Condition>(mc) else { return Trace::default() };
    let strings = Strings::new(mc);
    let (entries, truncated) = recorded(mc, condition);
    let mut contexts = Vec::with_capacity(entries.len());
    for entry in entries {
        let procedure = Symbol::of(entry.name).map(|symbol| string::to_string(&strings, symbol.name(mc)));
        let (file, line) = place(mc, entry.source, entry.offset);
        contexts.push(Context { procedure, top_level: entry.name == Value::VOID, file, line, inlined: entry.inlined });
    }
    Trace { contexts, truncated }
}

/// Builds the value of `(error-object-traceback condition)`: a list with one `(name file line)` entry per call, innermost first. `name` is the procedure's symbol or `#f`. `file` is the name of the source and `line` the line of the call or operation that was in progress in the procedure; they are `#f` when unknown.
pub(crate) fn traceback<'gc>(mc: &Mutation<'gc>, condition: Gc<'gc, Condition>) -> Result<Value<'gc>, Fault> {
    let (pairs, strings) = (Pairs::new(mc), Strings::new(mc));
    let (recorded, _) = recorded(mc, condition);
    let mut entries = Vec::with_capacity(recorded.len());
    for entry in recorded {
        let name = Symbol::of(entry.name).map_or(Value::FALSE, |symbol| symbol.value(mc));
        let (file, line) = place(mc, entry.source, entry.offset);
        let file = match file {
            Some(file) => string::from_str(&strings, &file)?.value(),
            None => Value::FALSE,
        };
        let line = if line == 0 {
            Value::FALSE
        } else {
            Value::fixnum(i64::from(line)).unwrap_or(Value::FALSE)
        };
        entries.push(list(mc, [name, file, line].into_iter())?);
    }
    let mut all = Value::NULL;
    for entry in entries.into_iter().rev() {
        all = pairs.cons(entry, all)?.value(mc);
    }
    Ok(all)
}

/// A raised value, decoded so that a host can match on it.
///
/// Every variant holds live values of the arena, so a `Raised` is usable only within the mutation that produced it. `operation` is the built-in operation or host function that failed, when the VM could identify one, and `operands` is the list of values it was given.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Raised<'gc> {
    /// An operation was given a value of the wrong type.
    WrongType { operation: Option<Operation>, operands: Value<'gc> },
    /// An operation was given an index or another value outside the range it accepts.
    OutOfRange { operation: Option<Operation>, operands: Value<'gc> },
    /// An operation tried to change an immutable object.
    Immutable { operation: Option<Operation>, operands: Value<'gc> },
    /// A numeric operation failed. `error` gives the reason.
    Number { error: NumError, operation: Option<Operation>, operands: Value<'gc> },
    /// A string operation failed. `error` gives the reason.
    String { error: StrError, operation: Option<Operation>, operands: Value<'gc> },
    /// A procedure or operation was called with a number of arguments it does not accept. `procedure` is the procedure that was called, when the call was to a procedure and not to a built-in operation.
    Arity { operation: Option<Operation>, procedure: Option<Value<'gc>>, given: usize },
    /// A place that takes exactly one value received `received` values.
    ValueCount { received: Option<usize> },
    /// A call's target was not a procedure.
    NotProcedure { value: Option<Value<'gc>> },
    /// A variable was read or assigned before its definition ran.
    Unbound { name: Option<Symbol<'gc>> },
    /// A call passed a keyword argument the procedure does not accept, or omitted one it requires.
    Keyword { message: Value<'gc>, irritants: Value<'gc> },
    /// A macro reported a syntax error.
    Syntax { message: Value<'gc>, irritants: Value<'gc> },
    /// The program called `(error message irritant ...)`.
    Error { message: Value<'gc>, irritants: Value<'gc> },
    /// A fault of any other kind.
    Other { fault: Fault, operation: Option<Operation>, operands: Value<'gc> },
    /// The program raised a value that is not an error object.
    Value(Value<'gc>),
}

/// A description of a raised value for a host: the raised value, the decoded error, and the calls that were in progress.
#[derive(Clone, Debug, PartialEq)]
pub struct Report<'gc> {
    /// The value that was raised.
    pub value: Value<'gc>,
    pub error: Raised<'gc>,
    pub trace: Trace,
}

impl<'gc> Report<'gc> {
    /// Describes `raised`, a value that a program raised, such as the value in [`Outcome::Raised`](crate::Outcome::Raised).
    pub fn of(mc: &Mutation<'gc>, raised: Value<'gc>) -> Self {
        Report { value: raised, error: decoded(mc, raised), trace: trace(mc, raised) }
    }
}

fn decoded<'gc>(mc: &Mutation<'gc>, raised: Value<'gc>) -> Raised<'gc> {
    let Some(condition) = raised.downcast::<Condition>(mc) else { return Raised::Value(raised) };
    let Some(&Failure { fault, operation }) = condition.failure(mc) else { return Raised::Value(raised) };
    let (message, operands) = (condition.message(mc), condition.irritants(mc));
    let first = Pair::of(operands).map(|cell| cell.head(mc));
    match fault {
        Fault::WrongType => Raised::WrongType { operation, operands },
        Fault::OutOfRange => Raised::OutOfRange { operation, operands },
        Fault::Immutable => Raised::Immutable { operation, operands },
        Fault::Num(error) => Raised::Number { error, operation, operands },
        Fault::Str(error) => Raised::String { error, operation, operands },
        Fault::Arity if operation.is_some() => Raised::Arity { operation, procedure: None, given: Pair::of(operands).and_then(|cell| cell.list_len(mc)).unwrap_or(0) as usize },
        Fault::Arity => {
            // A call's arity fault lists the procedure and the number of arguments it was given.
            let given = Pair::of(operands).and_then(|cell| Pair::of(cell.tail(mc))).and_then(|cell| cell.head(mc).as_fixnum());
            Raised::Arity { operation, procedure: first, given: given.and_then(|given| usize::try_from(given).ok()).unwrap_or(0) }
        }
        // For the `values` operation, the irritants are the values it was given. For a load, the only irritant is the number of values.
        Fault::ValueCount if operation.is_some() => Raised::ValueCount { received: Pairs::new(mc).list_len(operands).and_then(|received| usize::try_from(received).ok()) },
        Fault::ValueCount => Raised::ValueCount { received: first.and_then(Value::as_fixnum).and_then(|received| usize::try_from(received).ok()) },
        Fault::NotProcedure => Raised::NotProcedure { value: first },
        Fault::Unbound => Raised::Unbound { name: first.and_then(Symbol::of) },
        Fault::Keyword => Raised::Keyword { message, irritants: operands },
        Fault::Syntax => Raised::Syntax { message, irritants: operands },
        Fault::Error => Raised::Error { message, irritants: operands },
        fault => Raised::Other { fault, operation, operands },
    }
}

/// Returns the name of the operation that raised `condition` as a symbol, or `#f` when the VM identified none.
pub(crate) fn who<'gc>(mc: &Mutation<'gc>, condition: Gc<'gc, Condition>) -> Result<Value<'gc>, Fault> {
    let Some(operation) = condition.failure(mc).and_then(|failure| failure.operation) else { return Ok(Value::FALSE) };
    Ok(ragwort_types::symbol::Symbols::of_arena(mc)?.intern_str(&Strings::new(mc), operation.name())?.value(mc))
}

/// Returns the key of hinted table instruction `hint` of `code`, or `#<void>` if the code has no such hint.
fn hint_key<'gc>(mc: &Mutation<'gc>, code: Gc<'gc, Bytecode>, hint: u16) -> Value<'gc> {
    let Some(hints) = code.hints(mc) else { return Value::VOID };
    let hints = HintsFields::items(hints, mc);
    let slot = HINT_SLOTS * usize::from(hint) + HINT_KEY;
    if slot < hints.len() {
        hints.get(slot)
    } else {
        Value::VOID
    }
}
