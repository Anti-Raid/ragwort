//! Intrinsics for the running task's dynamic state, prompt tags, multiple values, procedures,
//! coroutines and error objects.

use ragwort_types::gc::{Gc, Mutation, Value};
use ragwort_types::pair::{Pair, Pairs};
use ragwort_types::string::{self, Strings};
use ragwort_types::symbol::Symbols;

use crate::op::Fuel;
use crate::report::Failure;
use crate::{Fault, coroutine, prompts};
use crate::objects::{self, Condition, ConditionFields, KeywordProcedureFields, Tag, Task, TaskFields};

use super::{Intrinsic, Operands, boolean, is_procedure, made};

impl Intrinsic {
    /// Evaluates less common dynamic intrinsics that inspect or mutate the running `task`'s
    /// state.
    #[inline(never)]
    pub(super) fn dynamic<'gc>(self, mc: &Mutation<'gc>, task: Gc<'gc, Task>, operands: impl Operands<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        if self == Intrinsic::FrameMarks {
            let tag = if operands.get(2).is_false() {
                None
            } else {
                Some(prompts::tag_of(mc, operands.get(2))?)
            };
            return Ok(made(mc, fuel, prompts::part_marks(mc, task, operands.get(0), operands.get(1), tag)?));
        }
        let winders = operands.get(0);
        if winders != Value::NULL && !Pair::of(winders).is_some_and(|cell| cell.head(mc).downcast::<objects::Winder>(mc).is_some()) {
            return Err(Fault::WrongType);
        }
        task.set_winders(mc, winders);
        Ok(Value::VOID)
    }

    /// Evaluates a prompt tag, multiple-value, keyword procedure, continuation or coroutine intrinsic on
    /// `operands`.
    #[inline(never)]
    pub(super) fn control<'gc>(self, mc: &Mutation<'gc>, operands: impl Operands<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        Ok(match self {
            Intrinsic::MakePromptTag => match operands.count() {
                0 => made(mc, fuel, Value::object(mc, Tag::new(mc, Value::VOID)?)),
                1 => made(mc, fuel, Value::object(mc, Tag::new(mc, operands.get(0))?)),
                _ => return Err(Fault::Arity),
            },
            Intrinsic::Values if operands.count() == 1 => operands.get(0),
            Intrinsic::Values => return Err(Fault::ValueCount),
            Intrinsic::MakeKeywordProcedure => {
                let (plain, core) = (operands.get(0), operands.get(1));
                if plain != Value::FALSE && !is_procedure(mc, plain) || !is_procedure(mc, core) {
                    return Err(Fault::WrongType);
                }
                made(mc, fuel, Value::object(mc, objects::KeywordProcedure::new(mc, plain, core, operands.get(2), operands.get(3))?))
            }
            Intrinsic::ProcedureKeywords => {
                let procedure = operands.get(0);
                if !is_procedure(mc, procedure) {
                    return Err(Fault::WrongType);
                }
                let (required, keywords) = match procedure.downcast::<objects::KeywordProcedure>(mc) {
                    Some(keyed) => (keyed.required(mc), keyed.keywords(mc)),
                    None => (Value::NULL, Value::NULL),
                };
                made(mc, fuel, Pairs::new(mc).cons(required, keywords)?.value(mc))
            }
            Intrinsic::IsContinuation => boolean(operands.get(0).downcast::<objects::Continuation>(mc).is_some()),
            Intrinsic::MakeCoroutine => {
                let body = operands.get(0);
                if !is_procedure(mc, body) {
                    return Err(Fault::WrongType);
                }
                made(mc, fuel, Value::object(mc, coroutine::new(mc, body)?))
            }
            Intrinsic::IsCoroutine => boolean(coroutine::of(mc, operands.get(0)).is_some()),
            Intrinsic::CoroutineState => {
                let co = coroutine::of(mc, operands.get(0)).ok_or(Fault::WrongType)?;
                Value::fixnum(i64::from(co.state(mc))).expect("states are fixnums")
            }
            _ => unreachable!("{self:?} isn't a control procedure"),
        })
    }

    /// Evaluates an error-object intrinsic on `operands`.
    #[inline(never)]
    pub(super) fn condition<'gc>(self, mc: &Mutation<'gc>, operands: impl Operands<'gc>, fuel: &mut Fuel) -> Result<Value<'gc>, Fault> {
        Ok(match self {
            Intrinsic::MakeError if operands.count() == 0 => return Err(Fault::Arity),
            Intrinsic::MakeSyntaxError if operands.count() < 2 => return Err(Fault::Arity),
            Intrinsic::MakeError | Intrinsic::MakeSyntaxError => {
                let pairs = Pairs::new(mc);
                let mut irritants = Value::NULL;
                for i in (1..operands.count()).rev() {
                    irritants = pairs.cons(operands.get(i), irritants)?.value(mc);
                }
                let fault = if self == Intrinsic::MakeError {
                    Fault::Error
                } else {
                    Fault::Syntax
                };
                made(mc, fuel, Value::object(mc, Condition::new(mc, mc.frozen(Failure { fault, operation: None })?, operands.get(0), irritants, Value::FALSE)?))
            }
            Intrinsic::ErrorObjectMessage => {
                let condition = operands.get(0).downcast::<Condition>(mc).ok_or(Fault::WrongType)?;
                match condition.message(mc) {
                    Value::VOID => {
                        let words = condition.failure(mc).ok_or(Fault::Malformed)?.fault.message();
                        made(mc, fuel, string::from_str(&Strings::new(mc), words)?.value())
                    }
                    message => message,
                }
            }
            Intrinsic::ErrorObjectIrritants => operands.get(0).downcast::<Condition>(mc).ok_or(Fault::WrongType)?.irritants(mc),
            Intrinsic::ErrorObjectWho => {
                let condition = operands.get(0).downcast::<Condition>(mc).ok_or(Fault::WrongType)?;
                made(mc, fuel, crate::report::who(mc, condition)?)
            }
            Intrinsic::ErrorObjectTraceback => {
                let condition = operands.get(0).downcast::<Condition>(mc).ok_or(Fault::WrongType)?;
                made(mc, fuel, crate::report::traceback(mc, condition)?)
            }
            Intrinsic::ErrorObjectKind => {
                let condition = operands.get(0).downcast::<Condition>(mc).ok_or(Fault::WrongType)?;
                let name = Fault::KINDS[condition.failure(mc).ok_or(Fault::Malformed)?.fault.kind()];
                made(mc, fuel, Symbols::of_arena(mc)?.intern_str(&Strings::new(mc), name)?.value(mc))
            }
            _ => unreachable!("{self:?} isn't an error-object procedure"),
        })
    }
}
