//! Pass 1 (`Core -> L1`): Validates the input AST structure, resolves top-level bindings and imports,
//! expands optional/keyword lambdas and calls, expands struct and cross-module inline templates,
//! and lowers module-level variable references (`Place::Slot`) into explicit slot access primitives.

use ragwort_types::gc::{Mutation, Value};
use ragwort_types::pair::Pairs;
use ragwort_types::string::{self, Strings};
use ragwort_types::symbol::{Keyword, Symbols};
use ragwort_types::syntax::SyntaxSpan;
use ragwort_types::vector::AnyVector;
use ragwort_vm::{Intrinsic, Request};

use crate::hash::{HashMap, HashSet};
use crate::ir::{Origins, Sites, Supply};
use crate::ir::l1::{Fun, Function, Id, L1, Node};
use crate::keyword::{self, CallShape};
use crate::module::{Binding, Import, Inline, Target, Unit};
use crate::structs::Call;
use crate::{CompileError, Core, GlobalError, OptionalLambda, Place, Position, Prim, SlotOp, Var};

/// Lowers the input `core` AST into the IR `tree`, returning the lowered root node ID and a
/// fresh `Supply` configured for subsequent variable and lambda identifier allocations.
///
/// Implemented iteratively using explicit work and value stacks, preventing machine stack
/// overflow regardless of expression nesting depth.
pub(crate) fn lower<'id, 'gc>(
    mc: &Mutation<'gc>,
    tree: &mut L1<'id, 'gc>,
    core: &Core<'gc>,
    names: &mut Origins<'gc>,
    slot_names: Option<AnyVector<'gc>>,
    unit: Option<&Unit<'_, 'gc>>,
) -> Result<(Id<'id>, Supply), CompileError> {
    let mut pass = Lower {
        mc,
        root: core,
        scanned: false,
        tree,
        names,
        slot_names,
        unit,
        bound: HashSet::default(),
        scope: HashSet::default(),
        lambdas: HashSet::default(),
        max_var: 0,
        max_lambda: 0,
        keyword_procedures: HashMap::default(),
        keyword_cores: HashSet::default(),
    };
    let mut vals = Vec::new();
    // Each task carries the source site of the expression it belongs to, which the nodes it adds receive.
    let mut todo = vec![(Task::Expr(core), 0)];
    let mut then = Vec::new();
    while let Some((task, mut site)) = todo.pop() {
        pass.tree.at(site);
        match task {
            Task::Expr(core) => {
                if let Some(at) = core.position() {
                    site = pass.names.sites.add(at);
                    pass.tree.at(site);
                }
                if let Some(leaf) = pass.enter(core, &mut then)? {
                    vals.push(pass.tree.add(leaf));
                }
                todo.extend(then.drain(..).rev().map(|task| (task, site)));
            }
            Task::Scope(binds) => pass.scope.extend(binds.iter().map(|&(var, _)| var)),
            Task::Bind(var) => {
                pass.scope.insert(var);
            }
            Task::Inline(import, inline, args) => {
                let args = vals.split_off(vals.len() - args);
                vals.push(pass.expand(import, inline, args)?);
            }
            Task::Optional(lambda) => {
                let id = pass.optional(lambda, &mut vals)?;
                vals.push(id);
            }
            Task::Struct(call, args) => {
                let args = vals.split_off(vals.len() - args);
                vals.push(pass.struct_call(call, args));
            }
            Task::Define(procedure, lambda) => {
                let value = vals.pop().expect("the core of a keyword procedure is lowered");
                vals.push(pass.define_keyword(procedure, lambda, value)?);
            }
            Task::Keyword(labels, direct) => {
                let id = pass.keyword_call(labels, direct, &mut vals)?;
                vals.push(id);
            }
            Task::Make(core) => {
                let node = pass.make(core, &mut vals)?;
                vals.push(pass.tree.add(node));
            }
        }
    }
    let supply = Supply { next_var: pass.max_var, next_lambda: pass.max_lambda };
    Ok((vals.pop().expect("the root's lowered"), supply))
}

/// Returns the lambda that the lowered form `root` stores in module variable `slot`, or `None` if `root` does not define `slot` as a lambda.
///
/// A plain definition is a store of the lambda. The definition of a keyword procedure is a `let` whose first binding stores the core lambda, so that binding is checked too.
pub(crate) fn defined<'id>(tree: &L1<'id, '_>, root: Id<'id>, slot: u32) -> Option<Fun<'id>> {
    let set = match tree[root] {
        Node::Let(binds, _) => tree[binds].first()?.1,
        _ => root,
    };
    let Node::Intrinsic(Prim::Slot(SlotOp::Store, stored), value) = tree[set] else { return None };
    let Node::Lambda(fun) = tree[*tree[value].first()?] else { return None };
    (stored == slot).then_some(fun)
}

/// A deferred lowering task: an unlowered AST expression, a lexical scope boundary, or an
/// instruction to assemble a node from lowered subexpressions.
enum Task<'c, 'gc> {
    Expr(&'c Core<'gc>),
    /// Expands a call of an import from its inline template. Runs after the given number of arguments are lowered.
    Inline(Import<'gc>, &'gc Inline, usize),
    /// Introduces the bindings of a `let` expression into the active lexical scope for its body.
    Scope(&'c [(Var, Core<'gc>)]),
    /// Expands a call of a struct procedure of this module. Runs after the given number of arguments are lowered.
    Struct(Call<'gc>, usize),
    /// Builds the definition of a keyword procedure in the given slot. Runs after the lambda is lowered to the core procedure.
    Define(u32, &'c OptionalLambda<'gc>),
    /// Brings one parameter of an optional lambda into scope.
    Bind(Var),
    /// Builds an optional lambda. Runs after its defaults and body are lowered.
    Optional(&'c OptionalLambda<'gc>),
    /// Builds a call with keyword arguments, or any call of a known keyword procedure. Runs after the arguments are lowered. The callee is lowered too, unless the call goes directly to a core procedure.
    ///
    /// The list has one entry per argument, in written order: the argument's keyword, or `None` for a positional argument.
    Keyword(Vec<Option<Keyword<'gc>>>, Option<Direct<'gc>>),
    Make(&'c Core<'gc>),
}

/// What the callee expression of a call refers to at module level.
#[derive(Clone, Copy)]
enum Callee<'gc> {
    /// A variable of this module, by slot.
    Slot(u32),
    Import(Import<'gc>),
    /// Anything else: a local variable, or an expression that is not a name.
    Other,
}

/// Builds the error `kind` for the module-level name at `span`.
fn global_error(kind: GlobalError, span: SyntaxSpan<'_>) -> CompileError {
    CompileError::Global { kind, start: span.start(), end: span.end() }
}

/// A keyword procedure that the compiler can identify at a call site, with its call shape. A call that matches the shape passes its arguments directly to the core procedure.
enum Direct<'gc> {
    /// The core is read from this place. It is a local variable for a procedure bound by `letrec`, and a slot for a procedure of this module.
    Own(Place, CallShape<'gc>),
    /// The core is an export of another module.
    Import(Import<'gc>, CallShape<'gc>),
}

impl<'gc> Direct<'gc> {
    fn shape(&self) -> &CallShape<'gc> {
        let (Direct::Own(_, shape) | Direct::Import(_, shape)) = self;
        shape
    }
}

struct Lower<'t, 'id, 'gc> {
    mc: &'t Mutation<'gc>,
    /// The whole expression being lowered. It is scanned once, the first time lowering needs a fresh variable or the list of keyword procedures.
    root: &'t Core<'gc>,
    scanned: bool,
    tree: &'t mut L1<'id, 'gc>,
    names: &'t mut Origins<'gc>,
    /// The names of the module's variables, indexed by slot. A lambda that defines a variable takes its name from here.
    slot_names: Option<AnyVector<'gc>>,
    /// The module context, if the expression is a top-level form of a module.
    unit: Option<&'t Unit<'t, 'gc>>,
    bound: HashSet<Var>,
    scope: HashSet<Var>,
    lambdas: HashSet<u32>,
    max_var: u32,
    max_lambda: u32,
    /// Keyword procedures bound by a `letrec` in the expression. The key is the procedure's variable. The value is the variable that holds its core, and its call shape.
    ///
    /// A variable that the expression assigns is left out, because a call of it may reach a different procedure.
    keyword_procedures: HashMap<Var, (Var, CallShape<'gc>)>,
    /// The lambda IDs of the procedures in `keyword_procedures`. Each of these lambdas is lowered to its core procedure only.
    keyword_cores: HashSet<u32>,
}

impl<'id, 'gc> Lower<'_, 'id, 'gc> {
    /// Validates `core` upon initial visit. If `core` is a leaf expression, lowers it immediately;
    /// otherwise, pushes tasks onto `then` to lower its subexpressions followed by a task to assemble the parent node.
    fn enter<'c>(&mut self, core: &'c Core<'gc>, then: &mut Vec<Task<'c, 'gc>>) -> Result<Option<Node<'id, 'gc>>, CompileError> {
        let all = |args: &'c [Core<'gc>], then: &mut Vec<Task<'c, 'gc>>| then.extend(args.iter().map(Task::Expr));
        match core {
            Core::Quote(value) => return Ok(Some(Node::Quote(*value))),
            Core::Ref(Place::Local(var)) => {
                self.check_bound(*var)?;
                return Ok(Some(Node::Ref(*var)));
            }
            Core::Ref(Place::Slot { slot, checked }) => {
                let op = if *checked { SlotOp::LoadChecked } else { SlotOp::Load };
                return Ok(Some(Node::Intrinsic(Prim::Slot(op, *slot), self.tree.list([]))));
            }
            Core::If(test, consequent, other) => then.extend([Task::Expr(test), Task::Expr(consequent), Task::Expr(other)]),
            Core::Let(binds, body) => {
                for &(var, _) in binds {
                    self.reserve_var(var)?;
                }
                then.extend(binds.iter().map(|(_, init)| Task::Expr(init)));
                then.extend([Task::Scope(binds), Task::Expr(body)]);
            }
            Core::Letrec(binds, body) => {
                // Find the keyword procedures that this `letrec` binds before lowering any call inside it.
                if binds.iter().any(|(_, init)| matches!(init, Core::OptionalLambda(_))) {
                    self.scan();
                }
                for &(var, _) in binds {
                    self.reserve_var(var)?;
                    self.scope.insert(var);
                }
                then.extend(binds.iter().map(|(_, init)| Task::Expr(init)));
                then.push(Task::Expr(body));
            }
            Core::Set(place, value) => {
                if let Place::Local(var) = place {
                    self.check_bound(*var)?;
                }
                // A definition of a keyword procedure also stores the core procedure in its own slot.
                if let (Place::Slot { slot, .. }, Core::OptionalLambda(lambda)) = (place, &**value)
                    && lambda.params.iter().any(|formal| formal.keyword.is_some())
                    && self.unit.is_some_and(|unit| unit.keyword_definition(*slot).is_some())
                {
                    self.keyword_cores.insert(lambda.id);
                    then.extend([Task::Expr(value), Task::Define(*slot, lambda)]);
                    return Ok(None);
                }
                then.push(Task::Expr(value));
            }
            Core::App(function, args, _) => {
                let callee = self.callee(function)?;
                if let (Callee::Slot(slot), Some(unit)) = (callee, self.unit)
                    && let Some(call) = unit.struct_call(slot, args.len())
                {
                    all(args, then);
                    then.push(Task::Struct(call, args.len()));
                    return Ok(None);
                }
                // A call of a known keyword procedure takes the keyword-call path, even though it has no keyword arguments.
                if let Some(known) = self.known(function, callee) {
                    let direct = Some(known).filter(|known| known.shape().matches(&[], args.len()));
                    if direct.is_none() {
                        then.push(Task::Expr(function));
                    }
                    all(args, then);
                    then.push(Task::Keyword(vec![None; args.len()], direct));
                    return Ok(None);
                }
                // A call that is inlined from an import's template does not evaluate the callee.
                if let Callee::Import(import) = callee
                    && let Some(inline) = import.inlined(self.mc, args.len())
                {
                    all(args, then);
                    then.push(Task::Inline(import, inline, args.len()));
                    return Ok(None);
                }
                then.push(Task::Expr(function));
                all(args, then);
            }
            Core::Import(import) => return self.import_node(*import).map(Some),
            Core::Global(name, span) => {
                let node = match self.global(*name, *span)? {
                    Binding::Slot(slot) => {
                        let unit = self.unit.expect("a name is bound in a module");
                        match unit.constant(slot) {
                            Some(value) => Node::Quote(value),
                            None => return Ok(Some(self.read_node(unit.place(slot)))),
                        }
                    }
                    Binding::Import(import) => self.import_node(import).map_err(|error| match error {
                        CompileError::Import(unusable) => global_error(GlobalError::Import(unusable), *span),
                        other => other,
                    })?,
                };
                return Ok(Some(node));
            }
            Core::SetGlobal(name, value, span) => {
                let assignable = match self.global(*name, *span)? {
                    Binding::Slot(slot) => self.unit.is_some_and(|unit| unit.assign(slot)),
                    Binding::Import(_) => false,
                };
                if !assignable {
                    return Err(global_error(GlobalError::Immutable, *span));
                }
                then.push(Task::Expr(value));
            }
            Core::OptionalLambda(lambda) => {
                if !self.lambdas.insert(lambda.id) {
                    return Err(CompileError::SameLambda(lambda.id));
                }
                self.max_lambda = self.max_lambda.max(lambda.id.saturating_add(1));
                let mut optional = false;
                for (index, formal) in lambda.params.iter().enumerate() {
                    let repeated = formal.keyword.is_some() && lambda.params[..index].iter().any(|other| other.keyword == formal.keyword);
                    let misplaced = formal.keyword.is_none() && formal.default.is_none() && optional;
                    if repeated || misplaced {
                        return Err(CompileError::Formals(lambda.id));
                    }
                    optional |= formal.keyword.is_none() && formal.default.is_some();
                    self.reserve_var(formal.var)?;
                    // A parameter enters scope after its default is lowered. A default can therefore refer only to earlier parameters.
                    then.extend(formal.default.as_ref().map(Task::Expr));
                    then.push(Task::Bind(formal.var));
                }
                if let Some(rest) = lambda.rest {
                    self.reserve_var(rest)?;
                    then.push(Task::Bind(rest));
                }
                then.extend([Task::Expr(&lambda.body), Task::Optional(lambda)]);
                return Ok(None);
            }
            Core::KeywordApp(function, args, _) => {
                let labels: Vec<Option<Keyword<'gc>>> = args.iter().map(|arg| arg.keyword).collect();
                if labels.iter().enumerate().any(|(index, label)| label.is_some() && labels[..index].contains(label)) {
                    return Err(CompileError::SameKeyword);
                }
                let mut given: Vec<Keyword<'gc>> = labels.iter().flatten().copied().collect();
                keyword::sort(self.mc, &mut given);
                let callee = self.callee(function)?;
                let direct = self.known(function, callee).filter(|known| known.shape().matches(&given, labels.len() - given.len()));
                if direct.is_none() {
                    then.push(Task::Expr(function));
                }
                then.extend(args.iter().map(|arg| Task::Expr(&arg.value)));
                then.push(Task::Keyword(labels, direct));
                return Ok(None);
            }
            Core::Lambda(lambda) => {
                if !self.lambdas.insert(lambda.id) {
                    return Err(CompileError::SameLambda(lambda.id));
                }
                if lambda.optional as usize > lambda.params.len() {
                    return Err(CompileError::TooManyOptional(lambda.id));
                }
                self.max_lambda = self.max_lambda.max(lambda.id.saturating_add(1));
                for &var in lambda.params.iter().chain(&lambda.rest) {
                    self.reserve_var(var)?;
                    self.scope.insert(var);
                }
                then.push(Task::Expr(&lambda.body));
            }
            Core::Intrinsic(prim, args, _) => {
                let takes = match *prim {
                    Prim::Intrinsic(intrinsic) => intrinsic.arity().is_none_or(|arity| usize::from(arity) == args.len()),
                    Prim::Request(request) => request.takes(args.len()),
                    Prim::Host(host) => host.takes(args.len()),
                    Prim::Slot(op, _) => op.arity() == args.len(),
                };
                if !takes {
                    return Err(CompileError::Arity(*prim));
                }
                all(args, then);
            }
            Core::ApplyIntrinsic(prim, args, _) => {
                // Host functions and slot primitives cannot be invoked via dynamic apply intrinsics; arguments must fit a VM call frame.
                if args.is_empty() || matches!(prim, Prim::Host(_) | Prim::Slot(..)) {
                    return Err(CompileError::Arity(*prim));
                }
                all(args, then);
            }
        }
        then.push(Task::Make(core));
        Ok(None)
    }

    /// Constructs the lowered L1 node for `core` by popping its lowered child IDs from `vals`, and
    /// removes any variables introduced by this binding form from the active lexical scope.
    fn make(&mut self, core: &Core<'gc>, vals: &mut Vec<Id<'id>>) -> Result<Node<'id, 'gc>, CompileError> {
        let mut last = |count: usize| vals.split_off(vals.len() - count);
        Ok(match core {
            Core::If(..) => {
                let [test, consequent, other] = last(3)[..] else { unreachable!("an if has three parts") };
                Node::If(test, consequent, other)
            }
            Core::Let(binds, _) | Core::Letrec(binds, _) => {
                let mut ids = last(binds.len() + 1);
                let body = ids.pop().expect("a body");
                let mut made = Vec::with_capacity(binds.len());
                for ((var, init), id) in binds.iter().zip(ids) {
                    self.scope.remove(var);
                    // An unnamed lambda takes the name of the variable that it is bound to.
                    let unnamed = match init {
                        Core::Lambda(lambda) if lambda.name.is_none() => Some(lambda.id),
                        Core::OptionalLambda(lambda) if lambda.name.is_none() => Some(lambda.id),
                        _ => None,
                    };
                    if let Some(lambda) = unnamed
                        && let Some(name) = self.unit.and_then(|unit| unit.local_name(*var))
                    {
                        self.names.name(lambda, name);
                    }
                    // For a keyword procedure, `id` is the core procedure. Bind the core first so that calls can reach it, then build the keyword procedure around it.
                    let core = match init {
                        Core::OptionalLambda(lambda) if self.keyword_cores.contains(&lambda.id) => self.keyword_procedures.get(var).cloned(),
                        _ => None,
                    };
                    match core {
                        Some((core, shape)) => {
                            made.push((core, id));
                            made.push((*var, self.procedure(&shape, Place::Local(core))?));
                        }
                        None => made.push((*var, id)),
                    }
                }
                let binds = self.tree.list(made);
                if matches!(core, Core::Let(..)) { Node::Let(binds, body) } else { Node::Letrec(binds, body) }
            }
            Core::Set(Place::Local(var), _) => Node::Set(*var, last(1)[0]),
            Core::Set(Place::Slot { slot, checked }, value) => {
                // An unnamed lambda takes the name of the module variable that it defines.
                let unnamed = match &**value {
                    Core::Lambda(lambda) if lambda.name.is_none() => Some(lambda.id),
                    Core::OptionalLambda(lambda) if lambda.name.is_none() => Some(lambda.id),
                    _ => None,
                };
                if let Some(id) = unnamed
                    && let Some(name) = self.slot_name(*slot)
                {
                    self.names.name(id, name);
                }
                let op = if *checked { SlotOp::StoreChecked } else { SlotOp::Store };
                let value = last(1);
                Node::Intrinsic(Prim::Slot(op, *slot), self.tree.list(value))
            }
            Core::App(_, args, _) => {
                let mut ids = last(args.len() + 1);
                let args = self.tree.list(ids.drain(1..));
                Node::App(ids[0], args)
            }
            Core::Lambda(lambda) => {
                let body = last(1)[0];
                for &var in lambda.params.iter().chain(&lambda.rest) {
                    self.scope.remove(&var);
                }
                let params = self.tree.list(lambda.params.iter().copied());
                self.names.describe(lambda.id, lambda.name, lambda.at);
                Node::Lambda(self.tree.function(Function { id: lambda.id, params, optional: lambda.optional, rest: lambda.rest, body }))
            }
            Core::Intrinsic(prim, args, _) => Node::Intrinsic(*prim, self.tree.list(last(args.len()))),
            Core::ApplyIntrinsic(prim, args, _) => Node::ApplyIntrinsic(*prim, self.tree.list(last(args.len()))),
            Core::SetGlobal(name, ..) => {
                let (Some(unit), Some(Binding::Slot(slot))) = (self.unit, self.unit.and_then(|unit| unit.binding(*name))) else { unreachable!("an assigned name is a variable of the module") };
                let Place::Slot { slot, checked } = unit.place(slot) else { unreachable!("a module variable has a slot") };
                let op = if checked { SlotOp::StoreChecked } else { SlotOp::Store };
                let value = last(1);
                Node::Intrinsic(Prim::Slot(op, slot), self.tree.list(value))
            }
            Core::Quote(_) | Core::Ref(_) | Core::Import(_) | Core::Global(..) => unreachable!("leaves are lowered as they're reached"),
            Core::OptionalLambda(_) | Core::KeywordApp(..) => unreachable!("optional lambdas and keyword calls have tasks of their own"),
        })
    }

    /// Builds the node for a reference to `import`. The node is a constant if the exporting module never assigns the variable, and a read of the variable otherwise.
    fn import_node(&mut self, import: Import<'gc>) -> Result<Node<'id, 'gc>, CompileError> {
        let reference = import.reference(self.mc).map_err(CompileError::Import)?;
        Ok(match &reference {
            Core::Quote(value) => Node::Quote(*value),
            Core::Intrinsic(prim, args, _) => {
                let mut ids = Vec::with_capacity(args.len());
                for arg in args {
                    let Core::Quote(value) = arg else { unreachable!("a module variable is read with constant operands") };
                    ids.push(self.tree.add(Node::Quote(*value)));
                }
                Node::Intrinsic(*prim, self.tree.list(ids))
            }
            _ => unreachable!("an import is a constant or a read of its module's variable"),
        })
    }

    /// Builds a call of `import` with the lowered arguments `args`. The call is inlined if the import has a template that accepts the arguments.
    fn call_import(&mut self, import: Import<'gc>, args: Vec<Id<'id>>) -> Result<Id<'id>, CompileError> {
        if let Some(inline) = import.inlined(self.mc, args.len()) {
            return self.expand(import, inline, args);
        }
        let callee = self.import_node(import)?;
        let (callee, args) = (self.tree.add(callee), self.tree.list(args));
        Ok(self.tree.add(Node::App(callee, args)))
    }

    /// Returns the module-level binding of `name`. Returns an unbound-name error located at `span` if the module has no such binding.
    fn global(&self, name: Value<'gc>, span: SyntaxSpan<'gc>) -> Result<Binding<'gc>, CompileError> {
        self.unit.and_then(|unit| unit.binding(name)).ok_or_else(|| global_error(GlobalError::Unbound, span))
    }

    /// Returns what `function`, the callee expression of a call, refers to at module level.
    fn callee(&self, function: &Core<'gc>) -> Result<Callee<'gc>, CompileError> {
        Ok(match function {
            Core::Ref(Place::Slot { slot, .. }) => Callee::Slot(*slot),
            Core::Import(import) => Callee::Import(*import),
            Core::Global(name, span) => match self.global(*name, *span)? {
                Binding::Slot(slot) => Callee::Slot(slot),
                Binding::Import(import) => Callee::Import(import),
            },
            _ => Callee::Other,
        })
    }

    /// Returns the keyword procedure that `function` is known to be, if any. `callee` is what `function` refers to at module level.
    fn known(&self, function: &Core<'gc>, callee: Callee<'gc>) -> Option<Direct<'gc>> {
        match (function, callee) {
            (Core::Ref(Place::Local(var)), _) if !self.keyword_procedures.is_empty() => {
                let (core, shape) = self.keyword_procedures.get(var)?;
                Some(Direct::Own(Place::Local(*core), shape.clone()))
            }
            (_, Callee::Slot(slot)) => {
                let (core, shape) = self.unit?.keyword_core(slot)?;
                Some(Direct::Own(core, shape.clone()))
            }
            (_, Callee::Import(import)) => {
                let (core, shape) = CallShape::of_import(self.mc, import)?;
                Some(Direct::Import(core, shape))
            }
            _ => None,
        }
    }

    /// Builds a direct call of the core procedure of `direct`.
    ///
    /// The core takes one argument per keyword of the procedure, in sorted order, followed by the positional arguments. `keyword_vars` maps each keyword that the call supplies to the variable holding its value. A keyword that the call does not supply is passed as the unsupplied value.
    fn direct(&mut self, direct: Direct<'gc>, keyword_vars: &[(Keyword<'gc>, Var)], positional: Vec<Id<'id>>) -> Result<Id<'id>, CompileError> {
        let mut args = Vec::with_capacity(direct.shape().keywords.len() + positional.len());
        for &(keyword, _) in &direct.shape().keywords {
            let value = match keyword_vars.iter().find(|&&(given, _)| given == keyword) {
                Some(&(_, var)) => Node::Ref(var),
                None => Node::Quote(Value::UNSUPPLIED),
            };
            args.push(self.tree.add(value));
        }
        args.extend(positional);
        match direct {
            Direct::Own(core, _) => {
                let (callee, args) = (self.read(core), self.tree.list(args));
                Ok(self.tree.add(Node::App(callee, args)))
            }
            Direct::Import(core, _) => self.call_import(core, args),
        }
    }

    /// Builds a read of `place`.
    fn read(&mut self, place: Place) -> Id<'id> {
        let node = self.read_node(place);
        self.tree.add(node)
    }

    fn read_node(&mut self, place: Place) -> Node<'id, 'gc> {
        match place {
            Place::Local(var) => Node::Ref(var),
            Place::Slot { slot, checked } => {
                let op = if checked { SlotOp::LoadChecked } else { SlotOp::Load };
                Node::Intrinsic(Prim::Slot(op, slot), self.tree.list([]))
            }
        }
    }

    /// Expands a call of a struct procedure of this module with the lowered arguments `args`.
    ///
    /// If the procedure's variable may be undefined when the call runs, the expansion reads the variable first. The call then fails the same way an ordinary call would.
    fn struct_call(&mut self, call: Call<'gc>, args: Vec<Id<'id>>) -> Id<'id> {
        let (inline, kind, check) = call.parts();
        if inline.needs_vars() || check.is_some() {
            self.scan();
        }
        let mut build = Build { mc: self.mc, slots: Slots::Kind(kind), tree: self.tree, bound: &mut self.bound, max_var: &mut self.max_var, lines: None };
        let expanded = inline.expand(&mut build, args);
        let Some(place) = check else { return expanded };
        let binds = [(self.fresh_var(), self.read(place))];
        let binds = self.tree.list(binds);
        self.tree.add(Node::Let(binds, expanded))
    }

    /// Builds the definition of the keyword procedure in slot `procedure`. `value` is the lowered core procedure made from `lambda`.
    ///
    /// The result stores the core in its own slot first. It then builds the keyword procedure around the core and stores it in `procedure`.
    fn define_keyword(&mut self, procedure: u32, lambda: &OptionalLambda<'gc>, value: Id<'id>) -> Result<Id<'id>, CompileError> {
        let unit = self.unit.expect("a keyword definition belongs to a module");
        let (core, place, shape) = unit.keyword_definition(procedure).expect("the variable was declared as a keyword procedure");
        if lambda.name.is_none()
            && let Some(name) = self.slot_name(core)
        {
            self.names.name(lambda.id, name);
        }
        let value = self.tree.list([value]);
        let set_core = self.tree.add(Node::Intrinsic(Prim::Slot(SlotOp::Store, core), value));
        let made = self.procedure(shape, place)?;
        let made = self.tree.list([made]);
        let set_procedure = self.tree.add(Node::Intrinsic(Prim::Slot(SlotOp::Store, procedure), made));
        let binds = [(self.fresh_var(), set_core)];
        let binds = self.tree.list(binds);
        Ok(self.tree.add(Node::Let(binds, set_procedure)))
    }

    /// Builds a keyword procedure. Its core procedure is read from `core`, and `shape` describes the arguments it accepts.
    ///
    /// A keyword procedure holds two procedures:
    /// - The core, which takes every keyword value and then the positional arguments.
    /// - A plain procedure for calls without keywords. It calls the core with the unsupplied value for each keyword. A procedure with a required keyword has no plain procedure.
    fn procedure(&mut self, shape: &CallShape<'gc>, core: Place) -> Result<Id<'id>, CompileError> {
        let mc = self.mc;
        let plain = if shape.keywords.iter().any(|&(_, required)| required) {
            self.tree.add(Node::Quote(Value::FALSE))
        } else {
            let params: Vec<Var> = (0..shape.required + shape.optional).map(|_| self.fresh_var()).collect();
            let rest = if shape.rest { Some(self.fresh_var()) } else { None };
            let callee = self.read(core);
            let mut passed = Vec::with_capacity(shape.keywords.len() + params.len() + 2);
            for _ in &shape.keywords {
                passed.push(self.tree.add(Node::Quote(Value::UNSUPPLIED)));
            }
            for &param in &params {
                passed.push(self.tree.add(Node::Ref(param)));
            }
            let body = match rest {
                None => {
                    let passed = self.tree.list(passed);
                    self.tree.add(Node::App(callee, passed))
                }
                Some(rest) => {
                    passed.insert(0, callee);
                    passed.push(self.tree.add(Node::Ref(rest)));
                    let passed = self.tree.list(passed);
                    self.tree.add(Node::Intrinsic(Prim::Request(Request::Apply), passed))
                }
            };
            let optional = u32::try_from(shape.optional).map_err(|_| CompileError::OutOfMemory)?;
            let (id, params) = (self.fresh_lambda(), self.tree.list(params));
            let fun = self.tree.function(Function { id, params, optional, rest, body });
            self.tree.add(Node::Lambda(fun))
        };
        let pairs = Pairs::new(mc);
        let all: Vec<Value<'gc>> = shape.keywords.iter().map(|&(keyword, _)| keyword.value(mc)).collect();
        let required: Vec<Value<'gc>> = shape.keywords.iter().filter(|&&(_, required)| required).map(|&(keyword, _)| keyword.value(mc)).collect();
        let (all, required) = (Node::Quote(pairs.list(&all)?), Node::Quote(pairs.list(&required)?));
        let parts = [plain, self.read(core), self.tree.add(all), self.tree.add(required)];
        let parts = self.tree.list(parts);
        Ok(self.tree.add(Node::Intrinsic(Prim::Intrinsic(Intrinsic::MakeKeywordProcedure), parts)))
    }

    /// Builds the plain lambda for the optional lambda `lambda` from its lowered defaults and body.
    ///
    /// The plain lambda takes the keyword parameters first, in sorted order, and then the positional parameters.
    ///
    /// A parameter with a default is received in a fresh variable. The body is wrapped in a `let` that binds the parameter: to its default if the received value is unsupplied, and to the received value otherwise. These `let`s nest in written order, so a default can refer to earlier parameters.
    ///
    /// For `(lambda (a [b (+ a 1)]) body)` the result is `(lambda (a b0) (let ([b (if (eq? b0 #<unsupplied>) (+ a 1) b0)]) body))`.
    fn optional(&mut self, lambda: &OptionalLambda<'gc>, vals: &mut Vec<Id<'id>>) -> Result<Id<'id>, CompileError> {
        let defaults = lambda.params.iter().filter(|formal| formal.default.is_some()).count();
        let mut ids = vals.split_off(vals.len() - defaults - 1);
        let mut body = ids.pop().expect("a body");
        for var in lambda.params.iter().map(|formal| formal.var).chain(lambda.rest) {
            self.scope.remove(&var);
        }
        // A parameter with a default is received in a fresh variable. Any other parameter is received in its own variable.
        let mut raws = Vec::with_capacity(lambda.params.len());
        for formal in &lambda.params {
            raws.push(if formal.default.is_some() { self.fresh_var() } else { formal.var });
        }
        let mut next = defaults;
        for (formal, &raw) in lambda.params.iter().zip(&raws).rev() {
            if formal.default.is_none() {
                continue;
            }
            next -= 1;
            let operands = [self.tree.add(Node::Ref(raw)), self.tree.add(Node::Quote(Value::UNSUPPLIED))];
            let operands = self.tree.list(operands);
            let missing = self.tree.add(Node::Intrinsic(Prim::Intrinsic(Intrinsic::Eq), operands));
            let given = self.tree.add(Node::Ref(raw));
            let value = self.tree.add(Node::If(missing, ids[next], given));
            let binds = self.tree.list([(formal.var, value)]);
            body = self.tree.add(Node::Let(binds, body));
        }
        let described = described(lambda);
        let shape = CallShape::of(self.mc, &described, lambda.rest.is_some());
        let params: Vec<Var> = keyword::order(self.mc, &described).into_iter().map(|index| raws[index]).collect();
        let optional = u32::try_from(shape.optional).map_err(|_| CompileError::TooManyOptional(lambda.id))?;
        let params = self.tree.list(params);
        self.names.describe(lambda.id, lambda.name, lambda.at);
        let fun = self.tree.function(Function { id: lambda.id, params, optional, rest: lambda.rest, body });
        let plain = self.tree.add(Node::Lambda(fun));
        // Without keywords, the lambda is the whole procedure. With keywords, it is the core: a `letrec` that binds the procedure builds the keyword procedure itself.
        if shape.keywords.is_empty() || self.keyword_cores.contains(&lambda.id) {
            return Ok(plain);
        }
        let core = self.fresh_var();
        let procedure = self.procedure(&shape, Place::Local(core))?;
        let binds = self.tree.list([(core, plain)]);
        Ok(self.tree.add(Node::Let(binds, procedure)))
    }

    /// Builds a call with keyword arguments from the lowered callee and arguments. `labels` holds the keyword of each argument, or `None` for a positional one. The callee is present only if the call is not `direct`.
    ///
    /// Each value is first bound to a fresh variable, callee first and then the arguments in written order. This fixes the evaluation order, because the call itself may pass the arguments in a different order.
    fn keyword_call(&mut self, labels: Vec<Option<Keyword<'gc>>>, direct: Option<Direct<'gc>>, vals: &mut Vec<Id<'id>>) -> Result<Id<'id>, CompileError> {
        let mc = self.mc;
        let count = labels.len() + usize::from(direct.is_none());
        let mut ids = vals.split_off(vals.len() - count).into_iter();
        let mut binds = Vec::with_capacity(count);
        let mut procedure = None;
        if direct.is_none() {
            let var = self.fresh_var();
            binds.push((var, ids.next().expect("the procedure of an indirect call")));
            procedure = Some(var);
        }
        let (mut keyword_vars, mut positional) = (Vec::new(), Vec::new());
        for (label, id) in labels.into_iter().zip(ids) {
            let var = self.fresh_var();
            binds.push((var, id));
            match label {
                Some(keyword) => keyword_vars.push((keyword, var)),
                None => positional.push(self.tree.add(Node::Ref(var))),
            }
        }
        let call = match (direct, procedure) {
            (Some(direct), _) => self.direct(direct, &keyword_vars, positional)?,
            (None, Some(procedure)) => {
                let mut given: Vec<Keyword<'gc>> = keyword_vars.iter().map(|&(keyword, _)| keyword).collect();
                keyword::sort(mc, &mut given);
                let keywords: Vec<Value<'gc>> = given.iter().map(|keyword| keyword.value(mc)).collect();
                let mut values = self.tree.add(Node::Quote(Value::NIL));
                for keyword in given.iter().rev() {
                    let &(_, var) = keyword_vars.iter().find(|&&(given, _)| given == *keyword).expect("a keyword the call gives");
                    let pair = [self.tree.add(Node::Ref(var)), values];
                    let pair = self.tree.list(pair);
                    values = self.tree.add(Node::Intrinsic(Prim::Intrinsic(Intrinsic::Cons), pair));
                }
                let keywords = Node::Quote(Pairs::new(mc).list(&keywords)?);
                let mut all = vec![self.tree.add(Node::Ref(procedure)), self.tree.add(keywords), values];
                all.extend(positional);
                all.push(self.tree.add(Node::Quote(Value::NIL)));
                let all = self.tree.list(all);
                self.tree.add(Node::Intrinsic(Prim::Request(Request::KeywordApply), all))
            }
            (None, None) => unreachable!("an indirect call has its procedure"),
        };
        if binds.is_empty() {
            return Ok(call);
        }
        let binds = self.tree.list(binds);
        Ok(self.tree.add(Node::Let(binds, call)))
    }

    /// Scans the whole expression once. The scan finds the highest variable number and lambda ID in use, so that fresh ones do not collide. It also records the keyword procedures that `letrec` forms bind.
    fn scan(&mut self) {
        if self.scanned {
            return;
        }
        self.scanned = true;
        let (mut vars, mut lambdas) = (0, 0);
        let (mut keyworded, mut assigned) = (Vec::new(), HashSet::default());
        let mut todo = vec![self.root];
        while let Some(core) = todo.pop() {
            match core {
                Core::Quote(_) | Core::Ref(_) | Core::Import(_) | Core::Global(..) => {}
                Core::SetGlobal(_, value, _) => todo.push(value),
                Core::If(test, then, other) => todo.extend([&**test, &**then, &**other]),
                Core::Let(binds, body) | Core::Letrec(binds, body) => {
                    for (var, init) in binds {
                        vars = vars.max(var.0.saturating_add(1));
                        todo.push(init);
                        if let (Core::Letrec(..), Core::OptionalLambda(lambda)) = (core, init)
                            && lambda.params.iter().any(|formal| formal.keyword.is_some())
                        {
                            keyworded.push((*var, lambda));
                        }
                    }
                    todo.push(body);
                }
                Core::Set(place, value) => {
                    if let Place::Local(var) = place {
                        assigned.insert(*var);
                    }
                    todo.push(value);
                }
                Core::App(function, args, _) => {
                    todo.push(function);
                    todo.extend(args);
                }
                Core::Lambda(lambda) => {
                    lambdas = lambdas.max(lambda.id.saturating_add(1));
                    for var in lambda.params.iter().chain(&lambda.rest) {
                        vars = vars.max(var.0.saturating_add(1));
                    }
                    todo.push(&lambda.body);
                }
                Core::OptionalLambda(lambda) => {
                    lambdas = lambdas.max(lambda.id.saturating_add(1));
                    for formal in &lambda.params {
                        vars = vars.max(formal.var.0.saturating_add(1));
                        todo.extend(&formal.default);
                    }
                    if let Some(rest) = lambda.rest {
                        vars = vars.max(rest.0.saturating_add(1));
                    }
                    todo.push(&lambda.body);
                }
                Core::Intrinsic(_, args, _) | Core::ApplyIntrinsic(_, args, _) => todo.extend(args),
                Core::KeywordApp(function, args, _) => {
                    todo.push(function);
                    todo.extend(args.iter().map(|arg| &arg.value));
                }
            }
        }
        self.max_var = self.max_var.max(vars);
        self.max_lambda = self.max_lambda.max(lambdas);
        for (var, lambda) in keyworded {
            if assigned.contains(&var) {
                continue;
            }
            let core = self.fresh_var();
            let shape = CallShape::of(self.mc, &described(lambda), lambda.rest.is_some());
            self.keyword_procedures.insert(var, (core, shape));
            self.keyword_cores.insert(lambda.id);
        }
    }

    /// Allocates a variable that the expression does not use.
    fn fresh_var(&mut self) -> Var {
        self.scan();
        let var = Var(self.max_var);
        self.max_var = self.max_var.checked_add(1).expect("fewer than 2^32 variables");
        self.bound.insert(var);
        var
    }

    /// Allocates a lambda ID that the expression does not use.
    fn fresh_lambda(&mut self) -> u32 {
        self.scan();
        let id = self.max_lambda;
        self.max_lambda = self.max_lambda.checked_add(1).expect("fewer than 2^32 lambdas");
        self.lambdas.insert(id);
        id
    }

    /// Inlines a call of `import` with the lowered arguments `args`, using the template `inline`.
    ///
    /// Unless the template is a thin wrapper, the call is recorded as an inlined call. An error in the expansion then has a traceback entry with the imported procedure's name. The entry shows the line of the failing operation if the template knows it, and the position of the call otherwise.
    fn expand(&mut self, import: Import<'gc>, inline: &'gc Inline, args: Vec<Id<'id>>) -> Result<Id<'id>, CompileError> {
        let mc = self.mc;
        if inline.needs_vars() {
            self.scan();
        }
        let call = self.tree.current();
        let mut lines = None;
        if !inline.is_wrapper() {
            let strings = Strings::new(mc);
            let name = Symbols::of_arena(mc)?.intern_str(&strings, import.name).map_err(|_| CompileError::OutOfMemory)?.value(mc);
            let inlined = self.names.sites.inline(name, call);
            let (site, file) = match inline.origin() {
                // A position whose source is a string holds a line number in `offset`, not a byte offset.
                Some((file, line)) => {
                    let file = string::from_str(&strings, file).map_err(|_| CompileError::OutOfMemory)?.value();
                    (self.names.sites.add_in(Position { source: file, offset: line }, inlined), Some(file))
                }
                None => match self.names.sites.get(call) {
                    Some(site) => (self.names.sites.add_in(site.at, inlined), None),
                    None => (0, None),
                },
            };
            self.tree.at(site);
            lines = file.map(|file| Lines { sites: &mut self.names.sites, file, inlined, definition: site, last: (0, site) });
        }
        let mut build = Build { mc, slots: Slots::Of(import), tree: self.tree, bound: &mut self.bound, max_var: &mut self.max_var, lines };
        let id = inline.expand(&mut build, args);
        self.tree.at(call);
        Ok(id)
    }

    /// Returns the name of module variable `slot`, if the module records one.
    fn slot_name(&self, slot: u32) -> Option<Value<'gc>> {
        self.slot_names?.get(self.mc, slot as usize)
    }

    fn reserve_var(&mut self, var: Var) -> Result<(), CompileError> {
        if !self.bound.insert(var) {
            return Err(CompileError::Rebound(var));
        }
        self.max_var = self.max_var.max(var.0.saturating_add(1));
        Ok(())
    }

    fn check_bound(&self, var: Var) -> Result<(), CompileError> {
        if !self.scope.contains(&var) {
            return Err(CompileError::Unbound(var));
        }
        Ok(())
    }
}

/// Returns the keyword and optionality of each parameter of `lambda`, in the order written.
fn described<'gc>(lambda: &OptionalLambda<'gc>) -> Vec<keyword::Param<'gc>> {
    lambda.params.iter().map(|formal| keyword::Param { keyword: formal.keyword, optional: formal.default.is_some() }).collect()
}

/// What a read of a module variable in an inline template expands to.
enum Slots<'gc> {
    /// The current value of the variable in the module that exports the import.
    Of(Import<'gc>),
    /// The struct's type object. It is the only module variable that the template of a struct procedure reads.
    Kind(Value<'gc>),
}

/// Builds the expansion of an inline template as `L1` nodes.
struct Build<'x, 'id, 'gc> {
    mc: &'x Mutation<'gc>,
    slots: Slots<'gc>,
    tree: &'x mut L1<'id, 'gc>,
    bound: &'x mut HashSet<Var>,
    max_var: &'x mut u32,
    /// Assigns source lines to the operations of a recorded inlined call. It is `None` for a call that is not recorded, and the whole expansion then keeps the position of the call.
    lines: Option<Lines<'x, 'gc>>,
}

/// Creates the source sites for the operations of one inlined call. Each site holds a line in the file that defines the procedure.
struct Lines<'x, 'gc> {
    sites: &'x mut Sites<'gc>,
    /// The name of the file that defines the procedure, as a string value.
    file: Value<'gc>,
    /// The number of the inlined call that these sites belong to.
    inlined: u32,
    /// The site for the line where the procedure's definition starts. An operation whose own line is unknown uses this site.
    definition: u32,
    /// The line and the site of the most recently created site. The next operation on the same line reuses it.
    last: (u32, u32),
}

impl<'id, 'gc> Target<'gc> for Build<'_, 'id, 'gc> {
    type Expr = Id<'id>;

    fn line(&mut self, line: u32) {
        let Some(lines) = &mut self.lines else { return };
        let site = if line == 0 {
            lines.definition
        } else if line == lines.last.0 {
            lines.last.1
        } else {
            let site = lines.sites.add_in(Position { source: lines.file, offset: line }, lines.inlined);
            lines.last = (line, site);
            site
        };
        self.tree.at(site);
    }

    fn fresh(&mut self) -> Var {
        let var = Var(*self.max_var);
        *self.max_var = self.max_var.checked_add(1).expect("fewer than 2^32 variables");
        self.bound.insert(var);
        var
    }

    fn quote(&mut self, value: Value<'gc>) -> Id<'id> {
        self.tree.add(Node::Quote(value))
    }

    fn local(&mut self, var: Var) -> Id<'id> {
        self.tree.add(Node::Ref(var))
    }

    fn slot(&mut self, slot: u32) -> Id<'id> {
        let value = match self.slots {
            Slots::Of(import) => import.variable(self.mc, slot).expect("a template expands only when its module's variables are defined"),
            Slots::Kind(kind) => kind,
        };
        self.tree.add(Node::Quote(value))
    }

    fn bind(&mut self, binds: Vec<(Var, Id<'id>)>, body: Id<'id>) -> Id<'id> {
        let binds = self.tree.list(binds);
        self.tree.add(Node::Let(binds, body))
    }

    fn branch(&mut self, test: Id<'id>, then: Id<'id>, other: Id<'id>) -> Id<'id> {
        self.tree.add(Node::If(test, then, other))
    }

    fn prim(&mut self, prim: Prim, args: Vec<Id<'id>>) -> Id<'id> {
        let args = self.tree.list(args);
        self.tree.add(Node::Intrinsic(prim, args))
    }

    fn apply(&mut self, prim: Prim, args: Vec<Id<'id>>) -> Id<'id> {
        let args = self.tree.list(args);
        self.tree.add(Node::ApplyIntrinsic(prim, args))
    }

    fn call(&mut self, function: Id<'id>, args: Vec<Id<'id>>) -> Id<'id> {
        let args = self.tree.list(args);
        self.tree.add(Node::App(function, args))
    }

    fn is_constant(&self, expr: &Id<'id>) -> bool {
        matches!(self.tree[*expr], Node::Quote(_))
    }

    fn copy(&mut self, expr: &Id<'id>) -> Id<'id> {
        let node = self.tree[*expr];
        self.tree.add(node)
    }
}
