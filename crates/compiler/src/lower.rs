//! Pass 1 (`Core -> L1`): Validates the input AST structure, resolves top-level bindings and imports,
//! expands optional/keyword lambdas and calls, expands struct and cross-module inline templates,
//! and lowers module-level variable references (`Place::Slot`) into explicit slot access primitives.

use ragwort_types::gc::{Mutation, Value};
use ragwort_types::pair::Pairs;
use ragwort_types::string::{self, Strings};
use ragwort_types::symbol::{Keyword, Symbols};
use ragwort_types::syntax::SyntaxSpan;
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
    slot_name: &dyn Fn(u32) -> Option<Value<'gc>>,
    unit: Option<&Unit<'_, 'gc>>,
) -> Result<(Id<'id>, Supply), CompileError> {
    let mut pass = Lower {
        mc,
        root: core,
        scanned: false,
        tree,
        names,
        slot_name,
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
            Task::Scope(binds) => pass.scope.extend(binds.iter().map(|&(v, _)| v)),
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

/// Returns the lambda that the lowered form `root` sets the module variable `slot` to, if the form is a definition of `slot` as a lambda. The definition of a keyword procedure sets the variable of its core first, in a `let` around the rest.
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
    /// Expands a call of the import from its inline template, once the given number of arguments are lowered.
    Inline(Import<'gc>, &'gc Inline, usize),
    /// Introduces the bindings of a `let` expression into the active lexical scope for its body.
    Scope(&'c [(Var, Core<'gc>)]),
    /// Expands a call of a struct procedure of the module being built, once the given number of arguments are lowered.
    Struct(Call<'gc>, usize),
    /// Assembles the definition of the keyword procedure in the given module variable, once the core that the lambda makes is lowered.
    Define(u32, &'c OptionalLambda<'gc>),
    /// Brings a parameter of an optional lambda into scope.
    Bind(Var),
    /// Assembles an optional lambda, once its defaults and body are lowered.
    Optional(&'c OptionalLambda<'gc>),
    /// Assembles a call with keyword arguments, or a call of a known keyword procedure, once the procedure (unless the call goes straight to its core) and the arguments are lowered. The list holds the keyword of each argument in the order written, or `None` for a positional argument.
    Keyword(Vec<Option<Keyword<'gc>>>, Option<Direct<'gc>>),
    Make(&'c Core<'gc>),
}

/// The module-level binding that the procedure expression of a call refers to.
#[derive(Clone, Copy)]
enum Callee<'gc> {
    /// A variable of the module being built.
    Slot(u32),
    Import(Import<'gc>),
    /// A local variable, or an expression that is not a name.
    Other,
}

/// Builds the error `kind` for the top-level name at `span`.
fn global_error(kind: GlobalError, span: SyntaxSpan<'_>) -> CompileError {
    CompileError::Global { kind, start: span.start(), end: span.end() }
}

/// The core of a keyword procedure that a call is known to reach, with the procedure's shape. A call that the shape accepts passes its arguments to the core directly.
enum Direct<'gc> {
    /// A procedure whose core is read from the place: a variable that a `letrec` of the expression being lowered binds, or a variable of the module being built.
    Own(Place, CallShape<'gc>),
    /// A procedure of another module, which exports its core.
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
    /// The whole expression being lowered, which is scanned the first time lowering needs a fresh variable or the keyword procedures the expression binds.
    root: &'t Core<'gc>,
    scanned: bool,
    tree: &'t mut L1<'id, 'gc>,
    names: &'t mut Origins<'gc>,
    /// Returns the name of a module variable slot, which names a lambda that the slot is defined as.
    slot_name: &'t dyn Fn(u32) -> Option<Value<'gc>>,
    /// The module being built, when the expression is one of its top-level forms.
    unit: Option<&'t Unit<'t, 'gc>>,
    bound: HashSet<Var>,
    scope: HashSet<Var>,
    lambdas: HashSet<u32>,
    max_var: u32,
    max_lambda: u32,
    /// The keyword procedures that a `letrec` of the expression binds: for each procedure's variable, the variable that holds its core and its shape. A variable the expression assigns is left out, since its calls may reach another procedure.
    keyword_procedures: HashMap<Var, (Var, CallShape<'gc>)>,
    /// The lambda IDs of those procedures, whose cores their `letrec` binds.
    keyword_cores: HashSet<u32>,
}

impl<'id, 'gc> Lower<'_, 'id, 'gc> {
    /// Validates `core` upon initial visit. If `core` is a leaf expression, lowers it immediately;
    /// otherwise, pushes tasks onto `then` to lower its subexpressions followed by a task to assemble the parent node.
    fn enter<'c>(&mut self, core: &'c Core<'gc>, then: &mut Vec<Task<'c, 'gc>>) -> Result<Option<Node<'id, 'gc>>, CompileError> {
        let all = |args: &'c [Core<'gc>], then: &mut Vec<Task<'c, 'gc>>| then.extend(args.iter().map(Task::Expr));
        match core {
            Core::Quote(v) => return Ok(Some(Node::Quote(*v))),
            Core::Ref(Place::Local(v)) => {
                self.check_bound(*v)?;
                return Ok(Some(Node::Ref(*v)));
            }
            Core::Ref(Place::Slot { slot, checked }) => {
                let op = if *checked { SlotOp::LoadChecked } else { SlotOp::Load };
                return Ok(Some(Node::Intrinsic(Prim::Slot(op, *slot), self.tree.list([]))));
            }
            Core::If(test, t, other) => then.extend([Task::Expr(test), Task::Expr(t), Task::Expr(other)]),
            Core::Let(binds, body) => {
                for &(v, _) in binds {
                    self.reserve_var(v)?;
                }
                then.extend(binds.iter().map(|(_, init)| Task::Expr(init)));
                then.extend([Task::Scope(binds), Task::Expr(body)]);
            }
            Core::Letrec(binds, body) => {
                // The keyword procedures a `letrec` binds must be known before any call in it is lowered.
                if binds.iter().any(|(_, init)| matches!(init, Core::OptionalLambda(_))) {
                    self.scan();
                }
                for &(v, _) in binds {
                    self.reserve_var(v)?;
                    self.scope.insert(v);
                }
                then.extend(binds.iter().map(|(_, init)| Task::Expr(init)));
                then.push(Task::Expr(body));
            }
            Core::Set(place, value) => {
                if let Place::Local(v) = place {
                    self.check_bound(*v)?;
                }
                // The definition of a keyword procedure of the module sets the variable of its core too.
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
            Core::App(f, args, _) => {
                let callee = self.callee(f)?;
                if let (Callee::Slot(slot), Some(unit)) = (callee, self.unit)
                    && let Some(call) = unit.struct_call(slot, args.len())
                {
                    all(args, then);
                    then.push(Task::Struct(call, args.len()));
                    return Ok(None);
                }
                // A call of a known keyword procedure is assembled as a call with keyword arguments is, although it has none.
                if let Some(known) = self.known(f, callee) {
                    let direct = Some(known).filter(|known| known.shape().matches(&[], args.len()));
                    if direct.is_none() {
                        then.push(Task::Expr(f));
                    }
                    all(args, then);
                    then.push(Task::Keyword(vec![None; args.len()], direct));
                    return Ok(None);
                }
                // A call that expands from an import's template has no callee to evaluate.
                if let Callee::Import(import) = callee
                    && let Some(inline) = import.inlined(self.mc, args.len())
                {
                    all(args, then);
                    then.push(Task::Inline(import, inline, args.len()));
                    return Ok(None);
                }
                then.push(Task::Expr(f));
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
                    Binding::Import(import) => self.import_node(import).map_err(|e| match e {
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
            Core::OptionalLambda(f) => {
                if !self.lambdas.insert(f.id) {
                    return Err(CompileError::SameLambda(f.id));
                }
                self.max_lambda = self.max_lambda.max(f.id.saturating_add(1));
                let mut optional = false;
                for (i, formal) in f.params.iter().enumerate() {
                    let repeated = formal.keyword.is_some() && f.params[..i].iter().any(|other| other.keyword == formal.keyword);
                    let misplaced = formal.keyword.is_none() && formal.default.is_none() && optional;
                    if repeated || misplaced {
                        return Err(CompileError::Formals(f.id));
                    }
                    optional |= formal.keyword.is_none() && formal.default.is_some();
                    self.reserve_var(formal.var)?;
                    // A parameter comes into scope after its default is lowered, so a default refers only to the parameters before it.
                    then.extend(formal.default.as_ref().map(Task::Expr));
                    then.push(Task::Bind(formal.var));
                }
                if let Some(rest) = f.rest {
                    self.reserve_var(rest)?;
                    then.push(Task::Bind(rest));
                }
                then.extend([Task::Expr(&f.body), Task::Optional(f)]);
                return Ok(None);
            }
            Core::KeywordApp(f, args, _) => {
                let labels: Vec<Option<Keyword<'gc>>> = args.iter().map(|arg| arg.keyword).collect();
                if labels.iter().enumerate().any(|(i, label)| label.is_some() && labels[..i].contains(label)) {
                    return Err(CompileError::SameKeyword);
                }
                let mut given: Vec<Keyword<'gc>> = labels.iter().flatten().copied().collect();
                keyword::sort(self.mc, &mut given);
                let callee = self.callee(f)?;
                let direct = self.known(f, callee).filter(|known| known.shape().matches(&given, labels.len() - given.len()));
                if direct.is_none() {
                    then.push(Task::Expr(f));
                }
                then.extend(args.iter().map(|arg| Task::Expr(&arg.value)));
                then.push(Task::Keyword(labels, direct));
                return Ok(None);
            }
            Core::Lambda(f) => {
                if !self.lambdas.insert(f.id) {
                    return Err(CompileError::SameLambda(f.id));
                }
                if f.optional as usize > f.params.len() {
                    return Err(CompileError::TooManyOptional(f.id));
                }
                self.max_lambda = self.max_lambda.max(f.id.saturating_add(1));
                for &v in f.params.iter().chain(&f.rest) {
                    self.reserve_var(v)?;
                    self.scope.insert(v);
                }
                then.push(Task::Expr(&f.body));
            }
            Core::Intrinsic(prim, args, _) => {
                let takes = match *prim {
                    Prim::Intrinsic(i) => i.arity().is_none_or(|n| usize::from(n) == args.len()),
                    Prim::Request(r) => r.takes(args.len()),
                    Prim::Host(h) => h.takes(args.len()),
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
        let mut last = |n: usize| vals.split_off(vals.len() - n);
        Ok(match core {
            Core::If(..) => {
                let [test, t, other] = last(3)[..] else { unreachable!("an if has three parts") };
                Node::If(test, t, other)
            }
            Core::Let(binds, _) | Core::Letrec(binds, _) => {
                let mut ids = last(binds.len() + 1);
                let body = ids.pop().expect("a body");
                let mut made = Vec::with_capacity(binds.len());
                for ((v, init), id) in binds.iter().zip(ids) {
                    self.scope.remove(v);
                    // A lambda takes the name of the variable it is bound to, unless it has one already.
                    let unnamed = match init {
                        Core::Lambda(f) if f.name.is_none() => Some(f.id),
                        Core::OptionalLambda(f) if f.name.is_none() => Some(f.id),
                        _ => None,
                    };
                    if let Some(lambda) = unnamed
                        && let Some(name) = self.unit.and_then(|unit| unit.local_name(*v))
                    {
                        self.names.name(lambda, name);
                    }
                    // A keyword procedure the `letrec` binds is lowered to its core, which is bound first so that calls can reach it, and the procedure is made around it.
                    let core = match init {
                        Core::OptionalLambda(f) if self.keyword_cores.contains(&f.id) => self.keyword_procedures.get(v).cloned(),
                        _ => None,
                    };
                    match core {
                        Some((core, shape)) => {
                            made.push((core, id));
                            made.push((*v, self.procedure(&shape, Place::Local(core))?));
                        }
                        None => made.push((*v, id)),
                    }
                }
                let binds = self.tree.list(made);
                if matches!(core, Core::Let(..)) { Node::Let(binds, body) } else { Node::Letrec(binds, body) }
            }
            Core::Set(Place::Local(v), _) => Node::Set(*v, last(1)[0]),
            Core::Set(Place::Slot { slot, checked }, value) => {
                // A lambda that defines a module variable takes the variable's name, unless it has one already.
                let unnamed = match &**value {
                    Core::Lambda(f) if f.name.is_none() => Some(f.id),
                    Core::OptionalLambda(f) if f.name.is_none() => Some(f.id),
                    _ => None,
                };
                if let Some(id) = unnamed
                    && let Some(name) = (self.slot_name)(*slot)
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
            Core::Lambda(f) => {
                let body = last(1)[0];
                for &v in f.params.iter().chain(&f.rest) {
                    self.scope.remove(&v);
                }
                let params = self.tree.list(f.params.iter().copied());
                self.names.describe(f.id, f.name, f.at);
                Node::Lambda(self.tree.function(Function { id: f.id, params, optional: f.optional, rest: f.rest, body }))
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

    /// Builds the node for a reference to `import`: the constant its module's variable holds, or a read of that variable if the module assigns it.
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

    /// Builds a call of `import` with the lowered arguments `args`, expanding its inline template if it has one that takes them.
    fn call_import(&mut self, import: Import<'gc>, args: Vec<Id<'id>>) -> Result<Id<'id>, CompileError> {
        if let Some(inline) = import.inlined(self.mc, args.len()) {
            return self.expand(import, inline, args);
        }
        let callee = self.import_node(import)?;
        let (callee, args) = (self.tree.add(callee), self.tree.list(args));
        Ok(self.tree.add(Node::App(callee, args)))
    }

    /// Returns what the name `name` is bound to at the top level of the module, or the error of a name that nothing binds, located at `span`.
    fn global(&self, name: Value<'gc>, span: SyntaxSpan<'gc>) -> Result<Binding<'gc>, CompileError> {
        self.unit.and_then(|unit| unit.binding(name)).ok_or_else(|| global_error(GlobalError::Unbound, span))
    }

    /// Returns the module-level binding that the procedure expression `f` of a call refers to, if it refers to one.
    fn callee(&self, f: &Core<'gc>) -> Result<Callee<'gc>, CompileError> {
        Ok(match f {
            Core::Ref(Place::Slot { slot, .. }) => Callee::Slot(*slot),
            Core::Import(import) => Callee::Import(*import),
            Core::Global(name, span) => match self.global(*name, *span)? {
                Binding::Slot(slot) => Callee::Slot(slot),
                Binding::Import(import) => Callee::Import(import),
            },
            _ => Callee::Other,
        })
    }

    /// Returns the core and shape of the keyword procedure that `f`, which refers to `callee`, is known to be, if it is one.
    fn known(&self, f: &Core<'gc>, callee: Callee<'gc>) -> Option<Direct<'gc>> {
        match (f, callee) {
            (Core::Ref(Place::Local(v)), _) if !self.keyword_procedures.is_empty() => {
                let (core, shape) = self.keyword_procedures.get(v)?;
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

    /// Builds a call that passes arguments straight to the core `direct`: the value of each keyword the core takes, in sorted order, then the positional arguments. `keyword_vars` holds the variable of each keyword the call gives; a keyword it leaves out is passed as unsupplied.
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

    /// Expands a call of a struct procedure of the module being built with the lowered arguments `args`. If the procedure's variable may be undefined when the call runs, the expansion reads it first, so that the call fails as an ordinary call would.
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

    /// Assembles the definition of the keyword procedure in the module variable `procedure` from `value`, the lowered core that `lambda` makes: the variable of the core is set, then the variable of the procedure built around it.
    fn define_keyword(&mut self, procedure: u32, lambda: &OptionalLambda<'gc>, value: Id<'id>) -> Result<Id<'id>, CompileError> {
        let unit = self.unit.expect("a keyword definition belongs to a module");
        let (core, place, shape) = unit.keyword_definition(procedure).expect("the variable was declared as a keyword procedure");
        if lambda.name.is_none()
            && let Some(name) = (self.slot_name)(core)
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

    /// Builds the keyword procedure whose core is read from `core` and whose shape is `shape`.
    ///
    /// The procedure holds the core and a plain procedure for calls without keywords, which passes the core an unsupplied value for each keyword. A procedure with a required keyword has no plain procedure.
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

    /// Assembles the optional lambda `f` from its lowered defaults and body.
    ///
    /// The plain lambda takes the keyword parameters first, sorted, then the positional ones. A parameter with a default arrives in a variable of its own: the body is wrapped in a binding of the parameter to its default when that variable is unsupplied, and to the variable otherwise. The bindings nest in the order the parameters are written, so a default sees the parameters before it.
    fn optional(&mut self, f: &OptionalLambda<'gc>, vals: &mut Vec<Id<'id>>) -> Result<Id<'id>, CompileError> {
        let defaults = f.params.iter().filter(|formal| formal.default.is_some()).count();
        let mut ids = vals.split_off(vals.len() - defaults - 1);
        let mut body = ids.pop().expect("a body");
        for var in f.params.iter().map(|formal| formal.var).chain(f.rest) {
            self.scope.remove(&var);
        }
        // A parameter with a default arrives in a fresh variable, and any other parameter in its own.
        let mut raws = Vec::with_capacity(f.params.len());
        for formal in &f.params {
            raws.push(if formal.default.is_some() { self.fresh_var() } else { formal.var });
        }
        let mut next = defaults;
        for (formal, &raw) in f.params.iter().zip(&raws).rev() {
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
        let described = described(f);
        let shape = CallShape::of(self.mc, &described, f.rest.is_some());
        let params: Vec<Var> = keyword::order(self.mc, &described).into_iter().map(|i| raws[i]).collect();
        let optional = u32::try_from(shape.optional).map_err(|_| CompileError::TooManyOptional(f.id))?;
        let params = self.tree.list(params);
        self.names.describe(f.id, f.name, f.at);
        let fun = self.tree.function(Function { id: f.id, params, optional, rest: f.rest, body });
        let lambda = self.tree.add(Node::Lambda(fun));
        // Without keywords the lambda is the procedure. With them, the `letrec` that binds the procedure makes it around this core.
        if shape.keywords.is_empty() || self.keyword_cores.contains(&f.id) {
            return Ok(lambda);
        }
        let core = self.fresh_var();
        let procedure = self.procedure(&shape, Place::Local(core))?;
        let binds = self.tree.list([(core, lambda)]);
        Ok(self.tree.add(Node::Let(binds, procedure)))
    }

    /// Assembles a call whose arguments have the keywords `labels` from the lowered procedure, if the call is not `direct`, and the lowered arguments.
    ///
    /// Each value is bound to a variable in the order the call is written, the procedure first, so that the arguments are evaluated in that order whatever order the call then passes them in.
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

    /// Scans the whole expression once, so that fresh variables and lambda IDs can be made above every one it uses, and records the keyword procedures its `letrec` forms bind.
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
                        if let (Core::Letrec(..), Core::OptionalLambda(f)) = (core, init)
                            && f.params.iter().any(|formal| formal.keyword.is_some())
                        {
                            keyworded.push((*var, f));
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
                Core::App(f, args, _) => {
                    todo.push(f);
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
                Core::KeywordApp(f, args, _) => {
                    todo.push(f);
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

    /// Makes a variable that the expression being lowered does not use.
    fn fresh_var(&mut self) -> Var {
        self.scan();
        let var = Var(self.max_var);
        self.max_var = self.max_var.checked_add(1).expect("fewer than 2^32 variables");
        self.bound.insert(var);
        var
    }

    /// Makes a lambda ID that the expression being lowered does not use.
    fn fresh_lambda(&mut self) -> u32 {
        self.scan();
        let id = self.max_lambda;
        self.max_lambda = self.max_lambda.checked_add(1).expect("fewer than 2^32 lambdas");
        self.lambdas.insert(id);
        id
    }

    /// Expands a call of `import` with the lowered arguments `args` from the template `inline`.
    ///
    /// A template with more than one operation is recorded as an inlined call, so that an error raised in the expansion reports the imported procedure by name. Its code reports the line where the procedure is defined when the template records one, and the position of the call otherwise.
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
                // A string source marks a position whose offset is already a line number.
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

    fn reserve_var(&mut self, v: Var) -> Result<(), CompileError> {
        if !self.bound.insert(v) {
            return Err(CompileError::Rebound(v));
        }
        self.max_var = self.max_var.max(v.0.saturating_add(1));
        Ok(())
    }

    fn check_bound(&self, v: Var) -> Result<(), CompileError> {
        if !self.scope.contains(&v) {
            return Err(CompileError::Unbound(v));
        }
        Ok(())
    }
}

/// Returns the keyword and optionality of each parameter of `lambda`, in the order written.
fn described<'gc>(lambda: &OptionalLambda<'gc>) -> Vec<keyword::Param<'gc>> {
    lambda.params.iter().map(|formal| keyword::Param { keyword: formal.keyword, optional: formal.default.is_some() }).collect()
}

/// The values that an inline template's reads of module variables expand to.
enum Slots<'gc> {
    /// The variables of the module that exports the import.
    Of(Import<'gc>),
    /// A struct's type object, which is the only variable that the template of a struct procedure reads.
    Kind(Value<'gc>),
}

/// Builds the expansion of an inline template as nodes of the first intermediate representation.
struct Build<'x, 'id, 'gc> {
    mc: &'x Mutation<'gc>,
    slots: Slots<'gc>,
    tree: &'x mut L1<'id, 'gc>,
    bound: &'x mut HashSet<Var>,
    max_var: &'x mut u32,
    /// Gives each operation of a recorded inlined call the line it is written on. A call that is not recorded keeps the position of the call for all its code.
    lines: Option<Lines<'x, 'gc>>,
}

/// Makes the source sites of the operations of one inlined call, from the line each is written on in the source that defines the procedure.
struct Lines<'x, 'gc> {
    sites: &'x mut Sites<'gc>,
    /// The name of the source that defines the procedure, a string.
    file: Value<'gc>,
    /// The number of the inlined call that the code belongs to.
    inlined: u32,
    /// The site of the line where the procedure's definition starts, which code without a line of its own reports.
    definition: u32,
    /// The line of the last site made, and that site, which the next operation on the same line shares.
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

    fn call(&mut self, f: Id<'id>, args: Vec<Id<'id>>) -> Id<'id> {
        let args = self.tree.list(args);
        self.tree.add(Node::App(f, args))
    }

    fn is_constant(&self, expr: &Id<'id>) -> bool {
        matches!(self.tree[*expr], Node::Quote(_))
    }

    fn copy(&mut self, expr: &Id<'id>) -> Id<'id> {
        let node = self.tree[*expr];
        self.tree.add(node)
    }
}
