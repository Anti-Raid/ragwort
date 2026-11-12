use std::thread;

use ragwort_types::gc::Value;

use super::*;

fn void<'id>(t: &mut L3<'id, 'static>) -> Id<'id> {
    t.add(Node::Quote(Value::VOID))
}

fn error<'id>(t: &L3<'id, 'static>, root: Id<'id>) -> String {
    t.verify(root).expect_err("malformed")
}

/// Builds a function with `params` and `body`.
fn function<'id>(t: &mut L3<'id, 'static>, params: &[u32], body: Id<'id>) -> Fun<'id> {
    let params = t.list(params.iter().map(|&v| Var(v)));
    t.function(Function { id: 0, optional: 0, params, rest: None, body })
}

#[test]
fn functions_see_what_encloses_them_but_not_its_joins() {
    scope(|mut t| {
        let body = t.add(Node::Ref(Var(0)));
        let fun = function(&mut t, &[], body);
        let (init, lambda) = (void(&mut t), t.add(Node::Lambda(fun)));
        let binds = t.list([Bind::Val(Var(0), init)]);
        let ok = t.add(Node::Let(binds, lambda));
        assert_eq!(t.verify(ok), Ok(()));

        let args = t.list([]);
        let jump = t.add(Node::Jump(Var(5), args));
        let fun = function(&mut t, &[], jump);
        let lambda = t.add(Node::Lambda(fun));
        let code = void(&mut t);
        let code = function(&mut t, &[], code);
        let codes = t.list([JoinCode { id: Var(5), fun: code }]);
        let across = t.add(Node::Join(lambda, codes));
        assert!(error(&t, across).contains("isn't in scope"), "a jump out of a function");
    });
}

#[test]
fn joins_take_their_parameters_and_have_one_parent() {
    scope(|mut t| {
        let (one, args) = (void(&mut t), void(&mut t));
        let args = t.list([one, args]);
        let jump = t.add(Node::Jump(Var(5), args));
        let body = t.add(Node::Ref(Var(1)));
        let code = function(&mut t, &[1, 2], body);
        let codes = t.list([JoinCode { id: Var(5), fun: code }]);
        let ok = t.add(Node::Join(jump, codes));
        assert_eq!(t.verify(ok), Ok(()));

        let shared = t.list([JoinCode { id: Var(6), fun: code }]);
        let scope = void(&mut t);
        let twice = t.add(Node::Join(scope, shared));
        let both = t.add(Node::Seq(ok, twice));
        assert!(error(&t, both).contains("two parents"));
    });
}

/// Checks and walks a tree one million nodes deep on a small machine stack.
#[test]
fn deep_trees_need_no_stack() {
    let run = || {
        scope(|mut t| {
            let mut e = void(&mut t);
            for _ in 0..1_000_000 {
                let fun = function(&mut t, &[], e);
                e = t.add(Node::Lambda(fun));
            }
            assert_eq!(t.verify(e), Ok(()));
            assert_eq!(t.deep(e).count(), 1_000_001);
            assert_eq!(t.frame(e).count(), 1);
        });
    };
    thread::Builder::new().stack_size(64 << 10).spawn(run).expect("spawned").join().expect("ran");
}
