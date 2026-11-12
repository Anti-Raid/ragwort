use std::thread;

use ragwort_types::gc::Value;

use super::*;

fn void<'id>(t: &mut L4<'id, 'static>) -> Id<'id> {
    t.add(Node::Quote(Value::VOID))
}

fn local<'id>(t: &mut L4<'id, 'static>, v: u32) -> Id<'id> {
    t.add(Node::Ref(VarRef::Local(Var(v))))
}

fn error<'id>(t: &L4<'id, 'static>, root: Id<'id>) -> String {
    t.verify(root).expect_err("malformed")
}

/// Builds a join with `scope` and one body, named `5`, accepting `params`.
fn join<'id>(t: &mut L4<'id, 'static>, params: &[u32], scope: Id<'id>) -> Id<'id> {
    let (params, body) = (t.list(params.iter().map(|&v| Var(v))), void(t));
    let codes = t.list([JoinCode { id: Var(5), params, body }]);
    t.add(Node::Join(scope, codes))
}

/// Builds a zero-argument closure with `captures` and `body`.
fn closure<'id>(t: &mut L4<'id, 'static>, captures: &[UpvalSource], body: Id<'id>) -> Fun<'id> {
    let (params, captures) = (t.list([]), t.list(captures.iter().copied()));
    t.closure(Closure { id: 0, optional: 0, params, rest: None, captures, body })
}

#[test]
fn only_what_the_root_reaches_is_checked() {
    scope(|mut t| {
        let (a, b) = (void(&mut t), void(&mut t));
        let shared = t.add(Node::Seq(a, a));
        assert_eq!(t.verify(b), Ok(()));
        assert!(error(&t, shared).contains("two parents"), "{}", error(&t, shared));
    });
}

#[test]
fn variables_are_bound_once_and_used_in_scope() {
    scope(|mut t| {
        let free = local(&mut t, 0);
        assert!(error(&t, free).contains("isn't in scope"));

        let (init, body) = (void(&mut t), local(&mut t, 0));
        let binds = t.list([Bind::Val(Var(0), init)]);
        let bound = t.add(Node::Let(binds, body));
        assert_eq!(t.verify(bound), Ok(()));

        let after = local(&mut t, 0);
        let past = t.add(Node::Seq(bound, after));
        assert!(error(&t, past).contains("isn't in scope"));

        let (a, b, body) = (void(&mut t), void(&mut t), void(&mut t));
        let binds = t.list([Bind::Val(Var(1), a), Bind::Val(Var(1), b)]);
        let twice = t.add(Node::Let(binds, body));
        assert!(error(&t, twice).contains("bound twice"));
    });
}

#[test]
fn jumps_go_to_joins_in_scope_in_their_function() {
    scope(|mut t| {
        let args = t.list([]);
        let alone = t.add(Node::Jump(Var(5), args));
        assert!(error(&t, alone).contains("isn't in scope"));

        let jump = t.add(Node::Jump(Var(5), args));
        let ok = join(&mut t, &[], jump);
        assert_eq!(t.verify(ok), Ok(()));

        let jump = t.add(Node::Jump(Var(5), args));
        let wrong = join(&mut t, &[1], jump);
        assert!(error(&t, wrong).contains("isn't in scope"), "a jump of too few values");

        let jump = t.add(Node::Jump(Var(5), args));
        let fun = closure(&mut t, &[], jump);
        let lambda = t.add(Node::Lambda(fun));
        let across = join(&mut t, &[], lambda);
        assert!(error(&t, across).contains("isn't in scope"), "a jump out of a closure");
    });
}

#[test]
fn closures_capture_and_use_what_they_have() {
    scope(|mut t| {
        let body = void(&mut t);
        let fun = closure(&mut t, &[UpvalSource::Local(Var(0))], body);
        let free = t.add(Node::Lambda(fun));
        assert!(error(&t, free).contains("isn't in scope"));

        let body = t.add(Node::Ref(VarRef::Upvalue(0)));
        let fun = closure(&mut t, &[UpvalSource::Local(Var(0))], body);
        let (init, lambda) = (void(&mut t), t.add(Node::Lambda(fun)));
        let binds = t.list([Bind::Val(Var(0), init)]);
        let ok = t.add(Node::Let(binds, lambda));
        assert_eq!(t.verify(ok), Ok(()));

        let body = t.add(Node::Ref(VarRef::Upvalue(1)));
        let fun = closure(&mut t, &[], body);
        let past = t.add(Node::Lambda(fun));
        assert!(error(&t, past).contains("isn't in scope"));
    });
}

/// Checks, walks, and drops a tree one million nodes deep on a small machine stack.
#[test]
fn deep_trees_need_no_stack() {
    let run = || {
        scope(|mut t| {
            let mut e = void(&mut t);
            for _ in 0..1_000_000 {
                let first = void(&mut t);
                e = t.add(Node::Seq(first, e));
            }
            assert_eq!(t.verify(e), Ok(()));
            assert_eq!(t.frame(e).count(), 2_000_001);
        });
    };
    thread::Builder::new().stack_size(64 << 10).spawn(run).expect("spawned").join().expect("ran");
}
