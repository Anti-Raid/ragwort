//! [`language!`], which makes an IR's table of nodes: everything but what's particular to the
//! language, which its module adds.

/// A language's table of nodes, in the module it's invoked in, with its own `Id`, `Span` and
/// function id types, whose constructors are private to it:
///
/// - `table`, the table, and `scope`, which makes one under a lifetime of its own;
/// - `node`, its nodes, each field named, its children in the frame, from its fields in order,
///   in the order they're evaluated;
/// - `functions`, the list of its functions, what they're ids of, the table's method that adds
///   one, and their field that's their body;
/// - `lists`, those spans can be of;
/// - `leaves`, the types of fields that have no children in the frame.
///
/// What else has children, as a binding does, implements the made `Children` trait itself, and
/// what else refers to functions, as a binding of them does, `Bodies`. A function id has neither:
/// its body is another frame.
macro_rules! language {
    (
        $(#[$table_meta:meta])*
        table $table:ident;
        $(#[$node_meta:meta])*
        node $node:ident {
            $( $(#[$variant_meta:meta])* $variant:ident ( $($field:ident: $ty:ty),* ) ),* $(,)?
        }
        functions $functions:ident: $function:ty, $fun:ident, $add_function:ident, body $body:ident;
        lists { $($list:ident: $item:ty),* $(,)? }
        leaves { $($leaf:ty),* $(,)? }
    ) => {
        /// Ties ids to the one table that made them: a lifetime only [`scope`] names, invariant
        /// so no other can stand for it.
        type Brand<'id> = std::marker::PhantomData<fn(&'id ()) -> &'id ()>;

        /// A node of the table branded `'id`.
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        pub(crate) struct Id<'id>(u32, Brand<'id>);

        /// A function of the table branded `'id`.
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        pub(crate) struct $fun<'id>(u32, Brand<'id>);

        /// Items of the table one after another.
        pub(crate) struct Span<'id, T> {
            start: u32,
            len: u32,
            of: std::marker::PhantomData<(Brand<'id>, fn() -> T)>,
        }

        impl<T> Clone for Span<'_, T> {
            fn clone(&self) -> Self {
                *self
            }
        }

        impl<T> Copy for Span<'_, T> {}

        impl std::fmt::Debug for Id<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "#{}", self.0)
            }
        }

        impl std::fmt::Debug for $fun<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "fn#{}", self.0)
            }
        }

        impl<T> std::fmt::Debug for Span<'_, T> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}..{}", self.start, self.start + self.len)
            }
        }

        $(#[$node_meta])*
        #[derive(Clone, Copy, Debug)]
        pub(crate) enum $node<'id, 'gc> {
            $( $(#[$variant_meta])* $variant($($ty),*), )*
        }

        $(#[$table_meta])*
        pub(crate) struct $table<'id, 'gc> {
            nodes: Vec<$node<'id, 'gc>>,
            $functions: Vec<$function>,
            $($list: Vec<$item>,)*
        }

        /// What a [`Span`] can be of: each kept in a list of the table's.
        pub(crate) trait Item<'id, 'gc>: Copy {
            fn all<'t>(tree: &'t $table<'id, 'gc>) -> &'t Vec<Self>;
            fn all_mut<'t>(tree: &'t mut $table<'id, 'gc>) -> &'t mut Vec<Self>;
        }

        $(
            impl<'id, 'gc> Item<'id, 'gc> for $item {
                fn all<'t>(tree: &'t $table<'id, 'gc>) -> &'t Vec<Self> {
                    &tree.$list
                }
                fn all_mut<'t>(tree: &'t mut $table<'id, 'gc>) -> &'t mut Vec<Self> {
                    &mut tree.$list
                }
            }
        )*

        /// What has children in the frame: their ids, to `f`, in the order they're evaluated.
        pub(crate) trait Children<'id, 'gc>: Copy {
            fn each(self, tree: &$table<'id, 'gc>, f: &mut impl FnMut(Id<'id>));
        }

        impl<'id, 'gc> Children<'id, 'gc> for Id<'id> {
            fn each(self, _: &$table<'id, 'gc>, f: &mut impl FnMut(Id<'id>)) {
                f(self);
            }
        }

        impl<'id, 'gc, T: Item<'id, 'gc> + Children<'id, 'gc>> Children<'id, 'gc> for Span<'id, T> {
            fn each(self, tree: &$table<'id, 'gc>, f: &mut impl FnMut(Id<'id>)) {
                for &item in &tree[self] {
                    item.each(tree, f);
                }
            }
        }

        $(
            impl<'id, 'gc> Children<'id, 'gc> for $leaf {
                fn each(self, _: &$table<'id, 'gc>, _: &mut impl FnMut(Id<'id>)) {}
            }
        )*

        impl<'id, 'gc> Children<'id, 'gc> for $fun<'id> {
            fn each(self, _: &$table<'id, 'gc>, _: &mut impl FnMut(Id<'id>)) {}
        }

        /// What refers to functions: their bodies, to `f`.
        pub(crate) trait Bodies<'id, 'gc>: Copy {
            fn bodies(self, tree: &$table<'id, 'gc>, f: &mut impl FnMut(Id<'id>));
        }

        impl<'id, 'gc> Bodies<'id, 'gc> for Id<'id> {
            fn bodies(self, _: &$table<'id, 'gc>, _: &mut impl FnMut(Id<'id>)) {}
        }

        impl<'id, 'gc> Bodies<'id, 'gc> for $fun<'id> {
            fn bodies(self, tree: &$table<'id, 'gc>, f: &mut impl FnMut(Id<'id>)) {
                f(tree[self].$body);
            }
        }

        impl<'id, 'gc, T: Item<'id, 'gc> + Bodies<'id, 'gc>> Bodies<'id, 'gc> for Span<'id, T> {
            fn bodies(self, tree: &$table<'id, 'gc>, f: &mut impl FnMut(Id<'id>)) {
                for &item in &tree[self] {
                    item.bodies(tree, f);
                }
            }
        }

        $(
            impl<'id, 'gc> Bodies<'id, 'gc> for $leaf {
                fn bodies(self, _: &$table<'id, 'gc>, _: &mut impl FnMut(Id<'id>)) {}
            }
        )*

        /// `f` with a new, empty table, branded with a lifetime of its own.
        pub(crate) fn scope<'gc, R>(f: impl for<'id> FnOnce($table<'id, 'gc>) -> R) -> R {
            f($table { nodes: Vec::new(), $functions: Vec::new(), $($list: Vec::new(),)* })
        }

        fn count(n: usize) -> u32 {
            u32::try_from(n).expect("fewer than 2^32 of each kind of node")
        }

        impl<'id, 'gc> $table<'id, 'gc> {
            pub(crate) fn add(&mut self, node: $node<'id, 'gc>) -> Id<'id> {
                let id = Id(count(self.nodes.len()), std::marker::PhantomData);
                self.nodes.push(node);
                id
            }

            /// Puts `node` in `id`'s place, as a pass that rewrites the table does.
            #[allow(dead_code)]
            pub(crate) fn set(&mut self, id: Id<'id>, node: $node<'id, 'gc>) {
                self.nodes[id.0 as usize] = node;
            }

            pub(crate) fn $add_function(&mut self, function: $function) -> $fun<'id> {
                let fun = $fun(count(self.$functions.len()), std::marker::PhantomData);
                self.$functions.push(function);
                fun
            }

            pub(crate) fn list<T: Item<'id, 'gc>>(&mut self, items: impl IntoIterator<Item = T>) -> Span<'id, T> {
                let all = T::all_mut(self);
                let start = all.len();
                all.extend(items);
                Span { start: count(start), len: count(all.len() - start), of: std::marker::PhantomData }
            }

            /// `id`'s children in its function's frame, in the order they're evaluated: not the
            /// bodies of its functions, which are other frames.
            pub(crate) fn children(&self, id: Id<'id>, mut f: impl FnMut(Id<'id>)) {
                match self[id] {
                    $( $node::$variant($($field),*) => { $( Children::each($field, self, &mut f); )* } )*
                }
            }

            /// The bodies of the functions `id` refers to, which are other frames.
            #[allow(dead_code)]
            pub(crate) fn bodies(&self, id: Id<'id>, mut f: impl FnMut(Id<'id>)) {
                match self[id] {
                    $( $node::$variant($($field),*) => { $( Bodies::bodies($field, self, &mut f); )* } )*
                }
            }

            /// The nodes of `root`'s function's frame from it: each before its children, in the
            /// order they're evaluated.
            #[allow(dead_code)]
            pub(crate) fn frame(&self, root: Id<'id>) -> Frame<'_, 'id, 'gc> {
                Frame { tree: self, next: Some(root), stack: Vec::new(), deep: false }
            }

            /// The nodes from `root`, as [`frame`](Self::frame) has them, and those of the
            /// functions in them, each function's after the node that refers to it.
            #[allow(dead_code)]
            pub(crate) fn deep(&self, root: Id<'id>) -> Frame<'_, 'id, 'gc> {
                Frame { tree: self, next: Some(root), stack: Vec::new(), deep: true }
            }
        }

        impl<'id, 'gc> std::ops::Index<Id<'id>> for $table<'id, 'gc> {
            type Output = $node<'id, 'gc>;

            fn index(&self, id: Id<'id>) -> &$node<'id, 'gc> {
                &self.nodes[id.0 as usize]
            }
        }

        impl<'id, 'gc> std::ops::Index<$fun<'id>> for $table<'id, 'gc> {
            type Output = $function;

            fn index(&self, fun: $fun<'id>) -> &$function {
                &self.$functions[fun.0 as usize]
            }
        }

        impl<'id, 'gc> std::ops::IndexMut<$fun<'id>> for $table<'id, 'gc> {
            fn index_mut(&mut self, fun: $fun<'id>) -> &mut $function {
                &mut self.$functions[fun.0 as usize]
            }
        }

        impl<'id, 'gc, T: Item<'id, 'gc>> std::ops::Index<Span<'id, T>> for $table<'id, 'gc> {
            type Output = [T];

            fn index(&self, span: Span<'id, T>) -> &[T] {
                &T::all(self)[span.start as usize..][..span.len as usize]
            }
        }

        /// An iterator of the nodes of a function's frame, as the table's `frame` makes, or
        /// `deep`, with those of its functions too.
        pub(crate) struct Frame<'t, 'id, 'gc> {
            tree: &'t $table<'id, 'gc>,
            next: Option<Id<'id>>,
            stack: Vec<Id<'id>>,
            deep: bool,
        }

        impl<'id> Iterator for Frame<'_, 'id, '_> {
            type Item = Id<'id>;

            fn next(&mut self) -> Option<Id<'id>> {
                let id = self.next.take().or_else(|| self.stack.pop())?;
                let at = self.stack.len();
                self.tree.children(id, |child| self.stack.push(child));
                if self.deep {
                    self.tree.bodies(id, |body| self.stack.push(body));
                }
                self.stack[at..].reverse();
                Some(id)
            }
        }
    };
}
