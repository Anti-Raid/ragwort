//! The `language!` macro generates an IR's node table and traversal support. Each language module
//! supplies its own records and validation rules.

/// Generates a node table in the invoking module, with private constructors for its distinct node,
/// span, and function IDs.
///
/// - `table` names the table type; `scope` creates a table with a fresh lifetime brand.
/// - `node` declares named node fields. Field order determines the traversal order of children
///   within the current frame.
/// - `functions` declares the function records, their ID type, insertion method, and body field.
/// - `lists` declares the element types supported by spans.
/// - `leaves` declares field types with no children in the current frame.
///
/// Additional compound types implement the generated `Children` trait to expose child nodes, or
/// `Bodies` to expose function bodies. Function IDs implement neither: entering a function body
/// crosses a frame boundary.
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
        /// An invariant lifetime marker that prevents IDs from different tables from being mixed. Only
        /// [`scope`] introduces the brand.
        type Brand<'id> = std::marker::PhantomData<fn(&'id ()) -> &'id ()>;

        /// Identifies a node in the table branded `'id`.
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        pub(crate) struct Id<'id>(u32, Brand<'id>);

        /// Identifies a function in the table branded `'id`.
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        pub(crate) struct $fun<'id>(u32, Brand<'id>);

        /// A contiguous range of elements in one of the table's lists.
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
            fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(formatter, "#{}", self.0)
            }
        }

        impl std::fmt::Debug for $fun<'_> {
            fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(formatter, "fn#{}", self.0)
            }
        }

        impl<T> std::fmt::Debug for Span<'_, T> {
            fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(formatter, "{}..{}", self.start, self.start + self.len)
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
            /// The source site of each node, parallel to `nodes`: an index into the compilation's [`Sites`](crate::ir::Sites), or 0 for a node with no known position.
            sites: Vec<u32>,
            /// The site given to each node as it is added.
            current: u32,
            $functions: Vec<$function>,
            $($list: Vec<$item>,)*
        }

        /// An element type supported by [`Span`], stored in its own list within the table.
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

        /// Passes child node IDs in the current frame to `visit`, in evaluation order.
        pub(crate) trait Children<'id, 'gc>: Copy {
            fn each(self, tree: &$table<'id, 'gc>, visit: &mut impl FnMut(Id<'id>));
        }

        impl<'id, 'gc> Children<'id, 'gc> for Id<'id> {
            fn each(self, _: &$table<'id, 'gc>, visit: &mut impl FnMut(Id<'id>)) {
                visit(self);
            }
        }

        impl<'id, 'gc, T: Item<'id, 'gc> + Children<'id, 'gc>> Children<'id, 'gc> for Span<'id, T> {
            fn each(self, tree: &$table<'id, 'gc>, visit: &mut impl FnMut(Id<'id>)) {
                for &item in &tree[self] {
                    item.each(tree, visit);
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

        /// Passes referenced function bodies to `visit`.
        pub(crate) trait Bodies<'id, 'gc>: Copy {
            fn bodies(self, tree: &$table<'id, 'gc>, visit: &mut impl FnMut(Id<'id>));
        }

        impl<'id, 'gc> Bodies<'id, 'gc> for Id<'id> {
            fn bodies(self, _: &$table<'id, 'gc>, _: &mut impl FnMut(Id<'id>)) {}
        }

        impl<'id, 'gc> Bodies<'id, 'gc> for $fun<'id> {
            fn bodies(self, tree: &$table<'id, 'gc>, visit: &mut impl FnMut(Id<'id>)) {
                visit(tree[self].$body);
            }
        }

        impl<'id, 'gc, T: Item<'id, 'gc> + Bodies<'id, 'gc>> Bodies<'id, 'gc> for Span<'id, T> {
            fn bodies(self, tree: &$table<'id, 'gc>, visit: &mut impl FnMut(Id<'id>)) {
                for &item in &tree[self] {
                    item.bodies(tree, visit);
                }
            }
        }

        $(
            impl<'id, 'gc> Bodies<'id, 'gc> for $leaf {
                fn bodies(self, _: &$table<'id, 'gc>, _: &mut impl FnMut(Id<'id>)) {}
            }
        )*

        /// Calls `callback` with a new empty table and a fresh lifetime brand.
        pub(crate) fn scope<'gc, R>(callback: impl for<'id> FnOnce($table<'id, 'gc>) -> R) -> R {
            callback($table { nodes: Vec::new(), sites: Vec::new(), current: 0, $functions: Vec::new(), $($list: Vec::new(),)* })
        }

        fn count(number: usize) -> u32 {
            u32::try_from(number).expect("fewer than 2^32 of each kind of node")
        }

        impl<'id, 'gc> $table<'id, 'gc> {
            pub(crate) fn add(&mut self, node: $node<'id, 'gc>) -> Id<'id> {
                let id = Id(count(self.nodes.len()), std::marker::PhantomData);
                self.nodes.push(node);
                self.sites.push(self.current);
                id
            }

            /// Sets the source site that nodes added from now on receive. A pass calls this with the site of the node it is translating, so that the nodes it builds for that node report the same source position.
            #[allow(dead_code)]
            pub(crate) fn at(&mut self, site: u32) {
                self.current = site;
            }

            /// Returns the source site that nodes added now receive.
            #[allow(dead_code)]
            pub(crate) fn current(&self) -> u32 {
                self.current
            }

            /// Returns the source site of the node `id`, or 0 if it has none.
            #[allow(dead_code)]
            pub(crate) fn site(&self, id: Id<'id>) -> u32 {
                self.sites[id.0 as usize]
            }

            /// Replaces the source site of the node `id`.
            #[allow(dead_code)]
            pub(crate) fn set_site(&mut self, id: Id<'id>, site: u32) {
                self.sites[id.0 as usize] = site;
            }

            /// Replaces the node at `id` during an in-place rewrite.
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

            /// Visits `id`'s children in evaluation order within the current function frame. Excludes nested
            /// function bodies.
            pub(crate) fn children(&self, id: Id<'id>, mut visit: impl FnMut(Id<'id>)) {
                match self[id] {
                    $( $node::$variant($($field),*) => { $( Children::each($field, self, &mut visit); )* } )*
                }
            }

            /// Visits the bodies of functions referenced by `id`, each of which belongs to a separate frame.
            #[allow(dead_code)]
            pub(crate) fn bodies(&self, id: Id<'id>, mut visit: impl FnMut(Id<'id>)) {
                match self[id] {
                    $( $node::$variant($($field),*) => { $( Bodies::bodies($field, self, &mut visit); )* } )*
                }
            }

            /// Iterates over nodes reachable from `root` in the same frame, visiting each parent before its
            /// children and preserving child evaluation order.
            #[allow(dead_code)]
            pub(crate) fn frame(&self, root: Id<'id>) -> Frame<'_, 'id, 'gc> {
                Frame { tree: self, next: Some(root), stack: Vec::new(), deep: false }
            }

            /// Traverses as [`frame`](Self::frame) does, but also enters nested functions after the nodes that
            /// reference them.
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

        /// An iterator for a single function frame, or for that frame and nested functions when created by
        /// `deep`.
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
