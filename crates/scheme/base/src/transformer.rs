//! `let-syntax` and `letrec-syntax`, which bind macros around a body. The shared expander creates and runs the transformers. See
//! [`ragwort_expander`].

use ragwort_compiler::steps::Step;
use ragwort_expander::Expand;

use crate::expand::{Binding, Call, Ex, Expander};
use crate::scope::{Op, Scope};
use crate::tree::Stx;
use crate::{ExpandError, ExpandErrorKind};

impl<'a, 'gc> Expander<'a, 'gc> {
    /// Expands a `let-syntax` form, or a `letrec-syntax` form if `recursive`. The transformer expressions of
    /// `letrec-syntax` are in the scope of the names that the form binds.
    pub(crate) fn let_syntax(&mut self, stx: Stx, binds: Stx, body: Vec<Stx>, recursive: bool) -> Result<Ex<'a, 'gc>, ExpandError> {
        let scope = self.engine.tree.scopes.fresh()?;
        let (mut ids, mut exprs) = (Vec::new(), Vec::new());
        for bind in self.proper(binds)? {
            match *self.proper(bind)?.as_slice() {
                [id, expr] if self.is_id(id) => {
                    ids.push(self.engine.tree.with(id, scope, Op::Add)?);
                    exprs.push(if recursive { self.engine.tree.with(expr, scope, Op::Add)? } else { expr });
                }
                _ => return Err(self.error(ExpandErrorKind::BadSyntax, bind)),
            }
        }
        self.distinct(&ids)?;
        let macros: Vec<_> = ids.into_iter().zip(exprs).collect();
        self.let_macros(stx, macros.into_iter(), body, scope)
    }

    /// Creates the transformer of each of `macros` in turn and binds the macro's identifier to it. Then expands `body`.
    fn let_macros(&mut self, stx: Stx, mut macros: std::vec::IntoIter<(Stx, Stx)>, body: Vec<Stx>, scope: Scope) -> Result<Ex<'a, 'gc>, ExpandError> {
        let Some((id, expr)) = macros.next() else {
            let body = self.scoped(&body, scope)?;
            return Ok(Step::Tail(Call::Run(Box::new(move |this: &mut Self| this.body(stx, body)))));
        };
        self.transformer(expr, stx, move |this, macro_index| {
            this.bind(id, Binding::Macro(macro_index))?;
            this.let_macros(stx, macros, body, scope)
        })
    }
}
