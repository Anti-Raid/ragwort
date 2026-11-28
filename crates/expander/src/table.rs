//! A table of bindings, keyed by name and scope set.

use ragwort_types::gc::OutOfMemory;

use crate::scope::{Map, Scope, Scopes, Set, TOP};

/// The error for an identifier with two candidate bindings, where neither binding's scope set is a subset of the other's.
#[derive(Debug)]
pub struct Ambiguous;

/// The bindings of one kind of name. `B` is what a name is bound to.
///
/// A binding is made for an identifier, and it records the identifier's scope set. An identifier refers to the binding of its name
/// whose scope set is the largest subset of the identifier's own.
///
/// An [`Engine`](crate::Engine) has one table for the names of variables, keywords and macros. A front end can keep further tables for names of
/// other kinds, such as the labels of loops.
pub struct Table<B> {
    /// Each entry is a binding and the scope set of the identifier that was bound. The key is the newest
    /// scope of that set and the raw bits of the name's symbol. So every binding that an identifier can refer to is stored under one of the identifier's own scopes.
    bindings: Map<(Scope, u64), Vec<(Set, B)>>,
    /// For each name, the scopes that `bindings` has entries for the name under. When a name has fewer
    /// such scopes than an identifier has scopes, the lookup goes through this list instead of the identifier's scopes.
    bound_in: Map<u64, Vec<Scope>>,
}

impl<B> Default for Table<B> {
    fn default() -> Self {
        Self { bindings: Map::default(), bound_in: Map::default() }
    }
}

impl<B: Copy> Table<B> {
    /// Binds the name with the word `name_key` to `binding`, for an identifier with the scope set `set`.
    pub fn bind(&mut self, scopes: &mut Scopes<'_>, name_key: u64, set: Set, binding: B) -> Result<(), OutOfMemory> {
        scopes.charge(size_of::<(Set, B)>())?;
        let newest = scopes.scopes(set).last().copied().unwrap_or(TOP);
        let under = self.bindings.entry((newest, name_key)).or_default();
        if under.is_empty() {
            scopes.charge(size_of::<Scope>())?;
            self.bound_in.entry(name_key).or_default().push(newest);
        }
        under.push((set, binding));
        Ok(())
    }

    /// Returns the bindings of the name with the word `name_key` whose scopes are all in `set`. The bindings are looked up under the scopes of `bound_in` that are in `set`, then under the scopes of `own`.
    #[inline]
    fn candidates<'s>(&'s self, scopes: &'s Scopes<'_>, name_key: u64, set: Set, bound_in: &'s [Scope], own: &'s [Scope]) -> impl Iterator<Item = &'s (Set, B)> {
        let under = bound_in.iter().filter(move |&&scope| scopes.contains(set, scope)).chain(own);
        let lists = under.filter_map(move |&scope| self.bindings.get(&(scope, name_key)));
        lists.flatten().filter(move |&&(bound, _)| scopes.subset(bound, set))
    }

    /// Returns the binding that an identifier with the scope set `set` refers to, where `name_key` is the word of its name. Returns `None` if the table has no binding
    /// for it.
    pub fn resolve(&self, scopes: &Scopes<'_>, name_key: u64, set: Set) -> Result<Option<B>, Ambiguous> {
        // Every binding that the identifier can refer to is stored under one of the identifier's scopes. So iterate over the shorter
        // list: the identifier's scopes, or the scopes that the name has bindings under.
        let bound_in = self.bound_in.get(&name_key).map_or(&[][..], Vec::as_slice);
        let own = scopes.scopes(set);
        let (bound_in, own) = if bound_in.len() < own.len() { (bound_in, &[][..]) } else { (&[][..], own) };
        let mut best: Option<(Set, B)> = None;
        for &(bound, binding) in self.candidates(scopes, name_key, set, bound_in, own) {
            if best.is_none_or(|(best_set, _)| scopes.subset(best_set, bound)) {
                best = Some((bound, binding));
            }
        }
        let Some((best, binding)) = best else { return Ok(None) };
        if self.candidates(scopes, name_key, set, bound_in, own).any(|&(bound, _)| !scopes.subset(bound, best)) {
            return Err(Ambiguous);
        }
        Ok(Some(binding))
    }
}
