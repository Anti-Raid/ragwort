pub use ragwort_gc as gc;

pub mod num;

pub enum Expr {
    Begin { exprs: Vec<Expr> },

}
