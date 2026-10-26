extern crate self as ragwort;

pub mod gc;

pub enum Expr {
    Begin { exprs: Vec<Expr> },

}
