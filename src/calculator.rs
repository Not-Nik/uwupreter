//! This module provides the [`Calculator`] struct, which is designed to
//! evaluate arithmetic expressions parsed into a [`Root`] structure from a
//! string representation. It supports operations including addition,
//! subtraction, multiplication, and division, along with variable assignments
//! from 'a' to 'z'.
//!
//! ## Example
//! ```
//! # use syntree::{Root, Visitor, Calculator};
//!
//! let mut calculator = Calculator::default();
//! let root = Root::from_str("a 1 = b 2 3 * = a b +").unwrap();
//! let result = calculator.calc(&root);
//!
//! println!("Final result: {}", result); // prints 7
//! ```

use std::collections::HashMap;
use crate::parse_tree::*;

/// `Calculator` is a struct designed to evaluate parsed arithmetic expressions.
///
/// ## Usage
/// ```
/// # use syntree::{Calculator, Root};
/// # fn doc(root: Root) {
/// let mut calculator = Calculator::default();
/// let result = calculator.calc(&root);
/// println!("The result of the calculation is: {}", result);
/// # }
/// ```
#[derive(Default)]
pub struct Calculator {
    variables: HashMap<char, i64>,
    last_result: i64,
}

impl Calculator {
    /// Evaluates the entire parse tree starting from a [`Root`] and returns the
    /// result of the last expression evaluated.
    pub fn calc(&mut self, r: &Root) -> i64 {
        self.visit_root(r);
        self.last_result
    }
}

impl Visitor for Calculator {
    fn visit_stmt(&mut self, s: &Stmt) {
        match s {
            // Either calculate the expression
            Stmt::Expr(expr) => self.visit_expr(expr),
            // Or calculate it and set the variable
            Stmt::Set(var, expr) => {
                self.visit_expr(expr);
                self.variables.insert(*var, self.last_result);
                // We were told the result can be anything after an assignment,
                // but apparently it does have to be zero...
                self.last_result = 0;
            }
        }
    }

    fn visit_expr(&mut self, e: &Expr) {
        self.last_result = match e {
            Expr::Int(int) => *int,
            Expr::Var(var) => self.variables[var],
            Expr::Add(left, right) => {
                self.visit_expr(left);
                let left_val = self.last_result;
                self.visit_expr(right);
                left_val + self.last_result
            },
            Expr::Sub(left, right) => {
                self.visit_expr(left);
                let left_val = self.last_result;
                self.visit_expr(right);
                left_val - self.last_result
            },
            Expr::Mul(left, right) => {
                self.visit_expr(left);
                let left_val = self.last_result;
                self.visit_expr(right);
                left_val * self.last_result
            },
            Expr::Div(left, right) => {
                self.visit_expr(left);
                let left_val = self.last_result;
                self.visit_expr(right);
                left_val / self.last_result
            },
        }
    }
}

// unit-tests

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add() {
        let tree = Root::from_stmt(Stmt::add(4, 2));
        assert_eq!(Calculator::default().calc(&tree), 6);
    }

    #[test]
    fn sub() {
        let tree = Root::from_stmt(Stmt::sub(4, 2));
        assert_eq!(Calculator::default().calc(&tree), 2);
    }

    #[test]
    fn mul() {
        let tree = Root::from_stmt(Stmt::mul(4, 2));
        assert_eq!(Calculator::default().calc(&tree), 8);
    }

    #[test]
    fn div() {
        let tree = Root::from_stmt(Stmt::div(4, 2));
        assert_eq!(Calculator::default().calc(&tree), 2);
    }

    #[test]
    #[should_panic(expected = "attempt to divide by zero")]
    fn division_by_zero() {
        let tree = Root::from_stmt(Stmt::div(4, 0));
        Calculator::default().calc(&tree);
    }

    #[test]
    fn set() {
        let tree = Root::from_stmt(Stmt::set('a', 1));
        assert_eq!(Calculator::default().calc(&tree), 0);
    }

    #[test]
    fn vars() {
        let tree = Root {
            stmt_list: vec![
                Stmt::set('i', 1),
                Stmt::set('j', 2),
                Stmt::Expr(Expr::Add(
                    Box::new(Expr::Var('i')),
                    Box::new(Expr::Var('j')),
                )),
            ],
        };
        assert_eq!(Calculator::default().calc(&tree), 3);
    }
}
