//! This module provides a [`Printer`] struct that implements the [`Visitor`]
//! trait to format and print parse trees represented by the [`Root`], [`Stmt`],
//! and [`Expr`] types.
//!
//! ## Functionality
//!
//! The `Printer` is designed to convert parsed expressions and statements into
//! a human-readable string format. It constructs a formatted string by visiting
//! each node in the parse tree and producing an appropriate string
//! representation, including handling nested expressions and variable
//! assignments.
//!
//! ## Usage
//!
//! Create an instance of `Printer`, then use it to format a parse tree by
//! passing a `Root` object to the `format` method. The method will visit each
//! node in the tree and accumulate the formatted output.
//!
//! ## Examples
//!
//! Basic usage:
//! ```
//! # use syntree::{Root, Printer};
//! let root = Root::from_str("a 3 5 + =").unwrap();
//! let mut printer = Printer::default();
//! let output = printer.format(&root);
//!
//! println!("{}", output); // prints a=(3+5)
//! ```

use std::mem::swap;
use crate::parse_tree::*;

/// `Printer` is a struct used for formatting parse trees into human-readable
/// strings.
///
/// ## Example
/// ```
/// # use syntree::{Root, Printer};
/// # fn doc(root: Root) {
/// let mut printer = Printer::default();
/// let formatted_output = printer.format(&root);
/// println!("{}", formatted_output);
/// # }
/// ```
#[derive(Default)]
pub struct Printer {
    result: String
}

impl Printer {
    /// Folds the entire parse tree starting from a [`Root`] object into a
    /// single string.
    ///
    /// Traverses the tree, visiting each statement and expression to generate
    /// formatted strings, and then concatenates these strings into a single
    /// result separated by newlines.
    pub fn format(&mut self, r: &Root) -> String {
        self.visit_root(r);
        let mut result = String::new();
        swap(&mut result, &mut self.result);
        result.pop();
        result
    }
}

impl Visitor for Printer {
    fn visit_stmt(&mut self, s: &Stmt) {
        match s {
            Stmt::Expr(e) => self.visit_expr(e),
            Stmt::Set(v, e) => {
                self.result = format!("{}{}=", self.result, v);
                self.visit_expr(e)
            },
        }
        self.result.push('\n');
    }

    fn visit_expr(&mut self, e: &Expr) {
        match e {
            Expr::Int(i) => self.result = format!("{}{}", self.result, i),
            Expr::Var(v) => self.result = format!("{}{}", self.result, v),
            Expr::Add(lhs, rhs) => {
                self.result.push('(');
                self.visit_expr(lhs);
                self.result.push('+');
                self.visit_expr(rhs);
                self.result.push(')');
            }
            Expr::Sub(lhs, rhs) => {
                self.result.push('(');
                self.visit_expr(lhs);
                self.result.push('-');
                self.visit_expr(rhs);
                self.result.push(')');
            }
            Expr::Mul(lhs, rhs) => {
                self.result.push('(');
                self.visit_expr(lhs);
                self.result.push('*');
                self.visit_expr(rhs);
                self.result.push(')');
            }
            Expr::Div(lhs, rhs) => {
                self.result.push('(');
                self.visit_expr(lhs);
                self.result.push('/');
                self.visit_expr(rhs);
                self.result.push(')');
            }
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
        assert_eq!(Printer::default().format(&tree), "(4+2)");
    }

    #[test]
    fn sub() {
        let tree = Root::from_stmt(Stmt::sub(4, 2));
        assert_eq!(Printer::default().format(&tree), "(4-2)");
    }

    #[test]
    fn mul() {
        let tree = Root::from_stmt(Stmt::mul(4, 2));
        assert_eq!(Printer::default().format(&tree), "(4*2)");
    }

    #[test]
    fn div() {
        let tree = Root::from_stmt(Stmt::div(4, 2));
        assert_eq!(Printer::default().format(&tree), "(4/2)");
    }

    #[test]
    fn set() {
        let tree = Root::from_stmt(Stmt::set('a', 1));
        assert_eq!(Printer::default().format(&tree), "a=1");
    }
}
