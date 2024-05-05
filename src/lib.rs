//! This library provides tools for parsing, printing, and evaluating simple
//! arithmetic expressions. It includes a parse tree module for constructing
//! abstract syntax trees, a printer module for formatting and displaying these
//! trees, and a calculator module for evaluating expressions.
//!
//! ## Modules
//! - `parse_tree`: Contains the fundamental structures ([`Root`], [`Stmt`],
//!   [`Expr`]) and a visitor trait ([`Visitor`]) for traversing parse trees.
//! - `printer`: Implements a [`Printer`] struct that formats and prints the
//!   expressions from the parse trees in a human-readable form.
//! - `calculator`: Provides a [`Calculator`] struct capable of evaluating
//!   parsed expressions, supporting basic arithmetic operations and variable
//!   assignments.
//!
//! ## Usage
//! This library can be used to parse arithmetic expressions from strings in
//! [reverse polish notation], print their structured representation, or
//! calculate their values.
//!
//! ## Example
//! ```
//! use syntree::{Root, Printer, Calculator};
//!
//! let expression = "a 1 2 3 * + = b a 2 * ="; // a = 1 + 2 * 3; b = a * 2;
//! let root = Root::from_str(expression).unwrap();
//!
//! // Print the expression
//! let mut printer = Printer::default();
//! println!("Printed expression: {}", printer.format(&root));
//!
//! // Evaluate the expression
//! let mut calculator = Calculator::default();
//! let result = calculator.calc(&root);
//! println!("Evaluation result: {}", result);
//! ```
//! 
//! [reverse polish notation]: https://en.wikipedia.org/wiki/Reverse_Polish_notation
#![forbid(unsafe_code)]

mod parse_tree;
mod printer;
mod calculator;

pub use parse_tree::{Root, Stmt, Expr, Error, Visitor};
pub use printer::Printer;
pub use calculator::Calculator;
