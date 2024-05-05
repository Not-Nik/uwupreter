//! This module provides functionality to parse and evaluate simple mathematical
//! expressions and assignments. It includes a parser that constructs a parse
//! tree from strings in [reverse polish notation], which can then be evaluated
//! or manipulated.
//!
//! ## Examples
//!
//! Basic parsing and evaluation:
//! ```
//! # use syntree::Root;
//! let expr = "1 2 + 3 4 * 5 6 / -";
//! let parse_result = Root::from_str(expr);
//!
//! match parse_result {
//!     Ok(root) => {
//!         // traverse or evaluate `root` here
//!     },
//!     Err(e) => println!("Error parsing expression: {}", e),
//! }
//! ```
//!
//! Implementing a visitor to evaluate expressions:
//! ```
//! # use syntree::{Expr, Visitor};
//! struct Evaluator;
//! impl Visitor for Evaluator {
//!     fn visit_expr(&mut self, e: &Expr) {
//!         // evaluation logic here
//!     }
//!     // other visit methods
//! }
//! ```
//! 
//! [reverse polish notation]: https://en.wikipedia.org/wiki/Reverse_Polish_notation

/// Represents the root of a parse tree.
///
/// This struct holds a list of statements parsed from a string representation
/// of expressions and assignments.
#[derive(Debug, Default, PartialEq)]
pub struct Root {
	pub stmt_list: Vec<Stmt>,
}

/// Defines the different types of statements that can appear in the parse tree.
///
/// Each statement can be either an expression or an assignment of a value to a
/// variable.
#[derive(Debug, PartialEq)]
pub enum Stmt {
	Expr(Expr),
	Set(char, Expr),
}

/// Represents all possible expressions that can be parsed and evaluated.
///
/// This enum covers basic integer constants, variables, and binary operations
/// (addition, subtraction, multiplication, division).
#[derive(Debug, PartialEq)]
pub enum Expr {
	Int(i64),
	Var(char),
	Add(Box<Expr>, Box<Expr>),
	Sub(Box<Expr>, Box<Expr>),
	Mul(Box<Expr>, Box<Expr>),
	Div(Box<Expr>, Box<Expr>),
}

/// Defines error types that can occur during the parsing of expressions.
///
/// Errors are categorized into lexical, syntax, and semantic types depending
/// on the nature of the error.
#[derive(Debug, PartialEq, Eq)]
pub enum Error {
	/// A lexical error, due to invalid character input.
	Lexical,
	/// A syntax error, due to improper arrangement of tokens.
	Syntax,
	/// A semantic error, due to assignment to a non-variable expression.
	Semantic,
}

impl Root {
	/// Parses a string into a `Root` struct, constructing a list of statements.
	///
	/// This method uses a simple stack-based parser to convert strings in
	/// [reverse polish notation] into statements and expressions.
	/// 
	/// Returns an error if the parsing fails due to invalid input.
	/// 
	/// [reverse polish notation]: https://en.wikipedia.org/wiki/Reverse_Polish_notation
	pub fn from_str(str: &str) -> Result<Self, Error> {
		// TODO: Funktionskörper vervollständigen
		let mut stmt_list = Vec::new();
		let mut expr_stack = Vec::new();
		
		for c in str.chars() {
			match c {
				c if c.is_whitespace() => {}
				c if c.is_digit(10) => {
					todo!("Ziffer in Zahl konvertieren und auf den Stapel legen")
				}
				c if c.is_ascii_lowercase() => {
					todo!("Variablenname auf den Stapel legen")
				}
				'+' => {
					todo!("Additionsknoten auf den Stapel legen")
				}
				'-' => {
					todo!("Subtraktionsknoten auf den Stapel legen")
				}
				'*' => {
					todo!("Multiplikationsknoten auf den Stapel legen")
				}
				'/' => {
					todo!("Divisionsknoten auf den Stapel legen")
				}
				'=' => {
					todo!("Zuweisungsknoten auf den Stapel legen");
				}
				_ => todo!("geeigneten Fehlercode zurückgeben"),
			}
		}
		
		if let Some(expr) = expr_stack.pop() {
			stmt_list.push(Stmt::Expr(expr));
		}
		
		if !expr_stack.is_empty() {
			todo!("geeigneten Fehlercode zurückgeben")
		} else {
			Ok(Root { stmt_list })
		}
	}
}

/// Provides a visitor for traversing the parse tree.
///
/// This trait should be implemented by any type that needs to perform
/// operations on the parse tree.
pub trait Visitor {
	fn visit_root(&mut self, r: &Root) {
		for item in r.stmt_list.iter() {
			self.visit_stmt(item);
		}
	}
	
	fn visit_stmt(&mut self, s: &Stmt) {
		match s {
			Stmt::Expr(e) => self.visit_expr(e),
			Stmt::Set(_, e) => self.visit_expr(e),
		}
	}
	
	fn visit_expr(&mut self, e: &Expr) {
		match e {
			Expr::Int(_) | Expr::Var(_) => {}
			Expr::Add(lhs, rhs) => {
				self.visit_expr(lhs);
				self.visit_expr(rhs);
			}
			Expr::Sub(lhs, rhs) => {
				self.visit_expr(lhs);
				self.visit_expr(rhs);
			}
			Expr::Mul(lhs, rhs) => {
				self.visit_expr(lhs);
				self.visit_expr(rhs);
			}
			Expr::Div(lhs, rhs) => {
				self.visit_expr(lhs);
				self.visit_expr(rhs);
			}
		}
	}
}

impl std::fmt::Display for Error {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Lexical => write!(f, "Lexical error: unexpected character"),
			Self::Syntax => write!(f, "Syntax error: wrong number of operands"),
			Self::Semantic => write!(f, "Semantic error: assignment to non-variable"),
		}
	}
}

// unit-tests

#[cfg(test)]
mod tests {
	use super::*;
	
	impl Root {
		/// Creates a parse tree from a single [`Stmt`].
		/// 
		/// This method only exists during testing.
		pub fn from_stmt(s: Stmt) -> Self {
			Self { stmt_list: vec![s] }
		}
	}
	
	impl Stmt {
		/// Creates an expression `Stmt` for adding two numbers.
		///
		/// This method only exists during testing.
		pub fn add(lhs: i64, rhs: i64) -> Self {
			Stmt::Expr(
				Expr::Add(
					Box::new(Expr::Int(lhs)),
					Box::new(Expr::Int(rhs)),
				)
			)
		}
		
		/// Creates an expression `Stmt` for subtracting two numbers.
		///
		/// This method only exists during testing.
		pub fn sub(lhs: i64, rhs: i64) -> Self {
			Stmt::Expr(
				Expr::Sub(
					Box::new(Expr::Int(lhs)),
					Box::new(Expr::Int(rhs)),
				)
			)
		}
		
		/// Creates an expression `Stmt` for multiplying two numbers.
		/// 
		/// This method only exists during testing.
		pub fn mul(lhs: i64, rhs: i64) -> Self {
			Stmt::Expr(
				Expr::Mul(
					Box::new(Expr::Int(lhs)),
					Box::new(Expr::Int(rhs)),
				)
			)
		}
		
		/// Creates an expression `Stmt` for dividing two numbers.
		/// 
		/// This method only exists during testing.
		pub fn div(lhs: i64, rhs: i64) -> Self {
			Stmt::Expr(
				Expr::Div(
					Box::new(Expr::Int(lhs)),
					Box::new(Expr::Int(rhs)),
				)
			)
		}
		
		/// Creates a `Stmt` for assigning a number to a variable.
		/// 
		/// This method only exists during testing.
		pub fn set(lhs: char, rhs: i64) -> Self {
			Stmt::Set(lhs, Expr::Int(rhs))
		}
	}
	
	#[test]
	fn parse_add() {
		let tree = Root::from_str("4 2 +");
		assert_eq!(tree, Ok(Root::from_stmt(Stmt::add(4, 2))));
	}
	
	#[test]
	fn parse_sub() {
		let tree = Root::from_str("4 2 -");
		assert_eq!(tree, Ok(Root::from_stmt(Stmt::sub(4, 2))));
	}
	
	#[test]
	fn parse_mul() {
		let tree = Root::from_str("4 2 *");
		assert_eq!(tree, Ok(Root::from_stmt(Stmt::mul(4, 2))));
	}
	
	#[test]
	fn parse_div() {
		let tree = Root::from_str("4 2 /");
		assert_eq!(tree, Ok(Root::from_stmt(Stmt::div(4, 2))));
	}
	
	#[test]
	fn parse_set() {
		let tree = Root::from_str("a 1 =");
		assert_eq!(tree, Ok(Root::from_stmt(Stmt::set('a', 1))));
	}
	
	#[test]
	fn parse_error1() {
		assert!(Root::from_str("1 2 ^").is_err());
	}
	
	#[test]
	fn parse_error2() {
		assert!(Root::from_str("1 2 3 + ").is_err());
	}
	
	#[test]
	fn parse_error3() {
		assert!(Root::from_str("1 2 + *").is_err());
	}
	
	#[test]
	fn parse_error4() {
		assert!(Root::from_str("1 1 =").is_err());
	}
}
