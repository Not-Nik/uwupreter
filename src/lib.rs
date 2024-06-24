#![forbid(unsafe_code)]

pub mod analysis;
pub mod ast;
pub mod lexer;
pub mod token;

pub use analysis::analyze;
pub use ast::parse;
