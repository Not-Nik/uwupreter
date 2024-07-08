#![forbid(unsafe_code)]
// Use `--document-private-items` to show private docs!
#![allow(rustdoc::private_intra_doc_links)]

pub mod analysis;
pub mod ast;
pub mod interpreter;
pub mod lexer;
pub mod token;

pub use analysis::analyze;
pub use ast::parse;
pub use interpreter::interpret;
