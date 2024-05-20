//! The C1 lexical analysis, implemented with the lexer generator [Logos](`logos`).
//!
//! The lexical analysis splits the source code into a steam of *tokens*, including
//! keywords, operators, literals, and identifiers.
//!
//! The centerpiece of this module is the [`Token`] enum, which defines all C1 tokens
//! with their respective regular expressions.
//!
//! # Examples
//!
//! Using the [`Lexer`] to iterate over the [`Token`]s in a string, skipping over all
//! whitespace and comments:
//!
//! ```rust
//! use uwupreter::lexer::Lexer;
//! use uwupreter::token::Token;
//!
//! let input = "int answer = 42;";
//! let lexer = Lexer::new(input);
//!
//! let mut tokens = Vec::new();
//! for token in lexer {
//!     println!("{:?}", token);
//!     tokens.push(token);
//! }
//!
//! assert_eq!(tokens, [
//!     Ok((0, Token::KwInt, 3)),
//!     Ok((4, Token::Ident("answer".to_owned()), 10)),
//!     Ok((11, Token::Assign, 12)),
//!     Ok((13, Token::IntLiteral(42), 15)),
//!     Ok((15, Token::Semicolon, 16)),
//! ]);
//! ```
//!
//! If an unknown token is encountered, an error is returned by the iterator:
//!
//! ```rust
//! use uwupreter::lexer::{Lexer, LexicalError};
//! use uwupreter::token::Token;
//!
//! let input = "100%";
//! let lexer = Lexer::new(input);
//!
//! let mut tokens = Vec::new();
//! for token in lexer {
//!     println!("{:?}", token);
//!     tokens.push(token);
//! }
//!
//! assert_eq!(tokens, [
//!     Ok((0, Token::IntLiteral(100), 3)),
//!     Err(LexicalError {
//!         text: "%".to_owned(),
//!         span: 3..4,
//!     }),
//! ]);
//! ```

use std::fmt;

use logos::{Logos, SpannedIter};
use crate::token::Token;

/// An error that occurred during lexing.
#[derive(Debug, Clone, PartialEq)]
pub struct LexicalError {
    /// The part of the input that could not be lexed.
    pub text: String,
    /// The location of the error in the input.
    ///
    /// Represented as byte offset from the beginning of the input.
    pub span: logos::Span,
}

impl fmt::Display for LexicalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Cannot lex token `{}` found at {}:{}",
            self.text, self.span.start, self.span.end,
        )
    }
}

/// Holds the state of the lexical analyzer.
pub struct Lexer<'input> {
    /// The iterator over tokens including their spans (locations).
    token_stream: SpannedIter<'input, Token>,
}

impl<'input> Lexer<'input> {
    /// Construct a new `Lexer` from an input string holding the source code.
    pub fn new(input: &'input str) -> Self {
        // The `Token::lexer()` method is provided by the `Logos` derive macro.
        Self {
            token_stream: Token::lexer(input).spanned(),
        }
    }
}

/// Adapts the iterator provided by Logos for use with LALRPOP.
impl<'input> Iterator for Lexer<'input> {
    /// The iterator returns a [`Token`] plus its start and end position, or an error.
    ///
    /// This format is required by LALRPOP, the parser generator that we will use.
    type Item = Result<(usize, Token, usize), LexicalError>;

    fn next(&mut self) -> Option<Self::Item> {
        let (token_or_err, span) = self.token_stream.next()?;

        // Convert from the Logos format to the LALRPOP format.
        let token_or_err = match token_or_err {
            Ok(token) => Ok((span.start, token, span.end)),
            Err(()) => Err(LexicalError {
                text: self.token_stream.slice().to_owned(),
                span,
            }),
        };

        Some(token_or_err)
    }
}
