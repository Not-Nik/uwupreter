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
//! use uwupreter::lexer::{Lexer, Token};
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
//! use uwupreter::lexer::{Lexer, Token, LexicalError};
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

/// The [`Lexer`] turns a string (`&str`) into a stream of `Token`s.
///
/// Possible tokens include
/// - keywords, e.g. `bool` or `for`
/// - combined punctuation symbols, e.g. `+` or `==` or `{`
/// - literals, e.g. `42` `3.14` or `false` or `"hello"`, but not `-1` (which is two separate tokens)
/// - identifiers, e.g. `foo`
/// - whitespace, e.g. spaces or tabs
/// - comments
///
/// Every token has an associated *regular expression* that matches the token.
///
/// Note that whitespace and comments will not be returned by the [`Lexer`].
#[derive(Logos, Debug, Clone, PartialEq)]
pub enum Token {

    #[token("bool")]
    KwBool,

    #[token("do")]
    KwDo,

    #[token("else")]
    KwElse,

    #[token("float")]
    KwFloat,

    #[token("for")]
    KwFor,

    #[token("if")]
    KwIf,

    #[token("int")]
    KwInt,

    #[token("print")]
    KwPrint,

    #[token("return")]
    KwReturn,

    #[token("void")]
    KwVoid,

    #[token("while")]
    KwWhile,

    #[token("+")]
    Add,

    #[token("-")]
    Sub,

    #[token("*")]
    Mul,

    #[token("/")]
    Div,

    #[token("=")]
    Assign,

    #[token("==")]
    Eq,

    #[token("!=")]
    Neq,

    #[token("<")]
    Lt,

    #[token(">")]
    Gt,

    #[token("<=")]
    Leq,

    #[token(">=")]
    Geq,

    #[token("&&")]
    LogAnd,

    #[token("||")]
    LogOr,

    #[token(",")]
    Comma,

    #[token(";")]
    Semicolon,

    #[token("(")]
    LParen,

    #[token(")")]
    RParen,

    #[token("{")]
    LBrace,

    #[token("}")]
    RBrace,

    #[regex("[0-9]+", |lex| lex.slice().parse::<i64>().unwrap())]
    IntLiteral(i64),

    //#[regex(r"([0-9]*\.[([0-9]+)|([0-9]+[e|E][-|+]?[0-9]+)])", |lex| lex.slice().parse::<f64>().unwrap())] ignowiewe diesen vewsuch
    #[regex(r"[0-9]*\.[0-9]+", |lex| lex.slice().parse::<f64>().unwrap())]
    #[regex(r"[0-9]*\.[0-9]+e[\+|-]?[0-9]+", |lex| lex.slice().parse::<f64>().unwrap())]
    #[regex(r"[0-9]+E[\+|-]?[0-9]+", |lex| lex.slice().parse::<f64>().unwrap())]
    FloatLiteral(f64),

    #[token("false", |_| false)]
    #[token("true", |_| true)]
    BoolLiteral(bool),

    //#[regex("\"[a-z|A-Z|\\\"| ]*\"", |lex| lex.slice().to_owned())] ignowiewe diesen vewsuch
    #[regex("\"[^.|\"]*\"", |lex| lex.slice().to_owned())]
    StringLiteral(String),

    #[regex("[a-z|A-Z|_]+[a-z|A-Z|_|0-9]*", |lex| lex.slice().to_owned())]
    Ident(String),

    //#[regex(r"/\*[^(/\*)]+\*/", logos::skip)] ignowiewe diesen vewsuch
    #[regex(r"/\*([^*]?|\*[^/])*\*/", logos::skip)]
    BlockComment,

    #[regex("//[.]*", logos::skip)]
    LineComment,

    #[regex(r"[ \t\n\f]+", logos::skip)]
    Whitespace,
}

/// Pretty-printing of the tokens. This is used for error messages.
impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::KwBool => f.write_str("bool"),
            Token::KwDo => f.write_str("do"),
            Token::KwElse => f.write_str("else"),
            Token::KwFloat => f.write_str("float"),
            Token::KwFor => f.write_str("for"),
            Token::KwIf => f.write_str("if"),
            Token::KwInt => f.write_str("int"),
            Token::KwPrint => f.write_str("print"),
            Token::KwReturn => f.write_str("return"),
            Token::KwVoid => f.write_str("void"),
            Token::KwWhile => f.write_str("while"),
            Token::Add => f.write_str("+"),
            Token::Sub => f.write_str("-"),
            Token::Mul => f.write_str("*"),
            Token::Div => f.write_str("/"),
            Token::Assign => f.write_str("="),
            Token::Eq => f.write_str("=="),
            Token::Neq => f.write_str("!="),
            Token::Lt => f.write_str("<"),
            Token::Gt => f.write_str(">"),
            Token::Leq => f.write_str("<="),
            Token::Geq => f.write_str(">="),
            Token::LogAnd => f.write_str("&&"),
            Token::LogOr => f.write_str("||"),
            Token::Comma => f.write_str(","),
            Token::Semicolon => f.write_str(";"),
            Token::LParen => f.write_str("("),
            Token::RParen => f.write_str(")"),
            Token::LBrace => f.write_str("{"),
            Token::RBrace => f.write_str("}"),
            Token::IntLiteral(value) => write!(f, "{value}"),
            Token::FloatLiteral(value) => write!(f, "{value}"),
            Token::BoolLiteral(value) => write!(f, "{value}"),
            Token::StringLiteral(value) => write!(f, "\"{value}\""),
            Token::Ident(ident) => write!(f, "identifier `{ident}`"),
            Token::BlockComment => f.write_str("block comment"),
            Token::LineComment => f.write_str("line comment"),
            Token::Whitespace => f.write_str("whitespace"),
        }
    }
}

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
