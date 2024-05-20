use std::fmt;
use logos::Logos;
use crate::lexer::Lexer;

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