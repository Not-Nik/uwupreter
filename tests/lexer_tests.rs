use uwupreter::lexer::Token::{self, *};
use logos::Logos;

#[test]
fn empty_stream() {
    let token = Token::lexer("").next();
    assert_eq!(token, None);
}

#[test]
fn bool_literals() {
    for (input, output) in [
        ("true", BoolLiteral(true)),
        ("false", BoolLiteral(false))
    ] {
        let token = Token::lexer(input).next();
        assert_eq!(token, Some(Ok(output)));
    }
}

#[test]
fn float_literals() {
    for (input, output) in [
        ("1.0", FloatLiteral(1.0)),
        (".01", FloatLiteral(0.01)),
        ("3.1e-12", FloatLiteral(3.1e-12)),
        ("2E3", FloatLiteral(2E3)),
    ] {
        let token = Token::lexer(input).next();
        assert_eq!(token, Some(Ok(output)));
    }
}

#[test]
fn int_literals() {
    for (input, output) in [
        ("13", IntLiteral(13)),
        ("001", IntLiteral(001)),
    ] {
        let token = Token::lexer(input).next();
        assert_eq!(token, Some(Ok(output)));
    }
}

#[test]
fn string_literals() {
    for (input, output) in [
        ("\"\"", StringLiteral(String::new())),
        ("\"Hallo\"", StringLiteral("Hallo".to_owned())),
    ] {
        let token = Token::lexer(input).next();
        assert_eq!(token, Some(Ok(output)));
    }
}

#[test]
fn identifiers() {
    for (input, output) in [
        ("Lexer", Ident("Lexer".to_owned())),
        ("is_power_of_two", Ident("is_power_of_two".to_owned())),
        ("LOG_2", Ident("LOG_2".to_owned())),
        ("_unused_ident", Ident("_unused_ident".to_owned())),
    ] {
        let token = Token::lexer(input).next();
        assert_eq!(token, Some(Ok(output)));
    }
}

#[test]
fn keywords() {
    for (input, output) in [
        ("bool", KwBool),
        ("do", KwDo),
        ("else", KwElse),
        ("for", KwFor),
        ("float", KwFloat),
        ("if", KwIf),
        ("int", KwInt),
        ("print", KwPrint),
        ("return", KwReturn),
        ("void", KwVoid),
        ("while", KwWhile),
    ] {
        let token = Token::lexer(input).next();
        assert_eq!(token, Some(Ok(output)));
    }
}

#[test]
fn operators() {
    for (input, output) in [
        ("+", Add),
        ("-", Sub),
        ("*", Mul),
        ("/", Div),
        ("=", Assign),
        ("==", Eq),
        ("!=", Neq),
        ("<", Lt),
        (">", Gt),
        ("<=", Leq),
        (">=", Geq),
        ("&&", LogAnd),
        ("||", LogOr),
    ] {
        let token = Token::lexer(input).next();
        assert_eq!(token, Some(Ok(output)));
    }
}

#[test]
fn separators() {
    for (input, output) in [
        (";", Semicolon),
        (",", Comma),
        ("(", LParen),
        (")", RParen),
        ("{", LBrace),
        ("}", RBrace),
    ] {
        let token = Token::lexer(input).next();
        assert_eq!(token, Some(Ok(output)));
    }
}

#[test]
fn unclosed_c_comment() {
    let token = Token::lexer("/*").next();
    assert_eq!(token, Some(Err(())));
}

#[test]
fn illegal_character() {
    let mut lexer = Token::lexer("100%");
    assert_eq!(lexer.next(), Some(Ok(Token::IntLiteral(100))));
    assert_eq!(lexer.next(), Some(Err(())));
}
