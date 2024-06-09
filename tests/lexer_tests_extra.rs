use logos::Logos;
use proptest::{collection::vec, prelude::*};

use uwupreter::token::Token::{self, *};

proptest! {
    #[test]
    fn int_test(val in 0i64..i64::MAX) {
        let output = IntLiteral(val);
        let token = Token::lexer(&val.to_string()).next();
        prop_assert_eq!(token, Some(Ok(output)));
    }

    #[test]
    fn float_test(val in r"([0-9]*\.[0-9]+([eE][-+]?[0-9]+)?)|([0-9]+[eE][-+]?[0-9]+)") {
        let input = val.parse::<f64>().unwrap();
        let output = FloatLiteral(input);
        let token = Token::lexer(&val).next();
        prop_assert_eq!(token, Some(Ok(output)));
    }

    #[test]
    fn str_test(val in "\"[^\n\"]*\"") {
        let output = StringLiteral(val[1..val.len()-1].to_string());
        let token = Token::lexer(&val).next();
        prop_assert_eq!(token, Some(Ok(output)));
    }

    #[test]
    fn ident_test(val in "[a-zA-Z_][0-9a-zA-Z_]*") {
        let output = Ident(val.clone());
        let token = Token::lexer(&val).next();
        prop_assert_eq!(token, Some(Ok(output)));
    }

    #[test]
    fn cpp_comment_test(val in "//[^\n]*\n") {
        let token = Token::lexer(&val).next();
        prop_assert!(token.is_none());
    }

    #[test]
    fn c_comment_test(val in r"/\*/*(\*|[^/\*][^\*]*\*)+/") {
        let token = Token::lexer(&val).next();
        prop_assert!(token.is_none());
    }

    #[test]
    fn whitespace_test(val in r"[ \t\n\f]+") {
        let token = Token::lexer(&val).next();
        prop_assert!(token.is_none());
    }

    #[test]
    fn full_program_test(v in vec(0u32..=34, 1..100)) {
        let (input, output): (Vec<_>, Vec<_>) = v.into_iter().map(|selector| match selector {
             0 => ("bool", KwBool),
             1 => ("do", KwDo),
             2 => ("else", KwElse),
             3 => ("float", KwFloat),
             4 => ("for", KwFor),
             5 => ("if", KwIf),
             6 => ("int", KwInt),
             7 => ("print", KwPrint),
             8 => ("return", KwReturn),
             9 => ("void", KwVoid),
            10 => ("while", KwWhile),
            11 => ("+", Add),
            12 => ("-", Sub),
            13 => ("*", Mul),
            14 => ("/", Div),
            15 => ("=", Assign),
            16 => ("==", Eq),
            17 => ("!=", Neq),
            18 => ("<", Lt),
            19 => (">", Gt),
            20 => ("<=", Leq),
            21 => (">=", Geq),
            22 => ("&&", LogAnd),
            23 => ("||", LogOr),
            24 => (",", Comma),
            25 => (";", Semicolon),
            26 => ("(", LParen),
            27 => (")", RParen),
            28 => ("{", LBrace),
            29 => ("}", RBrace),
            30 => ("123", IntLiteral(123)),
            31 => ("1.0", FloatLiteral(1.0)),
            32 => ("true", BoolLiteral(true)),
            33 => ("\"string\"", StringLiteral("string".to_string())),
            34 => ("ident", Ident("ident".to_string())),
            _ => unreachable!(),
        }).unzip();

        for (parsed, expected) in Token::lexer(&input.join(" ")).zip(output) {
            prop_assert_eq!(parsed, Ok(expected));
        }
    }
}
