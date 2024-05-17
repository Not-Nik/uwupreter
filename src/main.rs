use std::{env, fs};
use logos::Logos;
use c1::lexer::Token;

fn main() {
    let args: Vec<_> = env::args().collect();
    let path = match args.get(1) {
        None => "tests/inputs/ok/demorgan.c1",
        Some(path) => path
    };
    let input = fs::read_to_string(path).expect("input file should exist");
    let mut lexer = Token::lexer(input.as_str());

    while let Some(val) = lexer.next() {
        println!("{:?}: {:?}", val, lexer.slice());
    }
}