use uwupreter::{analyze, parse};
use std::{env, fs, process::ExitCode};

fn main() -> ExitCode {
    let mut args = env::args();

    if args.len() < 2 {
        println!(
            "Usage: {} <c1-source>",
            args.next().as_deref().unwrap_or("uwupreter")
        );
        return ExitCode::FAILURE;
    }

    // Read the source file into a string.
    let input = match fs::read_to_string(args.nth(1).unwrap()) {
        Ok(input) => input,
        Err(err) => {
            println!("failed to read c1 source file: {err}");
            return ExitCode::FAILURE;
        }
    };

    // Parse the source code into an AST.
    let mut ast = match parse(&input) {
        Ok(ast) => {
            println!("[✓] syntax");
            ast
        }
        Err(err) => {
            println!("[x] syntax");
            println!("{err}");
            return ExitCode::FAILURE;
        }
    };

    // Run semantic analysis on the AST, writing resolutions into the AST,
    // and collecting auxiliary information required for interpretation.
    let analysis = match analyze(&mut ast) {
        Ok(analysis) => {
            println!("[✓] analysis");
            analysis
        }
        Err(err) => {
            println!("[x] analysis");
            println!("{err}");
            return ExitCode::FAILURE;
        }
    };

    print!("{analysis:?}");

    ExitCode::SUCCESS
}
