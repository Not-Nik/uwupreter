mod util;

mod cases {
    include!(concat!(env!("OUT_DIR"), "/cases_interpreter.rs"));
}

fn run_test_ok(path: &str) {
    util::run_test_ok(path, "output", |input| {
        let mut ast = uwupreter::parse(input).expect("parsing failed");
        let analysis = uwupreter::analyze(&mut ast).expect("analysis failed");
        uwupreter::interpret(&ast, &analysis).expect("interpreting failed")
    });
}

fn run_test_err(path: &str) {
    util::run_test_err(path, |input| {
        let mut ast = uwupreter::parse(input).expect("parsing failed");
        let analysis = uwupreter::analyze(&mut ast).expect("analysis failed");
        let err = uwupreter::interpret(&ast, &analysis).expect_err("interpreting passed");
        format!("{err}")
    });
}
