mod util;

mod cases {
    include!(concat!(env!("OUT_DIR"), "/cases_analysis.rs"));
}

fn run_test_ok(path: &str) {
    util::run_test_ok(path, "analysis", |input| {
        let mut ast = uwupreter::parse(input).expect("parsing failed");
        let analysis = uwupreter::analyze(&mut ast).expect("analysis failed");
        format!("{analysis:#?}")
    });
    util::run_test_ok(path, "ast-resolved", |input| {
        let mut ast = uwupreter::parse(input).expect("parsing failed");
        let _analysis = uwupreter::analyze(&mut ast).expect("analysis failed");
        format!("{ast:#?}")
    });
}

fn run_test_err(path: &str) {
    util::run_test_err(path, |input| {
        let mut ast = uwupreter::parse(input).expect("parsing failed");
        let err = uwupreter::analyze(&mut ast).expect_err("analysis passed");
        format!("{err}")
    });
}
