mod util;

mod cases {
    include!(concat!(env!("OUT_DIR"), "/cases_parser.rs"));
}

fn run_test_ok(path: &str) {
    util::run_test_ok(path, "ast", |input| {
        let ast = uwupreter::parse(input).expect("parsing failed");
        format!("{ast:#?}")
    });
}

fn run_test_err(path: &str) {
    util::run_test_err(path, |input| {
        let err = uwupreter::parse(input).expect_err("parsing passed");
        format!("{err}")
    });
}
