use std::path::Path;
use std::{env, fs};

use similar::TextDiff;

fn run_test(input_path: &str, output_ext: &str, is_err: bool, run: impl FnOnce(&str) -> String) {
    let input = fs::read_to_string(input_path).expect("failed to read input");
    let output_path = Path::new(input_path).with_extension(output_ext);

    let actual_output = run(&input);

    let check_err = env::var("C1_TEST_CHECK_ERR").is_ok_and(|value| value == "1");
    if is_err && !check_err {
        return;
    }

    let bless = env::var("C1_TEST_BLESS").is_ok_and(|value| value == "1");

    if bless {
        fs::write(&output_path, actual_output).expect("failed to write output");
    } else {
        let expected_output = fs::read_to_string(&output_path).unwrap_or_else(|err| {
            let check_err_var = if check_err {
                "C1_TEST_CHECK_ERR=1 "
            } else {
                ""
            };
            panic!(
                "failed to read test output file \"{}\": {err}\n\
                help: run `C1_TEST_BLESS=1 {check_err_var}cargo test` to create the file.",
                output_path.display(),
            )
        });
        if expected_output != actual_output {
            // println!(">>> EXPECTED OUTPUT <<<");
            // println!("{expected_output}");
            // println!(">>> ACTUAL OUTPUT <<<");
            // println!("{actual_output}");
            // println!(">>> DIFF <<<");
            let diff = TextDiff::from_lines(&expected_output, &actual_output);
            println!("{}", diff.unified_diff().missing_newline_hint(false));
            panic!("test output differs");
        }
    }
}

pub fn run_test_ok(input_path: &str, output_ext: &str, run: impl FnOnce(&str) -> String) {
    run_test(input_path, output_ext, false, run);
}

pub fn run_test_err(input_path: &str, run: impl FnOnce(&str) -> String) {
    run_test(input_path, "err", true, run);
}
