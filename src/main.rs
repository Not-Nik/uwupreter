use syntree::{Root, Calculator, Printer};

fn main() -> Result<(), String> {
	// collect the command line arguments
	let args: Vec<String> = std::env::args().collect();
	let expr = args.get(1).map_or("12+", |e| e);
	
	// parse out the parse tree
	let tree = match Root::from_str(expr) {
		Ok(root) => root,
		Err(err) => return Err(err.to_string())
	};
	
	// use the pretty-printer for output
	let mut printer = Printer::default();
	println!("{}", printer.format(&tree));
	
	// use the calculator for evaluation
	let mut calc = Calculator::default();
	println!("{}", calc.calc(&tree));
	
	// return success
	Ok(())
}
