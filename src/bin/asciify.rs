use core::panic;
use math::format;

// Run with cargo run --bin formatter [input_file]
fn main() {
    // Select input file from command line arguments.
    let args: Vec<String> = std::env::args().collect();
    let input_file = if args.len() == 2 {
        &args[1]
    } else {
        panic!("Usage: asciify [input_file]");
    };
    format::format_file(input_file, input_file, /*as_ascii=*/ true);
}
