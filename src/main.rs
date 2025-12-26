use math::*;

fn main() -> UnitResult {
    logic::axioms()?;
    peano::axioms()?;
    let args: Vec<String> = std::env::args().collect();
    let input_file = if args.len() == 2 {
        &args[1]
    } else {
        "example.ll"
    };
    let tokens = preprocessor::preprocess(input_file)?;
    let tokens = preprocessor::strip_macro_definitions(tokens);
    let tokens = preprocessor::apply_abbreviations(tokens);
    format::write_formatted_file(&tokens, "preprocessed.ll");
    let mut interpreter = interpreter::Interpreter::new();
    interpreter.interpret(tokens.into_iter())?;
    println!("Hello, world!");
    Ok(())
}
